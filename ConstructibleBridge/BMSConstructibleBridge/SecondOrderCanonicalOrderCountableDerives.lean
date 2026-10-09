import BMSConstructibleBridge.SecondOrderCanonicalOrderUniformDerives
import BMSConstructibleBridge.PowerlessRelativeClassMemberDefCountability

/-! # 实际枚举母集的规范 Def 后继仍类内可数

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m；出口是
GraphTranslation 后的原 Derives。输入枚举图必须实际属于相对类，原 Def
对象也须已经属于类。输出同时保留规范后继、环境良序、旧序初段、唯一性
和 Def 的类内可数性。不从逐阶段存在性推断统一枚举历史或层界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderCountableDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderCanonicalOrderUniform (step_m step_l step_formula_l)
open PowerlessRelativeHierarchySyntax (class_m)
open PowerlessMemberDefClosureDerives (transitive_m transitive_formula_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

/-- 同一编码包先于所有母集和实际枚举图；见证只在 Prop 中消去。 -/
theorem class_total_l {ω : type_l hℳ B} (hΩ : omega_l (ℳ := ClassModel) ω) :
    ∃ e t₁ t₂ t₃ Pair Valid : type_l hℳ B,
      ∀ A P D G : type_l hℳ B, wellOrder_l (ℳ := 𝒱) A.val P.val →
        (∀ x y, SecondOrderQuotient.mem_l hℳ x A.val → SecondOrderQuotient.mem_l hℳ y x →
          SecondOrderQuotient.mem_l hℳ y A.val) → SecondOrderMemberDef.spec_l hℳ A.val D.val →
        map_l (ℳ := 𝒱) G.val ω.val A.val →
        (∀ x, SecondOrderQuotient.mem_l hℳ x A.val → ∃ i,
          SecondOrderQuotient.mem_l hℳ i ω.val ∧ value_l (ℳ := 𝒱) G.val i x) →
        ∃ E : type_l hℳ B,
          step_l (ℳ₀ := 𝒱) ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D.val E.val ∧
          wellOrder_l (ℳ := 𝒱) D.val E.val ∧
          PowerlessRelativeOrdinalCutoff.countable_l B ω.val D.val ∧
          ∀ E' : SecondOrderQuotient.type_l hℳ,
            step_l (ℳ₀ := 𝒱) ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D.val E' →
              E' = E.val := by
  obtain ⟨K, V, hV, e, t₁, t₂, t₃, Pair, Valid, hω, he, hTags, hPairMap, hPair, hValid, hDomains⟩ :=
    PowerlessRelativeClassCanonicalOrderUniform.coding_exists_l hΩ
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hTags
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  intro A P D G hP hTrans hDef hG hOnto
  obtain ⟨E, ⟨hStep, hOrder, _, _⟩, _⟩ := PowerlessRelativeClassCanonicalOrderUniform.exists_unique_l
    K hΩ hP hω he hTags hPairMap hPair hV hValid (hDomains A) hTrans hDef
  have hRaw := SecondOrderCanonicalOrderUniform.step_ambient_l K hω he hPairMap hPair hStep
  obtain ⟨R, _, L, hCandidate, _⟩ := hStep
  have hCount := PowerlessRelativeClassMemberDefCountability.of_candidate_l hΩ
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G ω A).mpr hG)
    ((PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) G ω A).mpr hOnto) hCandidate
  exact ⟨E, hRaw, hOrder, hCount, fun E' hE' =>
    SecondOrderCanonicalOrderUniform.unique_l K hω he ht₁ ht₂ ht₃ hPairMap hPair hV hValid hE' hRaw⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up₄ t))

def mode_m {Γ Δ : SortContext ℒ} (B ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let A : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
    let P := .bvar (.there (.there .here))
    let D := .bvar (.there .here)
    let G := .bvar .here
    .imp (.conj (class_m (up₄ B) A) <| .conj (class_m (up₄ B) P) <|
      .conj (class_m (up₄ B) D) (class_m (up₄ B) G)) <|
      .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m A P) <|
        .imp (transitive_m A) <| .imp (PowerlessMemberDefSyntax.global_m A D) <|
          .imp (SecondOrderObjectSyntax.map_m G (up₄ ω) A) <|
            .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G (up₄ ω) A) <|
              .existsE .set <|
                let E : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
                let v (t : Term ℒ Γ Δ .set) := up (up₄ t)
                .conj (class_m (v B) E) <|
                  .conj (step_m (v ω) (up A) (up P) (v e) (v t₁) (v t₂) (v t₃) (v Pair) (v Valid) (up D) E) <|
                    .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (up D) E) <|
                      .conj (SecondOrderWellOrderCoherentUnionDerives.extension_m (up A) (up P) (up D) E) <|
                        .conj (PowerlessRelativeOrdinalCutoff.countable_m (v B) (v ω) (up D)) <|
                          .forallE .set <|
                            .imp (step_m (up (v ω)) (up (up A)) (up (up P)) (up (v e)) (up (v t₁))
                              (up (v t₂)) (up (v t₃)) (up (v Pair)) (up (v Valid)) (up (up D)) (.bvar .here))
                              (.equal (.bvar .here) (up E))

theorem mode_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) :
    (mode_m B ω e t₁ t₂ t₃ Pair Valid).satisfies η ↔
      ∀ A P D G : SecondOrderQuotient.type_l hℳ,
        (PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) A ∧
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) P ∧
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D ∧
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) G) →
        wellOrder_l (ℳ := 𝒱) A P →
        (∀ x y, SecondOrderQuotient.mem_l hℳ x A → SecondOrderQuotient.mem_l hℳ y x →
          SecondOrderQuotient.mem_l hℳ y A) → SecondOrderMemberDef.spec_l hℳ A D →
        map_l (ℳ := 𝒱) G (ω.eval η) A →
        (∀ x, SecondOrderQuotient.mem_l hℳ x A → ∃ i,
          SecondOrderQuotient.mem_l hℳ i (ω.eval η) ∧ value_l (ℳ := 𝒱) G i x) →
        ∃ E : SecondOrderQuotient.type_l hℳ,
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) E ∧
          step_l (ℳ₀ := 𝒱) (ω.eval η) A P (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
            (Pair.eval η) (Valid.eval η) D E ∧ wellOrder_l (ℳ := 𝒱) D E ∧
          SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) A P D E ∧
          PowerlessRelativeOrdinalCutoff.countable_l (B.eval η) (ω.eval η) D ∧
          ∀ E', step_l (ℳ₀ := 𝒱) (ω.eval η) A P (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
            (Pair.eval η) (Valid.eval η) D E' → E' = E := by
  simp only [mode_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, transitive_formula_l,
    PowerlessMemberDefDerives.formula_l K, step_formula_l, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    SecondOrderWellOrderCoherentUnionDerives.extension_formula_l,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, up₄, up, Term.eval_weakenBound, Term.eval]
  rfl

def total_m {Γ Δ : SortContext ℒ} (B ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (transitive_m B) <| .imp (class_m B ω) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        mode_m (up₆ B) (up₆ ω) (.bvar (.there (.there (.there (.there (.there .here))))))
          (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def schema_m : Formula ℒ [] [.set, .set] := total_m (.fvar .here) (.fvar (.there .here))
def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, total_m, Formula.satisfies, transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, omega_formula_l, mode_formula_l K,
    up₆, up₄, up, Term.eval_weakenBound, Term.eval]
  intro hBase hClass hω
  let B : SecondOrderQuotient.type_l hℳ := η.freeVal .here
  have hBase' : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
      ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B :=
    fun x hx y hy => hBase x y hx hy
  let ω : type_l hℳ B := ⟨η.freeVal (.there .here), hClass⟩
  have hΩ : omega_l (ℳ := structure_l hℳ B hBase') ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase') ω).mpr hω
  obtain ⟨e, t₁, t₂, t₃, Pair, Valid, hAll⟩ := class_total_l hΩ
  refine ⟨e.val, t₁.val, t₂.val, t₃.val, Pair.val, Valid.val, ?_⟩
  intro A P D G hGuards hP hTrans hDef hG hOnto
  let A' : type_l hℳ B := ⟨A, hGuards.1⟩
  let P' : type_l hℳ B := ⟨P, hGuards.2.1⟩
  let D' : type_l hℳ B := ⟨D, hGuards.2.2.1⟩
  let G' : type_l hℳ B := ⟨G, hGuards.2.2.2⟩
  obtain ⟨E, hStep, hOrder, hCount, hUnique⟩ := hAll A' P' D' G' hP hTrans hDef hG hOnto
  exact ⟨E.val, E.property, hStep, hOrder,
    SecondOrderCanonicalOrderPreservation.extension_l hStep hTrans hDef, hCount, hUnique⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms class_total_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderCountableDerives
