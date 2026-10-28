import BMSConstructibleBridge.SecondOrderCanonicalOrderPreservation
import BMSConstructibleBridge.PowerlessMemberDefClosureDerives

/-! # 全域共用编码包的规范 Def 后继：原 Z₂ 对象模式

对象语言是纯隶属 ℒ，正式出口是原 Z₂ 核中的同一图翻译 Derives。
输入限制到显式相对并类；良序、完整 Sat、规范步骤和任意候选唯一性
均解释于完整模型。六对象包存在量词在所有域之前，未抽取 Type 函数。
这里完成后继模式，不包括内部相容历史、统一界或最终 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderUniformDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderCanonicalOrderUniform (step_m step_l step_formula_l)
open PowerlessRelativeHierarchySyntax (class_m)
open PowerlessMemberDefClosureDerives (transitive_m transitive_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def mode_m {Γ Δ : SortContext ℒ} (B ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let A : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let P := .bvar (.there .here)
    let D := .bvar .here
    .imp (.conj (class_m (up₃ B) A) (.conj (class_m (up₃ B) P) (class_m (up₃ B) D))) <|
      .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m A P) <|
        .imp (transitive_m A) <| .imp (PowerlessMemberDefSyntax.global_m A D) <|
          .existsE .set <|
            let E : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
            let v (t : Term ℒ Γ Δ .set) := up (up₃ t)
            .conj (class_m (v B) E) <|
              .conj (step_m (v ω) (up A) (up P) (v e) (v t₁) (v t₂) (v t₃) (v Pair) (v Valid) (up D) E) <|
                .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (up D) E) <|
                  .conj (SecondOrderWellOrderCoherentUnionDerives.extension_m (up A) (up P) (up D) E) <|
                  .forallE .set <|
                    .imp (step_m (up (v ω)) (up (up A)) (up (up P)) (up (v e)) (up (v t₁))
                      (up (v t₂)) (up (v t₃)) (up (v Pair)) (up (v Valid)) (up (up D)) (.bvar .here))
                      (.equal (.bvar .here) (up E))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem mode_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) :
    (mode_m B ω e t₁ t₂ t₃ Pair Valid).satisfies η ↔
      ∀ A P D : SecondOrderQuotient.type_l hℳ,
        (PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) A ∧
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) P ∧
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D) →
        wellOrder_l (ℳ := 𝒱) A P →
        (∀ x y, SecondOrderQuotient.mem_l hℳ x A → SecondOrderQuotient.mem_l hℳ y x →
          SecondOrderQuotient.mem_l hℳ y A) → SecondOrderMemberDef.spec_l hℳ A D →
        ∃ E : SecondOrderQuotient.type_l hℳ,
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) E ∧
          step_l (ℳ₀ := 𝒱) (ω.eval η) A P (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
            (Pair.eval η) (Valid.eval η) D E ∧ wellOrder_l (ℳ := 𝒱) D E ∧
          SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) A P D E ∧
          ∀ E', step_l (ℳ₀ := 𝒱) (ω.eval η) A P (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
            (Pair.eval η) (Valid.eval η) D E' → E' = E := by
  simp only [mode_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, transitive_formula_l,
    SecondOrderWellOrderCoherentUnionDerives.extension_formula_l,
    PowerlessMemberDefDerives.formula_l K, step_formula_l,
    up₃, up, Term.eval_weakenBound, Term.eval]
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
    up₆, up₃, up, Term.eval_weakenBound, Term.eval]
  intro hBase hClass hω
  let B : SecondOrderQuotient.type_l hℳ := η.freeVal .here
  have hBase' : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
      ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B :=
    fun x hx y hy => hBase x y hx hy
  let ω : PowerlessRelativeClassStructure.type_l hℳ B := ⟨η.freeVal (.there .here), hClass⟩
  have hΩ : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase') ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase') ω).mpr hω
  obtain ⟨e, t₁, t₂, t₃, Pair, Valid, hAll⟩ := SecondOrderCanonicalOrderUniform.class_total_l hΩ
  refine ⟨e.val, t₁.val, t₂.val, t₃.val, Pair.val, Valid.val, ?_⟩
  intro A P D hGuards hP hTrans hDef
  let A' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨A, hGuards.1⟩
  let P' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨P, hGuards.2.1⟩
  let D' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨D, hGuards.2.2⟩
  obtain ⟨E, hStep, hOrder, hUnique⟩ := hAll A' P' D' hP hTrans hDef
  exact ⟨E.val, E.property, hStep, hOrder,
    SecondOrderCanonicalOrderPreservation.extension_l hStep hTrans hDef, hUnique⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderUniformDerives
