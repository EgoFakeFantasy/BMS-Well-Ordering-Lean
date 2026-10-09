import BMSConstructibleBridge.SecondOrderCanonicalOrderAmbientTotal
import BMSConstructibleBridge.SecondOrderCanonicalOrderUniformDerives

/-! # 去掉旧类输入守卫后的原 Z₂ 规范后继推导

同一六对象编码包先于所有环境 A、P、D 固定。输入只要求真正良序、
传递母集及原 Def 规格；输出保持初段且在全部环境候选中唯一。
辅助传递包仅在模型证明内按当次有限参数取得，不进入对象句子前提。
这是后继模式的原核 Derives，不是整个 BMS 良序模式的终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderAmbientDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderCanonicalOrderUniform (step_m step_l step_formula_l)
open PowerlessMemberDefClosureDerives (transitive_m transitive_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def mode_m {Γ Δ : SortContext ℒ} (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let A : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let P := .bvar (.there .here)
    let D := .bvar .here
    .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m A P) <|
      .imp (transitive_m A) <| .imp (PowerlessMemberDefSyntax.global_m A D) <|
        .existsE .set <|
          let E : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
          let v (t : Term ℒ Γ Δ .set) := up (up₃ t)
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
    (η : Env 𝒱 Γ Δ) (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) :
    (mode_m ω e t₁ t₂ t₃ Pair Valid).satisfies η ↔
      ∀ A P D : SecondOrderQuotient.type_l hℳ,
        wellOrder_l (ℳ := 𝒱) A P →
        (∀ x y, SecondOrderQuotient.mem_l hℳ x A → SecondOrderQuotient.mem_l hℳ y x →
          SecondOrderQuotient.mem_l hℳ y A) → SecondOrderMemberDef.spec_l hℳ A D →
        ∃ E : SecondOrderQuotient.type_l hℳ,
          step_l (ℳ₀ := 𝒱) (ω.eval η) A P (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
            (Pair.eval η) (Valid.eval η) D E ∧ wellOrder_l (ℳ := 𝒱) D E ∧
          SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) A P D E ∧
          ∀ E', step_l (ℳ₀ := 𝒱) (ω.eval η) A P (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
            (Pair.eval η) (Valid.eval η) D E' → E' = E := by
  simp only [mode_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, transitive_formula_l,
    SecondOrderWellOrderCoherentUnionDerives.extension_formula_l,
    PowerlessMemberDefDerives.formula_l K, step_formula_l,
    up₃, up, Term.eval_weakenBound, Term.eval]
  rfl

def total_m {Γ Δ : SortContext ℒ} (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        mode_m (up₆ ω) (.bvar (.there (.there (.there (.there (.there .here))))))
          (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def schema_m : Formula ℒ [] [.set] := total_m (.fvar .here)
def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, total_m, Formula.satisfies, omega_formula_l, mode_formula_l K₀,
    up₆, up₃, up, Term.eval_weakenBound, Term.eval]
  intro hω
  let ω : SecondOrderQuotient.type_l hℳ := η.freeVal .here
  obtain ⟨B, hBase, hωB, _⟩ := SecondOrderFiniteParameterEnvelope.exists_l hℳ ω []
  let ω' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨ω, PowerlessRelativeClassCorrespondence.base_l hℳ hBase hωB⟩
  have hΩ : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω' :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr hω
  obtain ⟨K, V, hV, e, t₁, t₂, t₃, Pair, Valid, hωEq, he, hTags, hPairMap, hPair, hValid, _⟩ :=
    PowerlessRelativeClassCanonicalOrderUniform.coding_exists_l hΩ
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hTags
  have hTagsRaw : PowerlessEvaluationTags.tags_l (ℳ := 𝒱) e.val t₁.val t₂.val t₃.val :=
    ⟨(PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp hTags.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e t₁).mp hTags.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₁ t₂).mp hTags.2.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₂ t₃).mp hTags.2.2.2⟩
  refine ⟨e.val, t₁.val, t₂.val, t₃.val, Pair.val, Valid.val, ?_⟩
  intro A P D hP hTrans hDef
  obtain ⟨E, hStep, hOrder, hExtension⟩ := SecondOrderCanonicalOrderAmbientTotal.exists_l
    K hωEq he hTagsRaw hPairMap hPair hV hValid hP hTrans hDef
  exact ⟨E, hStep, hOrder, hExtension, fun E' hE' =>
    SecondOrderCanonicalOrderUniform.unique_l K hωEq he ht₁ ht₂ ht₃ hPairMap hPair hV hValid hE' hStep⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms mode_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderAmbientDerives
