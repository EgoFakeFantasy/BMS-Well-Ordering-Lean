import BMSConstructibleBridge.PowerlessBMSTransitiveImage

/-!
# 传递类像替换的原 Z₂ 对象模式

显式量化内部 ω，所有参数全称闭包。对每个实际纯公式，原 Z₂ 证明：总单值
映射若输出类传递，其精确值域为集合。该模式仍不等于完整 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSTransitiveImageDerives

open Logic FirstOrder PowerlessBMSQuotientCoding PowerlessBMSQuotientSubsetImageDerives

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def total_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here)
    (ω.weakenBound SetTheory.SetSort.set))
    (.existsE .set (at_m φ (.bvar (.there .here)) (.bvar .here))))

def transitive_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.forallE .set (.imp
    (.conj (at_m (PowerlessBMSQuotientBoundedImage.range_m φ)
      ((ω.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)
      (.bvar (.there .here)))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))
    (at_m (PowerlessBMSQuotientBoundedImage.range_m φ)
      ((ω.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set) (.bvar .here))))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set (
    let ω : Term ℒ [.set] Δ .set := .bvar .here
    .imp (SecondOrderOmegaSyntax.omega_m ω)
      (.imp (.conj (total_m φ ω) (.conj (unique_m φ ω) (transitive_m φ ω)))
        (.existsE .set (image_m φ (ω.weakenBound SetTheory.SetSort.set) (.bvar .here)))))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

theorem schema_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) :
    (schema_m φ).satisfies η ↔ ∀ ω : SecondOrderQuotient.type_l hℳ,
      SecondOrderOmega.omega_l hℳ ω →
      (∀ x, SecondOrderQuotient.mem_l hℳ x ω → ∃ y, φ.satisfies ((η.pushFree x).pushFree y)) →
      (∀ x y z, SecondOrderQuotient.mem_l hℳ x ω →
        φ.satisfies ((η.pushFree x).pushFree y) →
        φ.satisfies ((η.pushFree x).pushFree z) → y = z) →
      (∀ y z, (∃ x, SecondOrderQuotient.mem_l hℳ x ω ∧
        φ.satisfies ((η.pushFree x).pushFree y)) → SecondOrderQuotient.mem_l hℳ z y →
        ∃ x, SecondOrderQuotient.mem_l hℳ x ω ∧ φ.satisfies ((η.pushFree x).pushFree z)) →
      ∃ B, ∀ y, SecondOrderQuotient.mem_l hℳ y B ↔
        ∃ x, SecondOrderQuotient.mem_l hℳ x ω ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  simp only [schema_m, total_m, unique_m, transitive_m, image_m, Formula.satisfies,
    SecondOrderOmegaSyntax.omega_l, at_formula_l, PowerlessBMSQuotientBoundedImage.range_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval,
    parameters_pushBound_l, parameters_empty_l, and_imp]
  rfl

theorem models_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) : (schema_m φ).satisfies η := by
  apply (schema_formula_l hℳ φ η).mpr
  intro ω hω hTotal hUnique hTrans
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  obtain rfl := SecondOrderOmega.unique_l hℳ hω C.omega_spec
  have hTrans' n y (hy : φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y))
      z (hz : SecondOrderQuotient.mem_l hℳ z y) :
      ∃ m, φ.satisfies ((η.pushFree (numberCode_l C m).val).pushFree z) := by
    obtain ⟨x, hx, hφ⟩ := hTrans y z ⟨(numberCode_l C n).val, (numberCode_l C n).property, hy⟩ hz
    obtain ⟨m, hm⟩ := numberCode_surjective_l C ⟨x, hx⟩
    have hm' : (numberCode_l C m).val = x := congrArg Subtype.val hm
    exact ⟨m, hm'.symm ▸ hφ⟩
  obtain ⟨B, hB⟩ := PowerlessBMSTransitiveImage.exists_l C φ η
    (fun n => hTotal _ (numberCode_l C n).property)
    (fun n y z => hUnique _ y z (numberCode_l C n).property) hTrans'
  refine ⟨B, fun y => (hB y).trans ?_⟩
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨(numberCode_l C n).val, (numberCode_l C n).property, hn⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨x, hx⟩
    have hn' : (numberCode_l C n).val = x := congrArg Subtype.val hn
    exact ⟨n, hn'.symm ▸ hxy⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  exact (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr (models_l hℳ φ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSTransitiveImageDerives
