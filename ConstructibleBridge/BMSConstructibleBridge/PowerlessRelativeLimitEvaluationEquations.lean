import BMSConstructibleBridge.PowerlessFiniteEvaluationEquations

/-! # 极限层内实际稳定查询的四分支对象方程

由内部有限历史存在性消去预设求值方程这一条件，只保留层界、静态
编码规格、标签和单射性。不要求全体 C 值序列集属于 C，也不预设完整源模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationEquations

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def schema_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let w (t : Term ℒ [] Δ .set) := up (up (up t))
  PowerlessRelativeLimitEvaluationEquation.guarded_m ω e N T A S
    (.imp (PowerlessEvaluationTags.tags_m (w e) (w t₁) (w t₂) (w t₃)) <|
      .imp (PowerlessRelativeClassConstructorInjective.injective_m (w ω) (w e) (w T))
        (PowerlessFiniteEvaluationEquations.equations_m (.bvar .here)
          (w ω) (w e) (w N) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃)))

def sentence_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω e N T A S t₁ t₂ t₃)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    (sentence_m ω e N T A S t₁ t₂ t₃).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η B β C hBase hC hLimit hParams hSC hω hωC he hN hT hS hBounds hTags hInjective
  let ξ := ((η.pushBound B).pushBound β).pushBound C
  let w (t : Term ℒ [] Δ .set) := up (up (up t))
  have hRecursion := ((_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeLimitEvaluationEquation.models_l hℳ ω e N T A S t₁ t₂ t₃))
      η B β C hBase hC hLimit hParams hSC hω hωC he hN hT hS hBounds
  have hEquation := (PowerlessRelativeLimitEvaluationEquation.conclusion_formula_l ξ
    (.bvar .here) (w ω) (w e) (w N) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃)).mp hRecursion
  have hTags' := (PowerlessEvaluationTags.tags_formula_l ξ (w e) (w t₁) (w t₂) (w t₃)).mp hTags
  have hInjective' := (PowerlessRelativeClassConstructorInjective.injective_formula_l ξ (w ω) (w e) (w T)).mp hInjective
  apply (PowerlessFiniteEvaluationEquations.equations_formula_l ξ (.bvar .here)
    (w ω) (w e) (w N) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃)).mpr
  exact PowerlessFiniteEvaluationEquations.equations_of_recursion_l hℳ hTags' hInjective' hEquation

theorem derives_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω e N T A S t₁ t₂ t₃)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω e N T A S t₁ t₂ t₃)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationEquations
