import BMSConstructibleBridge.PowerlessLevyZero
import BMSConstructibleBridge.PowerlessLevyGeneration

/-!
# 普通存在假式数码区分内部零层与第一层

对任意内部绑定槽的实际数码，证明第一层接受、零层拒绝。这里区分
的是数码的语法分类，不声称其真值不能由有界公式表达。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevySeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessLevyCertificate

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ i c : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hc : PowerlessFormulaConstructor.constructor_l ω e T t₃ i e c)

include hℳ hω ht hT hc

theorem first_l : class_l ω e T t₁ t₂ t₃ c t₁ e := by
  have he := (PowerlessEvaluationTags.natural_l hℳ hω ht).1
  have h₁ := (PowerlessEvaluationTags.natural_l hℳ hω ht).2.1
  have hb : class_l ω e T t₁ t₂ t₃ e e e :=
    PowerlessLevyCertificateClosure.base_l hℳ hω ht.1 hT he he (Or.inl rfl)
    (PowerlessBoundedCertificateClosure.zero_l hℳ hω ht.1)
  exact PowerlessLevyGeneration.existential_l hℳ hω ht hT h₁ ((ht.2.1 e).mpr (Or.inr rfl)) hb
    (Or.inl ⟨rfl, fun x hx => (ht.1 x hx).elim⟩) hc

theorem not_zero_l (p : carrier_l ℳ) : ¬class_l ω e T t₁ t₂ t₃ c e p := by
  intro h
  obtain ⟨D, hD, hC⟩ := PowerlessLevyZero.class_l hℳ hω ht.1 hT h
  have ht₀ := PowerlessEvaluationTags.distinct_l hℳ ht
  rcases hD.2 c hC with h | ⟨j, k, h⟩ | ⟨j, k, h⟩ | ⟨a, b, _, _, h⟩ | ⟨j, k, b, _, h⟩
  · exact PowerlessFormulaConstructor.nonzero_l ht.1 hc h
  · exact ht₀.2.2.1 (PowerlessFormulaConstructor.injective_l hℳ hω ht.1 hT h hc).1
  · exact ht₀.2.2.2.2.1 (PowerlessFormulaConstructor.injective_l hℳ hω ht.1 hT h hc).1
  · exact ht₀.2.2.2.2.2 (PowerlessFormulaConstructor.injective_l hℳ hω ht.1 hT h hc).1
  · obtain ⟨_, d, a, q, _, _, hq, h⟩ := h
    have h₀ := (PowerlessFormulaConstructor.injective_l hℳ hω ht.1 hT hc h).2.2
    exact PowerlessFormulaConstructor.nonzero_l ht.1 hq h₀.symm

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevySeparation
