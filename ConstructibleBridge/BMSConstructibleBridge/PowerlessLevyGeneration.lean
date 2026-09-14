import BMSConstructibleBridge.PowerlessLevyCertificateClosure
import BMSConstructibleBridge.PowerlessEvaluationTags

/-!
# 层级判断的实际构造闭包

每个接口消费同一公式构造子的证据，合并或扩充实际记录集后给新分类。
层号是模型内自然数；有界存在不升层，无界存在保留明确的极性条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyGeneration

open Logic FirstOrder ThirdOrderSemantics PowerlessLevyEntry PowerlessLevyCertificate

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem boolean_l {a b c n k l p q : carrier_l ℳ} (hn : member_l ℳ n ω)
    (hk : subset_l k n) (hl : subset_l l n) (hP : opposite_l e t₁ p q)
    (ha : class_l ω e T t₁ t₂ t₃ a k q) (hb : class_l ω e T t₁ t₂ t₃ b l q)
    (hc : PowerlessFormulaConstructor.constructor_l ω e T t₂ a b c) :
    class_l ω e T t₁ t₂ t₃ c n p := by
  obtain ⟨D, hD, ha⟩ := ha
  obtain ⟨E, hE, hb⟩ := hb
  obtain ⟨K, hK, hDK, hEK⟩ := PowerlessLevyCertificateClosure.union_l hℳ hω hD hE
  have hp₀ : polarity_l e t₁ p := hP.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hp : member_l ℳ p ω := hp₀.elim
    (fun h => h.symm ▸ (PowerlessEvaluationTags.natural_l hℳ hω ht).1)
    (fun h => h.symm ▸ (PowerlessEvaluationTags.natural_l hℳ hω ht).2.1)
  obtain ⟨H, hH, h, _⟩ := PowerlessLevyCertificateClosure.extend_l hℳ hω ht.1 hT hK
    (PowerlessFormulaConstructor.natural_l hℳ hω ht.1 hT hc) hn hp hp₀
    (Or.inr (Or.inl ⟨a, b, k, l, q, hP, hk, hl,
      PowerlessLevyEntry.monotone_l hDK ha, PowerlessLevyEntry.monotone_l hEK hb, hc⟩))
  exact ⟨H, hH, h⟩

theorem bounded_l {i j b c n m p : carrier_l ℳ} (hn : member_l ℳ n ω) (hm : subset_l m n)
    (hb : class_l ω e T t₁ t₂ t₃ b m p) (hc : PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c) :
    class_l ω e T t₁ t₂ t₃ c n p := by
  obtain ⟨D, hD, hb⟩ := hb
  have hp := (PowerlessLevyEntry.natural_l hb).2.2
  have hP := (hD.2 b m p hb).1
  have hc₀ : member_l ℳ c ω := by
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hc
    exact PowerlessFormulaConstructor.natural_l hℳ hω ht.1 hT h
  obtain ⟨E, hE, h, _⟩ := PowerlessLevyCertificateClosure.extend_l hℳ hω ht.1 hT hD hc₀ hn hp hP
    (Or.inr (Or.inr (Or.inl ⟨i, j, b, m, hm, hb, hc⟩)))
  exact ⟨E, hE, h⟩

theorem existential_l {i b c n m q : carrier_l ℳ} (hn : member_l ℳ n ω) (he : member_l ℳ e n)
    (hb : class_l ω e T t₁ t₂ t₃ b m q)
    (hm : (q = e ∧ subset_l m n) ∨ (q = t₁ ∧ member_l ℳ m n))
    (hc : PowerlessFormulaConstructor.constructor_l ω e T t₃ i b c) :
    class_l ω e T t₁ t₂ t₃ c n e := by
  obtain ⟨D, hD, hb⟩ := hb
  obtain ⟨E, hE, h, _⟩ := PowerlessLevyCertificateClosure.extend_l hℳ hω ht.1 hT hD
    (PowerlessFormulaConstructor.natural_l hℳ hω ht.1 hT hc) hn
    (PowerlessNatural.zero_mem_l hℳ hω ht.1) (Or.inl rfl)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, he, i, b, m, q, hb, hm, hc⟩))))
  exact ⟨E, hE, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyGeneration
