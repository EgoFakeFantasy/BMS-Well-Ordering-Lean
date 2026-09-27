import BMSConstructibleBridge.PowerlessLevyAgreement
import BMSConstructibleBridge.PowerlessLevyGeneration
import BMSConstructibleBridge.PowerlessEvaluationEquations

/-!
# 指定正层查询一致给出的实际存在见证

对同一子码构造指定的存在节点，先向小域反射存在查询，再将见证的
子码查询传回原求值器。结论仍使用原求值器，不假定跨域源编译同码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyWitness

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A U S R F G n b k f : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hG : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G)
    (hS : ∀ g, member_l ℳ g S ↔ ∃ m, member_l ℳ m ω ∧ map_l g m U)
    (hAU : subset_l A U) (hC : PowerlessLevyAgreement.agreement_l ω e T t₁ t₂ t₃ A F G n)
    (he : member_l ℳ e n) (hk : member_l ℳ k ω)
    (hB : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ b n e)
    (hf : ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (h : PowerlessEvaluationClause.exists_l ω U F f k b) :
    PowerlessEvaluationClause.exists_l ω A F f k b := by
  obtain ⟨c, _, hc⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT
    (PowerlessEvaluationTags.natural_l hℳ hω ht).2.2.2 hk
    (PowerlessLevyCertificate.natural_l hB).1
  have hD := PowerlessLevyGeneration.existential_l hℳ hω ht hT
    (PowerlessLevyCertificate.natural_l hB).2.1 he hB (Or.inl ⟨rfl, fun _ hx => hx⟩) hc
  obtain ⟨m, hm, hf₀⟩ := hf
  have hf₁ := PowerlessFunction.range_l hℳ hf₀
    (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf₀ hy).2)
  have h₀ := (PowerlessEvaluationEquations.exists_l hℳ hω ht hT hF hc f).mpr
    ⟨(hS f).mpr ⟨m, hm, hf₁⟩, h⟩
  have h₁ := (hC c e hD f ⟨m, hm, hf₀⟩).mp h₀
  obtain ⟨l, hl, hf₂, hk₀, a, ha, g, hg, h₂, h₃⟩ :=
    ((PowerlessEvaluationEquations.exists_l hℳ hω ht hT hG hc f).mp h₁).2
  exact ⟨l, hl, hf₂, hk₀, a, ha, g, hg, h₂, (hC b e hB g ⟨l, hl, hg⟩).mpr h₃⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyWitness

