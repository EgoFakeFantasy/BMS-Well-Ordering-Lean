import BMSConstructibleBridge.PowerlessWitnessClosure
import BMSConstructibleBridge.PowerlessEvaluationHistory

/-!
# 见证闭包子域上的局部求值规则比较

原子式读取同一赋值图，联结词只读严格子码。存在分支先将见证取回
子域，再证明真实更新图的全部值回到子域，才可应用子码比较。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationCompare

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A U F G f i b : carrier_l ℳ} (hAU : subset_l A U)
    (hC : PowerlessWitnessClosure.closure_l ω U F A A)
    (hi : member_l ℳ i ω) (hb : member_l ℳ b ω) (hf : ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (h : ∀ g, (∃ m, member_l ℳ m ω ∧ map_l g m A) →
      (PowerlessEvaluationClause.query_l F b g ↔ PowerlessEvaluationClause.query_l G b g)) :
    PowerlessEvaluationClause.exists_l ω U F f i b ↔ PowerlessEvaluationClause.exists_l ω A G f i b := by
  constructor
  · intro h₀
    obtain ⟨a, ha, _, n, hn, hf₀, hi₀, g, hg, h₁, h₂⟩ := hC i b f hi hb hf h₀
    obtain ⟨m, _, hf⟩ := hf
    have h₃ := PowerlessAssignmentUpdate.length_unique_l hℳ hf hf₀
    subst m
    have hg₀ := PowerlessAssignmentUpdate.range_l hℳ hf hg ha h₁
    exact ⟨n, hn, hf, hi₀, a, ha, g, hg₀, h₁, (h g ⟨n, hn, hg₀⟩).mp h₂⟩
  · rintro ⟨n, hn, hf, hi₀, a, ha, g, hg, h₀, h₁⟩
    exact ⟨n, hn, PowerlessFunction.range_l hℳ hf (fun x y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2),
      hi₀, a, hAU a ha, g,
      PowerlessFunction.range_l hℳ hg (fun x y hy => hAU y (PowerlessFunction.value_mem_l hℳ hg hy).2),
      h₀, (h g ⟨n, hn, hg⟩).mpr h₁⟩

theorem clause_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A U t₁ t₂ t₃ F G n f : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hAU : subset_l A U) (hC : PowerlessWitnessClosure.closure_l ω U F A A)
    (hf : ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (h : ∀ k, member_l ℳ k n → ∀ g, (∃ m, member_l ℳ m ω ∧ map_l g m A) →
      (PowerlessEvaluationClause.query_l F k g ↔ PowerlessEvaluationClause.query_l G k g)) :
    PowerlessEvaluationClause.clause_l ω e T U t₁ t₂ t₃ F n f ↔
      PowerlessEvaluationClause.clause_l ω e T A t₁ t₂ t₃ G n f := by
  unfold PowerlessEvaluationClause.clause_l
  refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr ?_ ?_))
  · apply exists_congr
    intro a
    apply exists_congr
    intro b
    apply and_congr_right
    intro hc
    obtain ⟨ha, hb⟩ := PowerlessFormulaConstructor.bounds_l hℳ hω he hT hc
    exact not_congr (and_congr (h a ha f hf) (h b hb f hf))
  · apply exists_congr
    intro i
    apply exists_congr
    intro b
    apply and_congr_right
    intro hc
    exact exists_l hℳ hAU hC hc.1 hc.2.1 hf (h b (PowerlessFormulaConstructor.bounds_l hℳ hω he hT hc).2)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationCompare
