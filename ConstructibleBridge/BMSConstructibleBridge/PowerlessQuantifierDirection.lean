import BMSConstructibleBridge.PowerlessEvaluationDirection
import BMSConstructibleBridge.PowerlessBoundedQuantifier

/-!
# 实际赋值更新的单向量词保持

向上提升已有赋值和见证的值域；有界向下则先由传递性取回见证，
再收回整个更新图的值域。全过程不假定全初等性或 Skolem 闭包。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessQuantifierDirection

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationDirection

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A U F G f i b : carrier_l ℳ} (hAU : subset_l A U) (h : direction_l ω A G F b)
    (h₀ : PowerlessEvaluationClause.exists_l ω A G f i b) :
    PowerlessEvaluationClause.exists_l ω U F f i b := by
  obtain ⟨n, hn, hf, hi, a, ha, g, hg, h₁, h₂⟩ := h₀
  exact ⟨n, hn, PowerlessFunction.range_l hℳ hf
    (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2), hi, a, hAU a ha, g,
    PowerlessFunction.range_l hℳ hg (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hg hy).2),
    h₁, h g ⟨n, hn, hg⟩ h₂⟩

theorem bounded_up_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A U F G f i j b : carrier_l ℳ} (hAU : subset_l A U) (h : direction_l ω A G F b)
    (h₀ : PowerlessBoundedQuantifier.exists_l ω A G f i j b) :
    PowerlessBoundedQuantifier.exists_l ω U F f i j b := by
  obtain ⟨n, hn, hf, hi, z, hz, a, ha, g, hg, h₁, h₂⟩ := h₀
  exact ⟨n, hn, PowerlessFunction.range_l hℳ hf
    (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2), hi, z, hz, a, ha, g,
    PowerlessFunction.range_l hℳ hg (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hg hy).2),
    h₁, h g ⟨n, hn, hg⟩ h₂⟩

theorem bounded_down_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A U F G f i j b : carrier_l ℳ} (hA : PowerlessNaturalOrder.transitive_l A)
    (hf : ∃ m, member_l ℳ m ω ∧ map_l f m A) (h : direction_l ω A F G b)
    (h₀ : PowerlessBoundedQuantifier.exists_l ω U F f i j b) :
    PowerlessBoundedQuantifier.exists_l ω A G f i j b := by
  obtain ⟨n, hn, hf₀, hi, z, hz, a, ha, g, hg, h₁, h₂⟩ := h₀
  obtain ⟨m, _, hf⟩ := hf
  have h₃ := PowerlessAssignmentUpdate.length_unique_l hℳ hf hf₀
  subst m
  have ha₀ := hA z a (PowerlessFunction.value_mem_l hℳ hf hz).2 ha
  have hg₀ := PowerlessAssignmentUpdate.range_l hℳ hf hg ha₀ h₁
  exact ⟨n, hn, hf, hi, z, hz, a, ha, g, hg₀, h₁, h g ⟨n, hn, hg₀⟩ h₂⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessQuantifierDirection
