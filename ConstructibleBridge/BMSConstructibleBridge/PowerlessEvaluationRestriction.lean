import BMSConstructibleBridge.PowerlessEvaluationAgreement
import BMSConstructibleBridge.PowerlessEvaluationFamily

/-!
# 求值子集在一致子域上的精确限制

末尾追加同一个待定义元素，保持同一数码和参数图。小域求值子集恰为
原域子集与小域之交；参数必须来自小域，不声称一般 Def 算子单调。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationRestriction

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem point_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A U F G c f x : carrier_l ℳ} (hω : omega_l ω) (hAU : subset_l A U)
    (h : PowerlessEvaluationAgreement.agreement_l ω A F G) (hc : member_l ℳ c ω)
    (hf : ∃ m, member_l ℳ m ω ∧ map_l f m A) (hx : member_l ℳ x A) :
    PowerlessEvaluationSlice.point_l ω U F c f x ↔ PowerlessEvaluationSlice.point_l ω A G c f x := by
  obtain ⟨_, _, hfA⟩ := hf
  constructor
  · rintro ⟨m, hm, hf, g, hg, h₀⟩
    have hf₀ := PowerlessFunction.range_l hℳ hf (fun _ y hy => (PowerlessFunction.value_mem_l hℳ hfA hy).2)
    obtain ⟨n, hn⟩ := PowerlessNatural.successor_exists_l hℳ m
    have h₁ := PowerlessAppendGraph.map_l hℳ hf₀ hx hn hg
    exact ⟨m, hm, hf₀, g, hg, (h c hc g ⟨n, PowerlessNatural.successor_mem_l hℳ hω hm hn, h₁⟩).mp h₀⟩
  · rintro ⟨m, hm, hf, g, hg, h₀⟩
    obtain ⟨n, hn⟩ := PowerlessNatural.successor_exists_l hℳ m
    have h₁ := PowerlessAppendGraph.map_l hℳ hf hx hn hg
    exact ⟨m, hm, PowerlessFunction.range_l hℳ hf (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2),
      g, hg, (h c hc g ⟨n, PowerlessNatural.successor_mem_l hℳ hω hm hn, h₁⟩).mpr h₀⟩

theorem slice_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A U F G c f B D : carrier_l ℳ} (hω : omega_l ω) (hAU : subset_l A U)
    (h : PowerlessEvaluationAgreement.agreement_l ω A F G) (hc : member_l ℳ c ω)
    (hf : ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (hB : PowerlessEvaluationSlice.slice_l ω U F c f B) (hD : PowerlessEvaluationSlice.slice_l ω A G c f D) :
    ∀ x, member_l ℳ x D ↔ member_l ℳ x A ∧ member_l ℳ x B := by
  intro x
  constructor
  · intro hx
    obtain ⟨hx, h₀⟩ := (hD x).mp hx
    exact ⟨hx, (hB x).mpr ⟨hAU x hx, (point_l hℳ hω hAU h hc hf hx).mpr h₀⟩⟩
  · rintro ⟨hx, h₀⟩
    exact (hD x).mpr ⟨hx, (point_l hℳ hω hAU h hc hf hx).mp ((hB x).mp h₀).2⟩

theorem family_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A U F G S D c f B : carrier_l ℳ} (hω : omega_l ω) (hAU : subset_l A U)
    (h : PowerlessEvaluationAgreement.agreement_l ω A F G) (hc : member_l ℳ c ω)
    (hf : ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (hS : ∀ g, member_l ℳ g S ↔ ∃ m, member_l ℳ m ω ∧ map_l g m A)
    (hD : PowerlessEvaluationFamily.family_l ω A G S D) (hB : PowerlessEvaluationSlice.slice_l ω U F c f B) :
    ∃ E, member_l ℳ E D ∧ ∀ x, member_l ℳ x E ↔ member_l ℳ x A ∧ member_l ℳ x B := by
  obtain ⟨E, hE⟩ := PowerlessEvaluationSlice.exists_l hℳ ω A G c f
  exact ⟨E, (hD E).mpr ⟨c, hc, f, (hS f).mpr hf, hE⟩, slice_l hℳ hω hAU h hc hf hB hE⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationRestriction
