import BMSConstructibleBridge.ThirdOrderSkolemSequence
import BMSConstructibleBridge.PowerlessOrdinalSupremum

/-!
# 推进序列的真实共尾极限与层次并

严格增长使每项属于值域之并。内部可数取界只用于证明该精确并小于 κ，
不把任取的较大界当成极限。极限级的元素随后由序列对应层次精确覆盖。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemLimit

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessHierarchyStage ThirdOrderSkolemSequence

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem upper_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α f ξ : carrier_l ℳ} (hω : omega_l ω)
    (hf : sequence_l ω e T t₁ t₂ t₃ κ U F α f) (hξ : PowerlessOrdinalSupremum.supremum_l f ξ) :
    ∀ n a, value_l f n a → member_l ℳ a ξ := by
  intro n a ha
  have hn := (PowerlessFunction.value_mem_l hℳ hf.1 ha).1
  obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
  obtain ⟨b, hb, _⟩ := hf.1.2 m (PowerlessNatural.successor_mem_l hℳ hω hn hm)
  exact (hξ a).mpr ⟨m, b, hb.2, (hf.2.2 n m a b hn hm ha hb.2).1⟩

theorem limit_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α f ξ : carrier_l ℳ} (hω : omega_l ω)
    (hf : sequence_l ω e T t₁ t₂ t₃ κ U F α f) (hξ : PowerlessOrdinalSupremum.supremum_l f ξ) :
    ∀ x, member_l ℳ x ξ → ∃ a, member_l ℳ a ξ ∧ member_l ℳ x a := by
  intro x hx
  obtain ⟨n, a, ha, hx⟩ := (hξ x).mp hx
  exact ⟨a, upper_l hℳ hω hf hξ n a ha, hx⟩

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α f : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hf : sequence_l ω e T t₁ t₂ t₃ κ U F α f) :
    ∃ ξ, member_l ℳ ξ κ ∧ PowerlessOrdinalSupremum.supremum_l f ξ ∧ member_l ℳ α ξ ∧
      ∀ x, member_l ℳ x ξ → ∃ a, member_l ℳ a ξ ∧ member_l ℳ x a := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨ξ, hξ⟩ := PowerlessOrdinalSupremum.exists_l h₀ f
  obtain ⟨b, hb, h⟩ := ThirdOrderCountableBounds.omega_l hℳ hω hκ hf.1
  exact ⟨ξ, PowerlessOrdinalSupremum.member_l h₀ hκ.1 hf.1 hξ hb h, hξ,
    upper_l h₀ hω hf hξ e α hf.2.1, limit_l h₀ hω hf hξ⟩

theorem levels_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α f ξ C : carrier_l ℳ} (hω : omega_l ω)
    (hf : sequence_l ω e T t₁ t₂ t₃ κ U F α f) (hξ : PowerlessOrdinalSupremum.supremum_l f ξ)
    (hC : stage_l ω e T t₁ t₂ t₃ ξ C) (x : carrier_l ℳ) :
    member_l ℳ x C ↔ ∃ n a A, value_l f n a ∧ stage_l ω e T t₁ t₂ t₃ a A ∧ member_l ℳ x A := by
  constructor
  · intro hx
    obtain ⟨b, B, hb, hB, hx⟩ := (PowerlessStageStructure.limit_l hℳ hω hC (limit_l hℳ hω hf hξ) x).mp hx
    obtain ⟨n, a, ha, hb⟩ := (hξ b).mp hb
    obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l hℳ hω
      (PowerlessOrdinal.mem_l hC.1 (upper_l hℳ hω hf hξ n a ha)) e T t₁ t₂ t₃
    exact ⟨n, a, A, ha, hA, PowerlessStageStructure.subset_l hℳ hω hB hA hb x hx⟩
  · rintro ⟨n, a, A, ha, hA, hx⟩
    exact PowerlessStageStructure.subset_l hℳ hω hA hC (upper_l hℳ hω hf hξ n a ha) x hx

theorem level_exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α f : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hf : sequence_l ω e T t₁ t₂ t₃ κ U F α f) :
    ∃ ξ C, member_l ℳ ξ κ ∧ PowerlessOrdinalSupremum.supremum_l f ξ ∧ member_l ℳ α ξ ∧
      stage_l ω e T t₁ t₂ t₃ ξ C ∧ countable_l ω C ∧ ∀ x, member_l ℳ x C ↔
        ∃ n a A, value_l f n a ∧ stage_l ω e T t₁ t₂ t₃ a A ∧ member_l ℳ x A := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨ξ, hξ, h, hα, _⟩ := exists_l hℳ hω hκ hf
  obtain ⟨C, hC⟩ := PowerlessHierarchyStage.exists_l h₀ hω (PowerlessOrdinal.mem_l hκ.1 hξ) e T t₁ t₂ t₃
  exact ⟨ξ, C, hξ, h, hα, hC, ThirdOrderHierarchyStage.countable_l hℳ hω hC (hκ.2.2 ξ hξ),
    levels_l h₀ hω hf h hC⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemLimit
