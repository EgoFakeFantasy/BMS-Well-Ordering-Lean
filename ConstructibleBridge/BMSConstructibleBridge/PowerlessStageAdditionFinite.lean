import BMSConstructibleBridge.PowerlessAdditionFiniteAbsolute
import BMSConstructibleBridge.PowerlessStageFiniteGraphs

/-!
# 实际 C 层中的有限加法见证

有限自然数图已属于 Cω，向任意更高层传输后消去闭包前提。
每个高于 ω 的实际层正确解释有限见证加法公式，包括 Cω+1；
没有断言旧的无限迭代图已属于该层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageAdditionFinite

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)

include hℳ hω ht hT hA

theorem graphs_l (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α) :
    ∀ n, member_l ℳ n ω → ∀ g, map_l g n ω → member_l ℳ g A := by
  intro n hn g hg
  have h := PowerlessStageParameters.naturals_l hℳ hω ht hT hA hωα
  exact PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hA hα hωα n hn g
    (PowerlessFunction.range_l hℳ hg (fun k x hx => h x (PowerlessFunction.value_mem_l hℳ hg hx).2))

theorem witness_l (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    {a n g : carrier_l ℳ} (hn : member_l ℳ n ω)
    (hg : PowerlessAdditionFinite.trace_l ω e a n g) : member_l ℳ g A := by
  obtain ⟨m, hm, hg, _⟩ := hg
  exact graphs_l hℳ hω ht hT hA hα hωα m (PowerlessNatural.successor_mem_l hℳ hω hn hm) g hg

theorem graphs_above_l (hωα : member_l ℳ ω α) :
    ∀ n, member_l ℳ n ω → ∀ g, map_l g n ω → member_l ℳ g A := by
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOmegaOrdinal.ordinal_l hℳ hω) e T t₁ t₂ t₃
  have hωB := PowerlessStageParameters.naturals_l hℳ hω ht hT hB (fun _ hx => hx)
  intro n hn g hg
  have hgB := PowerlessStageFiniteGraphs.first_l hℳ hω ht hT hB n hn g
    (PowerlessFunction.range_l hℳ hg (fun k x hx => hωB x (PowerlessFunction.value_mem_l hℳ hg hx).2))
  exact PowerlessStageStructure.subset_l hℳ hω hB hA hωα g hgB

theorem witness_above_l (hωα : member_l ℳ ω α) {a n g : carrier_l ℳ} (hn : member_l ℳ n ω)
    (hg : PowerlessAdditionFinite.trace_l ω e a n g) : member_l ℳ g A := by
  obtain ⟨m, hm, hg, _⟩ := hg
  exact graphs_above_l hℳ hω ht hT hA hωα m (PowerlessNatural.successor_mem_l hℳ hω hn hm) g hg

theorem stage_l (hωα : member_l ℳ ω α) :
    ∃ hA₀ : ∃ x, member_l ℳ x A, ∃ w z : type_l A, w.val = ω ∧ z.val = e ∧
      ∀ a b c : type_l A, member_l ℳ a.val ω → member_l ℳ b.val ω →
        (PowerlessAdditionFinite.addition_l (ℳ := structure_l A hA₀) w z a b c ↔
          PowerlessAddition.addition_l ω e a.val b.val c.val) := by
  have hω₀ : subset_l ω α := fun n hn => PowerlessOrdinal.transitive_l hA.1 ω n hωα hn
  have hw := PowerlessStageParameters.omega_l hℳ hω ht hT hA hωα
  have hz := (PowerlessStageParameters.tags_l hℳ hω ht hT hA hω₀).1
  have hAT := PowerlessStageStructure.transitive_l hℳ hω ht hT hA
  refine ⟨⟨ω, hw⟩, ⟨ω, hw⟩, ⟨e, hz⟩, rfl, rfl, ?_⟩
  intro a b c ha hb
  exact PowerlessAdditionFiniteAbsolute.addition_l hℳ hAT hω ht.1 ha hb
    (graphs_above_l hℳ hω ht hT hA hωα)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageAdditionFinite
