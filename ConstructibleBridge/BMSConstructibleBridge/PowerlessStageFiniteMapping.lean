import BMSConstructibleBridge.PowerlessStageFiniteGraphs
import BMSConstructibleBridge.PowerlessStageFiniteRanges

/-!
# 实际内部有限图及其真实值域同时落入极限层

先保留原函数图，收集其真实值域，再分别使用有限图与有限覆盖闭包。
所得小层陪域不是整个读取层自身；这给共同存在量词提供两个合法成员见证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteMapping

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

theorem member_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α U q g : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α U)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hq : ThirdOrderSemantics.member_l ℳ q ω) (hg : map_l g q U) :
    ThirdOrderSemantics.member_l ℳ g U ∧
      ∃ B, ThirdOrderSemantics.member_l ℳ B U ∧ map_l g q B ∧
        ∀ a, ThirdOrderSemantics.member_l ℳ a B ↔ ∃ i, value_l g i a := by
  have hgU := PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hU hα hωα q hq g hg
  obtain ⟨B, hB⟩ := PowerlessCoordinates.range_exists_l hℳ g
  have hBU := PowerlessStageFiniteRanges.finite_l hℳ hω ht hT hU hα q hq g B hg
    (fun a ha => (hB a).mp ha)
  exact ⟨hgU, B, hBU, PowerlessFunction.range_l hℳ hg
    (fun i a ha => (hB a).mpr ⟨i, ha⟩), hB⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteMapping
