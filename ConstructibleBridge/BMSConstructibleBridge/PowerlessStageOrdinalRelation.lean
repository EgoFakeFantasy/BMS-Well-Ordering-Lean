import BMSConstructibleBridge.PowerlessOrdinalRelationAbsolute
import BMSConstructibleBridge.PowerlessStageFiniteGraphs

/-!
# 内部自然数隶属关系图的实际极限层成员性

先在 Cω 中取得每个自然数有序对，再在含 ω 的早级使用原成员条件
定义整个关系。极限层取严格位于 ω 与层号之间的早级，不要求小层核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageOrdinalRelation

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem subset_l {α A R : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hR : PowerlessOrdinalRelation.relation_l ω R) : ThirdOrderSemantics.subset_l R A := by
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOmegaOrdinal.ordinal_l hℳ hω) e T t₁ t₂ t₃
  have hωB := PowerlessStageParameters.naturals_l hℳ hω ht hT hB (fun _ hx => hx)
  have hω₀ : PowerlessStagePair.limit_l ω := ⟨PowerlessOmegaOrdinal.ordinal_l hℳ hω,
    ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1⟩, PowerlessOmegaOrdinal.limit_l hℳ hω⟩
  intro p hp
  obtain ⟨x, y, hx, hy, _, hp⟩ := (hR p).mp hp
  have hpB := PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hB hω₀ (hωB x hx) (hωB y hy) hp
  exact PowerlessStageStructure.subset_l hℳ hω hB hA hωα p hpB

theorem operator_l {α A D R : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D)
    (hR : PowerlessOrdinalRelation.relation_l ω R) : member_l ℳ R D :=
  PowerlessOrdinalRelationAbsolute.operator_l hℳ hω ht hT hD
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hA)
    (PowerlessStageParameters.omega_l hℳ hω ht hT hA hωα) hR (subset_l hℳ hω ht hT hA hωα hR)

theorem limit_l {α A R : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α)
    (hR : PowerlessOrdinalRelation.relation_l ω R) : member_l ℳ R A := by
  obtain ⟨β, hβ, hωβ⟩ := hα.2.2 ω hωα
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOrdinal.mem_l hα.1 hβ) e T t₁ t₂ t₃
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ B
  exact PowerlessStageClosure.image_l hℳ hω hA hB hβ hD R (operator_l hℳ hω ht hT hB hωβ hD hR)

theorem exists_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α) :
    ∃ R, PowerlessOrdinalRelation.relation_l ω R ∧ member_l ℳ R A := by
  obtain ⟨R, hR⟩ := PowerlessOrdinalRelation.exists_l hℳ ω
  exact ⟨R, hR, limit_l hℳ hω ht hT hA hωα hα hR⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageOrdinalRelation
