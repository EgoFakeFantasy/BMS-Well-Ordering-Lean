import BMSConstructibleBridge.PowerlessStageOrdinalRelation

/-!
# 内部有限初段的隶属关系图落级

各坐标为自然数，所有关系对都在 Cω；以初段 m 作参数的原成员条件
把整个关系图放入 D(Cω)，再传入任意高于 ω 的层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteRelation

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : ThirdOrderSemantics.omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem member_l {α A m R : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : ThirdOrderSemantics.member_l ℳ ω α) (hm : ThirdOrderSemantics.member_l ℳ m ω)
    (hR : PowerlessOrdinalRelation.relation_l m R) : ThirdOrderSemantics.member_l ℳ R A := by
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOmegaOrdinal.ordinal_l hℳ hω) e T t₁ t₂ t₃
  have hωB := PowerlessStageParameters.naturals_l hℳ hω ht hT hB (fun _ hx => hx)
  have hω₀ : PowerlessStagePair.limit_l ω := ⟨PowerlessOmegaOrdinal.ordinal_l hℳ hω,
    ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1⟩, PowerlessOmegaOrdinal.limit_l hℳ hω⟩
  have hRB : subset_l R B := by
    intro p hp
    obtain ⟨x, y, hx, hy, _, hp⟩ := (hR p).mp hp
    exact PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hB hω₀
      (hωB x (PowerlessNaturalOrder.subset_l hℳ hω m hm x hx))
      (hωB y (PowerlessNaturalOrder.subset_l hℳ hω m hm y hy)) hp
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ B
  exact PowerlessStageClosure.image_l hℳ hω hA hB hωα hD R
    (PowerlessOrdinalRelationAbsolute.operator_l hℳ hω ht hT hD
      (PowerlessStageStructure.transitive_l hℳ hω ht hT hB) (hωB m hm) hR hRB)

theorem exists_l {α A m : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : ThirdOrderSemantics.member_l ℳ ω α) (hm : ThirdOrderSemantics.member_l ℳ m ω) :
    ∃ R, PowerlessOrdinalRelation.relation_l m R ∧ ThirdOrderSemantics.member_l ℳ R A := by
  obtain ⟨R, hR⟩ := PowerlessOrdinalRelation.exists_l hℳ m
  exact ⟨R, hR, member_l hℳ hω ht hT hA hωα hm hR⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteRelation
