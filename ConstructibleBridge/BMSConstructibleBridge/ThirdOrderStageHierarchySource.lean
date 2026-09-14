import BMSConstructibleBridge.PowerlessCoreStageHierarchySource
import BMSConstructibleBridge.ThirdOrderStageHierarchy

/-! # 原 hierarchy_m 与 stage_m 在 Cκ 中的实际解释 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageHierarchySource

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U κ : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val) (hκ : ThirdOrderOmegaOne.first_l ω.val κ)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val κ U)

include hℳ hω hκ ht hT hU

theorem stage_l {α A : type_l U} :
    PowerlessHierarchyStage.stage_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ α A ↔
      PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val α.val A.val :=
  PowerlessCoreStageHierarchySource.stage_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ)

variable {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
  (w z V s₁ s₂ s₃ : Term ℒ Γ Δ .set)
  (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
  (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)

include hw hz hV hs₁ hs₂ hs₃

theorem hierarchy_source_l (f α : Term ℒ Γ Δ .set) :
    (PowerlessHierarchyPresentation.hierarchy_m w z V s₁ s₂ s₃ f α).satisfies η ↔
      PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val (f.eval η).val (α.eval η).val :=
  PowerlessCoreStageHierarchySource.hierarchy_source_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ) η w z V s₁ s₂ s₃ hw hz hV hs₁ hs₂ hs₃ f α

theorem stage_source_l (α A : Term ℒ Γ Δ .set) :
    (PowerlessHierarchyStage.stage_m w z V s₁ s₂ s₃ α A).satisfies η ↔
      PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val (α.eval η).val (A.eval η).val :=
  PowerlessCoreStageHierarchySource.stage_source_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ) η w z V s₁ s₂ s₃ hw hz hV hs₁ hs₂ hs₃ α A

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageHierarchySource
