import BMSConstructibleBridge.PowerlessCoreStageHierarchy
import BMSConstructibleBridge.ThirdOrderStageHierarchyStep
import BMSConstructibleBridge.ThirdOrderStageRecursionClosure

/-!
# Cκ 中原层次图的内外一致及实际成员性

反向递归语义使用域内二次并作统一值域界，再用已证一般前史闭包取回见证。
内部核心的存在性只有在内外一致证明后才用于环境图成员性，不作循环假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageHierarchy

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

theorem ordinal_l (a : type_l U) :
    PowerlessOrdinal.ordinal_l (ℳ := structure_l U hU₀) a ↔ PowerlessOrdinal.ordinal_l a.val :=
  PowerlessCoreStageHierarchy.ordinal_l (ThirdOrderTheory.core_l hℳ)
    (PowerlessStageStructure.transitive_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU) a

theorem hierarchy_l {f α : type_l U} :
    PowerlessEvaluationHierarchy.hierarchy_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ f α ↔
      PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val f.val α.val :=
  PowerlessCoreStageHierarchy.hierarchy_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ)

theorem exists_l (α : type_l U) (hα : PowerlessOrdinal.ordinal_l α.val) : ∃ f : type_l U,
    PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val f.val α.val := by
  let hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U := ⟨α.val, α.property⟩
  exact PowerlessCoreStageHierarchy.exists_l (hU₀ := hU₀) (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ) α hα

theorem member_l {α f : carrier_l ℳ} (hα : PowerlessOrdinal.ordinal_l α) (hαU : member_l ℳ α U)
    (hf : PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val f α) :
    member_l ℳ f U := by
  let hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U := ⟨ω.val, ω.property⟩
  exact PowerlessCoreStageHierarchy.member_l (hU₀ := hU₀) (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ) hα hαU hf

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageHierarchy
