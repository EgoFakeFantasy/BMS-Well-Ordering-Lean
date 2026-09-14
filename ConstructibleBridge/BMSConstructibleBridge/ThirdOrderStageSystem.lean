import BMSConstructibleBridge.PowerlessCoreStageSystem
import BMSConstructibleBridge.ThirdOrderStageHierarchySource

/-!
# Cκ 中的原层、赋值全集和求值系统

system_m 保持原正文。成员性先取得实际层，再逐项调用赋值与求值闭包，
不把 system 的域内存在作为输入，也不将 κ 本身当作 Cκ 的元素。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageSystem

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

theorem system_l {α A S F : type_l U} :
    PowerlessStageEvaluation.system_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ α A S F ↔
      PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α.val A.val S.val F.val :=
  PowerlessCoreStageSystem.system_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ)

theorem member_l {α A S F : carrier_l ℳ} (hα : member_l ℳ α κ)
    (h : PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α A S F) :
    member_l ℳ A U ∧ member_l ℳ S U ∧ member_l ℳ F U := by
  let hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U := ⟨ω.val, ω.property⟩
  exact PowerlessCoreStageSystem.member_l (hU₀ := hU₀) (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ) hα h

theorem exists_l {α : carrier_l ℳ} (hα : ThirdOrderSemantics.member_l ℳ α κ) : ∃ A S F,
    PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α A S F ∧
    ThirdOrderSemantics.member_l ℳ A U ∧ ThirdOrderSemantics.member_l ℳ S U ∧ ThirdOrderSemantics.member_l ℳ F U := by
  let hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U := ⟨ω.val, ω.property⟩
  exact PowerlessCoreStageSystem.exists_l (hU₀ := hU₀) (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ) hα

theorem source_l {hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U}
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ α A S F : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessStageEvaluation.system_m w z V s₁ s₂ s₃ α A S F).satisfies η ↔
      PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (α.eval η).val (A.eval η).val (S.eval η).val (F.eval η).val :=
  PowerlessCoreStageSystem.source_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ) η w z V s₁ s₂ s₃ α A S F hw hz hV hs₁ hs₂ hs₃

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageSystem
