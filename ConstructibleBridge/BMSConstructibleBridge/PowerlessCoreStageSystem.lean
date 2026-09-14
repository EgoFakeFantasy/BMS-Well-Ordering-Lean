import BMSConstructibleBridge.PowerlessCoreStageHierarchySource
import BMSConstructibleBridge.PowerlessStageEvaluation

/-!
# 满足核心公理的实际极限层中的原层、赋值全集和求值系统

system_m 保持原正文。成员性先取得实际层，再逐项调用赋值与求值闭包，
层内核心显式列入前提，不把 system 的域内存在作为输入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageSystem

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m)
  (hωδ : ThirdOrderSemantics.member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ

theorem system_l {α A S F : type_l U} :
    PowerlessStageEvaluation.system_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ α A S F ↔
      PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α.val A.val S.val F.val := by
  exact and_congr (PowerlessCoreStageHierarchySource.stage_l hℳ hω ht hT hU hδ h𝒩 hωδ)
    (and_congr (PowerlessCoreStageEvaluation.assignments_l hℳ hω ht hT hU hωδ hδ)
      (PowerlessCoreStageEvaluation.evaluation_l hℳ hω ht hT hU hωδ hδ))

theorem member_l {α A S F : carrier_l ℳ} (hα : member_l ℳ α δ)
    (h : PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α A S F) :
    member_l ℳ A U ∧ member_l ℳ S U ∧ member_l ℳ F U := by
  have hA := PowerlessStageStructure.member_l hℳ hω ht hT h.1 hU hα
  have hS := PowerlessCoreStageEvaluation.assignments_member_l hℳ hω ht hT hU hωδ hδ h𝒩 hA h.2.1
  exact ⟨hA, hS, PowerlessCoreStageEvaluation.evaluation_member_l hℳ hω ht hT hU hωδ hδ h𝒩 hA hS h.2.2⟩

theorem exists_l {α : carrier_l ℳ} (hα : ThirdOrderSemantics.member_l ℳ α δ) : ∃ A S F,
    PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α A S F ∧
    ThirdOrderSemantics.member_l ℳ A U ∧ ThirdOrderSemantics.member_l ℳ S U ∧ ThirdOrderSemantics.member_l ℳ F U := by
  obtain ⟨A, S, F, h⟩ := PowerlessStageEvaluation.exists_l hℳ hω
    (PowerlessOrdinal.mem_l hδ.1 hα) e.val T.val t₁.val t₂.val t₃.val
  exact ⟨A, S, F, h, member_l hℳ hω ht hT hU hδ h𝒩 hωδ hα h⟩

theorem source_l
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ α A S F : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessStageEvaluation.system_m w z V s₁ s₂ s₃ α A S F).satisfies η ↔
      PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (α.eval η).val (A.eval η).val (S.eval η).val (F.eval η).val := by
  have h := PowerlessStageEvaluation.system_formula_l h𝒩
    η w z V s₁ s₂ s₃ α A S F
  rw [show w.eval η = ω from Subtype.ext hw, show z.eval η = e from Subtype.ext hz,
    show V.eval η = T from Subtype.ext hV, show s₁.eval η = t₁ from Subtype.ext hs₁,
    show s₂.eval η = t₂ from Subtype.ext hs₂, show s₃.eval η = t₃ from Subtype.ext hs₃] at h
  exact h.trans (system_l (hU₀ := hU₀) hℳ hω ht hT hU hδ h𝒩 hωδ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageSystem
