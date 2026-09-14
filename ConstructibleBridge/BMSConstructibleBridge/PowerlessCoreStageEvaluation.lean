import BMSConstructibleBridge.PowerlessAssignmentsAbsolute
import BMSConstructibleBridge.PowerlessEvaluationAbsolute
import BMSConstructibleBridge.PowerlessSourceOmegaAbsolute

/-!
# 满足核心公理的实际极限层中完整求值系统的成员性

绝对性只需原极限层闭包；完整赋值集与求值图的存在另显式消费层内
核心。先比较同一语义，再用环境唯一性取回原图，不假定所有早层有核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageEvaluation

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U β : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val β U)
  (hωβ : member_l ℳ ω.val β) (hβ : PowerlessStagePair.limit_l β)

include hℳ hω ht hT hU hωβ hβ

theorem assignments_l {A S : type_l U} :
    PowerlessEvaluationOperator.assignments_l (ℳ := structure_l U hU₀) ω A S ↔
      PowerlessEvaluationOperator.assignments_l ω.val A.val S.val := by
  obtain ⟨_, w, hw, h⟩ := PowerlessAssignmentsAbsolute.stage_l hℳ hω ht hT hU hωβ hβ
  rw [show w = ω from Subtype.ext hw] at h
  exact h A S

theorem evaluation_l {A S F : type_l U} :
    PowerlessEvaluationRecursion.evaluation_l (ℳ := structure_l U hU₀) ω e T A t₁ t₂ t₃ S F ↔
      PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val S.val F.val := by
  obtain ⟨_, w, z, V, s₁, s₂, s₃, hw, hz, hV, hs₁, hs₂, hs₃, h⟩ :=
    PowerlessEvaluationAbsolute.stage_l hℳ hω ht hT hU hωβ hβ
  rw [show w = ω from Subtype.ext hw, show z = e from Subtype.ext hz, show V = T from Subtype.ext hV,
    show s₁ = t₁ from Subtype.ext hs₁, show s₂ = t₂ from Subtype.ext hs₂, show s₃ = t₃ from Subtype.ext hs₃] at h
  exact h A S F

variable (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m)

include h𝒩

theorem assignments_exists_l (A : type_l U) : ∃ S : type_l U,
    PowerlessEvaluationOperator.assignments_l ω.val A.val S.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hw := (PowerlessSourceOmegaAbsolute.omega_l (hA := hU₀) hℳ hUT hω ω.property ω).mpr rfl
  obtain ⟨S, hS⟩ := PowerlessFiniteAssignments.all_exists_l h𝒩 hw A
  exact ⟨S, (assignments_l hℳ hω ht hT hU hωβ hβ).mp hS⟩

theorem assignments_member_l {A S : carrier_l ℳ} (hA : member_l ℳ A U)
    (hS : PowerlessEvaluationOperator.assignments_l ω.val A S) : member_l ℳ S U := by
  obtain ⟨R, hR⟩ := assignments_exists_l hℳ hω ht hT hU hωβ hβ h𝒩 ⟨A, hA⟩
  have hSR : S = R.val := (PowerlessTheory.ext_l hℳ).eq_of_same_members S R.val
    (fun f => (hS f).trans (hR f).symm)
  exact hSR.symm ▸ R.property

theorem evaluation_exists_l (A S : type_l U) : ∃ F : type_l U,
    PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val S.val F.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hw := (PowerlessSourceOmegaAbsolute.omega_l (hA := hU₀) hℳ hUT hω ω.property ω).mpr rfl
  obtain ⟨F, hF, _⟩ := PowerlessEvaluationRecursion.exists_unique_l h𝒩 hw e T A t₁ t₂ t₃ S
  exact ⟨F, (evaluation_l hℳ hω ht hT hU hωβ hβ).mp hF⟩

theorem evaluation_member_l {A S F : carrier_l ℳ} (hA : member_l ℳ A U) (hS : member_l ℳ S U)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val A t₁.val t₂.val t₃.val S F) : member_l ℳ F U := by
  obtain ⟨G, hG⟩ := evaluation_exists_l hℳ hω ht hT hU hωβ hβ h𝒩 ⟨A, hA⟩ ⟨S, hS⟩
  obtain ⟨H, _, h⟩ := PowerlessEvaluationRecursion.exists_unique_l hℳ hω e.val T.val A t₁.val t₂.val t₃.val S
  have hFG : F = G.val := (h F hF).trans (h G.val hG).symm
  exact hFG.symm ▸ G.property

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageEvaluation
