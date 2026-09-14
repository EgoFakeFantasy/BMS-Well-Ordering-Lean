import BMSConstructibleBridge.PowerlessStageStructure
import BMSConstructibleBridge.ThirdOrderHierarchyStage
import BMSConstructibleBridge.ThirdOrderCountableSuccessor

/-!
# 首个不可数指标处的统一层次与实际求值系统

Cκ 由单级纯定义实际构造。它传递且非空，包含每个早级；全部早级可数，
其成员由早级并精确覆盖。随后在这个可能不可数的域上构造全部有限赋值
与实际求值图，不要求数值满呈现，也不把 Cκ 称为经典 Lκ。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderHierarchyLimit

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessHierarchyStage

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem nonempty_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : stage_l ω e T t₁ t₂ t₃ κ U) : ∃ x, member_l ℳ x U := by
  have h : ∃ a, member_l ℳ a κ := by
    by_contra h
    have h₀ : PowerlessNatural.zero_l κ := fun a ha => h ⟨a, ha⟩
    apply hκ.2.1
    refine ⟨κ, PowerlessFiniteAssignments.empty_l h₀ ω, ?_⟩
    rintro x y z ⟨p, hp, _⟩ _
    exact (h₀ p hp).elim
  obtain ⟨a, ha⟩ := h
  obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOrdinal.mem_l hκ.1 ha) e T t₁ t₂ t₃
  exact ⟨A, PowerlessStageStructure.member_l hℳ hω ht hT hA hU ha⟩

theorem union_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hU : stage_l ω e T t₁ t₂ t₃ κ U) (x : carrier_l ℳ) :
    member_l ℳ x U ↔ ∃ a A, member_l ℳ a κ ∧ stage_l ω e T t₁ t₂ t₃ a A ∧ member_l ℳ x A := by
  apply PowerlessStageStructure.limit_l hℳ hω hU ?_ x
  intro a ha
  obtain ⟨b, hb⟩ := PowerlessNatural.successor_exists_l hℳ a
  exact ⟨b, ThirdOrderCountableSuccessor.limit_l hℳ hω hκ ha hb, (hb a).mpr (Or.inr rfl)⟩

theorem levels_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : stage_l ω e T t₁ t₂ t₃ κ U) :
    ∀ a A, member_l ℳ a κ → stage_l ω e T t₁ t₂ t₃ a A → countable_l ω A ∧ member_l ℳ A U := by
  intro a A ha hA
  exact ⟨ThirdOrderHierarchyStage.countable_l hℳ hω hA (hκ.2.2 a ha),
    PowerlessStageStructure.member_l (ThirdOrderTheory.core_l hℳ) hω ht hT hA hU ha⟩

theorem system_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T) :
    ∃ U S F, stage_l ω e T t₁ t₂ t₃ κ U ∧ (∃ x, member_l ℳ x U) ∧
      PowerlessNaturalOrder.transitive_l U ∧
      (∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n U) ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F ∧
      ∀ a A, member_l ℳ a κ → stage_l ω e T t₁ t₂ t₃ a A → countable_l ω A ∧ member_l ℳ A U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨U, hU⟩ := PowerlessHierarchyStage.exists_l h₀ hω hκ.1 e T t₁ t₂ t₃
  obtain ⟨S, F, hS, hF, _⟩ := PowerlessEvaluationRecursion.exists_l h₀ hω ht.1 hT U t₁ t₂ t₃
  exact ⟨U, S, F, hU, nonempty_l h₀ hω hκ ht hT hU,
    PowerlessStageStructure.transitive_l h₀ hω ht hT hU, hS, hF, levels_l hℳ hω hκ ht hT hU⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderHierarchyLimit
