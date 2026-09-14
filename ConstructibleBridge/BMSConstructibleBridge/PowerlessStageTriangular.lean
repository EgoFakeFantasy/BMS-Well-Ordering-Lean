import BMSConstructibleBridge.PowerlessTriangularCut
import BMSConstructibleBridge.PowerlessStageAdditionFinite

/-!
# 实际三角数图 T 的早级成员性

各个自然数有序对先在 Cω 中；Cω+1 含 ω 且正确解释有限计算。
原源覆盖将整个 T 放入 Cω+2，再用实际层次方程传入 proper 极限层。
不以小层满足背景核心或已经含有 T 为前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageTriangular

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem subset_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) : ThirdOrderSemantics.subset_l T A := by
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOmegaOrdinal.ordinal_l hℳ hω) e T t₁ t₂ t₃
  have hωB := PowerlessStageParameters.naturals_l hℳ hω ht hT hB (fun _ hx => hx)
  have hω₀ : PowerlessStagePair.limit_l ω := ⟨PowerlessOmegaOrdinal.ordinal_l hℳ hω,
    ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1⟩, PowerlessOmegaOrdinal.limit_l hℳ hω⟩
  intro p hp
  obtain ⟨n, t, hn, ht₀, hp⟩ := hT.1.1 p hp
  have hpB := PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hB hω₀ (hωB n hn) (hωB t ht₀) hp
  exact PowerlessStageStructure.subset_l hℳ hω hB hA hωα p hpB

theorem operator_l {α A D : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D) : member_l ℳ T D := by
  obtain ⟨hωA, heA, _⟩ := PowerlessStageParameters.proper_l hℳ hω ht hT hA hωα
  exact PowerlessTriangularCut.operator_l hℳ hω ht hT hD
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hA) hωA heA
    (PowerlessStageAdditionFinite.graphs_above_l hℳ hω ht hT hA hωα) (subset_l hℳ hω ht hT hA hωα)

theorem successor_l {α β A B : carrier_l ℳ}
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωα : member_l ℳ ω α) (hαβ : PowerlessNatural.successor_l α β) : member_l ℳ T B :=
  operator_l hℳ hω ht hT hA hωα (PowerlessStageStructure.successor_l hℳ hω ht hT hA hB hαβ)

theorem second_l : ∃ α β B, PowerlessNatural.successor_l ω α ∧ PowerlessNatural.successor_l α β ∧
    PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B ∧ member_l ℳ T B := by
  obtain ⟨α, hα⟩ := PowerlessNatural.successor_exists_l hℳ ω
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ α
  have hα₀ := PowerlessOrdinalOrder.successor_l hℳ (PowerlessOmegaOrdinal.ordinal_l hℳ hω) hα
  have hβ₀ := PowerlessOrdinalOrder.successor_l hℳ hα₀ hβ
  obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l hℳ hω hα₀ e T t₁ t₂ t₃
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω hβ₀ e T t₁ t₂ t₃
  exact ⟨α, β, B, hα, hβ, hB, successor_l hℳ hω ht hT hA hB ((hα ω).mpr (Or.inr rfl)) hβ⟩

theorem limit_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α) : member_l ℳ T A := by
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ ω
  have hβ₀ := PowerlessOrdinalOrder.successor_l hℳ (PowerlessOmegaOrdinal.ordinal_l hℳ hω) hβ
  obtain ⟨γ, hγ, hωγ⟩ := hα.2.2 ω hωα
  have hβα : member_l ℳ β α := by
    rcases PowerlessOrdinalOrder.trichotomy_l hℳ hβ₀ (PowerlessOrdinal.mem_l hα.1 hγ) with h | h | h
    · exact PowerlessOrdinal.transitive_l hα.1 γ β hγ h
    · exact h.symm ▸ hγ
    · rcases (hβ γ).mp h with h | h
      · exact (PowerlessNatural.asymmetry_l hℳ h hωγ).elim
      · subst γ
        exact (PowerlessNatural.asymmetry_l hℳ hωγ hωγ).elim
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω hβ₀ e T t₁ t₂ t₃
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ B
  exact PowerlessStageClosure.image_l hℳ hω hA hB hβα hD T
    (operator_l hℳ hω ht hT hB ((hβ ω).mpr (Or.inr rfl)) hD)

theorem parameters_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α) :
    member_l ℳ ω A ∧ member_l ℳ e A ∧ member_l ℳ T A ∧
      member_l ℳ t₁ A ∧ member_l ℳ t₂ A ∧ member_l ℳ t₃ A := by
  obtain ⟨hωA, heA, h₁, h₂, h₃⟩ := PowerlessStageParameters.proper_l hℳ hω ht hT hA hωα
  exact ⟨hωA, heA, limit_l hℳ hω ht hT hA hωα hα, h₁, h₂, h₃⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageTriangular
