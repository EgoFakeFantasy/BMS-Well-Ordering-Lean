import BMSConstructibleBridge.PowerlessTruthReflectingStage
import BMSConstructibleBridge.PowerlessFiniteStageHierarchy

/-!
# 稳定公式与部分真值共用的实际有限核心

保留原层次系统、求值及部分真值支持，全部都是 PowerlessTheory
中已有公理的有限列表。实际反射层同时满足这些支持并保持共同真值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStabilitySupport

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

noncomputable def basis_m (k : Nat) : List (Sentence ℒ) :=
  PowerlessTruthStage.basis_m (PowerlessTruthFiniteStage.formulas_m k) ++ PowerlessFiniteStageHierarchy.basis_m

theorem hierarchy_subset_l : ∀ φ ∈ PowerlessFiniteStageHierarchy.basis_m, PowerlessTheory.theory_m φ := by
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · rcases List.mem_append.mp hφ with hφ | hφ
    · rcases List.mem_append.mp hφ with hφ | hφ
      · exact PowerlessAssignmentsFiniteSupport.support_m.subset φ hφ
      · exact PowerlessEvaluationFiniteSupport.support_m.subset φ hφ
    · rcases List.mem_append.mp hφ with hφ | hφ
      · rcases List.mem_append.mp hφ with hφ | hφ
        · exact PowerlessSliceFiniteSupport.support_m.subset φ hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · exact PowerlessHistoryFiniteSupport.support_m.subset φ hφ
          · exact PowerlessRelationFiniteSupport.support_m.subset φ hφ
      · exact PowerlessOperatorFiniteSupport.support_m.subset φ hφ
  · exact PowerlessHierarchyFiniteSupport.support_m.subset φ hφ

theorem subset_l (k : Nat) : ∀ φ ∈ basis_m k, PowerlessTheory.theory_m φ := by
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · exact PowerlessTruthStage.subset_l _ φ hφ
  · exact hierarchy_subset_l φ hφ

theorem hierarchy_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {k : Nat}
    (hℳ : Theory.Models ℳ (Theory.ofList (basis_m k))) :
    Theory.Models ℳ PowerlessFiniteStageHierarchy.theory_m :=
  fun φ hφ => hℳ φ (List.mem_append.mpr (Or.inr hφ))

theorem monotone_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {j k : Nat}
    (hjk : j ≤ k) (hℳ : Theory.Models ℳ (Theory.ofList (basis_m k))) :
    Theory.Models ℳ (Theory.ofList (basis_m j)) := by
  intro φ hφ
  apply hℳ φ
  rcases List.mem_append.mp hφ with hφ | hφ
  · apply List.mem_append.mpr ∘ Or.inl
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact List.mem_append.mpr (Or.inl hφ)
    · obtain ⟨B, hB, hφ⟩ := List.mem_flatMap.mp hφ
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hB
      exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi) hjk), rfl⟩, hφ⟩))
  · exact List.mem_append.mpr (Or.inr hφ)

theorem introduction_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {k : Nat}
    (hℳ : Theory.Models ℳ (Theory.ofList (basis_m k))) :
    Theory.Models ℳ PowerlessTruthIntroduction.theory_m :=
  fun φ hφ => hℳ φ (List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hφ))))))

theorem oracle_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {k j : Nat}
    (hℳ : Theory.Models ℳ (Theory.ofList (basis_m k))) (hj : j < k) :
    Theory.Models ℳ (PowerlessOracleIntroduction.theory_m
      (PowerlessPartialTruthIntroduction.oracle_m (PowerlessPartialTruth.formula_m j))) := by
  intro φ hφ
  apply hℳ φ
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
    ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, List.mem_append.mpr (Or.inr hφ)⟩))))

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (k : Nat) (α : carrier_l ℳ) (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U R H, ∃ hU₀ : ∃ x, member_l ℳ x U,
      PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧ member_l ℳ ω δ ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ δ U R H ∧
      Theory.Models (structure_l U hU₀) (Theory.ofList (basis_m k)) ∧
      PowerlessTruthReflectingStage.correct_l k ω e T t₁ t₂ t₃ U H :=
  PowerlessTruthReflectingStage.supported_l hℳ hω ht hT k
    PowerlessFiniteStageHierarchy.basis_m hierarchy_subset_l α hα

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStabilitySupport
