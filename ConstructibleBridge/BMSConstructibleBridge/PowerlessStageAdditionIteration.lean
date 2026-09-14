import BMSConstructibleBridge.PowerlessAdditionIterationCut
import BMSConstructibleBridge.PowerlessAdditionAbsolute
import BMSConstructibleBridge.PowerlessStageAdditionFinite

/-!
# 原加法迭代图的早级成员性与原公式解释

自然数初值的整条迭代图由有限值公式定义在 Cω+1 上，故进入
Cω+2 及 proper 极限层。以此消去原无限加法绝对性的图成员前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageAdditionIteration

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem subset_l {α A F : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hF : map_l F ω ω) : ThirdOrderSemantics.subset_l F A := by
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOmegaOrdinal.ordinal_l hℳ hω) e T t₁ t₂ t₃
  have hωB := PowerlessStageParameters.naturals_l hℳ hω ht hT hB (fun _ hx => hx)
  have hω₀ : PowerlessStagePair.limit_l ω := ⟨PowerlessOmegaOrdinal.ordinal_l hℳ hω,
    ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1⟩, PowerlessOmegaOrdinal.limit_l hℳ hω⟩
  intro p hp
  obtain ⟨n, t, hn, ht₀, hp⟩ := hF.1 p hp
  have hpB := PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hB hω₀ (hωB n hn) (hωB t ht₀) hp
  exact PowerlessStageStructure.subset_l hℳ hω hB hA hωα p hpB

theorem operator_l {α A D a F : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D)
    (ha : member_l ℳ a ω) (hF : PowerlessAddition.iteration_l ω e a F) : member_l ℳ F D :=
  PowerlessAdditionIterationCut.operator_l hℳ hω ht hT hD
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hA)
    (PowerlessStageParameters.omega_l hℳ hω ht hT hA hωα) ha hF
    (PowerlessStageAdditionFinite.graphs_above_l hℳ hω ht hT hA hωα)
    (subset_l hℳ hω ht hT hA hωα (PowerlessAdditionIteration.map_l hℳ hω ht.1 ha hF))

theorem successor_l {α β A B a F : carrier_l ℳ}
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωα : member_l ℳ ω α) (hαβ : PowerlessNatural.successor_l α β)
    (ha : member_l ℳ a ω) (hF : PowerlessAddition.iteration_l ω e a F) : member_l ℳ F B :=
  operator_l hℳ hω ht hT hA hωα (PowerlessStageStructure.successor_l hℳ hω ht hT hA hB hαβ) ha hF

theorem second_l {a F : carrier_l ℳ} (ha : member_l ℳ a ω) (hF : PowerlessAddition.iteration_l ω e a F) :
    ∃ α β B, PowerlessNatural.successor_l ω α ∧ PowerlessNatural.successor_l α β ∧
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B ∧ member_l ℳ F B := by
  obtain ⟨α, hα⟩ := PowerlessNatural.successor_exists_l hℳ ω
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ α
  have hα₀ := PowerlessOrdinalOrder.successor_l hℳ (PowerlessOmegaOrdinal.ordinal_l hℳ hω) hα
  have hβ₀ := PowerlessOrdinalOrder.successor_l hℳ hα₀ hβ
  obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l hℳ hω hα₀ e T t₁ t₂ t₃
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω hβ₀ e T t₁ t₂ t₃
  exact ⟨α, β, B, hα, hβ, hB, successor_l hℳ hω ht hT hA hB ((hα ω).mpr (Or.inr rfl)) hβ ha hF⟩

theorem limit_l {α A a F : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α)
    (ha : member_l ℳ a ω) (hF : PowerlessAddition.iteration_l ω e a F) : member_l ℳ F A := by
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
  exact PowerlessStageClosure.image_l hℳ hω hA hB hβα hD F
    (operator_l hℳ hω ht hT hB ((hβ ω).mpr (Or.inr rfl)) hD ha hF)

theorem stage_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α) :
    ∃ hA₀ : ∃ x, member_l ℳ x A, ∃ w z : type_l A, w.val = ω ∧ z.val = e ∧
      ∀ a b c : type_l A, member_l ℳ a.val ω →
        (PowerlessAddition.addition_l (ℳ := structure_l A hA₀) w z a b c ↔
          PowerlessAddition.addition_l ω e a.val b.val c.val) := by
  obtain ⟨hw, hz, _⟩ := PowerlessStageParameters.proper_l hℳ hω ht hT hA hωα
  have hAT := PowerlessStageStructure.transitive_l hℳ hω ht hT hA
  refine ⟨⟨ω, hw⟩, ⟨ω, hw⟩, ⟨e, hz⟩, rfl, rfl, ?_⟩
  intro a b c ha
  exact PowerlessAdditionAbsolute.addition_l hℳ hAT hω ht.1 ha
    (fun F hF => limit_l hℳ hω ht hT hA hωα hα ha hF)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageAdditionIteration
