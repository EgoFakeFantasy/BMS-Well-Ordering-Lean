import BMSConstructibleBridge.PowerlessEvaluationStepAbsolute
import BMSConstructibleBridge.PowerlessOrdinalHistoryAbsolute
import BMSConstructibleBridge.PowerlessEvaluationRecursion

/-!
# 原递归求值关系的传递子域绝对性

图的二次并提供域内统一值域；每个内部自然数前史是有限图，因而也在域内。
这里只比较原语义关系。原 evaluation_m 另量化序数关系图，其实际成员性
及不假定小结构核心的语法桥由 PowerlessEvaluationSourceAbsolute 接续。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)

include hℳ

theorem evaluation_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {ω e T A t₁ t₂ t₃ S F : type_l B}
    (hω : omega_l ω.val)
    (hU : ∀ a, member_l ℳ a B → ∀ b,
      (∀ x, member_l ℳ x b ↔ ∃ y, member_l ℳ y a ∧ member_l ℳ x y) → member_l ℳ b B)
    (hG : ∀ n, member_l ℳ n ω.val → ∀ g, map_l g n B → member_l ℳ g B)
    (hS : ∀ H n Y : type_l B,
      PowerlessEvaluationStep.step_l (ℳ := structure_l B hB) ω e T A t₁ t₂ t₃ S H n Y ↔
        PowerlessEvaluationStep.step_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val S.val H.val n.val Y.val) :
    PowerlessEvaluationRecursion.evaluation_l (ℳ := structure_l B hB) ω e T A t₁ t₂ t₃ S F ↔
      PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val S.val F.val := by
  constructor
  · rintro ⟨D, hF, h⟩
    refine ⟨D.val, (PowerlessSourceGraphAbsolute.map_l hBT).mp hF, ?_⟩
    intro n Y hY
    obtain ⟨hnB, hYB⟩ := PowerlessValueAbsolute.coordinates_l hBT F.property hY
    obtain ⟨H, hH, hY₀⟩ := h ⟨n, hnB⟩ ⟨Y, hYB⟩ ((PowerlessSourceGraphAbsolute.value_l hBT).mpr hY)
    exact ⟨H.val, (PowerlessOrdinalHistoryAbsolute.history_l hℳ hBT).mp hH,
      (hS H ⟨n, hnB⟩ ⟨Y, hYB⟩).mp hY₀⟩
  · rintro ⟨C, hF, h⟩
    obtain ⟨D, hD⟩ := PowerlessOrdinalHistoryAbsolute.bounds_l hℳ hU F
    have hF₀ := PowerlessFunction.range_l hℳ hF hD
    refine ⟨D, (PowerlessSourceGraphAbsolute.map_l hBT).mpr hF₀, ?_⟩
    intro n Y hY
    have hY₀ := (PowerlessSourceGraphAbsolute.value_l hBT).mp hY
    have hn := (PowerlessFunction.value_mem_l hℳ hF₀ hY₀).1
    obtain ⟨H, hH, hY₁⟩ := h n.val Y.val hY₀
    have hH₀ := PowerlessOrdinalHistory.map_l hℳ (PowerlessOmegaOrdinal.ordinal_l hℳ hω) hF₀ hn hH
    have hHB : member_l ℳ H B := by
      apply hG n.val hn H
      exact PowerlessFunction.range_l hℳ hH₀
        (fun x y hxy => hBT D.val y D.property (PowerlessFunction.value_mem_l hℳ hH₀ hxy).2)
    exact ⟨⟨H, hHB⟩, (PowerlessOrdinalHistoryAbsolute.history_l hℳ hBT).mpr hH,
      (hS ⟨H, hHB⟩ n Y).mpr hY₁⟩

theorem stage_l {ω e T t₁ t₂ t₃ β B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωβ : member_l ℳ ω β) (hβ : PowerlessStagePair.limit_l β) :
    ∃ hB₀ : ∃ x, member_l ℳ x B, ∃ w z U s₁ s₂ s₃ : type_l B,
      w.val = ω ∧ z.val = e ∧ U.val = T ∧ s₁.val = t₁ ∧ s₂.val = t₂ ∧ s₃.val = t₃ ∧
      ∀ A S F : type_l B,
        PowerlessEvaluationRecursion.evaluation_l (ℳ := structure_l B hB₀) w z U A s₁ s₂ s₃ S F ↔
          PowerlessEvaluationRecursion.evaluation_l ω e T A.val t₁ t₂ t₃ S.val F.val := by
  obtain ⟨hB₀, w, z, U, s₁, s₂, s₃, hw, hz, hU, h₁, h₂, h₃, hS⟩ :=
    PowerlessEvaluationStepAbsolute.stage_l hℳ hω ht hT hB hωβ hβ
  have hBT := PowerlessStageStructure.transitive_l hℳ hω ht hT hB
  have hG := PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hB hβ
    (fun x hx => PowerlessOrdinal.transitive_l hβ.1 ω x hωβ hx)
  refine ⟨hB₀, w, z, U, s₁, s₂, s₃, hw, hz, hU, h₁, h₂, h₃, ?_⟩
  intro A S F
  have hS₀ : ∀ H n Y : type_l B,
      PowerlessEvaluationStep.step_l (ℳ := structure_l B hB₀) w z U A s₁ s₂ s₃ S H n Y ↔
        PowerlessEvaluationStep.step_l w.val z.val U.val A.val s₁.val s₂.val s₃.val S.val H.val n.val Y.val := by
    simpa only [hw, hz, hU, h₁, h₂, h₃] using hS A S
  have hw₀ : omega_l w.val := hw.symm ▸ hω
  have hG₀ : ∀ n, member_l ℳ n w.val → ∀ g, map_l g n B → member_l ℳ g B := by
    simpa only [hw] using hG
  simpa only [hw, hz, hU, h₁, h₂, h₃] using
    (evaluation_l hℳ hBT (F := F) hw₀
      (fun _ ha _ hb => PowerlessStageClosure.union_l hℳ hω hB hβ ht hT ha hb) hG₀ hS₀)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationAbsolute
