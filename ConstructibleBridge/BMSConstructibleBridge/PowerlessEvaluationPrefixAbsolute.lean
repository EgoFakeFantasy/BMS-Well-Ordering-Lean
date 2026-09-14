import BMSConstructibleBridge.PowerlessEvaluationPrefix
import BMSConstructibleBridge.PowerlessEvaluationSourceAbsolute
import BMSConstructibleBridge.PowerlessStageFiniteRelation

/-!
# 原求值初段公式在小层中的正确解释

使用原 recursion_m 的有限初段关系图，不把小结构假设为核心模型。
原步骤的绝对性与有限前史闭包处理语义关系，域内关系图处理原语法。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationPrefixAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)

include hℳ

theorem prefix_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {ω e T A t₁ t₂ t₃ S F m : type_l B}
    (hω : omega_l ω.val) (hm : member_l ℳ m.val ω.val)
    (hU : ∀ a, member_l ℳ a B → ∀ b,
      (∀ x, member_l ℳ x b ↔ ∃ y, member_l ℳ y a ∧ member_l ℳ x y) → member_l ℳ b B)
    (hG : ∀ n, member_l ℳ n ω.val → ∀ g, map_l g n B → member_l ℳ g B)
    (hS : ∀ H n Y : type_l B,
      PowerlessEvaluationStep.step_l (ℳ := structure_l B hB) ω e T A t₁ t₂ t₃ S H n Y ↔
        PowerlessEvaluationStep.step_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val S.val H.val n.val Y.val) :
    PowerlessEvaluationPrefix.prefix_l (ℳ := structure_l B hB) ω e T A t₁ t₂ t₃ S F m ↔
      PowerlessEvaluationPrefix.prefix_l ω.val e.val T.val A.val t₁.val t₂.val t₃.val S.val F.val m.val := by
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
    have hH₀ := PowerlessOrdinalHistory.map_l hℳ
      (PowerlessOrdinal.mem_l (PowerlessOmegaOrdinal.ordinal_l hℳ hω) hm) hF₀ hn hH
    have hHB : member_l ℳ H B := by
      apply hG n.val (PowerlessNaturalOrder.subset_l hℳ hω m.val hm n.val hn) H
      exact PowerlessFunction.range_l hℳ hH₀
        (fun x y hxy => hBT D.val y D.property (PowerlessFunction.value_mem_l hℳ hH₀ hxy).2)
    exact ⟨⟨H, hHB⟩, (PowerlessOrdinalHistoryAbsolute.history_l hℳ hBT).mpr hH,
      (hS ⟨H, hHB⟩ n Y).mpr hY₁⟩

theorem source_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {Γ Δ : SortContext ℒ}
    (η : Env (structure_l B hB) Γ Δ) (ω e T A t₁ t₂ t₃ S F m : Term ℒ Γ Δ .set)
    (hR : ∃ R : type_l B, PowerlessOrdinalRelation.relation_l (m.eval η).val R.val) :
    (PowerlessEvaluationPrefix.prefix_m ω e T A t₁ t₂ t₃ S F m).satisfies η ↔
      PowerlessEvaluationPrefix.prefix_l (ω.eval η) (e.eval η) (T.eval η) (A.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (S.eval η) (F.eval η) (m.eval η) :=
  (PowerlessEvaluationPrefix.presentation_l η ω e T A t₁ t₂ t₃ S F m).trans
    ((PowerlessOrdinalRecursionAbsolute.source_l hℳ hBT PowerlessEvaluationStep.operator_m _ _ _ hR).trans
      (PowerlessEvaluationPrefix.recursion_iff_l _ _ _ _ _ _ _ _ _ _))

theorem stage_l {ω e T t₁ t₂ t₃ β B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωβ : member_l ℳ ω β) (hβ : PowerlessStagePair.limit_l β)
    {hB₀ : ∃ x, member_l ℳ x B} {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB₀) Γ Δ)
    (w z U A s₁ s₂ s₃ S F m : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω) (hz : (z.eval η).val = e) (hU : (U.eval η).val = T)
    (h₁ : (s₁.eval η).val = t₁) (h₂ : (s₂.eval η).val = t₂) (h₃ : (s₃.eval η).val = t₃)
    (hm : member_l ℳ (m.eval η).val ω) :
    (PowerlessEvaluationPrefix.prefix_m w z U A s₁ s₂ s₃ S F m).satisfies η ↔
      PowerlessEvaluationPrefix.prefix_l ω e T (A.eval η).val t₁ t₂ t₃
        (S.eval η).val (F.eval η).val (m.eval η).val := by
  have hBT := PowerlessStageStructure.transitive_l hℳ hω ht hT hB
  obtain ⟨R, hR, hRB⟩ := PowerlessStageFiniteRelation.exists_l hℳ hω ht hT hB hωβ hm
  obtain ⟨hB₁, w₁, z₁, U₁, r₁, r₂, r₃, hw₁, hz₁, hU₁, hr₁, hr₂, hr₃, hS⟩ :=
    PowerlessEvaluationStepAbsolute.stage_l hℳ hω ht hT hB hωβ hβ
  have hw₂ : w.eval η = w₁ := Subtype.ext (hw.trans hw₁.symm)
  have hz₂ : z.eval η = z₁ := Subtype.ext (hz.trans hz₁.symm)
  have hU₂ : U.eval η = U₁ := Subtype.ext (hU.trans hU₁.symm)
  have hs₁ : s₁.eval η = r₁ := Subtype.ext (h₁.trans hr₁.symm)
  have hs₂ : s₂.eval η = r₂ := Subtype.ext (h₂.trans hr₂.symm)
  have hs₃ : s₃.eval η = r₃ := Subtype.ext (h₃.trans hr₃.symm)
  rw [← hw₂, ← hz₂, ← hU₂, ← hs₁, ← hs₂, ← hs₃] at hS
  have hS₀ : ∀ H n Y : type_l B,
      PowerlessEvaluationStep.step_l (ℳ := structure_l B hB₀)
        (w.eval η) (z.eval η) (U.eval η) (A.eval η) (s₁.eval η) (s₂.eval η) (s₃.eval η) (S.eval η) H n Y ↔
      PowerlessEvaluationStep.step_l (w.eval η).val (z.eval η).val (U.eval η).val (A.eval η).val
        (s₁.eval η).val (s₂.eval η).val (s₃.eval η).val (S.eval η).val H.val n.val Y.val := by
    simpa only [hw, hz, hU, h₁, h₂, h₃] using hS (A.eval η) (S.eval η)
  have hG := PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hB hβ
    (fun x hx => PowerlessOrdinal.transitive_l hβ.1 ω x hωβ hx)
  have hG₀ : ∀ n, member_l ℳ n (w.eval η).val → ∀ g, map_l g n B → member_l ℳ g B := by
    simpa only [hw] using hG
  have h := (source_l hℳ hBT η w z U A s₁ s₂ s₃ S F m ⟨⟨R, hRB⟩, hR⟩).trans
    (prefix_l hℳ hBT (F := F.eval η) (m := m.eval η)
      (by simpa only [hw] using hω) (by simpa only [hw] using hm)
      (fun _ ha _ hb => PowerlessStageClosure.union_l hℳ hω hB hβ ht hT ha hb) hG₀ hS₀)
  simpa only [hw, hz, hU, h₁, h₂, h₃] using h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationPrefixAbsolute
