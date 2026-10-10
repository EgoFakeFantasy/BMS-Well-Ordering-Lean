import BMSConstructibleBridge.PowerlessFiniteHierarchyStep
import BMSConstructibleBridge.PowerlessOrdinalRecursionAbsolute
import BMSConstructibleBridge.PowerlessOrdinalHistoryAbsolute

/-!
# 有限核心早层中原累计层次源公式的绝对性

原递归的关系见证、任意前史和二次并值域界都由实际闭包给出。
先解释原规则，再比较递归，最后沿原 hierarchy_m 的替换传回任意项环境。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteHierarchySource

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageOperator.theory_m)
  (hωδ : member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ

theorem recursion_l (f α : type_l U) :
    PowerlessOrdinalRecursion.recursion_l (ℳ := structure_l U hU₀) PowerlessEvaluationHierarchy.operator_m
      (PowerlessEvaluationHierarchy.env_l ω e T t₁ t₂ t₃) f α ↔
      PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val f.val α.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  constructor
  · rintro ⟨B, hf, h⟩
    refine ⟨B.val, (PowerlessSourceGraphAbsolute.map_l hUT).mp hf, ?_⟩
    intro a Y hY
    obtain ⟨haU, hYU⟩ := PowerlessValueAbsolute.coordinates_l hUT f.property hY
    obtain ⟨H, hH, h⟩ := h ⟨a, haU⟩ ⟨Y, hYU⟩ ((PowerlessSourceGraphAbsolute.value_l hUT).mpr hY)
    exact ⟨H.val, (PowerlessOrdinalHistoryAbsolute.history_l hℳ hUT).mp hH,
      (PowerlessFiniteHierarchyStep.rule_l hℳ hω ht hT hU hδ h𝒩 hωδ _ H _).mp h⟩
  · rintro ⟨B, hf, h⟩
    obtain ⟨D, hD⟩ := PowerlessOrdinalHistoryAbsolute.bounds_l hℳ (B := U)
      (fun a ha b hb => PowerlessStageClosure.union_l hℳ hω hU hδ ht hT ha hb) f
    refine ⟨D, (PowerlessSourceGraphAbsolute.map_l hUT).mpr (PowerlessFunction.range_l hℳ hf hD), ?_⟩
    intro a Y hY
    obtain ⟨H, hH, h⟩ := h a.val Y.val ((PowerlessSourceGraphAbsolute.value_l hUT).mp hY)
    have hHU := PowerlessFiniteStageClosure.history_member_l hℳ hUT
      (PowerlessFiniteStageOperator.closure_models_l h𝒩) f.property a.property hH
    exact ⟨⟨H, hHU⟩, (PowerlessOrdinalHistoryAbsolute.history_l hℳ hUT).mpr hH,
      (PowerlessFiniteHierarchyStep.rule_l hℳ hω ht hT hU hδ h𝒩 hωδ a ⟨H, hHU⟩ Y).mpr h⟩

theorem presentation_l (f α : type_l U) :
    (PowerlessOrdinalRecursion.recursion_m PowerlessEvaluationHierarchy.operator_m).satisfies
      (((PowerlessComprehension.env_l (ℳ := structure_l U hU₀) (Γ := [.set, .set, .set, .set, .set, .set])
        (PowerlessEvaluationHierarchy.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃)).pushFree α).pushFree f) ↔
      PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val f.val α.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hR := PowerlessFiniteStageClosure.relation_exists_l hUT
    (PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hU hδ)
    (PowerlessFiniteStageOperator.closure_models_l h𝒩) α
  exact (PowerlessOrdinalRecursionAbsolute.source_l hℳ hUT PowerlessEvaluationHierarchy.operator_m
    (PowerlessEvaluationHierarchy.env_l ω e T t₁ t₂ t₃) f α hR).trans
      (recursion_l hℳ hω ht hT hU hδ h𝒩 hωδ f α)

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ f α : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessHierarchyPresentation.hierarchy_m w z V s₁ s₂ s₃ f α).satisfies η ↔
      PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val (f.eval η).val (α.eval η).val := by
  rw [← presentation_l hℳ hω ht hT hU hδ h𝒩 hωδ (f.eval η) (α.eval η)]
  simp only [PowerlessHierarchyPresentation.hierarchy_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => (PowerlessOrdinalRecursion.recursion_m PowerlessEvaluationHierarchy.operator_m).satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there .here) => exact Subtype.ext hw
    | .set, .there (.there (.there .here)) => exact Subtype.ext hz
    | .set, .there (.there (.there (.there .here))) => exact Subtype.ext hV
    | .set, .there (.there (.there (.there (.there .here)))) => exact Subtype.ext hs₁
    | .set, .there (.there (.there (.there (.there (.there .here))))) => exact Subtype.ext hs₂
    | .set, .there (.there (.there (.there (.there (.there (.there .here)))))) => exact Subtype.ext hs₃

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteHierarchySource
