import BMSConstructibleBridge.PowerlessFiniteStageOperator

/-!
# 有限核心早层中原累计步骤的源公式解释

直接解释原 step_m，算子见证由已证 D 闭包取回。
不先使用需要内部完整核心的 step_formula_l，也不限制前史 H 为有限图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteHierarchyStep

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

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ H Y : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessHierarchyStep.step_m w z V s₁ s₂ s₃ H Y).satisfies η ↔
      PowerlessHierarchyStep.step_l ω.val e.val T.val t₁.val t₂.val t₃.val (H.eval η).val (Y.eval η).val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  let q (t : Term ℒ Γ Δ .set) :=
    (((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  have hd (x a B D : type_l U) :
      (PowerlessEvaluationOperator.operator_m (q w) (q z) (q V) (q s₁) (q s₂) (q s₃)
        (.bvar (.there .here)) (.bvar .here)).satisfies ((((η.pushBound x).pushBound a).pushBound B).pushBound D) ↔
      PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val B.val D.val := by
    have h := PowerlessFiniteStageOperator.source_l hℳ hω ht hT hU hδ h𝒩 hωδ
      ((((η.pushBound x).pushBound a).pushBound B).pushBound D)
      (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (.bvar (.there .here)) (.bvar .here)
      (by simpa only [q, Term.eval_weakenBound] using hw)
      (by simpa only [q, Term.eval_weakenBound] using hz)
      (by simpa only [q, Term.eval_weakenBound] using hV)
      (by simpa only [q, Term.eval_weakenBound] using hs₁)
      (by simpa only [q, Term.eval_weakenBound] using hs₂)
      (by simpa only [q, Term.eval_weakenBound] using hs₃)
    simpa only [Term.eval, Env.pushBound, Assignment.push] using h
  have h₀ : (PowerlessHierarchyStep.step_m w z V s₁ s₂ s₃ H Y).satisfies η ↔
      ∀ x : type_l U, member_l ℳ x.val (Y.eval η).val ↔ ∃ a B D : type_l U,
        value_l (H.eval η).val a.val B.val ∧
        PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val B.val D.val ∧
        member_l ℳ x.val D.val := by
    simp only [PowerlessHierarchyStep.step_m, Formula.satisfies, value_formula_l,
      SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
    apply forall_congr'
    intro x
    apply iff_congr Iff.rfl
    apply exists_congr
    intro a
    apply exists_congr
    intro B
    apply exists_congr
    intro D
    exact and_congr (PowerlessSourceGraphAbsolute.value_l hUT) (and_congr (hd x a B D) Iff.rfl)
  rw [h₀]
  constructor
  · intro h x
    constructor
    · intro hx
      obtain ⟨a, B, D, hB, hD, hx⟩ := (h ⟨x, hUT (Y.eval η).val x (Y.eval η).property hx⟩).mp hx
      exact ⟨a.val, B.val, D.val, hB, hD, hx⟩
    · rintro ⟨a, B, D, hB, hD, hx⟩
      obtain ⟨haU, hBU⟩ := PowerlessValueAbsolute.coordinates_l hUT (H.eval η).property hB
      have hDU := PowerlessFiniteStageOperator.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hBU hD
      exact (h ⟨x, hUT D x hDU hx⟩).mpr ⟨⟨a, haU⟩, ⟨B, hBU⟩, ⟨D, hDU⟩, hB, hD, hx⟩
  · intro h x
    constructor
    · intro hx
      obtain ⟨a, B, D, hB, hD, hx⟩ := (h x.val).mp hx
      obtain ⟨haU, hBU⟩ := PowerlessValueAbsolute.coordinates_l hUT (H.eval η).property hB
      have hDU := PowerlessFiniteStageOperator.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hBU hD
      exact ⟨⟨a, haU⟩, ⟨B, hBU⟩, ⟨D, hDU⟩, hB, hD, hx⟩
    · rintro ⟨a, B, D, hB, hD, hx⟩
      exact (h x.val).mpr ⟨a.val, B.val, D.val, hB, hD, hx⟩

theorem rule_l (a H Y : type_l U) :
    PowerlessWellRecursionSyntax.rule_l (ℳ := structure_l U hU₀) PowerlessEvaluationHierarchy.operator_m
      (PowerlessEvaluationHierarchy.env_l ω e T t₁ t₂ t₃) a H Y ↔
      PowerlessHierarchyStep.step_l ω.val e.val T.val t₁.val t₂.val t₃.val H.val Y.val := by
  let η : Env (structure_l U hU₀) [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    (((PowerlessComprehension.env_l (ℳ := structure_l U hU₀) (Γ := [.set, .set, .set, .set, .set, .set])
    (PowerlessEvaluationHierarchy.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃)).pushFree a).pushFree H).pushFree Y
  exact source_l hℳ hω ht hT hU hδ h𝒩 hωδ η
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there .here)) (.fvar .here) rfl rfl rfl rfl rfl rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteHierarchyStep
