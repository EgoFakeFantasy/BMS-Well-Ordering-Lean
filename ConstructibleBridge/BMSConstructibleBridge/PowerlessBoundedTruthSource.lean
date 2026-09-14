import BMSConstructibleBridge.PowerlessBoundedTruth
import BMSConstructibleBridge.PowerlessFiniteStageEvaluation
import BMSConstructibleBridge.PowerlessCoreStageEvaluation

/-!
# 有界真值候选的早层源解释

逐项核验传递性、完整赋值集、完整求值图与查询的原公式；见证仍在
源层量化。源解释本身不要求早层满足有限或完整核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedTruthSource

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
  (hωδ : member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ hωδ


theorem certificate_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ c f A S F n : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessBoundedTruth.certificate_m w z V s₁ s₂ s₃ c f A S F n).satisfies η ↔
      PowerlessBoundedTruth.certificate_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (c.eval η).val (f.eval η).val (A.eval η).val (S.eval η).val (F.eval η).val (n.eval η).val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hA : (PowerlessOrdinalBounded.transitive_m A).satisfies η ↔
      PowerlessNaturalOrder.transitive_l (A.eval η).val := by
    rw [PowerlessSourceAmbient.formula_l hUT (PowerlessOrdinalBounded.transitive_delta_l A) η,
      PowerlessOrdinalBounded.transitive_formula_l, PowerlessSourceAmbient.term_l]
  have hn : (SecondOrderObjectSyntax.member_m n w).satisfies η ↔ member_l ℳ (n.eval η).val ω.val := by
    change member_l ℳ (n.eval η).val (w.eval η).val ↔ _
    rw [hw]
  have hS : (PowerlessEvaluationOperator.assignments_m w A S).satisfies η ↔
      PowerlessEvaluationOperator.assignments_l ω.val (A.eval η).val (S.eval η).val := by
    have h := PowerlessEvaluationOperator.assignments_formula_l η w A S
    rw [show w.eval η = ω from Subtype.ext hw] at h
    exact h.trans (PowerlessCoreStageEvaluation.assignments_l hℳ hω ht hT hU hωδ hδ)
  exact and_congr hA (and_congr hn
    (and_congr (PowerlessSourceGraphAbsolute.map_source_l hUT η f n A)
      (and_congr hS (and_congr
        (PowerlessEvaluationSourceAbsolute.stage_l hℳ hω ht hT hU hωδ hδ
          η w z V A s₁ s₂ s₃ S F hw hz hV hs₁ hs₂ hs₃)
        ((PowerlessEvaluationClause.query_formula_l η F c f).trans (PowerlessValueAbsolute.query_l hUT))))))

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ c f : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessBoundedTruth.truth_m w z V s₁ s₂ s₃ c f).satisfies η ↔
      ∃ A S F n : type_l U, PowerlessBoundedTruth.certificate_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (c.eval η).val (f.eval η).val A.val S.val F.val n.val := by
  let q (t : Term ℒ Γ Δ .set) := (((t.weakenBound SetTheory.SetSort.set).weakenBound
    SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  simp only [PowerlessBoundedTruth.truth_m, Formula.satisfies]
  apply exists_congr
  intro A
  apply exists_congr
  intro S
  apply exists_congr
  intro F
  apply exists_congr
  intro n
  have h := certificate_l hℳ hω ht hT hU hδ hωδ ((((η.pushBound A).pushBound S).pushBound F).pushBound n)
    (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (q c) (q f)
    (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)
    (by simpa only [q, Term.eval_weakenBound] using hw)
    (by simpa only [q, Term.eval_weakenBound] using hz)
    (by simpa only [q, Term.eval_weakenBound] using hV)
    (by simpa only [q, Term.eval_weakenBound] using hs₁)
    (by simpa only [q, Term.eval_weakenBound] using hs₂)
    (by simpa only [q, Term.eval_weakenBound] using hs₃)
  simp only [q, Term.eval_weakenBound] at h
  simpa only [Term.eval, Env.pushBound, Assignment.push] using h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedTruthSource
