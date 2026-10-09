import BMSConstructibleBridge.SecondOrderRelativeHierarchyStrongFormula
import BMSConstructibleBridge.SecondOrderPredecessorComparability
import BMSConstructibleBridge.SecondOrderRelativeHierarchyTheorem

/-! # 原 Z₂ 中的强闭合相对历史

实际对象句同时证明历史、根良基、传递、子集单调、基集保持及前驱阶段
隶属。共同上界下的可比性明列为前提；尚不证明最终源公理覆盖或 BMS 句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyStrongTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderWellFoundedRecursionTheorem (wellFounded_m transitive_m irreflexive_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

structure spec_l (B R S : set_l ℳ) (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) : Prop where
  history : SecondOrderRelativeHierarchy.spec_l B R S
  wellFounded : ∀ n W, SecondOrderSections.spec_l S n W → SecondOrderDomain.wf_l W (zero_l ℳ)
  transitive : ∀ n W, SecondOrderSections.spec_l S n W → ∀ hW : SecondOrderDomain.wf_l W (zero_l ℳ),
    SecondOrderTransitiveSuperset.transitive_l ⟨W, zero_l ℳ, hW⟩
  monotone : ∀ n, SecondOrderRelativeHierarchyMonotonicityStep.rows_l R S n
  base : ∀ n W, SecondOrderSections.spec_l S n W → ∀ hW : SecondOrderDomain.wf_l W (zero_l ℳ),
    SecondOrderGraphSubsetFormula.subset_l ⟨B, zero_l ℳ, hB⟩ ⟨W, zero_l ℳ, hW⟩
  members : ∀ n, SecondOrderRelativeHierarchyMembershipStep.rows_l R S n

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B R S : Term signature_m Γ Δ .set)
    (hB : SecondOrderDomain.wf_l (B.eval η) (zero_l ℳ)) :
    (SecondOrderRelativeHierarchyStrongFormula.formula_m B R S).satisfies η ↔
      spec_l (B.eval η) (R.eval η) (S.eval η) hB := by
  simp only [SecondOrderRelativeHierarchyStrongFormula.formula_m,
    SecondOrderRelativeHierarchyClosedFormula.formula_m, Formula.satisfies,
    SecondOrderRelativeHierarchyHistoryFormula.formula_l hℳ,
    SecondOrderRelativeHierarchyClosedFormula.transitive_formula_l hℳ,
    SecondOrderRelativeHierarchyClosedFormula.monotone_formula_l hℳ,
    SecondOrderRelativeHierarchyStrongFormula.base_formula_l hℳ _ _ _ hB,
    SecondOrderRelativeHierarchyStrongFormula.member_formula_l]
  constructor
  · intro h
    exact ⟨fun n W hW => (h.1.1 n W hW).2, fun n W hW => (h.1.1 n W hW).1,
      h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩
  · intro h
    exact ⟨⟨fun n W hW => ⟨h.wellFounded n W hW, h.history n W hW⟩,
      h.transitive, h.monotone⟩, h.base, h.members⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (B R : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hTrans : ∀ a b c, SecondOrderPairing.relation_l R a b → SecondOrderPairing.relation_l R b c →
      SecondOrderPairing.relation_l R a c) (hIrrefl : ∀ n, ¬SecondOrderPairing.relation_l R n n)
    (hCompare : SecondOrderRelativeHierarchyMembershipStep.comparable_l R) : ∃ S, spec_l B R S hB := by
  obtain ⟨S, hS⟩ := SecondOrderRelativeHierarchy.exists_l hℳ B R hWf hTrans hIrrefl
  exact ⟨S, hS, SecondOrderRelativeHierarchy.rows_wf_l hℳ hB hWf hS,
    SecondOrderRelativeHierarchyTransitivity.transitive_l hℳ hB hBase hWf hS,
    SecondOrderRelativeHierarchyMonotonicity.monotone_l hℳ hB hBase hWf hS,
    SecondOrderRelativeHierarchyBase.contains_l hℳ hB hBase hWf hS,
    SecondOrderRelativeHierarchyMembership.member_l hℳ hB hBase hWf hCompare hS⟩

def sentence_m : Sentence signature_m :=
  .forallE .set <| .forallE .set <| .imp
    (GraphTranslation.domain_m (.bvar (.there .here)) (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (SecondOrderGraphTransitivityFormula.formula_m (.bvar (.there .here))
      (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (wellFounded_m (.bvar .here)) <| .imp (transitive_m (.bvar .here)) <|
    .imp (irreflexive_m (.bvar .here)) <| .imp (SecondOrderPredecessorComparability.formula_m (.bvar .here)) <|
    .existsE .set <| SecondOrderRelativeHierarchyStrongFormula.formula_m
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem models_l (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  intro B R hB hBase hWf hTrans hIrrefl hCompare
  have hB' : SecondOrderDomain.wf_l B (zero_l ℳ) := (SecondOrderInterpretation.domain_l _ _ _).mp hB
  have hBase' := (SecondOrderGraphTransitivityFormula.formula_l hℳ
    ((Env.empty (M := ℳ)).pushBound B |>.pushBound R) (.bvar (.there .here))
    (Term.app (σ := signature_m) .zero .nil) hB').mp hBase
  have hWf' := (SecondOrderWellFoundedRecursionTheorem.wellFounded_formula_l _ _).mp hWf
  have hTrans' := (SecondOrderWellFoundedRecursionTheorem.transitive_formula_l _ _).mp hTrans
  have hIrrefl' := (SecondOrderWellFoundedRecursionTheorem.irreflexive_formula_l _ _).mp hIrrefl
  have hCompare' := (SecondOrderPredecessorComparability.formula_l _ _).mp hCompare
  obtain ⟨S, hS⟩ := exists_l hℳ B R hB' hBase' hWf' hTrans' hIrrefl' hCompare'
  exact ⟨S, (formula_l hℳ (((Env.empty (M := ℳ)).pushBound B).pushBound R |>.pushBound S)
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here) hB').mpr hS⟩

theorem derives_m : Derives theory_m [] sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => models_l hℳ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyStrongTheorem
