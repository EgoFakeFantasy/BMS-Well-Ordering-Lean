import BMSConstructibleBridge.SecondOrderRelativeHierarchyAgreement
import BMSConstructibleBridge.SecondOrderPredecessorCorrespondenceFormula

/-! # 原 Z₂ 中历史换码一致性的对象推导

实际对象句绑定双方基图、双方前驱关系、对应实数与两套历史。对象前提保留
各项真实规格；本定理不是 BMS 良序终局，也不声称源收集公理已经验证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyAgreementTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderWellFoundedRecursionTheorem (wellFounded_m transitive_m irreflexive_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def statement_m {Γ Δ : SortContext signature_m} (B B' R R' I S T : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .imp (GraphTranslation.domain_m B (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (GraphTranslation.domain_m B' (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (GraphTranslation.atom_m GraphSyntax.eq_m B B'
      (Term.app (σ := signature_m) .zero .nil) (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (wellFounded_m R) <| .imp (transitive_m R') <| .imp (irreflexive_m R') <|
    .imp (SecondOrderPredecessorCorrespondenceFormula.formula_m R R' I) <|
    .imp (SecondOrderRelativeHierarchyStrongFormula.formula_m B R S) <|
    .imp (SecondOrderRelativeHierarchyStrongFormula.formula_m B' R' T) <|
    .forallE .num <| SecondOrderRelativeHierarchyAgreement.formula_m
      (I.weakenBound sort_m.num) (S.weakenBound sort_m.num) (T.weakenBound sort_m.num) (.bvar .here)

def schema_m : Formula signature_m [] [.set, .set, .set, .set, .set, .set, .set] :=
  statement_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))

def sentence_m : Sentence signature_m := Metatheory.Formula.forall_close schema_m

theorem statement_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B B' R R' I S T : Term signature_m Γ Δ .set) :
    (statement_m B B' R R' I S T).satisfies η := by
  intro hB hB' hEq hWf hTrans hIrrefl hI hS hT n
  have hBwf := (SecondOrderInterpretation.domain_l η B (Term.app (σ := signature_m) .zero .nil)).mp hB
  have hB'wf := (SecondOrderInterpretation.domain_l η B' (Term.app (σ := signature_m) .zero .nil)).mp hB'
  have hEq' : SecondOrderGraph.eq_l ⟨B.eval η, zero_l ℳ, hBwf⟩ ⟨B'.eval η, zero_l ℳ, hB'wf⟩ :=
    (SecondOrderInterpretation.eq_l η B B' (Term.app (σ := signature_m) .zero .nil)
      (Term.app (σ := signature_m) .zero .nil)).mp hEq
  have hWf' := (SecondOrderWellFoundedRecursionTheorem.wellFounded_formula_l η R).mp hWf
  have hTrans' := (SecondOrderWellFoundedRecursionTheorem.transitive_formula_l η R').mp hTrans
  have hIrrefl' := (SecondOrderWellFoundedRecursionTheorem.irreflexive_formula_l η R').mp hIrrefl
  have hI' := (SecondOrderPredecessorCorrespondenceFormula.formula_l η R R' I).mp hI
  have hS' := (SecondOrderRelativeHierarchyStrongTheorem.formula_l hℳ η B R S hBwf).mp hS
  have hT' := (SecondOrderRelativeHierarchyStrongTheorem.formula_l hℳ η B' R' T hB'wf).mp hT
  have hRows := SecondOrderRelativeHierarchyAgreement.agree_l hℳ hEq' hI'
    (fun a b hab hba => hIrrefl' a (hTrans' a b a hab hba)) hS' hT' hWf' n
  apply (SecondOrderRelativeHierarchyAgreement.formula_arguments_l (η.pushBound n)
    (I.weakenBound sort_m.num) (S.weakenBound sort_m.num) (T.weakenBound sort_m.num) (.bvar .here)).mpr
  rw [Term.eval_weakenBound η n I, Term.eval_weakenBound η n S, Term.eval_weakenBound η n T]
  dsimp only [Term.eval, Env.pushBound, Assignment.push]
  exact hRows

theorem models_l (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact statement_formula_l hℳ η _ _ _ _ _ _ _

theorem derives_m : Derives theory_m [] sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyAgreementTheorem
