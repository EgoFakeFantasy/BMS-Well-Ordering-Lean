import BMSConstructibleBridge.SecondOrderFiniteDisjunctionCorrectness

/-! # 内部有限析取正确性的原 Z₂ 对象模式

合法性图与求值图的完整固定点方程作为显式守卫进入对象闭句。所有长度、
赋值码及公式码均由对象数量词量化，没有把外部 AST 归纳冒充内部码覆盖。
固定点存在由已有原 Z₂ 对象定理提供；这些闭句验证同一实际码的正确性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteDisjunctionDerives

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) : Term signature_m (.num :: Γ) Δ s :=
  t.weakenBound sort_m.num

def validity_m {Γ Δ : SortContext signature_m} (V : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .forallE .num (.forallE .num (.iff
    (GraphSyntax.edge_m (up (up V)) (.bvar (.there .here)) (.bvar .here))
    (SecondOrderInternalFormulaSyntax.rule_m (up (up V)) (.bvar (.there .here)) (.bvar .here))))

theorem validity_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V : Term signature_m Γ Δ .set) :
    (validity_m V).satisfies η ↔ SecondOrderInternalFormulaSyntax.spec_l (V.eval η) := by
  simp only [validity_m, Formula.satisfies, SecondOrderPairing.edge_l,
    SecondOrderInternalFormulaSyntax.rule_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

private def evaluation_bind_m {Γ Δ : SortContext signature_m} (E D Q R T : Term signature_m Γ Δ .set)
    (n a : Term signature_m Γ Δ .num) :
    Substitution signature_m [] SecondOrderEvaluationRule.context_m Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => n
    | .there .here => a
    | .there (.there .here) => T
    | .there (.there (.there .here)) => E
    | .there (.there (.there (.there .here))) => D
    | .there (.there (.there (.there (.there .here)))) => Q
    | .there (.there (.there (.there (.there (.there .here))))) => R)

def evaluation_body_m {Γ Δ : SortContext signature_m} (E D Q R T : Term signature_m Γ Δ .set)
    (n a : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  SecondOrderEvaluationRule.formula_m.substitute (evaluation_bind_m E D Q R T n a)

theorem evaluation_body_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E D Q R T : Term signature_m Γ Δ .set) (n a : Term signature_m Γ Δ .num) :
    (evaluation_body_m E D Q R T n a).satisfies η ↔
      SecondOrderEvaluationRule.rule_l (E.eval η) (D.eval η) (Q.eval η) (R.eval η) (T.eval η)
        (n.eval η) (a.eval η) := by
  rw [evaluation_body_m, Formula.satisfies_substitute, SecondOrderEvaluationRule.formula_l]
  rfl

def evaluation_m {Γ Δ : SortContext signature_m} (E D Q R T : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .forallE .num (.forallE .num (.iff
    (GraphSyntax.edge_m (up (up T)) (.bvar (.there .here)) (.bvar .here))
    (evaluation_body_m (up (up E)) (up (up D)) (up (up Q)) (up (up R)) (up (up T))
      (.bvar (.there .here)) (.bvar .here))))

theorem evaluation_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E D Q R T : Term signature_m Γ Δ .set) :
    (evaluation_m E D Q R T).satisfies η ↔
      SecondOrderEvaluationEquations.spec_l (E.eval η) (D.eval η) (Q.eval η) (R.eval η) (T.eval η) := by
  simp only [evaluation_m, Formula.satisfies, SecondOrderPairing.edge_l,
    evaluation_body_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def legality_schema_m : Formula signature_m [] [.set, .set] :=
  let S : Term signature_m [] [.set, .set] .set := .fvar .here
  let V := .fvar (.there .here)
  .imp (SecondOrderFiniteDisjunctionSyntax.fixed_m S) (.imp (validity_m V)
    (.forallE .num (SecondOrderFiniteDisjunctionCorrectness.legal_m (up S) (up V) (.bvar .here))))

def legality_sentence_m : Sentence signature_m := Metatheory.Formula.forall_close legality_schema_m

theorem legality_models_l (hℳ : Theory.Models ℳ theory_m) : legality_sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [legality_schema_m, Formula.satisfies, SecondOrderFiniteDisjunctionSyntax.fixed_formula_l,
    validity_formula_l, SecondOrderFiniteDisjunctionCorrectness.legal_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact fun hS hV => SecondOrderFiniteDisjunctionCorrectness.legal_l hℳ hS hV

theorem legality_derives_m : Derives theory_m [] legality_sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => legality_models_l hℳ)

def truth_schema_m : Formula signature_m [] [.set, .set, .set, .set, .set, .set] :=
  let S : Term signature_m [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let E := .fvar (.there .here)
  let D := .fvar (.there (.there .here))
  let Q := .fvar (.there (.there (.there .here)))
  let R := .fvar (.there (.there (.there (.there .here))))
  let T := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (SecondOrderFiniteDisjunctionSyntax.fixed_m S) (.imp (evaluation_m E D Q R T)
    (.forallE .num (.forallE .num (.imp
      (SecondOrderAssignmentSyntax.formula_m (up (up E)) (.bvar .here) (.bvar (.there .here)))
      (.forallE .num (SecondOrderFiniteDisjunctionCorrectness.correct_m
        (up (up (up S))) (up (up (up T))) (up (up (up E))) (up (up (up Q)))
        (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar .here)))))))

def truth_sentence_m : Sentence signature_m := Metatheory.Formula.forall_close truth_schema_m

theorem truth_models_l (hℳ : Theory.Models ℳ theory_m) : truth_sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [truth_schema_m, Formula.satisfies, SecondOrderFiniteDisjunctionSyntax.fixed_formula_l,
    evaluation_formula_l, SecondOrderAssignmentSyntax.raw_l,
    SecondOrderFiniteDisjunctionCorrectness.correct_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact fun hS hT l c hc => SecondOrderFiniteDisjunctionCorrectness.correct_l hℳ hS hT c l hc

theorem truth_derives_m : Derives theory_m [] truth_sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => truth_models_l hℳ)

#print axioms legality_derives_m
#print axioms truth_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteDisjunctionDerives
