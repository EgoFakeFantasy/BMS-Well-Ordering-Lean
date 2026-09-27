import BMSConstructibleBridge.PowerlessEvaluationParameters
import BMSConstructibleBridge.PowerlessTruthClosure

/-!
# 接受证书规则的无核心参数语义

完整求值见证保留为原递归公式的真值，而不改写为集合递归关系。
这样可在任意结构比较不同绑定环境中的同一检查式；不增加模型公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthParameters

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
attribute [local irreducible] PowerlessOrdinalRecursion.recursion_m

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def truth_l (ω e T t₁ t₂ t₃ c f : carrier_l ℳ) : Prop :=
  ∃ A S F n, PowerlessNaturalOrder.transitive_l A ∧ member_l ℳ n ω ∧ map_l f n A ∧
    PowerlessEvaluationOperator.assignments_l ω A S ∧
    (PowerlessOrdinalRecursion.recursion_m PowerlessEvaluationStep.operator_m).satisfies
      (PowerlessEvaluationParameters.env_l ω e T A t₁ t₂ t₃ S F) ∧
    PowerlessEvaluationClause.query_l F c f

theorem truth_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ c f : Term ℒ Γ Δ .set) :
    (PowerlessBoundedTruth.truth_m ω e T t₁ t₂ t₃ c f).satisfies η ↔
      truth_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (c.eval η) (f.eval η) := by
  simp only [PowerlessBoundedTruth.truth_m, PowerlessBoundedTruth.certificate_m,
    truth_l, Formula.satisfies, PowerlessOrdinalBounded.transitive_formula_l,
    map_formula_l, PowerlessEvaluationOperator.assignments_formula_l,
    PowerlessEvaluationParameters.formula_l, PowerlessEvaluationClause.query_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def step_l (ω e T t₁ t₂ t₃ D p c f : carrier_l ℳ) : Prop :=
  (PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c ∧
    PowerlessAmbientAssignments.finite_l ω f ∧
      ((p = e ∧ truth_l ω e T t₁ t₂ t₃ c f) ∨
        (p = t₁ ∧ ¬truth_l ω e T t₁ t₂ t₃ c f))) ∨
  (∃ a b, PowerlessFormulaConstructor.constructor_l ω e T t₂ a b c ∧
    PowerlessAmbientAssignments.finite_l ω f ∧ PowerlessTruthNand.branch_l e t₁ D p a b f) ∨
  (p = e ∧ ∃ i b, PowerlessFormulaConstructor.constructor_l ω e T t₃ i b c ∧
    PowerlessAmbientAssignments.slot_l ω f i ∧ ∃ a,
      PowerlessTruthWitness.witness_l ω D e b f i a) ∨
  ∃ i j b, PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c ∧
    ((p = e ∧ PowerlessTruthBounded.positive_l ω D e b f i j) ∨
      (p = t₁ ∧ PowerlessTruthBounded.negative_l ω D t₁ b f i j))

theorem step_formula_l
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ D p c f : Term ℒ Γ Δ .set) :
    (PowerlessTruthStep.step_m ω e T t₁ t₂ t₃ D p c f).satisfies η ↔
      step_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (D.eval η) (p.eval η) (c.eval η) (f.eval η) := by
  simp only [PowerlessTruthStep.step_m, step_l, Formula.satisfies,
    PowerlessBoundedCertificate.recognizes_formula_l, PowerlessTruthBase.rule_m,
    PowerlessAmbientAssignments.finite_formula_l, truth_formula_l,
    PowerlessFormulaConstructor.constructor_formula_l, PowerlessTruthNand.rule_formula_l,
    PowerlessTruthExists.rule_m, PowerlessAmbientExistential.exists_m,
    PowerlessAmbientAssignments.slot_formula_l, PowerlessTruthWitness.witness_l,
    PowerlessAssignmentUpdate.update_formula_l, PowerlessTruthRecord.entry_formula_l,
    PowerlessBoundedCode.code_formula_l, PowerlessTruthBounded.rule_m,
    PowerlessTruthBounded.positive_formula_l, PowerlessTruthBounded.negative_formula_l,
    Term.eval_weakenBound]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthParameters

