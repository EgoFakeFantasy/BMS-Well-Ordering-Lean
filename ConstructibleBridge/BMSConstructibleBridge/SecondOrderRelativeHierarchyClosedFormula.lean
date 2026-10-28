import BMSConstructibleBridge.SecondOrderRelativeHierarchyHistoryFormula
import BMSConstructibleBridge.SecondOrderRelativeHierarchyMonotonicity

/-! # 闭合相对历史的对象正文

阶段规格、内部良基性、传递性和单调性均由实际公式同时断言。任意环境的
回读保持同一历史实数及同一前驱关系，没有增加收集或反射公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyClosedFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def transitive_m {Γ Δ : SortContext signature_m} (S : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .num <| SecondOrderFormulaArguments.formula_m SecondOrderRelativeHierarchyTransitivity.rows_m
    (.cons (.bvar .here) (.cons (S.weakenBound sort_m.num) .nil))

def monotone_m {Γ Δ : SortContext signature_m} (R S : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .num <| SecondOrderFormulaArguments.formula_m SecondOrderRelativeHierarchyMonotonicity.rows_m
    (.cons (.bvar .here) (.cons (S.weakenBound sort_m.num) (.cons (R.weakenBound sort_m.num) .nil)))

def formula_m {Γ Δ : SortContext signature_m} (B R S : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .conj (SecondOrderRelativeHierarchyHistoryFormula.formula_m B R S)
    (.conj (transitive_m S) (monotone_m R S))

theorem pure_m {Γ Δ : SortContext signature_m} (B R S : Term signature_m Γ Δ .set)
    (hB : pure_term_m B = true) (hR : pure_term_m R = true) (hS : pure_term_m S = true) :
    language_m (formula_m B R S) = true := by
  have hSW := (SecondOrderSubstitution.term_weaken_m S sort_m.num).trans hS
  have hRW := (SecondOrderSubstitution.term_weaken_m R sort_m.num).trans hR
  have hT : language_m (transitive_m S) = true := by
    apply SecondOrderFormulaArguments.forall_pure_m
    apply SecondOrderFormulaArguments.pure_m _ _ SecondOrderRelativeHierarchyTransitivity.pure_m
    simp only [pure_args_m, hSW]
    rfl
  have hM : language_m (monotone_m R S) = true := by
    apply SecondOrderFormulaArguments.forall_pure_m
    apply SecondOrderFormulaArguments.pure_m _ _ SecondOrderRelativeHierarchyMonotonicity.pure_m
    simp only [pure_args_m, hSW, hRW]
    rfl
  exact SecondOrderFormulaArguments.conj_pure_m _ _
    (SecondOrderRelativeHierarchyHistoryFormula.pure_m B R S hB hR hS)
    (SecondOrderFormulaArguments.conj_pure_m _ _ hT hM)

theorem transitive_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (S : Term signature_m Γ Δ .set) :
    (transitive_m S).satisfies η ↔ ∀ n W, SecondOrderSections.spec_l (S.eval η) n W →
      ∀ hW : SecondOrderDomain.wf_l W (zero_l ℳ),
        SecondOrderTransitiveSuperset.transitive_l ⟨W, zero_l ℳ, hW⟩ := by
  simp only [transitive_m, Formula.satisfies]
  apply forall_congr'
  intro n
  rw [SecondOrderFormulaArguments.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l (η.pushBound n)
      (Automation.RelationalTranslation.argumentsSubstitution (.cons (.bvar .here)
        (.cons (S.weakenBound sort_m.num) .nil))) =
      ((Env.empty (M := ℳ)).pushFree (S.eval η)).pushFree n := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      match v with
      | .here => rfl
      | .there .here => exact Term.eval_weakenBound η n S
  rw [hEnv, SecondOrderRelativeHierarchyTransitivity.formula_l hℳ]

theorem monotone_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (R S : Term signature_m Γ Δ .set) :
    (monotone_m R S).satisfies η ↔
      ∀ n, SecondOrderRelativeHierarchyMonotonicityStep.rows_l (R.eval η) (S.eval η) n := by
  simp only [monotone_m, Formula.satisfies]
  apply forall_congr'
  intro n
  rw [SecondOrderFormulaArguments.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l (η.pushBound n)
      (Automation.RelationalTranslation.argumentsSubstitution (.cons (.bvar .here)
        (.cons (S.weakenBound sort_m.num) (.cons (R.weakenBound sort_m.num) .nil)))) =
      (((Env.empty (M := ℳ)).pushFree (R.eval η)).pushFree (S.eval η)).pushFree n := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      match v with
      | .here => rfl
      | .there .here => exact Term.eval_weakenBound η n S
      | .there (.there .here) => exact Term.eval_weakenBound η n R
  rw [hEnv, SecondOrderRelativeHierarchyMonotonicity.formula_l hℳ]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyClosedFormula
