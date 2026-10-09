import BMSConstructibleBridge.SecondOrderRelativeHierarchyClosedFormula
import BMSConstructibleBridge.SecondOrderRelativeHierarchyBase
import BMSConstructibleBridge.SecondOrderRelativeHierarchyMembership

/-! # 同时保持基集和前驱阶段对象的历史正文 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyStrongFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def base_m {Γ Δ : SortContext signature_m} (B S : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .num <| SecondOrderFormulaArguments.formula_m SecondOrderRelativeHierarchyBase.rows_m
    (.cons (.bvar .here) (.cons (S.weakenBound sort_m.num) (.cons (B.weakenBound sort_m.num) .nil)))

def member_m {Γ Δ : SortContext signature_m} (R S : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .num <| SecondOrderFormulaArguments.formula_m SecondOrderRelativeHierarchyMembership.rows_m
    (.cons (.bvar .here) (.cons (S.weakenBound sort_m.num) (.cons (R.weakenBound sort_m.num) .nil)))

def formula_m {Γ Δ : SortContext signature_m} (B R S : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .conj (SecondOrderRelativeHierarchyClosedFormula.formula_m B R S)
    (.conj (base_m B S) (member_m R S))

theorem pure_m {Γ Δ : SortContext signature_m} (B R S : Term signature_m Γ Δ .set)
    (hB : pure_term_m B = true) (hR : pure_term_m R = true) (hS : pure_term_m S = true) :
    language_m (formula_m B R S) = true := by
  have hSW := (SecondOrderSubstitution.term_weaken_m S sort_m.num).trans hS
  have hBW := (SecondOrderSubstitution.term_weaken_m B sort_m.num).trans hB
  have hRW := (SecondOrderSubstitution.term_weaken_m R sort_m.num).trans hR
  have hBase : language_m (base_m B S) = true := by
    apply SecondOrderFormulaArguments.forall_pure_m
    apply SecondOrderFormulaArguments.pure_m _ _ SecondOrderRelativeHierarchyBase.pure_m
    simp only [pure_args_m, hSW, hBW]
    rfl
  have hMember : language_m (member_m R S) = true := by
    apply SecondOrderFormulaArguments.forall_pure_m
    apply SecondOrderFormulaArguments.pure_m _ _ SecondOrderRelativeHierarchyMembership.pure_m
    simp only [pure_args_m, hSW, hRW]
    rfl
  exact SecondOrderFormulaArguments.conj_pure_m _ _
    (SecondOrderRelativeHierarchyClosedFormula.pure_m B R S hB hR hS)
    (SecondOrderFormulaArguments.conj_pure_m _ _ hBase hMember)

theorem base_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B S : Term signature_m Γ Δ .set)
    (hB : SecondOrderDomain.wf_l (B.eval η) (zero_l ℳ)) :
    (base_m B S).satisfies η ↔ ∀ n W, SecondOrderSections.spec_l (S.eval η) n W →
      ∀ hW : SecondOrderDomain.wf_l W (zero_l ℳ),
        SecondOrderGraphSubsetFormula.subset_l ⟨B.eval η, zero_l ℳ, hB⟩ ⟨W, zero_l ℳ, hW⟩ := by
  simp only [base_m, Formula.satisfies]
  apply forall_congr'
  intro n
  rw [SecondOrderFormulaArguments.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l (η.pushBound n)
      (Automation.RelationalTranslation.argumentsSubstitution (.cons (.bvar .here)
        (.cons (S.weakenBound sort_m.num) (.cons (B.weakenBound sort_m.num) .nil)))) =
      (((Env.empty (M := ℳ)).pushFree (B.eval η)).pushFree (S.eval η)).pushFree n := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      match v with
      | .here => rfl
      | .there .here => exact Term.eval_weakenBound η n S
      | .there (.there .here) => exact Term.eval_weakenBound η n B
  rw [hEnv, SecondOrderRelativeHierarchyBase.formula_l hℳ _ _ _ hB]

theorem member_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (R S : Term signature_m Γ Δ .set) :
    (member_m R S).satisfies η ↔
      ∀ n, SecondOrderRelativeHierarchyMembershipStep.rows_l (R.eval η) (S.eval η) n := by
  simp only [member_m, Formula.satisfies]
  apply forall_congr'
  intro n
  rw [SecondOrderFormulaArguments.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l (η.pushBound n)
      (Automation.RelationalTranslation.argumentsSubstitution (.cons (.bvar .here)
        (.cons (S.weakenBound sort_m.num) (.cons (R.weakenBound sort_m.num) .nil)))) =
      (((Env.empty (M := ℳ)).pushFree (R.eval η)).pushFree (S.eval η)).pushFree n := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      match v with
      | .here => rfl
      | .there .here => exact Term.eval_weakenBound η n S
      | .there (.there .here) => exact Term.eval_weakenBound η n R
  rw [hEnv, SecondOrderRelativeHierarchyMembership.formula_l]

#print axioms base_formula_l
#print axioms member_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyStrongFormula
