import BMSConstructibleBridge.SecondOrderRelativeHierarchyMembershipStep
import BMSConstructibleBridge.SecondOrderFormulaArguments

/-! # 共同上界前驱可比性的对象公式 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorComparability

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

def template_m : Formula signature_m [] [.set] :=
  .forallE .num <| .forallE .num <| .forallE .num <| .imp
    (GraphSyntax.edge_m (.fvar .here) (.bvar (.there .here)) (.bvar (.there (.there .here)))) <|
    .imp (GraphSyntax.edge_m (.fvar .here) (.bvar .here) (.bvar (.there (.there .here)))) <|
    .disj (GraphSyntax.edge_m (.fvar .here) (.bvar (.there .here)) (.bvar .here)) <|
      .disj (.equal (.bvar (.there .here)) (.bvar .here))
        (GraphSyntax.edge_m (.fvar .here) (.bvar .here) (.bvar (.there .here)))

def formula_m {Γ Δ : SortContext signature_m} (R : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderFormulaArguments.formula_m template_m (.cons R .nil)

theorem pure_m {Γ Δ : SortContext signature_m} (R : Term signature_m Γ Δ .set)
    (hR : pure_term_m R = true) : language_m (formula_m R) = true := by
  apply SecondOrderFormulaArguments.pure_m _ _ (show language_m template_m = true from rfl)
  simp only [pure_args_m, hR]
  rfl

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (R : Term signature_m Γ Δ .set) :
    (formula_m R).satisfies η ↔ SecondOrderRelativeHierarchyMembershipStep.comparable_l (R.eval η) := by
  rw [formula_m, SecondOrderFormulaArguments.formula_l]
  simp only [template_m, Formula.satisfies, SecondOrderPairing.edge_l, Term.eval]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorComparability
