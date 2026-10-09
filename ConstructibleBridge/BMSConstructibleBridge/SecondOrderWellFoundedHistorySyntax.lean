import BMSConstructibleBridge.SecondOrderWellFoundedAgreement
import BMSConstructibleBridge.SecondOrderSetOperator

/-! # 内部递归历史的实际公式

自由槽依次为历史末端、前驱关系、历史实数及原操作参数。该公式供原理解
模式构造历史的相容并；操作原有的两个集合绑定槽保持原来次序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedHistorySyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def parameters_m {Γ Δ : SortContext signature_m} :
    VariableSubstitution signature_m Δ Γ (.num :: .set :: .set :: Δ) :=
  fun v => .fvar (.there (.there (.there v)))

def formula_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [] (.num :: .set :: .set :: Δ) :=
  .existsE .set <| .conj
    (SecondOrderSetOperator.formula_m φ (.fvar (.there (.there .here))) (.bvar .here) parameters_m) <|
      .forallE .num <| .imp
        (SecondOrderWellFoundedAgreement.prefix_m (.fvar (.there .here)) (.bvar .here) (.fvar .here)) <|
          .forallE .num <| .iff
            (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
            (GraphSyntax.edge_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))

theorem pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : language_m (formula_m φ) = true := by
  have h := SecondOrderSetOperator.pure_m φ
    (Γ := [.set]) (Ξ := .num :: .set :: .set :: Δ)
    (.fvar (.there (.there .here))) (.bvar .here) parameters_m hφ rfl rfl (fun _ => rfl)
  change (language_m (SecondOrderSetOperator.formula_m φ
    (Γ := [.set]) (.fvar (.there (.there .here))) (.bvar .here) parameters_m) && _) = true
  rw [h]
  rfl

theorem formula_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (η : Env ℳ [] Δ) (R H : set_l ℳ) (n : num_l ℳ) :
    (formula_m φ).satisfies (((η.pushFree H).pushFree R).pushFree n) ↔
      SecondOrderWellFoundedAgreement.good_l (SecondOrderSetOperator.relation_l φ η) R H n := by
  simp only [formula_m, Formula.satisfies, SecondOrderSetOperator.formula_l,
    SecondOrderWellFoundedAgreement.prefix_formula_l, SecondOrderPairing.edge_l, Term.eval]
  apply exists_congr
  intro U
  apply and_congr _ Iff.rfl
  apply Iff.of_eq
  apply congrArg (fun ξ => SecondOrderSetOperator.relation_l φ ξ H U)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    rfl

#print axioms pure_m
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedHistorySyntax
