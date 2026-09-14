import BMSConstructibleBridge.SecondOrderPowers

/-!
# 内部幂图的纯公式规格

一般底数与幂实数均为显式参数，规格完整包含函数性、零值及后继方程。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPowerSyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

def template_m : Formula signature_m [] [.set, .num] :=
  .conj
    (.forallE .num (.existsE .num (.conj
      (GraphSyntax.edge_m (.fvar .here) (.bvar (.there .here)) (.bvar .here))
      (.forallE .num (.imp (GraphSyntax.edge_m (.fvar .here) (.bvar (.there (.there .here))) (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here))))))))
    (.conj (GraphSyntax.edge_m (.fvar .here) zero (succ zero))
      (.forallE .num (.forallE .num (.forallE .num (.imp
        (GraphSyntax.edge_m (.fvar .here) (.bvar (.there (.there .here))) (.bvar (.there .here)))
        (.imp (GraphSyntax.edge_m (.fvar .here) (succ (.bvar (.there (.there .here)))) (.bvar .here))
          (.equal (.bvar .here) (Term.app (σ := signature_m) .mul
            (.cons (.bvar (.there .here)) (.cons (.fvar (.there .here)) .nil))))))))))

private def bind {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (b : Term signature_m Γ Δ .num) : Substitution signature_m [] [.set, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => E
    | .there .here => b)

def formula_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ := template_m.substitute (bind E b)

theorem pure_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (b : Term signature_m Γ Δ .num) (hE : pure_term_m E = true) (hb : pure_term_m b = true) :
    language_m (formula_m E b) = true := by
  refine (SecondOrderSubstitution.form_subst_m template_m _ _ ?_ ?_).trans (pure_language_m _ rfl)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hE
    | .there .here => exact hb

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (b : Term signature_m Γ Δ .num) :
    Formula.satisfies η (formula_m E b) ↔ SecondOrderPowers.spec_l (b.eval η) (E.eval η) := by
  simp only [formula_m, Formula.satisfies_substitute, template_m, Formula.satisfies,
    SecondOrderPairing.edge_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPowerSyntax
