import BMSConstructibleBridge.SecondOrderSections

/-! # 内部关系在初段上的一致性及其实际公式 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInitialAgreement

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def agree_l (H K : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∀ i, SecondOrderOrder.lt_l i n → ∀ a, relation_l H i a ↔ relation_l K i a

def template_m : Formula signature_m [] [.set, .set, .num] :=
  .forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there (.there .here))))
    (.forallE .num (.iff
      (GraphSyntax.edge_m (.fvar .here) (.bvar (.there .here)) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here)))))

private def bind {Γ Δ : SortContext signature_m} (H K : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Substitution signature_m [] [.set, .set, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => H
    | .there .here => K
    | .there (.there .here) => n)

def formula_m {Γ Δ : SortContext signature_m} (H K : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ := template_m.substitute (bind H K n)

theorem pure_m {Γ Δ : SortContext signature_m} (H K : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) (hH : pure_term_m H = true) (hK : pure_term_m K = true)
    (hn : pure_term_m n = true) : language_m (formula_m H K n) = true := by
  refine (SecondOrderSubstitution.form_subst_m template_m _ _ ?_ ?_).trans (pure_language_m _ rfl)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hH
    | .there .here => exact hK
    | .there (.there .here) => exact hn

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (H K : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num) :
    Formula.satisfies η (formula_m H K n) ↔ agree_l (H.eval η) (K.eval η) (n.eval η) := by
  simp only [formula_m, Formula.satisfies_substitute, template_m, Formula.satisfies,
    SecondOrderOrder.formula_l, SecondOrderPairing.edge_l]
  rfl

theorem successor_l (hℳ : Theory.Models ℳ theory_m) (H K : set_l ℳ) (n : num_l ℳ) :
    agree_l H K (succ_l n) ↔ agree_l H K n ∧ ∀ a, relation_l H n a ↔ relation_l K n a := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hn : n < succ_l n := (SecondOrderNaturalGraph.lt_succ_l hℳ _ _).mpr le_rfl
  constructor
  · intro h
    exact ⟨fun i hi => h i (lt_trans hi hn), h n hn⟩
  · intro h i hi a
    rcases eq_or_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ i n).mp hi) with rfl | hi
    · exact h.2 a
    · exact h.1 i hi a

theorem ext_l (hℳ : Theory.Models ℳ theory_m) (H K : set_l ℳ)
    (h : ∀ n, agree_l H K n) : H = K := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  apply SecondOrderRelations.ext_l hℳ
  intro i a
  exact h (succ_l i) i ((SecondOrderNaturalGraph.lt_succ_l hℳ _ _).mpr le_rfl) a

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInitialAgreement
