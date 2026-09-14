import BMSConstructibleBridge.SecondOrderHistory

/-!
# 一个内部实数所编码的实数行

每行由实际理解公式获得且唯一。有限延长只拼接一个已有实数，不假定任何
外部实数序列已经具有内部代码，也不消费可数选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSections

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (H : set_l ℳ) (i : num_l ℳ) (X : set_l ℳ) : Prop :=
  ∀ a, mem_l a X ↔ relation_l H i a

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (H : set_l ℳ) (i : num_l ℳ) :
    ∃ X : set_l ℳ, spec_l H i X := by
  let φ : Formula signature_m [] [.num, .set, .num] :=
    GraphSyntax.edge_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  obtain ⟨X, hX⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree i).pushFree H)
  exact ⟨X, fun a => (hX a).trans (SecondOrderPairing.edge_l _ _ _ _)⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {H X Y : set_l ℳ} {i : num_l ℳ}
    (hX : spec_l H i X) (hY : spec_l H i Y) : X = Y :=
  ext_l hℳ X Y (fun a => (hX a).trans (hY a).symm)

def template_m : Formula signature_m [] [.set, .set, .num] :=
  .forallE .num (.iff
    (.rel .mem (.cons (.bvar .here) (.cons (.fvar (.there .here)) .nil)))
    (GraphSyntax.edge_m (.fvar .here) (.fvar (.there (.there .here))) (.bvar .here)))

private def bind {Γ Δ : SortContext signature_m} (H X : Term signature_m Γ Δ .set)
    (i : Term signature_m Γ Δ .num) : Substitution signature_m [] [.set, .set, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => H
    | .there .here => X
    | .there (.there .here) => i)

def formula_m {Γ Δ : SortContext signature_m} (H X : Term signature_m Γ Δ .set)
    (i : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  template_m.substitute (bind H X i)

theorem pure_m {Γ Δ : SortContext signature_m} (H X : Term signature_m Γ Δ .set)
    (i : Term signature_m Γ Δ .num) (hH : pure_term_m H = true) (hX : pure_term_m X = true)
    (hi : pure_term_m i = true) : language_m (formula_m H X i) = true := by
  refine (SecondOrderSubstitution.form_subst_m template_m _ _ ?_ ?_).trans (pure_language_m _ rfl)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hH
    | .there .here => exact hX
    | .there (.there .here) => exact hi

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (H X : Term signature_m Γ Δ .set) (i : Term signature_m Γ Δ .num) :
    Formula.satisfies η (formula_m H X i) ↔ spec_l (H.eval η) (i.eval η) (X.eval η) := by
  simp only [formula_m, Formula.satisfies_substitute, template_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

theorem constant_l (hℳ : Theory.Models ℳ theory_m) (X : set_l ℳ) :
    ∃ H : set_l ℳ, ∀ i, spec_l H i X := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .rel .mem (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there .here))) .nil))
  obtain ⟨H, hH⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree X)
  exact ⟨H, fun i a => (hH i a).symm⟩

theorem extend_l (hℳ : Theory.Models ℳ theory_m) (H X : set_l ℳ) (n : num_l ℳ) :
    ∃ K : set_l ℳ, spec_l K (succ_l n) X ∧ ∀ i,
      SecondOrderOrder.lt_l i (succ_l n) → ∀ a, relation_l K i a ↔ relation_l H i a := by
  let φ : Formula signature_m [] [.num, .num, .set, .set, .num] :=
    .disj (.conj
      (PrimitiveFormulas.lt_m (.fvar .here)
        (Term.app (σ := signature_m) .succ (.cons (.fvar (.there (.there (.there (.there .here))))) .nil)))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))))
      (.conj
        (.equal (.fvar .here)
          (Term.app (σ := signature_m) .succ (.cons (.fvar (.there (.there (.there (.there .here))))) .nil)))
        (.rel .mem (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there (.there .here)))) .nil))))
  obtain ⟨K, hK⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree n).pushFree X).pushFree H)
  have h : ∀ i a, relation_l K i a ↔
      (SecondOrderOrder.lt_l i (succ_l n) ∧ relation_l H i a) ∨ (i = succ_l n ∧ mem_l a X) := by
    intro i a
    refine (hK i a).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderOrder.formula_l, SecondOrderPairing.edge_l]
    rfl
  refine ⟨K, ?_, ?_⟩
  · intro a
    simp only [h, SecondOrderOrder.irrefl_l hℳ, false_and, true_and, false_or]
  · intro i hi a
    have h₁ : i ≠ succ_l n := fun h₁ => SecondOrderOrder.irrefl_l hℳ _ (h₁ ▸ hi)
    simp only [h, hi, h₁, true_and, false_and, or_false]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSections
