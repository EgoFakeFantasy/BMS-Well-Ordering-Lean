import BMSConstructibleBridge.SecondOrderSetOperator

/-!
# 内部集合值有限历史

历史是一个内部实数，其行是阶段集合。存在性只使用实际操作公式、逐次存在
和模型归纳；不选择外部集合序列，也不把有限存在升级为可数依赖选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetHistory

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (P : set_l ℳ → set_l ℳ → Prop) (H A : set_l ℳ) (n : num_l ℳ) : Prop :=
  SecondOrderSections.spec_l H (zero_l ℳ) A ∧ ∀ i X Y, SecondOrderOrder.lt_l i n →
    SecondOrderSections.spec_l H i X → SecondOrderSections.spec_l H (succ_l i) Y → P X Y

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

private def params {Γ Δ : SortContext signature_m} :
    VariableSubstitution signature_m Δ Γ (.set :: .set :: .num :: Δ) :=
  fun v => .fvar (.there (.there (.there v)))

def parameters_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ (.set :: .set :: .num :: Δ)) :
    Env ℳ [] Δ where
  boundVal := fun v => nomatch v
  freeVal := fun v => η.freeVal (.there (.there (.there v)))

def formula_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [] (.set :: .set :: .num :: Δ) :=
  .conj (SecondOrderSections.formula_m (.fvar .here) (.fvar (.there .here)) zero)
    (.forallE .num (.forallE .set (.forallE .set (.imp
      (PrimitiveFormulas.lt_m (.bvar (.there (.there .here))) (.fvar (.there (.there .here))))
      (.imp (SecondOrderSections.formula_m (.fvar .here) (.bvar (.there .here)) (.bvar (.there (.there .here))))
        (.imp (SecondOrderSections.formula_m (.fvar .here) (.bvar .here) (succ (.bvar (.there (.there .here)))))
          (SecondOrderSetOperator.formula_m φ (.bvar (.there .here)) (.bvar .here) params)))))))

theorem pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : language_m (formula_m φ) = true := by
  have h := SecondOrderSetOperator.pure_m (Γ := [.set, .set, .num]) φ
    (.bvar (.there .here)) (.bvar .here) params hφ rfl rfl (fun _ => rfl)
  simp only [formula_m, language_m]
  rw [h]
  rfl

theorem formula_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (η : Env ℳ [] (.set :: .set :: .num :: Δ)) :
    Formula.satisfies η (formula_m φ) ↔
      spec_l (SecondOrderSetOperator.relation_l φ (parameters_l η)) (η.freeVal .here)
        (η.freeVal (.there .here)) (η.freeVal (.there (.there .here))) := by
  simp only [formula_m, Formula.satisfies, SecondOrderSections.formula_l,
    SecondOrderSetOperator.formula_l, SecondOrderOrder.formula_l]
  rfl

theorem base_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop) (A : set_l ℳ) :
    ∃ H, spec_l P H A (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨H, hH⟩ := SecondOrderSections.constant_l hℳ A
  exact ⟨H, hH _, fun i _ _ hi => False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi)⟩

theorem step_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop)
    (H A : set_l ℳ) (n : num_l ℳ) (hH : spec_l P H A n) (hP : ∀ X, ∃ Y, P X Y) :
    ∃ K, spec_l P K A (succ_l n) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨X, hX⟩ := SecondOrderSections.exists_l hℳ H n
  obtain ⟨Y, hY⟩ := hP X
  obtain ⟨K, hK, h⟩ := SecondOrderSections.extend_l hℳ H Y n
  have hn : n < succ_l n := (SecondOrderNaturalGraph.lt_succ_l hℳ _ _).mpr le_rfl
  have h₀ : ∀ i, i < succ_l n → ∀ Z, SecondOrderSections.spec_l K i Z → SecondOrderSections.spec_l H i Z :=
    fun i hi Z hZ a => (hZ a).trans (h i hi a)
  refine ⟨K, (fun a => (hH.1 a).trans (h _ (SecondOrderOrder.zero_succ_l hℳ n) a).symm), ?_⟩
  intro i U V hi hU hV
  rcases eq_or_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ i n).mp hi) with rfl | hi
  · obtain rfl := SecondOrderSections.unique_l hℳ (h₀ i hn U hU) hX
    obtain rfl := SecondOrderSections.unique_l hℳ hV hK
    exact hY
  · exact hH.2 i U V hi (h₀ i (lt_trans hi hn) U hU)
      (h₀ (succ_l i) ((SecondOrderOrder.succ_iff_l hℳ i n).mpr hi) V hV)

private def bind {Δ : SortContext signature_m} :
    Substitution signature_m [] (.set :: .set :: .num :: Δ) [.set] (.num :: .set :: Δ) :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => .bvar .here
    | .there .here => .fvar (.there .here)
    | .there (.there .here) => .fvar .here
    | .there (.there (.there v)) => .fvar (.there (.there v)))

def existence_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [] (.num :: .set :: Δ) := .existsE .set ((formula_m φ).substitute bind)

theorem existence_pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : language_m (existence_m φ) = true := by
  refine (SecondOrderSubstitution.form_subst_m (formula_m φ) _ _ ?_ ?_).trans (pure_m φ hφ)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here | .there .here | .there (.there .here) => rfl
    | .there (.there (.there _)) => cases s <;> rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (A : set_l ℳ) (hP : ∀ X, ∃ Y, SecondOrderSetOperator.relation_l φ η X Y) (n : num_l ℳ) :
    ∃ H, spec_l (SecondOrderSetOperator.relation_l φ η) H A n := by
  apply induct_l hℳ (existence_m φ) (existence_pure_m φ hφ) (η.pushFree A)
    (fun n => ∃ H, spec_l (SecondOrderSetOperator.relation_l φ η) H A n) ?_
    (base_l hℳ _ A) (fun n ⟨H, hH⟩ => step_l hℳ _ H A n hH hP) n
  intro n
  change (∃ H, Formula.satisfies (((η.pushFree A).pushFree n).pushBound H)
    ((formula_m φ).substitute bind)) ↔ _
  apply exists_congr
  intro H
  rw [Formula.satisfies_substitute, formula_l]
  have h : parameters_l ((((η.pushFree A).pushFree n).pushBound H).pullback (bind (Δ := Δ))) = η := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases s <;> rfl
  rw [h]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSetHistory
