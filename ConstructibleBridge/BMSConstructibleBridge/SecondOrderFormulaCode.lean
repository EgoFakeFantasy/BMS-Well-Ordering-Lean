import BMSConstructibleBridge.SecondOrderUnpairing

/-!
# 内部公式节点的数值编码

节点以 `succ (pair tag payload)` 编码，零留作空码。标签和正文可为模型数，
两个配对坐标及嵌套子节点都严格小于节点码；这里尚未定义完整公式合法性或
满足关系，不能把节点代数当作已完成的语法解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaCode

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

noncomputable def node_l (t p : num_l ℳ) : num_l ℳ := succ_l (value_l t p)

theorem pair_bound_l (hℳ : Theory.Models ℳ theory_m) (a b : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    a ≤ value_l a b ∧ b ≤ value_l a b := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have h (x : num_l ℳ) : x ≤ x * x := by
    rcases predecessor_l hℳ x with rfl | ⟨y, rfl⟩
    · change (0 : num_l ℳ) ≤ 0 * 0
      simp
    · apply le_mul_of_one_le_right (zero_le_l hℳ _)
      simpa only [zero_add] using
        (lt_iff_add_one_le_l hℳ 0 (succ_l y)).mp (SecondOrderOrder.zero_succ_l hℳ y)
  have h₁ := (h (max a b)).trans (SecondOrderPairingBounds.interval_l hℳ a b).1
  exact ⟨(le_max_left _ _).trans h₁, (le_max_right _ _).trans h₁⟩

theorem bounds_l (hℳ : Theory.Models ℳ theory_m) (t p : num_l ℳ) :
    SecondOrderOrder.lt_l t (node_l t p) ∧ SecondOrderOrder.lt_l p (node_l t p) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨h, h₁⟩ := pair_bound_l hℳ t p
  have h₂ : value_l t p < succ_l (value_l t p) :=
    ⟨zero_l ℳ, by rw [add_succ_l hℳ, add_zero_l hℳ]⟩
  exact ⟨lt_of_le_of_lt h h₂, lt_of_le_of_lt h₁ h₂⟩

theorem children_l (hℳ : Theory.Models ℳ theory_m) (t a b : num_l ℳ) :
    SecondOrderOrder.lt_l a (node_l t (value_l a b)) ∧
      SecondOrderOrder.lt_l b (node_l t (value_l a b)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨h, h₁⟩ := pair_bound_l hℳ a b
  have h₂ := (bounds_l hℳ t (value_l a b)).2
  exact ⟨lt_of_le_of_lt h h₂, lt_of_le_of_lt h₁ h₂⟩

theorem injective_l (hℳ : Theory.Models ℳ theory_m) (t p s q : num_l ℳ)
    (h : node_l t p = node_l s q) : t = s ∧ p = q :=
  SecondOrderPairingBounds.injective_l hℳ t p s q (SecondOrderModel.injective_l hℳ h)

theorem decode_l (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) (hn : n ≠ zero_l ℳ) :
    ∃ t p, node_l t p = n := by
  obtain ⟨m, rfl⟩ := (predecessor_l hℳ n).resolve_left hn
  obtain ⟨t, p, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ m
  exact ⟨t, p, rfl⟩

def template_m : Formula signature_m [] [.num, .num, .num] :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
    (.equal (Term.app (σ := signature_m) .succ (.cons (.bvar .here) .nil))
      (.fvar (.there (.there .here)))))

private def bind {Γ Δ : SortContext signature_m} (t p n : Term signature_m Γ Δ .num) :
    Substitution signature_m [] [.num, .num, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => t
    | .there .here => p
    | .there (.there .here) => n)

def formula_m {Γ Δ : SortContext signature_m} (t p n : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := template_m.substitute (bind t p n)

theorem pure_m {Γ Δ : SortContext signature_m} (t p n : Term signature_m Γ Δ .num)
    (ht : pure_term_m t = true) (hp : pure_term_m p = true) (hn : pure_term_m n = true) :
    language_m (formula_m t p n) = true := by
  refine (SecondOrderSubstitution.form_subst_m template_m _ _ ?_ ?_).trans (pure_language_m _ rfl)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact ht
    | .there .here => exact hp
    | .there (.there .here) => exact hn

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (t p n : Term signature_m Γ Δ .num) :
    Formula.satisfies η (formula_m t p n) ↔ node_l (t.eval η) (p.eval η) = n.eval η := by
  simp only [formula_m, Formula.satisfies_substitute, template_m, Formula.satisfies, SecondOrderPairing.formula_l]
  change (∃ z, value_l (t.eval η) (p.eval η) = z ∧ succ_l z = n.eval η) ↔ _
  constructor
  · rintro ⟨z, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaCode
