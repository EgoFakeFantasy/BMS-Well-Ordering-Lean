import BMSConstructibleBridge.SecondOrderPairingBounds

/-!
# 任意二阶算术模型中的反配对总性

使用实际公式「存在两个坐标，其配对值是当前数」作模型归纳。
归纳步沿同一平方区间前进并跨越端点，不对模型数作宿主自然数递归。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnpairing

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderPairingBounds

set_option autoImplicit false

universe u

/-- 任一配对值的后继仍有两个模型数作为坐标。 -/
theorem successor_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) :
    ∃ a b, value_l a b = succ_l (value_l m n) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  rw [succ_eq_l hℳ]
  by_cases h : m < n
  · by_cases h₁ : m + 1 < n
    · refine ⟨m + 1, n, ?_⟩
      rw [value_eq_l hℳ, value_eq_l hℳ, if_pos h₁, if_pos h, add_assoc]
    · have h₂ : m + 1 = n := le_antisymm ((lt_iff_add_one_le_l hℳ _ _).mp h)
        (le_of_not_gt h₁)
      refine ⟨n, 0, ?_⟩
      rw [value_eq_l hℳ, value_eq_l hℳ, if_neg (not_lt_of_ge (zero_le_l hℳ n)),
        if_pos h, add_zero, add_assoc, h₂]
  · by_cases h₁ : n < m
    · have h₂ : ¬m < n + 1 := not_lt_of_ge ((lt_iff_add_one_le_l hℳ _ _).mp h₁)
      refine ⟨m, n + 1, ?_⟩
      rw [value_eq_l hℳ, value_eq_l hℳ, if_neg h₂, if_neg h]
      simp only [add_assoc]
    · have h₂ : n = m := le_antisymm (le_of_not_gt h) (le_of_not_gt h₁)
      subst n
      refine ⟨0, m + 1, ?_⟩
      have h₃ : 0 < m + 1 := lt_of_le_of_lt (zero_le_l hℳ m)
        (lt_add_of_pos_right m zero_lt_one)
      rw [value_eq_l hℳ, value_eq_l hℳ, if_pos h₃, if_neg (lt_irrefl m), add_zero]
      ring

/-- 实际反配对存在公式，不含额外函数符号。 -/
def formula_m : Formula signature_m [] [.num] :=
  .existsE .num (.existsE .num
    (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here) (.fvar .here)))

theorem pure_m : language_m formula_m = true :=
  pure_language_m _ (PrimitiveFormulas.pair_pure_l _ _ _ rfl rfl rfl)

/-- 包括非标准数在内的每个数都有反配对坐标。 -/
theorem surjective_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (z : num_l ℳ) : ∃ m n, value_l m n = z := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  apply induct_l hℳ formula_m pure_m (Env.empty (M := ℳ))
    (fun z => ∃ m n, value_l m n = z) ?_ ?_ ?_ z
  · intro z
    simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l]
    rfl
  · refine ⟨0, 0, ?_⟩
    rw [value_eq_l hℳ, if_neg (lt_irrefl (0 : num_l ℳ)), mul_zero, add_zero, add_zero]
    rfl
  · rintro z ⟨m, n, rfl⟩
    exact successor_l hℳ m n

/-- 全数域的唯一反解，不仅是标准有限测试或正向函数性。 -/
theorem unique_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (z : num_l ℳ) :
    ∃! p : num_l ℳ × num_l ℳ, value_l p.1 p.2 = z := by
  obtain ⟨m, n, h⟩ := surjective_l hℳ z
  refine ⟨(m, n), h, ?_⟩
  rintro ⟨a, b⟩ h₁
  exact Prod.ext ((SecondOrderPairingBounds.injective_l hℳ a b m n (h₁.trans h.symm)).1)
    ((SecondOrderPairingBounds.injective_l hℳ a b m n (h₁.trans h.symm)).2)

/-- 唯一反解的宿主函数接口；对象层仍使用已经核验的纯公式图。 -/
noncomputable def value_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (z : num_l ℳ) : num_l ℳ × num_l ℳ :=
  (unique_l hℳ z).exists.choose

theorem pair_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (z : num_l ℳ) :
    SecondOrderPairing.value_l (value_l hℳ z).1 (value_l hℳ z).2 = z :=
  (unique_l hℳ z).exists.choose_spec

theorem unpair_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) :
    value_l hℳ (SecondOrderPairing.value_l m n) = (m, n) := by
  have h := SecondOrderPairingBounds.injective_l hℳ _ _ m n
    (pair_l hℳ (SecondOrderPairing.value_l m n))
  exact Prod.ext h.1 h.2

/-- 原编译器的第一投影公式在任意模型中仍有同一个唯一输出。 -/
theorem left_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (PrimitiveFormulas.left_l.form s t) ↔
      (value_l hℳ (s.eval η)).1 = t.eval η := by
  simp only [PrimitiveFormulas.left_l, Formula.satisfies, SecondOrderPairing.formula_l,
    Term.eval_weakenBound, Term.eval]
  change (∃ n, SecondOrderPairing.value_l (t.eval η) n = s.eval η) ↔ _
  constructor
  · rintro ⟨n, h⟩
    rw [← h, unpair_l]
  · intro h
    exact ⟨(value_l hℳ (s.eval η)).2, by rw [← h, pair_l]⟩

/-- 原编译器的第二投影公式也不需要标准模型假设。 -/
theorem right_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (PrimitiveFormulas.right_l.form s t) ↔
      (value_l hℳ (s.eval η)).2 = t.eval η := by
  simp only [PrimitiveFormulas.right_l, Formula.satisfies, SecondOrderPairing.formula_l,
    Term.eval_weakenBound, Term.eval]
  change (∃ m, SecondOrderPairing.value_l m (t.eval η) = s.eval η) ↔ _
  constructor
  · rintro ⟨m, h⟩
    rw [← h, unpair_l]
  · intro h
    exact ⟨(value_l hℳ (s.eval η)).1, by rw [← h, pair_l]⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderUnpairing
