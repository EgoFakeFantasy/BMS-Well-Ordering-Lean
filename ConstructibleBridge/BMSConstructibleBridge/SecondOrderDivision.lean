import BMSConstructibleBridge.SecondOrderNaturalGraph

/-!
# 任意模型数的带余除法

除数是正的模型数，归纳正文是实际纯算术公式。所得商和余数覆盖非标准数域，
不调用宿主 `Nat.div`，也不假设模型具有外部良基的数序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDivision

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由数参数依次是被除数和除数。 -/
def formula_m : Formula signature_m [] [.num, .num] :=
  .existsE .num (.existsE .num (.conj
    (.equal
      (Term.app (σ := signature_m) .add (.cons
        (Term.app (σ := signature_m) .mul
          (.cons (.bvar (.there .here)) (.cons (.fvar (.there .here)) .nil)))
        (.cons (.bvar .here) .nil))) (.fvar .here))
    (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here)))))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (n d : num_l ℳ)
    (hd : SecondOrderOrder.lt_l (zero_l ℳ) d) :
    ∃ q r, add_l (mul_l q d) r = n ∧ SecondOrderOrder.lt_l r d := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  apply induct_l hℳ formula_m pure_m ((Env.empty (M := ℳ)).pushFree d)
    (fun n => ∃ q r : num_l ℳ, q * d + r = n ∧ r < d) ?_ ?_ ?_ n
  · intro n
    simp only [formula_m, Formula.satisfies, SecondOrderOrder.formula_l]
    rfl
  · exact ⟨0, 0, by change 0 * d + 0 = 0; simp, hd⟩
  · rintro n ⟨q, r, h, hr⟩
    have h₁ : r + 1 ≤ d := (lt_iff_add_one_le_l hℳ r d).mp hr
    rcases eq_or_lt_of_le h₁ with h₁ | h₁
    · refine ⟨q + 1, 0, ?_, hd⟩
      rw [succ_eq_l hℳ, ← h, add_mul, one_mul, add_zero, ← h₁]
      simp only [add_assoc]
    · refine ⟨q, r + 1, ?_, h₁⟩
      rw [succ_eq_l hℳ, ← h, add_assoc]

/-- 同一被除数的两组规范商余数相等。 -/
theorem eq_l (hℳ : Theory.Models ℳ theory_m) (d q r a b : num_l ℳ)
    (h : add_l (mul_l q d) r = add_l (mul_l a d) b)
    (hr : SecondOrderOrder.lt_l r d) (hb : SecondOrderOrder.lt_l b d) :
    q = a ∧ r = b := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  change q * d + r = a * d + b at h
  have h₁ (q r a b : num_l ℳ) (hr : r < d) (hqa : q < a) :
      q * d + r < a * d + b := by
    calc
      q * d + r < q * d + d := add_lt_add_right hr _
      _ = (q + 1) * d := by rw [add_mul, one_mul]
      _ ≤ a * d := mul_le_mul_of_nonneg_right
        ((lt_iff_add_one_le_l hℳ q a).mp hqa) (zero_le_l hℳ d)
      _ ≤ a * d + b := le_add_of_nonneg_right (zero_le_l hℳ b)
  have h₂ : q = a := by
    rcases lt_trichotomy q a with h₂ | h₂ | h₂
    · exact False.elim ((ne_of_lt (h₁ q r a b hr h₂)) h)
    · exact h₂
    · exact False.elim ((ne_of_lt (h₁ a b q r hb h₂)) h.symm)
  subst a
  exact ⟨rfl, add_left_cancel h⟩

/-- 唯一值接口仍由模型内纯公式规定，不扩展算术签名。 -/
theorem unique_l (hℳ : Theory.Models ℳ theory_m) (n d : num_l ℳ)
    (hd : SecondOrderOrder.lt_l (zero_l ℳ) d) :
    ∃! p : num_l ℳ × num_l ℳ,
      add_l (mul_l p.1 d) p.2 = n ∧ SecondOrderOrder.lt_l p.2 d := by
  obtain ⟨q, r, h, hr⟩ := exists_l hℳ n d hd
  refine ⟨(q, r), ⟨h, hr⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨h₁, hb⟩
  obtain ⟨h₂, h₃⟩ := eq_l hℳ d a b q r (h₁.trans h.symm) hb hr
  exact Prod.ext h₂ h₃

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDivision
