import BMSConstructibleBridge.SecondOrderDivision

/-!
# 二进制位的纯算术公式

权重为正数 `p` 时，编码模 `p+p` 的余数位于后半段恰表示该位为一。
周期不变性使用模型内带余除法，不借用标准自然数的位运算。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDigit

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def holds_l (a p : num_l ℳ) : Prop :=
  ∃ q r, a = add_l (mul_l q (add_l p p)) r ∧
    ¬SecondOrderOrder.lt_l r p ∧ SecondOrderOrder.lt_l r (add_l p p)

private def add {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

private def mul {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .mul (.cons s (.cons t .nil))

def template_m : Formula signature_m [] [.num, .num] :=
  .existsE .num (.existsE .num (.conj
    (.equal (.fvar .here)
      (add (mul (.bvar (.there .here))
        (add (.fvar (.there .here)) (.fvar (.there .here)))) (.bvar .here)))
    (.conj
      (.neg (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here))))
      (PrimitiveFormulas.lt_m (.bvar .here)
        (add (.fvar (.there .here)) (.fvar (.there .here)))))))

private def bind {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Substitution signature_m [] [.num, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => s
    | .there .here => t)

def formula_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := template_m.substitute (bind s t)

theorem pure_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num)
    (hs : pure_term_m s = true) (ht : pure_term_m t = true) :
    language_m (formula_m s t) = true := by
  refine (SecondOrderSubstitution.form_subst_m template_m _ _ ?_ ?_).trans (pure_language_m _ rfl)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hs
    | .there .here => exact ht

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (formula_m s t) ↔ holds_l (s.eval η) (t.eval η) := by
  simp only [formula_m, Formula.satisfies_substitute, template_m, Formula.satisfies,
    SecondOrderOrder.formula_l, add, mul, Term.eval]
  rfl

theorem below_l (hℳ : Theory.Models ℳ theory_m) (a p : num_l ℳ)
    (h : SecondOrderOrder.lt_l a p) : ¬holds_l a p := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  rintro ⟨q, r, h₁, h₂, _⟩
  change a = q * (p + p) + r at h₁
  have h₃ : p ≤ r := le_of_not_gt h₂
  have h₄ : r ≤ a := by
    rw [h₁]
    exact le_add_of_nonneg_left (zero_le_l hℳ _)
  exact (not_le_of_gt h) (h₃.trans h₄)

theorem interval_l (hℳ : Theory.Models ℳ theory_m) (a p : num_l ℳ)
    (h : ¬SecondOrderOrder.lt_l a p) (h₁ : SecondOrderOrder.lt_l a (add_l p p)) :
    holds_l a p := by
  refine ⟨zero_l ℳ, a, ?_, h, h₁⟩
  rw [SecondOrderMultiplication.zero_mul_l hℳ, SecondOrderNumbers.zero_add_l hℳ]

/-- 加上位周期的任意模型数倍，不改变该位。 -/
theorem periodic_l (hℳ : Theory.Models ℳ theory_m) (a p k : num_l ℳ)
    (hp : SecondOrderOrder.lt_l (zero_l ℳ) p) :
    holds_l (add_l a (mul_l k (add_l p p))) p ↔ holds_l a p := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hd : 0 < p + p := lt_of_lt_of_le hp (le_add_of_nonneg_right (zero_le_l hℳ p))
  constructor
  · rintro ⟨q, r, h, hr, hr₁⟩
    obtain ⟨b, c, h₁, hc⟩ := SecondOrderDivision.exists_l hℳ a (p + p) hd
    change b * (p + p) + c = a at h₁
    have h₂ : mul_l q (add_l p p) + r = (b + k) * (p + p) + c := by
      calc
        mul_l q (add_l p p) + r = a + k * (p + p) := h.symm
        _ = (b * (p + p) + c) + k * (p + p) := by rw [← h₁]
        _ = (b + k) * (p + p) + c := by ring
    obtain ⟨_, h₃⟩ := SecondOrderDivision.eq_l hℳ (p + p) q r (b + k) c h₂ hr₁ hc
    exact ⟨b, c, h₁.symm, h₃ ▸ hr, hc⟩
  · rintro ⟨q, r, h, hr, hr₁⟩
    refine ⟨q + k, r, ?_, hr, hr₁⟩
    change a + k * (p + p) = (q + k) * (p + p) + r
    change a = q * (p + p) + r at h
    rw [h]
    ring

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDigit
