import BMSConstructibleBridge.SecondOrderPowers

/-!
# 内部二进制幂的增长与整除

本模块为有限数集编码提供全部模型指数上的界和偶倍数分解。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBinaryPowers

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

abbrev spec_l (E : set_l ℳ) : Prop :=
  SecondOrderPowers.spec_l (succ_l (succ_l (zero_l ℳ))) E

theorem exists_l (hℳ : Theory.Models ℳ theory_m) : ∃ E : set_l ℳ, spec_l E :=
  SecondOrderPowers.exists_l hℳ _

theorem successor_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : spec_l E)
    (n : num_l ℳ) :
    SecondOrderPowers.value_l hE (succ_l n) =
      add_l (SecondOrderPowers.value_l hE n) (SecondOrderPowers.value_l hE n) := by
  rw [SecondOrderPowers.successor_l hE, mul_succ_l hℳ, mul_succ_l hℳ,
    mul_zero_l hℳ, SecondOrderNumbers.zero_add_l hℳ]

theorem growth_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : spec_l E)
    (n : num_l ℳ) : SecondOrderOrder.lt_l n (SecondOrderPowers.value_l hE n) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  let φ : Formula signature_m [] [.num, .set] :=
    .forallE .num (.imp
      (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
      (PrimitiveFormulas.lt_m (.fvar .here) (.bvar .here)))
  apply induct_l hℳ φ (pure_language_m _ rfl) ((Env.empty (M := ℳ)).pushFree E)
    (fun n => n < SecondOrderPowers.value_l hE n) ?_ ?_ ?_ n
  · intro n
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
    change (∀ a, relation_l E n a → n < a) ↔ _
    simp only [SecondOrderPowers.eq_l hE]
    constructor
    · intro h
      exact h _ rfl
    · rintro h a rfl
      exact h
  · rw [SecondOrderPowers.zero_l hE]
    exact zero_lt_one (α := num_l ℳ)
  · intro n hn
    rw [successor_l hℳ hE, succ_eq_l hℳ]
    change n + 1 < SecondOrderPowers.value_l hE n + SecondOrderPowers.value_l hE n
    exact lt_of_le_of_lt ((lt_iff_add_one_le_l hℳ _ _).mp hn)
      (lt_add_of_pos_right _ (lt_of_le_of_lt (zero_le_l hℳ n) hn))

theorem positive_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : spec_l E)
    (n : num_l ℳ) :
    SecondOrderOrder.lt_l (zero_l ℳ) (SecondOrderPowers.value_l hE n) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  exact lt_of_le_of_lt (zero_le_l hℳ n) (growth_l hℳ hE n)

theorem monotone_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : spec_l E)
    (m n : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    m ≤ n → SecondOrderPowers.value_l hE m ≤ SecondOrderPowers.value_l hE n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  intro h
  obtain ⟨k, rfl⟩ := (le_iff_l hℳ m n).mp h
  change SecondOrderPowers.value_l hE m ≤ SecondOrderPowers.value_l hE (add_l m k)
  rw [SecondOrderPowers.add_l hℳ hE]
  change SecondOrderPowers.value_l hE m ≤
    SecondOrderPowers.value_l hE m * SecondOrderPowers.value_l hE k
  have h₁ : 1 ≤ SecondOrderPowers.value_l hE k := by
    simpa only [zero_add] using
      (lt_iff_add_one_le_l hℳ 0 _).mp (positive_l hℳ hE k)
  exact le_mul_of_one_le_right (zero_le_l hℳ _) h₁

/-- 较高位的幂是较低位权重的偶数倍。 -/
theorem even_multiple_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : spec_l E)
    (m n : num_l ℳ) (h : SecondOrderOrder.lt_l m n) :
    ∃ k, SecondOrderPowers.value_l hE n =
      mul_l k (add_l (SecondOrderPowers.value_l hE m) (SecondOrderPowers.value_l hE m)) := by
  letI := semiring_l hℳ
  obtain ⟨k, rfl⟩ := h
  refine ⟨SecondOrderPowers.value_l hE k, ?_⟩
  rw [SecondOrderPowers.add_l hℳ hE, successor_l hℳ hE]
  change SecondOrderPowers.value_l hE m *
    (SecondOrderPowers.value_l hE k + SecondOrderPowers.value_l hE k) =
      SecondOrderPowers.value_l hE k *
        (SecondOrderPowers.value_l hE m + SecondOrderPowers.value_l hE m)
  ring

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBinaryPowers
