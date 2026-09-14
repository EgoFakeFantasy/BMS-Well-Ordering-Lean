import BMSConstructibleBridge.SecondOrderBinaryPowers
import BMSConstructibleBridge.SecondOrderDigit

/-!
# 任意模型中的有限数集编码

每个内部数集在任意模型界以下的截段都有一个数值二进制码。归纳正文是明确
的纯算术公式，带内部幂函数和原数集两个实数参数；不要求界是标准数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteCode

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由参数依次为截段界、二进制幂图、被编码的内部数集。 -/
def formula_m : Formula signature_m [] [.num, .set, .set] :=
  .existsE .num (.existsE .num (.conj
    (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there .here)))
    (.conj (PrimitiveFormulas.lt_m (.bvar .here) (.bvar (.there .here)))
      (.forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar .here))
        (.forallE .num (.imp
          (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
          (.iff (SecondOrderDigit.formula_m (.bvar (.there (.there .here))) (.bvar .here))
            (.rel .mem (.cons (.bvar (.there .here))
              (.cons (.fvar (.there (.there .here))) .nil)))))))))))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (X : set_l ℳ) (n : num_l ℳ) :
    ∃ c, SecondOrderOrder.lt_l c (SecondOrderPowers.value_l hE n) ∧
      ∀ i, SecondOrderOrder.lt_l i n →
        (SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE i) ↔ mem_l i X) := by
  classical
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  apply induct_l hℳ formula_m pure_m (((Env.empty (M := ℳ)).pushFree X).pushFree E)
    (fun n => ∃ c, c < SecondOrderPowers.value_l hE n ∧ ∀ i, i < n →
      (SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE i) ↔ mem_l i X)) ?_ ?_ ?_ n
  · intro n
    simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l,
      SecondOrderOrder.formula_l, SecondOrderDigit.formula_l]
    change (∃ p c, relation_l E n p ∧ c < p ∧ ∀ i, i < n → ∀ q,
      relation_l E i q → (SecondOrderDigit.holds_l c q ↔ mem_l i X)) ↔ _
    constructor
    · rintro ⟨p, c, hp, hc, h⟩
      obtain rfl := (SecondOrderPowers.eq_l hE n p).mp hp
      exact ⟨c, hc, fun i hi => h i hi _ (SecondOrderPowers.edge_l hE i)⟩
    · rintro ⟨c, hc, h⟩
      refine ⟨_, c, SecondOrderPowers.edge_l hE n, hc, ?_⟩
      intro i hi q hq
      obtain rfl := (SecondOrderPowers.eq_l hE i q).mp hq
      exact h i hi
  · refine ⟨0, SecondOrderBinaryPowers.positive_l hℳ hE _, ?_⟩
    intro i hi
    exact False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi)
  · rintro n ⟨c, hc, h⟩
    have hp := SecondOrderBinaryPowers.positive_l hℳ hE n
    have h₁ : c + SecondOrderPowers.value_l hE n < SecondOrderPowers.value_l hE (succ_l n) := by
      rw [SecondOrderBinaryPowers.successor_l hℳ hE]
      exact add_lt_add_left hc _
    by_cases hn : mem_l n X
    · refine ⟨c + SecondOrderPowers.value_l hE n, h₁, ?_⟩
      intro i hi
      rcases eq_or_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ i n).mp hi) with rfl | hi
      · exact iff_of_true (SecondOrderDigit.interval_l hℳ _ _
          (not_lt_of_ge (le_add_of_nonneg_left (zero_le_l hℳ c)))
          (by rw [← SecondOrderBinaryPowers.successor_l hℳ hE]; exact h₁)) hn
      · obtain ⟨k, hk⟩ := SecondOrderBinaryPowers.even_multiple_l hℳ hE i n hi
        change SecondOrderDigit.holds_l (add_l c (SecondOrderPowers.value_l hE n)) _ ↔ _
        rw [hk, SecondOrderDigit.periodic_l hℳ _ _ _ (SecondOrderBinaryPowers.positive_l hℳ hE i)]
        exact h i hi
    · refine ⟨c, lt_trans hc ?_, ?_⟩
      · rw [SecondOrderBinaryPowers.successor_l hℳ hE]
        exact lt_add_of_pos_right _ hp
      · intro i hi
        rcases eq_or_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ i n).mp hi) with rfl | hi
        · exact iff_of_false (SecondOrderDigit.below_l hℳ _ _ hc) hn
        · exact h i hi

/-- 同一个码在所有更高位为零，因此精确编码截段而非只在界内碰巧相符。 -/
theorem segment_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (X : set_l ℳ) (n : num_l ℳ) :
    ∃ c, SecondOrderOrder.lt_l c (SecondOrderPowers.value_l hE n) ∧ ∀ i,
      SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE i) ↔
        SecondOrderOrder.lt_l i n ∧ mem_l i X := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨c, hc, h⟩ := exists_l hℳ hE X n
  refine ⟨c, hc, fun i => ?_⟩
  by_cases hi : i < n
  · exact (h i hi).trans (iff_and_self.mpr (fun _ => hi))
  · exact iff_of_false (SecondOrderDigit.below_l hℳ _ _
      (lt_of_lt_of_le hc (SecondOrderBinaryPowers.monotone_l hℳ hE n i (le_of_not_gt hi))))
      (fun h => hi h.1)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteCode
