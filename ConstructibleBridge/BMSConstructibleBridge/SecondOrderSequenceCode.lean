import BMSConstructibleBridge.SecondOrderFiniteCode
import BMSConstructibleBridge.SecondOrderFiniteRange

/-!
# 内部有限函数及迭代历史的单数编码

有限函数图先截为内部数集，再以值域界和配对区间证明其有界。二进制码精确
保存整段关系，不仅保存已知输出；长度参数仍可为非标准模型数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSequenceCode

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem selector_l (hℳ : Theory.Models ℳ theory_m) (H : set_l ℳ) (n : num_l ℳ) :
    ∃ P : set_l ℳ, ∀ z, mem_l z P ↔
      ∃ i a, value_l i a = z ∧ SecondOrderOrder.lt_l i n ∧ relation_l H i a := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
      (.conj (PrimitiveFormulas.lt_m (.bvar (.there .here)) (.fvar (.there .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree H).pushFree n)
  refine ⟨P, fun z => (hP z).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderOrder.formula_l, SecondOrderPairing.edge_l]
  rfl

theorem bound_l (hℳ : Theory.Models ℳ theory_m) (H P : set_l ℳ) (n : num_l ℳ)
    (hH : ∀ i, SecondOrderOrder.lt_l i n → ∃! a, relation_l H i a)
    (hP : ∀ z, mem_l z P ↔
      ∃ i a, value_l i a = z ∧ SecondOrderOrder.lt_l i n ∧ relation_l H i a) :
    ∃ m, ∀ z, mem_l z P → SecondOrderOrder.lt_l z m := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨b, hb⟩ := SecondOrderFiniteRange.partial_bound_l hℳ H n hH
  refine ⟨(max n b + 1) * (max n b + 1), ?_⟩
  intro z hz
  obtain ⟨i, a, rfl, hi, ha⟩ := (hP z).mp hz
  have h₁ : max i a + 1 ≤ max n b + 1 :=
    add_le_add_left (max_le_max (le_of_lt hi) (le_of_lt (hb i hi a ha))) _
  exact lt_of_lt_of_le (SecondOrderPairingBounds.interval_l hℳ i a).2
    (mul_self_le_mul_self (zero_le_l hℳ _) h₁)

/-- 二进制位读取数值函数图：界内精确，界外不存在额外边。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (H : set_l ℳ) (n : num_l ℳ)
    (hH : ∀ i, SecondOrderOrder.lt_l i n → ∃! a, relation_l H i a) :
    ∃ c, ∀ i a, SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE (value_l i a)) ↔
      SecondOrderOrder.lt_l i n ∧ relation_l H i a := by
  obtain ⟨P, hP⟩ := selector_l hℳ H n
  obtain ⟨m, hm⟩ := bound_l hℳ H P n hH hP
  obtain ⟨c, _, hc⟩ := SecondOrderFiniteCode.segment_l hℳ hE P m
  have h : ∀ z, SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE z) ↔ mem_l z P := by
    intro z
    exact (hc z).trans ⟨fun h => h.2, fun h => ⟨hm z h, h⟩⟩
  refine ⟨c, fun i a => ((h (value_l i a)).trans (hP (value_l i a))).trans ?_⟩
  constructor
  · rintro ⟨j, b, h₁, hj, hb⟩
    obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ j b i a h₁
    exact ⟨hj, hb⟩
  · intro h₁
    exact ⟨i, a, rfl, h₁⟩

/-- 任一已构造的内部有限迭代历史都能用一个模型数编码其完整有限图。 -/
theorem history_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (F H : set_l ℳ) (a n : num_l ℳ)
    (hH : SecondOrderHistory.spec_l F H a n) :
    ∃ c, ∀ i b, SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE (value_l i b)) ↔
      SecondOrderOrder.lt_l i (succ_l n) ∧ relation_l H i b :=
  exists_l hℳ hE H (succ_l n) hH.1

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSequenceCode
