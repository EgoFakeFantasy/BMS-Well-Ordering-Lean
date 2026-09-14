import BMSConstructibleBridge.SecondOrderNumberHistory

/-!
# 内部有限赋值及量词扩张

赋值是一个数值有限函数图，长度覆盖任意模型数。前插一个值同时移动全部旧
变量位置，且保证新码没有界外边，为内部量词语义提供实际可实现的赋值操作。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignment

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderNumberHistory

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E) (c n : num_l ℳ) : Prop :=
  (∀ i, SecondOrderOrder.lt_l i n → ∃! b, entry_l hE c i b) ∧
    ∀ i b, entry_l hE c i b → SecondOrderOrder.lt_l i n

theorem encode_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (H : set_l ℳ) (n : num_l ℳ)
    (hH : ∀ i, SecondOrderOrder.lt_l i n → ∃! b, relation_l H i b) :
    ∃ c, spec_l hE c n ∧ ∀ i b, entry_l hE c i b ↔ SecondOrderOrder.lt_l i n ∧ relation_l H i b := by
  obtain ⟨c, hc⟩ := SecondOrderSequenceCode.exists_l hℳ hE H n hH
  refine ⟨c, ⟨?_, fun i b hi => ((hc i b).mp hi).1⟩, hc⟩
  intro i hi
  obtain ⟨b, hb, h⟩ := hH i hi
  exact ⟨b, (hc i b).mpr ⟨hi, hb⟩, fun a ha => h a ((hc i a).mp ha).2⟩

theorem empty_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) : spec_l hE (zero_l ℳ) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  refine ⟨fun i hi => False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi), ?_⟩
  intro i b hi
  exact False.elim (SecondOrderDigit.below_l hℳ _ _ (SecondOrderBinaryPowers.positive_l hℳ hE _) hi)

/-- 任意模型长度的赋值都可前插一个值，并精确平移其余变量。 -/
theorem prepend_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (c n x : num_l ℳ) (hc : spec_l hE c n) :
    ∃ d, spec_l hE d (succ_l n) ∧
      (∀ b, entry_l hE d (zero_l ℳ) b ↔ b = x) ∧
        ∀ i b, entry_l hE d (succ_l i) b ↔ entry_l hE c i b := by
  obtain ⟨H, hH⟩ := SecondOrderSequenceSyntax.decode_l hℳ hE c
  obtain ⟨K, h₀, h₁⟩ := SecondOrderFunctions.prefix_l hℳ H x
  have hK : ∀ i, SecondOrderOrder.lt_l i (succ_l n) → ∃! b, relation_l K i b := by
    intro i hi
    rcases predecessor_l hℳ i with rfl | ⟨j, rfl⟩
    · exact ⟨x, (h₀ x).mpr rfl, fun b hb => (h₀ b).mp hb⟩
    · obtain ⟨b, hb, h⟩ := hc.1 j ((SecondOrderOrder.succ_iff_l hℳ j n).mp hi)
      refine ⟨b, (h₁ j b).mpr ((hH j b).mpr hb), ?_⟩
      intro a ha
      exact h a ((hH j a).mp ((h₁ j a).mp ha))
  obtain ⟨d, hd, h⟩ := encode_l hℳ hE K (succ_l n) hK
  refine ⟨d, hd, ?_, ?_⟩
  · intro b
    exact (h (zero_l ℳ) b).trans ⟨fun h => (h₀ b).mp h.2,
      fun hb => ⟨SecondOrderOrder.zero_succ_l hℳ n, (h₀ b).mpr hb⟩⟩
  · intro i b
    refine (h (succ_l i) b).trans ?_
    constructor
    · intro hb
      exact (hH i b).mp ((h₁ i b).mp hb.2)
    · intro hb
      exact ⟨(SecondOrderOrder.succ_iff_l hℳ i n).mpr (hc.2 i b hb),
        (h₁ i b).mpr ((hH i b).mpr hb)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAssignment
