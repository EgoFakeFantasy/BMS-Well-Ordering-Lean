import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderNumeralBounds

/-!
# 外部固定长度的内部列表码

使用外部有限列表描述固定标准长度的内部码，其条目仍可为非标准内部数。
只有长度等于外部数码 `ν n` 时才给出这样的有限展开；不把任意内部长度、种子高度、
轨迹长度或中间数组宽度视为标准有界。本节是固定行数论证的有限视图，不是最终良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListFiniteView

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListIteration SecondOrderProgramListLength
open SecondOrderProgramListShift SecondOrderProgramListLookup SecondOrderNumeralBounds
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 外部有限列表在模型内部的原配对编码；元素不要求是标准数码。 -/
noncomputable def encode_l : List (num_l ℳ) → num_l ℳ
  | [] => zero_l ℳ
  | a :: s => succ_l (value_l a (encode_l s))

/-- 内部配对与后继的注入性保证这个外部有限视图唯一。 -/
theorem encode_injective_l (hℳ : Theory.Models ℳ theory_m) :
    Function.Injective (encode_l (ℳ := ℳ)) := by
  intro s
  induction s with
  | nil =>
      intro t ht
      cases t with
      | nil => rfl
      | cons b t => exact False.elim (nonzero_l hℳ _ ht.symm)
  | cons a s ih =>
      intro t ht
      cases t with
      | nil => exact False.elim (nonzero_l hℳ _ ht)
      | cons b t =>
          have hp := SecondOrderPairingBounds.injective_l hℳ a (encode_l s) b (encode_l t)
            (injective_l hℳ ht)
          exact congrArg₂ List.cons hp.1 (ih hp.2)

/-- 外部有限列表的内部长度恰为其外部长度的原数码。 -/
theorem length_spec_encode_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (s : List (num_l ℳ)) :
    length_spec_l I (encode_l s) (numeral_val_l s.length) := by
  induction s with
  | nil => exact (length_zero_l hℳ hI (zero_l ℳ)).mpr rfl
  | cons a s ih =>
      exact (length_cons_l hℳ hI a (encode_l s) (numeral_val_l s.length)).mpr ih

/-- 仅对外部长度归纳：长度为 `ν n` 的任意内部码能展开为 `n` 个内部条目。 -/
theorem finite_decode_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (n : Nat) :
    ∀ x : num_l ℳ, length_spec_l I x (numeral_val_l n) →
      ∃ s : List (num_l ℳ), s.length = n ∧ x = encode_l s := by
  induction n with
  | zero =>
      intro x hx
      exact ⟨List.nil, rfl, (length_zero_l hℳ hI x).mp hx⟩
  | succ n ih =>
      intro x hx
      rcases predecessor_l hℳ x with rfl | ⟨p, rfl⟩
      · apply False.elim
        exact hx.2 (zero_l ℳ) (SecondOrderOrder.zero_succ_l hℳ (numeral_val_l n))
          ((iterate_zero_l hℳ hI (zero_l ℳ) (zero_l ℳ)).mpr rfl)
      · obtain ⟨a, t, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ p
        have ht := (length_cons_l hℳ hI a t (numeral_val_l n)).mp hx
        obtain ⟨s, hs, hts⟩ := ih t ht
        refine ⟨a :: s, congrArg Nat.succ hs, ?_⟩
        change succ_l (value_l a t) = succ_l (value_l a (encode_l s))
        rw [hts]

/-- 固定长度的精确双向刻画，而非只有从标准列表到内部码的方向。 -/
theorem finite_decode_iff_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (n : Nat) (x : num_l ℳ) :
    length_spec_l I x (numeral_val_l n) ↔
      ∃ s : List (num_l ℳ), s.length = n ∧ x = encode_l s := by
  constructor
  · exact finite_decode_l hℳ hI n x
  · rintro ⟨s, hs, rfl⟩
    rw [← hs]
    exact length_spec_encode_l hℳ hI s

/-- 固定外部长度下的外部有限视图确实唯一。 -/
theorem finite_decode_unique_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) {n : Nat} {x : num_l ℳ}
    (hx : length_spec_l I x (numeral_val_l n)) :
    ∃! s : List (num_l ℳ), s.length = n ∧ x = encode_l s := by
  obtain ⟨s, hs, hx⟩ := finite_decode_l hℳ hI n x hx
  exact ⟨s, ⟨hs, hx⟩, fun t ht => encode_injective_l hℳ (ht.2.symm.trans hx)⟩

/-- 原读取图在有限视图的标准下标上返回相应的内部条目。 -/
theorem lookup_finite_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E) (s : List (num_l ℳ)) (k : Nat)
    (y : num_l ℳ) :
    relation_l E (value_l (encode_l s) (numeral_val_l k)) y ↔
      s[k]?.getD (zero_l ℳ) = y := by
  induction s generalizing k with
  | nil =>
      obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
      exact lookup_past_end_l hℳ hE hI (length_spec_encode_l hℳ hI [])
        (numeral_val_l k) y (zero_le_l hℳ (numeral_val_l k))
  | cons a s ih =>
      cases k with
      | zero => exact lookup_cons_zero_l hℳ hE a (encode_l s) y
      | succ k =>
          change relation_l E (value_l (succ_l (value_l a (encode_l s)))
            (succ_l (numeral_val_l k))) y ↔ s[k]?.getD (zero_l ℳ) = y
          rw [lookup_cons_succ_l hℳ hE]
          exact ih k

/-- 每个合法内部下标对应一个外部有限位置，读取图返回该处的实际内部条目。 -/
theorem lookup_at_internal_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E) (s : List (num_l ℳ))
    {j : num_l ℳ} (hj : SecondOrderOrder.lt_l j (numeral_val_l s.length)) :
    ∃ k : Fin s.length, j = numeral_val_l k.val ∧
      ∀ y, relation_l E (value_l (encode_l s) j) y ↔ s[k] = y := by
  obtain ⟨k, hk, hj⟩ := (lt_numeral_iff_l hℳ s.length j).mp hj
  refine ⟨⟨k, hk⟩, hj, fun y => ?_⟩
  rw [hj, lookup_finite_l hℳ hE, List.getElem?_eq_getElem hk]
  rfl

#print axioms encode_l
#print axioms encode_injective_l
#print axioms length_spec_encode_l
#print axioms finite_decode_l
#print axioms finite_decode_iff_l
#print axioms finite_decode_unique_l
#print axioms lookup_finite_l
#print axioms lookup_at_internal_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListFiniteView
