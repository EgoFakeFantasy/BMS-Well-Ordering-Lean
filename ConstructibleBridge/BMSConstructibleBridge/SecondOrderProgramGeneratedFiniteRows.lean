import BMSConstructibleBridge.SecondOrderProgramGeneratedNormalized
import BMSConstructibleBridge.SecondOrderProgramListFiniteView

/-!
# 当前外部行界下的原生成数组列视图

准确当前高度受固定外部n的数码约束，因此它自身是某个k<=n的数码。
每个有效列随之具有外部有限长度k，条目仍是任意内部数；数组宽度、种子高度与
生成轨迹不被标准化。这里没有把整个内部数组换成宿主有限列表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedFiniteRows

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramGeneratedDecode (decode_m)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramZeroRows (zero_rows_l)
open SecondOrderProgramListFiniteView (encode_l finite_decode_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 仅当前实际高度落在固定外部初始段中；没有对输入码或宽度加标准性假设。 -/
theorem height_numeral_l (hℳ : Theory.Models ℳ theory_m) {D H L E : set_l ℳ}
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) (n : Nat) {c y : num_l ℳ}
    (hy : relation_l D c y) (hb : zero_rows_l E y (numeral_val_l n)) :
    ∃ (w : num_l ℳ) (k : Nat), k ≤ n ∧ rectangular_l L E y w (numeral_val_l k) ∧
      relation_l H y (numeral_val_l k) := by
  obtain ⟨w, h, hyr, hh, hle⟩ :=
    SecondOrderProgramGeneratedNormalized.decode_bounded_l hℳ hD hH hL hE hy hb
  rcases hle with he | hlt
  · rw [he] at hyr hh
    exact ⟨w, n, le_refl n, hyr, hh⟩
  · obtain ⟨k, hk, he⟩ := (SecondOrderNumeralBounds.lt_numeral_iff_l hℳ n h).mp hlt
    rw [he] at hyr hh
    exact ⟨w, k, Nat.le_of_lt hk, hyr, hh⟩

/-- 每个有效原列都有至多n个内部条目的准确有限视图，保留其原码身份。 -/
theorem columns_finite_l (hℳ : Theory.Models ℳ theory_m) {D H L E : set_l ℳ}
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) (n : Nat) {c y : num_l ℳ}
    (hy : relation_l D c y) (hb : zero_rows_l E y (numeral_val_l n)) :
    ∃ (w : num_l ℳ) (k : Nat), k ≤ n ∧ rectangular_l L E y w (numeral_val_l k) ∧
      relation_l H y (numeral_val_l k) ∧
      ∀ j a, SecondOrderOrder.lt_l j w → relation_l E (value_l y j) a →
        ∃ s : List (num_l ℳ), s.length = k ∧ a = encode_l s := by
  obtain ⟨w, k, hk, hyr, hh⟩ := height_numeral_l hℳ hD hH hL hE n hy hb
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramListIteration.iterate_m
  refine ⟨w, k, hk, hyr, hh, ?_⟩
  intro j a hj ha
  exact finite_decode_l hℳ hI k a ((length_rel_l hℳ hL hI a (numeral_val_l k)).mp (hyr.2 j hj a ha))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedFiniteRows
