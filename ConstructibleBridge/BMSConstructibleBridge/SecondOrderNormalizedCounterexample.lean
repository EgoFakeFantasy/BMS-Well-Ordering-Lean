import BMSConstructibleBridge.SecondOrderDecodedCounterexample
import BMSConstructibleBridge.SecondOrderProgramGeneratedFiniteRows

/-!
# 原固定行界反例实数中的准确有限列视图

保留从原反例轨迹实数与原解码图复合得到的同一数组实数Y，不另造下降链。
每项的当前高度成为k<=n的标准数码，每个有效列恰有k个内部条目；相邻项仍由
原严格展开相连。此处只加强反例规格，尚未排除它，也不是最终普通Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNormalizedCounterexample

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramArithmetic
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramGeneratedDecode (decode_m)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListFiniteView (encode_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原闭句的固定外部行界反例产生同一内部数组实数，其每个有效列有准确有限视图。
宽度与条目可以非标准，逐步展开指标只留存在，不引入额外选择实数。 -/
theorem arrays_l (hℳ : Theory.Models ℳ theory_m) {D X H L E : set_l ℳ}
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) (n : Nat) (η : Env ℳ [.set] [.num])
    (hη : η.freeVal .here = numeral_val_l n)
    (hbad : ¬Formula.satisfies η SecondOrderConcreteFormula.matrix_m) :
    ∃ Y : set_l ℳ, function_l Y ∧
      (∀ i u, relation_l Y i u ↔ ∃ c, relation_l (η.boundVal .here) i c ∧ relation_l D c u) ∧
      (∀ i u, relation_l Y i u → ∃ (w : num_l ℳ) (k : Nat), k ≤ n ∧
        rectangular_l L E u w (numeral_val_l k) ∧ relation_l H u (numeral_val_l k) ∧
        ∀ j a, SecondOrderOrder.lt_l j w → relation_l E (value_l u j) a →
          ∃ s : List (num_l ℳ), s.length = k ∧ a = encode_l s) ∧
      ∀ i u v, relation_l Y i u → relation_l Y (succ_l i) v →
        ∃ k, relation_l X (value_l u k) v ∧ v ≠ u := by
  obtain ⟨Y, hY, hsource, hbound, hstep⟩ :=
    SecondOrderDecodedCounterexample.arrays_l hℳ hD hX hE η hbad
  refine ⟨Y, hY, hsource, ?_, hstep⟩
  intro i u hu
  obtain ⟨c, _, hc⟩ := (hsource i u).mp hu
  have hb := hbound i u hu
  rw [hη] at hb
  exact SecondOrderProgramGeneratedFiniteRows.columns_finite_l hℳ hD hH hL hE n hc hb

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNormalizedCounterexample
