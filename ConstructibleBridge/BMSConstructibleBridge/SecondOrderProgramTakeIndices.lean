import BMSConstructibleBridge.SecondOrderProgramListTake
import BMSConstructibleBridge.SecondOrderProgramReverseConsequences
import BMSConstructibleBridge.SecondOrderProgramSubtractionBounds

/-!
# 原前缀程序的全部内部有效下标

两次反转之间的drop偏移与截断长度精确相消，因此输出的每个有效位置读原码
同一位置。另保留越界返回零的单向语义；合法零值不被误判成越界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTakeIndices

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramListTake (take_m take_rel_l take_length_min_l)
open SecondOrderProgramListDrop (drop_length_l drop_lookup_l)
open SecondOrderProgramListReverse (reverse_m reverse_step_m)
open SecondOrderProgramListReverseEntries (reverse_length_l)
open SecondOrderProgramListFold (fold_m)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m lookup_past_end_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramSubtractionBounds (sub_le_l sub_add_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原前缀输出的每个有效内部位置保持原位置读值，不仅保持输出长度。 -/
theorem take_lookup_l (hℳ : Theory.Models ℳ theory_m) {K L E : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n k y j : num_l ℳ}
    (hn : relation_l L x n) (hy : relation_l K (value_l x k) y) :
    letI := order_l hℳ
    j < min n k → ∀ z, relation_l E (value_l y j) z ↔ relation_l E (value_l x j) z := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  intro hj z
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨D, hDf, hD⟩ := graph_total_l hℳ sub_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨v, d, w, hv, hd, hw, hwy⟩ := (take_rel_l hℳ hK hT hI hL hD hn k y).mp hy
  obtain ⟨m, hm, _⟩ := hDf (value_l n d)
  have hvn := reverse_length_l hℳ hT hF hL hI x v n hv hn
  have hwm := drop_length_l hℳ hI hL hD hvn hw hm
  have hym := reverse_length_l hℳ hT hF hL hI w y m hwy hwm
  have hmin : m = min n k := function_value_unique_l
    (function_of_semantics_l hℳ length_m hL) hym (take_length_min_l hℳ hK hL hn hy)
  have hjm : SecondOrderOrder.lt_l j m := hmin.symm ▸ hj
  obtain ⟨q, hjq, _⟩ := SecondOrderProgramReverseConsequences.index_exists_l hℳ hjm
  have hmd : add_l m d = n := sub_add_l hℳ hD hm (sub_le_l hℳ hD hd)
  have hidx : add_l (succ_l (add_l d q)) j = n := calc
    _ = add_l (add_l (succ_l j) q) d := by
      simp only [succ_eq_l hℳ]
      change (d + q + 1) + j = (j + 1 + q) + d
      ac_rfl
    _ = add_l m d := congrArg (fun a => add_l a d) hjq
    _ = n := hmd
  exact (SecondOrderProgramReverseConsequences.lookup_l hℳ hT hL hE hwy hwm hjq z).trans
    ((drop_lookup_l hℳ hI hE hw q z).trans
      (SecondOrderProgramReverseConsequences.lookup_l hℳ hT hL hE hv hn hidx z))

/-- 超过真实前缀长度后，原lookup返回零；不取逆命题判定位置有效性。 -/
theorem take_lookup_past_l (hℳ : Theory.Models ℳ theory_m) {K L E : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n k y j : num_l ℳ}
    (hn : relation_l L x n) (hy : relation_l K (value_l x k) y) :
    letI := order_l hℳ
    min n k ≤ j → ∀ z, relation_l E (value_l y j) z ↔ zero_l ℳ = z := by
  intro hj z
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  exact lookup_past_end_l hℳ hE hI
    ((length_rel_l hℳ hL hI _ _).mp (take_length_min_l hℳ hK hL hn hy)) j z hj

/-- 取到全部原长度时，前缀程序输出等于同一原码，而非仅逐项读取相同。 -/
theorem take_full_l (hℳ : Theory.Models ℳ theory_m) {K L : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hL : graph_semantics_l (graph_m length_m) L) {x n k y : num_l ℳ}
    (hn : relation_l L x n) (hy : relation_l K (value_l x k) y)
    (hk : n = k ∨ SecondOrderOrder.lt_l n k) : y = x := by
  letI := order_l hℳ
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  have hym := take_length_min_l hℳ hK hL hn hy
  rw [min_eq_left (show n ≤ k from hk)] at hym
  apply SecondOrderProgramListExtensionality.extensionality_l hℳ hL hE hym hn
  intro i hi z hz
  have him : i < min n k := by rwa [min_eq_left (show n ≤ k from hk)]
  exact (take_lookup_l hℳ hK hL hE hn hy him z).mp hz

#print axioms take_lookup_l
#print axioms take_lookup_past_l
#print axioms take_full_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTakeIndices
