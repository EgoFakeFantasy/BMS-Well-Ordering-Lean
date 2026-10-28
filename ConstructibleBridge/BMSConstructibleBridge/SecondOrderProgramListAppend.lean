import BMSConstructibleBridge.SecondOrderProgramReverseConsequences

/-!
# 原列表拼接程序与内部下标

先反转左列表，再用已有反转折叠接到右列表前面。标准端等于原List.append；
内部长度相加，左段与右段读值分别保序，供原复制块拼接调用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListAppend

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramListReverse (reverse_m reverse_step_m reverse_encode_l reverse_fold_encode_l)
open SecondOrderProgramListReverseEntries (reverse_length_l fold_length_l)
open SecondOrderProgramListReverseIndices (fold_back_l fold_front_l)
open SecondOrderProgramListFold (fold_m)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 折叠输入为反转后的左码与未改变的右码。 -/
def input_m : code_m := .pair (.comp reverse_m .left) .right

/-- 原七构造中的拼接程序，没有新的列表拼接原语。 -/
def append_m : code_m := .comp (fold_m reverse_step_m) input_m

/-- 标准端精确等于原列表拼接，保留两个列表内部顺序。 -/
theorem append_encode_l (s t : List Nat) :
    eval_l append_m (Nat.pair (Encodable.encode s) (Encodable.encode t)) =
      Encodable.encode (s ++ t) := by
  change eval_l (fold_m reverse_step_m) (Nat.pair
    (eval_l reverse_m (Nat.pair (Encodable.encode s) (Encodable.encode t)).unpair.1)
    (Nat.pair (Encodable.encode s) (Encodable.encode t)).unpair.2) = _
  rw [Nat.unpair_pair, reverse_encode_l, reverse_fold_encode_l, List.reverse_reverse]

/-- 输入接线准确保留右码，只对左码调用同一原反转图。 -/
theorem input_rel_l (hℳ : Theory.Models ℳ theory_m) {P T : set_l ℳ}
    (hP : graph_semantics_l (graph_m input_m) P)
    (hT : graph_semantics_l (graph_m reverse_m) T) (x y z : num_l ℳ) :
    relation_l P (value_l x y) z ↔ ∃ v, relation_l T x v ∧ value_l v y = z := by
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ .left
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ .right
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ (.comp reverse_m .left)
  have hq (v : num_l ℳ) : relation_l Q (value_l x y) v ↔ relation_l T x v := by
    rw [comp_rel_l hℳ (graph_m reverse_m) (graph_m .left) T A hT hA hQ]
    simp only [left_rel_l hℳ hA, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [pair_rel_l hℳ (graph_m (.comp reverse_m .left)) (graph_m .right) Q B hQ hB hP]
  simp only [hq, right_rel_l hℳ hB, SecondOrderUnpairing.unpair_l]
  constructor
  · rintro ⟨v, _, hv, rfl, hz⟩
    exact ⟨v, hv, hz⟩
  · rintro ⟨v, hv, hz⟩
    exact ⟨v, y, hv, rfl, hz⟩

/-- 拼接图由同一反转图与同一反转折叠图组成。 -/
theorem append_rel_l (hℳ : Theory.Models ℳ theory_m) {A T F : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hF : graph_semantics_l (graph_m (fold_m reverse_step_m)) F) (x y z : num_l ℳ) :
    relation_l A (value_l x y) z ↔ ∃ v, relation_l T x v ∧ relation_l F (value_l v y) z := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ input_m
  rw [comp_rel_l hℳ (graph_m (fold_m reverse_step_m)) (graph_m input_m) F P hF hP hA]
  simp only [input_rel_l hℳ hP hT]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, hz⟩
    exact ⟨v, hv, hz⟩
  · rintro ⟨v, hv, hz⟩
    exact ⟨value_l v y, ⟨v, hv, rfl⟩, hz⟩

/-- 原拼接输出的真实内部长度等于两段真实长度之和。 -/
theorem append_length_l (hℳ : Theory.Models ℳ theory_m) {A L : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hL : graph_semantics_l (graph_m length_m) L) {x y z n m : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l L y m) (hz : relation_l A (value_l x y) z) :
    relation_l L z (add_l n m) := by
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨v, hv, hvz⟩ := (append_rel_l hℳ hA hT hF x y z).mp hz
  exact fold_length_l hℳ hF hL hI v y z n m hvz
    (reverse_length_l hℳ hT hF hL hI x v n hv hx) hy

/-- 拼接的左段所有有效内部位置读值不变。 -/
theorem append_left_l (hℳ : Theory.Models ℳ theory_m) {A L E : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y z n m i : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l L y m) (hz : relation_l A (value_l x y) z)
    (hi : SecondOrderOrder.lt_l i n) (w : num_l ℳ) :
    relation_l E (value_l z i) w ↔ relation_l E (value_l x i) w := by
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨v, hv, hvz⟩ := (append_rel_l hℳ hA hT hF x y z).mp hz
  have hvn := reverse_length_l hℳ hT hF hL hI x v n hv hx
  obtain ⟨k, hik, _⟩ := SecondOrderProgramReverseConsequences.index_exists_l hℳ hi
  exact (fold_front_l hℳ hF hL hE hI v y z n m i k w hvz hvn hy hik).trans
    (SecondOrderProgramReverseConsequences.lookup_l hℳ hT hL hE hv hx
      (SecondOrderProgramReverseConsequences.index_symm_l hℳ hik) w)

/-- 拼接右段读值按左段真实内部长度偏移。 -/
theorem append_right_l (hℳ : Theory.Models ℳ theory_m) {A L E : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y z n m i : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l L y m) (hz : relation_l A (value_l x y) z)
    (hi : SecondOrderOrder.lt_l i m) (w : num_l ℳ) :
    relation_l E (value_l z (add_l n i)) w ↔ relation_l E (value_l y i) w := by
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨v, hv, hvz⟩ := (append_rel_l hℳ hA hT hF x y z).mp hz
  exact fold_back_l hℳ hF hL hE hI v y z n m i w hvz
    (reverse_length_l hℳ hT hF hL hI x v n hv hx) hy hi

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListAppend
