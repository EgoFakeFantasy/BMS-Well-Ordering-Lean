import BMSConstructibleBridge.SecondOrderProgramListTake
import BMSConstructibleBridge.SecondOrderProgramMapConsequences

/-!
# 原 trimZeroRows 的完整数组程序

先在原数组上计算同一trimHeight，再把每一原列裁到该长度。高度不是外部给定界，
各列也不补齐为矩形。标准身份精确等于原trimZeroRows；任意内部数组的外层长度
由已证完整map长度保持给出。此模块不把裁剪高度界误用为生成历史高度界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimArray

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramListMap (map_m map_encode_l)
open SecondOrderProgramListTake (take_m take_encode_l)
open SecondOrderProgramTrimHeight (array_encode_l trim_encode_l)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 映射回调只取当前原列与共享高度，不使用列下标。 -/
def column_m : code_m := .comp take_m (.pair (.comp .right .right) .left)

/-- 同一原数组既供计算裁剪高度，也作为被遍历列表。 -/
def input_m : code_m := .pair SecondOrderProgramTrimHeight.trim_m PrimitiveProgram.id_m

/-- 完整裁剪数组程序，保留列顺序和外层长度。 -/
def trim_m : code_m := .comp (map_m column_m) input_m

/-- 标准每列的回调恰为原take。 -/
theorem column_encode_l (h i : Nat) (s : List Nat) :
    eval_l column_m (Nat.pair h (Nat.pair i (Encodable.encode s))) = Encodable.encode (s.take h) := by
  change eval_l take_m (Nat.pair
    (Nat.pair h (Nat.pair i (Encodable.encode s))).unpair.2.unpair.2
    (Nat.pair h (Nat.pair i (Encodable.encode s))).unpair.1) = _
  rw [Nat.unpair_pair, Nat.unpair_pair, take_encode_l]

/-- 全部标准数组上的实际输出等于原trimZeroRows，不只证明一个高度界。 -/
theorem array_encode_correct_l (a : BMSArray) :
    eval_l trim_m (Encodable.encode a) = Encodable.encode (BMS.trimZeroRows a) := by
  change eval_l (map_m column_m) (Nat.pair
    (eval_l SecondOrderProgramTrimHeight.trim_m (Encodable.encode a))
    (eval_l PrimitiveProgram.id_m (Encodable.encode a))) = _
  rw [trim_encode_l, PrimitiveProgram.id_l]
  have hm := map_encode_l column_m (BMS.trimHeight a) (a.map Encodable.encode)
  rw [← array_encode_l a] at hm
  rw [hm, array_encode_l (BMS.trimZeroRows a)]
  apply congrArg Encodable.encode
  apply List.ext_getElem?
  intro i
  simp only [BMS.trimZeroRows, List.getElem?_map, List.getElem?_mapIdx]
  cases hi : a[i]? with
  | none => rfl
  | some s =>
      simp only [Option.map_some]
      exact congrArg some (column_encode_l (BMS.trimHeight a) i s)

/-- 任意内部高度及原列上的实际回调图。 -/
theorem column_rel_l (hℳ : Theory.Models ℳ theory_m) {C T : set_l ℳ}
    (hC : graph_semantics_l (graph_m column_m) C)
    (hT : graph_semantics_l (graph_m take_m) T) (h i s y : num_l ℳ) :
    relation_l C (value_l h (value_l i s)) y ↔ relation_l T (value_l s h) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ take_m hT
  have hv := (comp_value_l hℳ hf (pair_value_l hℳ
    (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (left_value_l hℳ)))
    hC (value_l h (value_l i s)) y
  simpa only [SecondOrderUnpairing.unpair_l, hf hT] using hv

/-- 裁剪图使用原高度图和同一map图，数组输入保持不变。 -/
theorem trim_rel_l (hℳ : Theory.Models ℳ theory_m) {T H M : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hM : graph_semantics_l (graph_m (map_m column_m)) M) (x y : num_l ℳ) :
    relation_l T x y ↔ ∃ h, relation_l H x h ∧ relation_l M (value_l h x) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ SecondOrderProgramTrimHeight.trim_m hH
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ (map_m column_m) hM
  have hv := (comp_value_l hℳ hg (pair_value_l hℳ hf (id_value_l hℳ))) hT x y
  rw [hv]
  simp only [hf hH, hg hM, exists_eq_left']

/-- 全部内部原数组上，实际裁剪保持外层列数。 -/
theorem width_l (hℳ : Theory.Models ℳ theory_m) {T L : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hL : graph_semantics_l (graph_m length_m) L) (x y n : num_l ℳ)
    (ht : relation_l T x y) (hn : relation_l L x n) : relation_l L y n := by
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ SecondOrderProgramTrimHeight.trim_m
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m column_m)
  obtain ⟨h, _, hm⟩ := (trim_rel_l hℳ hT hH hM x y).mp ht
  exact SecondOrderProgramMapConsequences.map_length_l hℳ column_m hM hL h x y n hm hn

#print axioms column_m
#print axioms input_m
#print axioms trim_m
#print axioms column_encode_l
#print axioms array_encode_correct_l
#print axioms column_rel_l
#print axioms trim_rel_l
#print axioms width_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimArray
