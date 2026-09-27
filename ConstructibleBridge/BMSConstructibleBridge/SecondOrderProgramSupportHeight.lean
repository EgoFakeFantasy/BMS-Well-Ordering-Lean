import BMSConstructibleBridge.SecondOrderProgramSupportCorrectness
import YesMetaZFC.BMS.Reference

/-!
# 原列支撑高度的程序身份与内部规格

以同一原列表码的长度作为扫描次数。标准端逐步对应 `BMS.supportHeight`，
内部端得到原读取图的最小零尾边界，不把非标准列外部解码成有限列表。
程序本身只使用原七构造；长度、读取和扫描图全部由原模型公理产生。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSupportHeight

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListLookup SecondOrderProgramSupportScan
open SecondOrderProgramLength
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 末尾新添一个非零项时，原支撑高度恰好刷新为新长度。 -/
theorem support_append_l (s : List Nat) (a : Nat) :
    BMS.supportHeight (s ++ [a]) = if a = 0 then BMS.supportHeight s else s.length + 1 := by
  by_cases ha : a = 0
  · subst a
    exact BMS.supportHeight_append_zero s
  · simp only [if_neg ha]
    induction s with
    | nil =>
        change BMS.supportHeight (a :: []) = 1
        rw [BMS.supportHeight_cons_l]
        change (if (0 : Nat) = 0 then (if a = 0 then 0 else 1) else 0 + 1) = 1
        rw [if_pos rfl, if_neg ha]
    | cons b s ih =>
        rw [List.cons_append, BMS.supportHeight_cons_l, ih, if_neg (Nat.succ_ne_zero _)]
        rfl

/-- 扫描前缀的实际程序恰好计算原定义的前缀支撑高度，包括越界补零。 -/
theorem scan_encode_l (s : List Nat) (k : Nat) :
    eval_l scan_m (Nat.pair (Encodable.encode s) k) = BMS.supportHeight (s.take k) := by
  rw [scan_m, PrimitiveProgram.prec_l]
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [PrimitiveHistory.run_l] at ih ⊢
      rw [scan_step_eval_l, ih, lookup_encode_l]
      by_cases hk : k < s.length
      · rw [List.take_succ_eq_append_getElem hk, support_append_l,
          List.getElem?_eq_getElem hk, Option.getD_some, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hk)]
      · have hle := Nat.le_of_not_lt hk
        rw [List.getElem?_eq_none_iff.mpr hle, Option.getD_none, if_pos rfl,
          List.take_of_length_le hle, List.take_of_length_le (Nat.le_succ_of_le hle)]

/-- 原输入码与其实际长度组成扫描输入。 -/
def support_input_m : code_m := .pair PrimitiveProgram.id_m length_m

/-- 原支撑高度的显式程序，不含额外图符号或最小化指令。 -/
def support_m : code_m := .comp scan_m support_input_m

/-- 与原仓库列支撑高度逐标准输入相同，而非仅为新规格命名。 -/
theorem support_encode_l (s : List Nat) :
    eval_l support_m (Encodable.encode s) = BMS.supportHeight s := by
  change eval_l scan_m (Nat.pair (eval_l PrimitiveProgram.id_m (Encodable.encode s))
    (eval_l length_m (Encodable.encode s))) = _
  rw [PrimitiveProgram.id_l, length_encode_l, scan_encode_l, List.take_length]

/-- 任意内部输入按同一个长度图送入扫描，没有标准长度假设。 -/
theorem support_bridge_l (hℳ : Theory.Models ℳ theory_m) {H R L : set_l ℳ}
    (hH : graph_semantics_l (graph_m support_m) H)
    (hR : graph_semantics_l (graph_m scan_m) R)
    (hL : graph_semantics_l (graph_m length_m) L) (x h : num_l ℳ) :
    relation_l H x h ↔ ∃ n, relation_l L x n ∧ relation_l R (value_l x n) h := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ support_input_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  rw [comp_rel_l hℳ (graph_m scan_m) (graph_m support_input_m) R D hR hD hH]
  simp only [pair_rel_l hℳ (graph_m PrimitiveProgram.id_m) (graph_m length_m)
    A L hA hL hD, id_spec_l hℳ hA]
  constructor
  · rintro ⟨p, ⟨a, n, rfl, hn, rfl⟩, hh⟩
    exact ⟨n, hn, hh⟩
  · rintro ⟨n, hn, hh⟩
    exact ⟨value_l x n, ⟨x, n, rfl, hn, rfl⟩, hh⟩

/-- 原长度图给定的全部内部位置上的完整支撑规格。 -/
theorem support_rel_l (hℳ : Theory.Models ℳ theory_m) {H L E : set_l ℳ}
    (hH : graph_semantics_l (graph_m support_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n : num_l ℳ}
    (hn : relation_l L x n) (h : num_l ℳ) :
    relation_l H x h ↔ SecondOrderProgramSupportCorrectness.support_l E x n h := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ scan_m
  rw [support_bridge_l hℳ hH hR hL]
  have hLf := function_of_semantics_l hℳ length_m hL
  constructor
  · rintro ⟨k, hk, hh⟩
    obtain rfl := function_value_unique_l hLf hn hk
    exact (SecondOrderProgramSupportCorrectness.scan_rel_l hℳ hR hE x n h).mp hh
  · intro hh
    exact ⟨n, hn, (SecondOrderProgramSupportCorrectness.scan_rel_l hℳ hR hE x n h).mpr hh⟩

#print axioms support_append_l
#print axioms scan_encode_l
#print axioms support_input_m
#print axioms support_m
#print axioms support_encode_l
#print axioms support_bridge_l
#print axioms support_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSupportHeight
