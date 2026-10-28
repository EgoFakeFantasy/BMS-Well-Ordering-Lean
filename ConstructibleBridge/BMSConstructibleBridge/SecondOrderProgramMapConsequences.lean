import BMSConstructibleBridge.SecondOrderProgramListMapEntries
import BMSConstructibleBridge.SecondOrderProgramListReverseEntries

/-!
# 完整带参映射的内部长度与空码

消费已证的广义折叠长度归纳，接上实际零初值、末值提取和反转。结论针对完整
map_m图的任意内部输入，不要求参数、列表长度或条目外部标准。它不包含逐条目
映射对应；后者仍须独立的下标不变量。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMapConsequences

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListMap
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListFold (fold_m)
open SecondOrderProgramListReverse (reverse_m reverse_step_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 完整map保留任意内部输入列表的长度，辅助图由原程序总性取得。 -/
theorem map_length_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {M L : set_l ℳ}
    (hM : graph_semantics_l (graph_m (map_m c)) M)
    (hL : graph_semantics_l (graph_m length_m) L) (p x y n : num_l ℳ)
    (hm : relation_l M (value_l p x) y) (hn : relation_l L x n) : relation_l L y n := by
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ c
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m (map_step_m c))
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ map_extract_m
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ map_call_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨v, s, hf, he, ht⟩ := (map_graph_rel_l hℳ c hM hF hE hB T hT p x y).mp hm
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl)
  have hinit : relation_l E (value_l p (value_l (zero_l ℳ) (zero_l ℳ))) (zero_l ℳ) :=
    (map_extract_rel_l hℳ hE p _ _ _).mpr rfl
  have hs := SecondOrderProgramListMapEntries.fold_length_l hℳ c hC hF hL hE hI
    x (value_l p (value_l (zero_l ℳ) (zero_l ℳ))) v n (zero_l ℳ) (zero_l ℳ) s
    hf hinit hn h00 he
  rw [add_zero_l hℳ n] at hs
  exact SecondOrderProgramListReverseEntries.reverse_length_l hℳ hT hG hL hI s y n ht hs

/-- 完整map输出空码当且仅当输入为空，与回调的具体值无关。 -/
theorem map_zero_iff_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m (map_m c)) M) (p x y : num_l ℳ)
    (hm : relation_l M (value_l p x) y) : y = zero_l ℳ ↔ x = zero_l ℳ := by
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  have hz (a : num_l ℳ) : relation_l L a (zero_l ℳ) ↔ a = zero_l ℳ :=
    (length_rel_l hℳ hL hI a _).trans (length_zero_l hℳ hI a)
  obtain ⟨n, hn, _⟩ := hLf x
  have hy := map_length_l hℳ c hM hL p x y n hm hn
  constructor
  · intro h
    have hn0 : n = zero_l ℳ := function_value_unique_l hLf hy ((hz y).mpr h)
    exact (hz x).mp (hn0 ▸ hn)
  · intro h
    exact (hz y).mp (map_length_l hℳ c hM hL p x y (zero_l ℳ) hm ((hz x).mpr h))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMapConsequences
