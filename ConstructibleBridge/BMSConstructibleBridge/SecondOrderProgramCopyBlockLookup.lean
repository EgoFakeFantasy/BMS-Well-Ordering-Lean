import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramMapLookup

/-!
# `copy_m` 两层的逐内部下标读取规格

已验形状层只给出长度保持；本层把两层映射读到具体一位：

- `column_entry_l`：一列映射的第 `i` 位等于该位源码条目经原 `entry_m` 回调图的输出；
- `copy_column_l`：整块复制的第 `j` 位等于共享参数列下同一位置的列映射输出。

两条都在任意 `ℳ ⊨ theory_m` 上陈述，参数、块、下标与长度均可是非标准元素，
界只由 `SecondOrderOrder.lt_l` 的内部正差见证给出；不要求矩形性或外部标准性。
公开签名给定实际回调图与原参数码、源条目见证，供后续逐列组合直接消费；
证明只把实际图经已验接线识别为对应 `map_m` 图再套映射读取规格，无新公式与归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyBlockLookup

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListMap
open SecondOrderProgramCopyEntry (entry_m)
open SecondOrderProgramCopyBlock (column_m parameter_m copy_m column_rel_l copy_rel_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramMapLookup (map_lookup_entry_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 一列原条目映射的逐内部下标读取：`column_m` 图经 `column_rel_l` 识别为
`map_m entry_m` 图后套映射读取规格，回调输入 `pair (pair q j) (pair i e)` 保持原参数列。 -/
theorem column_entry_l (hℳ : Theory.Models ℳ theory_m) {C A L E : set_l ℳ}
    (hC : graph_semantics_l (graph_m column_m) C)
    (hA : graph_semantics_l (graph_m entry_m) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {q j s y n i e w : num_l ℳ}
    (hc : relation_l C (value_l q (value_l j s)) y)
    (hn : relation_l L s n)
    (hi : SecondOrderOrder.lt_l i n)
    (he : relation_l E (value_l s i) e) :
    relation_l E (value_l y i) w ↔
      relation_l A (value_l (value_l q j) (value_l i e)) w := by
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m entry_m)
  have hm := (column_rel_l hℳ hC hM q j s y).mp hc
  exact map_lookup_entry_l hℳ entry_m hM hA hL hE (value_l q j) s y n i e w hm hn hi he

/-- 整块复制逐内部下标读回所在列的映射输出：`copy_rel_l` 拆出的实际参数码由
参数图函数性与给定 `hq` 统一，不假设块矩形；给定源条目见证直接消去存在量词。 -/
theorem copy_column_l (hℳ : Theory.Models ℳ theory_m) {C K P L E : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hK : graph_semantics_l (graph_m column_m) K)
    (hP : graph_semantics_l (graph_m parameter_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {b t y q j n s w : num_l ℳ}
    (hc : relation_l C (value_l b t) y)
    (hq : relation_l P (value_l b t) q)
    (hn : relation_l L b n)
    (hj : SecondOrderOrder.lt_l j n)
    (hs : relation_l E (value_l b j) s) :
    relation_l E (value_l y j) w ↔ relation_l K (value_l q (value_l j s)) w := by
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m column_m)
  obtain ⟨q', hpq', hqm⟩ := (copy_rel_l hℳ hC hM hP b t y).mp hc
  have hqq : q' = q :=
    function_value_unique_l (function_of_semantics_l hℳ parameter_m hP) hpq' hq
  rw [hqq] at hqm
  exact map_lookup_entry_l hℳ column_m hM hK hL hE q b y n j s w hqm hn hj hs

#print axioms column_entry_l
#print axioms copy_column_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyBlockLookup
