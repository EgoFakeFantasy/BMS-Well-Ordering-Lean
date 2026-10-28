import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramMapConsequences

/-!
# `copy_m` 两层实际映射保持内部长度

`copy_m = map_m column_m ∘ copy_input_m` 与 `column_m = map_m entry_m ∘ column_input_m`
都是带参映射程序，其外层遍历不改变被遍历列表的长度。本模块只在任意 `ℳ ⊨ theory_m`
上给出这两层的形状保持：

- `column_length_l`：一列映射把输入码 `s` 的内部长度原样带到输出 `y`；
- `copy_width_l`：整块复制把输入块 `b` 的内部长度原样带到输出块 `y`，即宽度不变。

两条结论都先把实际图经接线定理识别为对应的 `map_m` 图，再消费映射的通用长度定理；
内层映射图与参数图由程序总性在证明内部取得，不外露给调用者。长度、下标与参数码
都可以是非标准元素，不要求任何外部标准性或原参数块的矩形性。逐条目复制内容
不在此模块，这里只证形状。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyBlockShape

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListMap
open SecondOrderProgramCopyEntry (entry_m)
open SecondOrderProgramCopyBlock (column_m parameter_m copy_m column_rel_l copy_rel_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramMapConsequences (map_length_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 一整列的原条目映射保持输入码的任意内部长度：`column_m` 图经 `column_rel_l`
识别为 `map_m entry_m` 图，其参数槽 `value_l q j` 不外露。 -/
theorem column_length_l (hℳ : Theory.Models ℳ theory_m) {C L : set_l ℳ}
    (hC : graph_semantics_l (graph_m column_m) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    {q j s y n : num_l ℳ}
    (hc : relation_l C (value_l q (value_l j s)) y)
    (hn : relation_l L s n) : relation_l L y n := by
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m entry_m)
  have hm := (column_rel_l hℳ hC hM q j s y).mp hc
  exact map_length_l hℳ entry_m hM hL (value_l q j) s y n hm hn

/-- 整块复制保持输入块的任意内部长度（宽度不变）：`copy_m` 图经 `copy_rel_l` 拆出
实际参数图上的共享参数码 `q` 与外层 `map_m column_m` 关系后套通用长度定理。 -/
theorem copy_width_l (hℳ : Theory.Models ℳ theory_m) {C L : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    {b t y n : num_l ℳ}
    (hc : relation_l C (value_l b t) y)
    (hn : relation_l L b n) : relation_l L y n := by
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m column_m)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parameter_m
  obtain ⟨q, _, hqm⟩ := (copy_rel_l hℳ hC hM hP b t y).mp hc
  exact map_length_l hℳ column_m hM hL q b y n hqm hn

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyBlockShape
