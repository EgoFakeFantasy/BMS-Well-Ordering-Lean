import BMSConstructibleBridge.SecondOrderProgramListAll
import BMSConstructibleBridge.SecondOrderProgramMapLookup

/-!
# `map_m c` 对内部集合性质的逐位保持

回调程序 `c` 把内部列表码逐项映射成 `y` 时，输出每个有效位的值都来自某个源码项经
实际回调图的像。于是只要源码各有效位的回调值都落在同一模型内部集合 `S` 中，映射
输出也满足 `all_l E S y n`：输出位经 `map_lookup_lt_l` 拆成源码位与回调见证后直接
代入收集假设。`S` 必须是内部集合而非宿主任意谓词；下标、长度与各项码全程可非标准，
越界补零不参与任何一侧的陈述。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListMapAll

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramMapLookup (map_lookup_lt_l)
open SecondOrderProgramListMap (map_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListAll (all_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 逐位收集保持：源码有效位的每个回调值都属于内部集合 `S` 时，映射输出在同一个
读取图与同一长度下也满足 `all_l`。内部任取界内输出位 `j` 与输出值 `a`，
`map_lookup_lt_l` 的左到右方向给出源码项 `e` 与实际回调见证，收集假设直接闭合。
不假设长度标准，也不经任何外部谓词。 -/
theorem map_all_l (hℳ : Theory.Models ℳ theory_m) (c : code_m)
    {M C L E S : set_l ℳ}
    (hM : graph_semantics_l (graph_m (map_m c)) M)
    (hC : graph_semantics_l (graph_m c) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (p x y n : num_l ℳ) (hm : relation_l M (value_l p x) y)
    (hn : relation_l L x n)
    (hcallback : ∀ j e w : num_l ℳ, SecondOrderOrder.lt_l j n →
      relation_l E (value_l x j) e → relation_l C (value_l p (value_l j e)) w →
        mem_l w S) :
    all_l E S y n := by
  intro j hj a ha
  obtain ⟨e, hxe, hCw⟩ := (map_lookup_lt_l hℳ c hM hC hL hE p x y n j a hm hn hj).mp ha
  exact hcallback j e a hj hxe hCw

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），无新增公理，
亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

#print axioms map_all_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListMapAll
