import BMSConstructibleBridge.SecondOrderProgramExpansion
import BMSConstructibleBridge.SecondOrderProgramExpansionRectangular
import BMSConstructibleBridge.SecondOrderProgramRectangularHeight
import BMSConstructibleBridge.SecondOrderProgramRectangular
import BMSConstructibleBridge.SecondOrderProgramTrimHeight
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.PrimitiveFormulas

/-!
# 裁剪高度沿真实展开步的非增性（阶段 B 秩的第一分量单调性）

阶段 B1 选定 route 3（外部 `n` 编译出的有限多层自然数秩）。其第一分量取模型内部裁剪高度图
`SecondOrderProgramTrimHeight.trim_m`：规范化反例 `SecondOrderNormalizedCounterexample.arrays_l`
对下降链每个数组 `u` 给出 `relation_l H u (numeral k)` 且 `k ≤ n`，故该分量是**内部、按外部 `n`
有界的自然数码**，正是秩主坐标所需。本模块证明它沿真实 `expand_m` 一步**非增**：

  `x` 以 `hx` 为支撑高矩形、`expand x k = y`、`H y = hy` ⟹ `hy ≤ hx`。

证明只用两张官方图搬运：`expand_rectangular_l` 把 `x` 的支撑高 `hx` 传到 `y` 的某支撑高 `g` 并给
`g ≤ hx`；`trim_le_l` 由 `y` 的矩形性与高度图 `H y = hy` 得 `hy ≤ g`；内部 `≤` 传递闭合。全程用
`order_l` 的实例序，不引宿主 `Nat` 归纳、不要求数域外部标准性或数组矩形性之外的任何假设，
列号、宽度、高度与展开指标均取任意内部非标准元素。

本模块只给**非增**——严格下降的次坐标（等高时的词典下降）是 B2/C 的核心未决块，须消费阶段 A
的父列平移 `reloc_ge_rows_l` / `ancestor_exit_sync_l`，不在此处声张。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRankHeight

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionRectangular (expand_rectangular_l)
open SecondOrderProgramRectangularHeight (trim_le_l)
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramTrimHeight (trim_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 真实展开不抬高裁剪高度图的值：`x` 以其高度图值 `hx` 为支撑高呈矩形，`expand x k = y`，
`y` 的高度图值为 `hy`，则内部序下 `hy ≤ hx`。宽度、列号、行号与两个高度都可为任意内部元素。 -/
theorem expand_height_noninc_l (hℳ : Theory.Models ℳ theory_m)
    {X H L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hH : graph_semantics_l (graph_m trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {x y w hx hy k : num_l ℳ}
    (hxrect : rectangular_l L E x w hx)
    (hyH : relation_l H y hy) (hexp : relation_l X (value_l x k) y) :
    letI := order_l hℳ
    hy ≤ hx := by
  letI := order_l hℳ
  obtain ⟨m, g, hyrect, hge⟩ := expand_rectangular_l hℳ hX hL hE hxrect hexp
  exact le_trans (trim_le_l hℳ hH hL hE hyrect hyH) hge

#print axioms expand_height_noninc_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRankHeight
