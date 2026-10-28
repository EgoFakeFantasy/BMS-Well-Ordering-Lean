import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramCopyBlockShape
import BMSConstructibleBridge.SecondOrderProgramCopyBlockLookup
import BMSConstructibleBridge.SecondOrderProgramRectangular

/-!
# 整块复制保持内部矩形性

矩形性是同一模型内两条实际图（长度图 `L` 与读取图 `E`）上的性质：块宽为 `n`，
且每个有效下标处的列都是高 `h` 的码。本模块证明原 `copy_m` 图的任意内部输出
保持该性质：宽度由已验形状层搬运，逐列高度由已验读取层把输出列读回原列映射、
再消费列映射的长度保持。

列图、参数图、共享参数码与源列见证全部在证明内部由程序总性与实际图函数性取得，
公开签名只带结论中出现的三张图。全程在任意 `ℳ ⊨ theory_m` 上陈述，宽、高、下标
与参数码均可是非标准元素；无新公式、无归纳、不要求外部矩形前提之外的任何标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyRectangular

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListMap
open SecondOrderProgramCopyBlock (column_m parameter_m copy_m)
open SecondOrderProgramCopyBlockShape (copy_width_l column_length_l)
open SecondOrderProgramCopyBlockLookup (copy_column_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramRectangular (rectangular_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 整块复制保持内部矩形性：宽度经 `copy_width_l` 搬运；每个有效下标处，读取图
函数性给出源列见证，`copy_column_l` 把输出列的读证据转成原列映射关系，再由
`column_length_l` 从该列的矩形高度得到同一高度。 -/
theorem copy_rectangular_l (hℳ : Theory.Models ℳ theory_m) {C L E : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {b t y n h : num_l ℳ}
    (hx : rectangular_l L E b n h)
    (hy : relation_l C (value_l b t) y) :
    rectangular_l L E y n h := by
  refine ⟨copy_width_l hℳ hC hL hy hx.1, ?_⟩
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ column_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parameter_m
  obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ parameter_m hP (value_l b t)
  intro j hj s hs
  obtain ⟨s', hs', _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l b j)
  have hc := (copy_column_l hℳ hC hK hP hL hE hy hq hx.1 hj hs').mp hs
  exact column_length_l hℳ hK hL hc (hx.2 j hj s' hs')

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyRectangular
