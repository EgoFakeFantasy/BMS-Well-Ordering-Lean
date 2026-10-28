import BMSConstructibleBridge.SecondOrderProgramCopies
import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramCopyBlockShape
import BMSConstructibleBridge.SecondOrderProgramCopiesShape
import BMSConstructibleBridge.SecondOrderProgramListAppend

/-!
# 末尾非零副本在原多副本输出中的列定位

首副本（乘子任意、局部列在原块宽内）已由 `SecondOrderProgramCopiesFirst` 处理。
本模块闭合阶段 A1 的最小一环：复制次数为 `succ s` 时，最后追加的那一块
（同一 `copy_m` 图以乘子 `s` 作用于原块）在总输出的平坦列 `w·s + r` 处，
读值与直接读该块的第 `r` 列完全一致。

次数 `s`、块宽 `w`、局部列 `r`、参数码与原块都可取任意内部非标准元素；
定位只消费原 `copies_m` 的后继展开 `copies_succ_l`、真实宽度保持
`copies_width_l` / `copy_width_l` 与真实拼接右段读取 `append_right_l`，
不使用宿主 `Nat` 归纳，也不要求矩形性或外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlock

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramCopies (copies_m copies_succ_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramCopiesShape (copies_width_l)
open SecondOrderProgramCopyBlockShape (copy_width_l)
open SecondOrderProgramListAppend (append_m append_right_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- `succ s` 次复制的输出末尾块为 `blk` 时，总输出平坦列 `w·s + r`（`r < w`）
的读值等价于直接读 `blk` 的第 `r` 列。所有数均可内部非标准。 -/
theorem block_read_last_l (hℳ : Theory.Models ℳ theory_m) {R C L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {b w A l s blk y r : num_l ℳ} (hb : relation_l L b w)
    (hblk : relation_l C (value_l b (value_l A (value_l s l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) (succ_l s)) y)
    (hr : SecondOrderOrder.lt_l r w) (a : num_l ℳ) :
    relation_l E (value_l y (add_l (mul_l w s) r)) a ↔ relation_l E (value_l blk r) a := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ append_m
  obtain ⟨acc, blkc, hacc, hblkc, hpy⟩ := (copies_succ_l hℳ hR hC hP b A l s y).mp hy
  have hbb : blk = blkc :=
    function_value_unique_l (function_of_semantics_l hℳ copy_m hC) hblk hblkc
  rw [hbb]
  exact append_right_l hℳ hP hL hE (copies_width_l hℳ hR hL hb hacc)
    (copy_width_l hℳ hC hL hblkc hb) hpy hr a

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlock
