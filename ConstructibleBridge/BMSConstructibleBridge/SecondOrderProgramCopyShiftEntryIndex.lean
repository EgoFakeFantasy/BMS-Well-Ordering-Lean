import BMSConstructibleBridge.SecondOrderProgramCopies
import BMSConstructibleBridge.SecondOrderProgramCopiesBlockIndex
import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramCopyOptional
import BMSConstructibleBridge.SecondOrderProgramCopyShiftEntry
import BMSConstructibleBridge.SecondOrderProgramListCode
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderProgramAscending
import BMSConstructibleBridge.SecondOrderProgramOptionalLookup
import BMSConstructibleBridge.SecondOrderProgramLength

/-!
# 任意内部副本下标的逐内部行值公式（阶段 A2 一般化）

`SecondOrderProgramCopyShiftEntry` 只在末尾第 `succ k` 份副本上闭合了值分支公式，
因为它消费的 `block_read_last_l` 只能定位末尾块。本模块改用
`SecondOrderProgramCopiesBlockIndex.block_read_index_l`，把同一公式搬到任意内部下标
`k < count` 的副本上：总输出平坦列 `w·k + j` 与原块第 `j` 列读出同一个列码，
于是列内逐行的四分支公式（上升测试输出零则不变、首末列缺项则不变、
两项都在则精确加次数乘截断差值）在一般下标下逐字保持。

下标 `k`、总次数 `count`、块宽 `w`、列 `j`、行 `r`、源块列码与长度都可取任意内部
非标准元素；界只由 `SecondOrderOrder.lt_l` 的内部正差见证给出，不使用宿主 `Nat` 归纳，
不要求矩形性、生成性或外部标准性。块级的不变／平移引理本身不含副本下标，
故经此列定位即可直接复用，无需重复。父／祖先重定位属阶段 A3、A4，不在本模块。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyShiftEntryIndex

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramValue
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramCopies (copies_m)
open SecondOrderProgramCopiesBlockIndex (block_read_index_l)
open SecondOrderProgramCopyShiftEntry (copy_entry_value_l)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 完整分支公式对 `copies_m` 的任意内部副本成立：满足 `k < count` 的第 `k` 份副本，
其块列在总输出平坦列 `w·k + j` 处，逐行读值与原块同位置的分支公式完全一致。 -/
theorem copies_entry_value_index_l (hℳ : Theory.Models ℳ theory_m)
    {R C H L E B O U : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    {b A k l blk f : num_l ℳ} (hf : relation_l H b f)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    {w j s n r v out colj count e : num_l ℳ} (hw : relation_l L b w)
    (hk : SecondOrderOrder.lt_l k count)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) out)
    (hj : SecondOrderOrder.lt_l j w) (hs : relation_l E (value_l b j) s)
    (hn : relation_l L s n) (hr : SecondOrderOrder.lt_l r n)
    (hv : relation_l E (value_l s r) v)
    (hcol : relation_l E (value_l out (add_l (mul_l w k) j)) colj) :
    relation_l E (value_l colj r) e ↔
      (relation_l B (value_l A (value_l j r)) (zero_l ℳ) ∧ v = e) ∨
        (¬relation_l B (value_l A (value_l j r)) (zero_l ℳ) ∧ ∃ first last,
          relation_l O (value_l f r) first ∧ relation_l O (value_l l r) last ∧
            relation_l U (value_l v (value_l k (value_l first last))) e) :=
  copy_entry_value_l hℳ hC hH hL hE hB hO hU hf hblk hw hj hs hn hr hv colj e
    ((block_read_index_l hℳ hR hC hL hE hw hk hblk hy hj colj).mp hcol)

#print axioms copies_entry_value_index_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyShiftEntryIndex
