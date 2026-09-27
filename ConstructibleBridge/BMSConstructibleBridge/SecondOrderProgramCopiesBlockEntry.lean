import BMSConstructibleBridge.SecondOrderProgramCopies
import BMSConstructibleBridge.SecondOrderProgramCopiesBlockIndex
import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramCopyBlockShape
import BMSConstructibleBridge.SecondOrderProgramCopiesShape
import BMSConstructibleBridge.SecondOrderProgramEntry
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramOptionalLookup

/-!
# 副本平坦列与原块同局部列的条目一致（阶段 A3 的条目半边）

阶段 A1 把总输出的平坦列 `w·k + j` 定位到第 `k` 份副本的块 `blk` 的第 `j` 列，
阶段 A2 给出该列逐行的值分支公式。父查询 `parent_m` 的实际规格
（`SecondOrderProgramUniformParentSpecification.parent_succ_some_l` /
`parent_succ_none_l`）把父输出完全归约为 `eligible_l`，而 `eligible_l` 由三部分组成：
上一行的祖先成员、本行两个条目坐标的存在与严格比较、以及候选的最大性。
本模块处理其中**只依赖条目读取**的半边，祖先成员与最大性属后续出口。

关键是先把 `optional_m` 与 `entry_m` 两级读取搬到同一列上：两侧数组宽度分别由
`copies_width_l` 与 `copy_width_l` 给出，平坦下标 `w·k + j < w·count` 由内部正差见证
`k < count`、`j < w` 经乘法单调性得到，于是界外零分支同时被排除，界内的列码见证
由 A1 的 `block_read_index_l` 逐值双向搬运。因此本模块**不需要矩形性、生成性、
外部标准性或任何"父列只平移 `s·d`"式假设**；全部下标、宽度、次数、行号与列码
都可取任意内部非标准元素。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlockEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramCopies (copies_m)
open SecondOrderProgramCopiesBlockIndex (block_read_index_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramCopiesShape (copies_width_l)
open SecondOrderProgramCopyBlockShape (copy_width_l)
open SecondOrderProgramEntry (entry_m entry_rel_l)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramOptionalLookup (optional_m optional_rel_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 第 `k` 份副本的局部列 `j < w` 映到总输出时，平坦下标 `w·k + j` 严格落在总宽度
`w·count` 内。两处界都是内部正差见证，不用外部归纳。 -/
theorem flat_index_lt_l (hℳ : Theory.Models ℳ theory_m) {w k j count : num_l ℳ}
    (hk : SecondOrderOrder.lt_l k count) (hj : SecondOrderOrder.lt_l j w) :
    SecondOrderOrder.lt_l (add_l (mul_l w k) j) (mul_l w count) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨d, hd⟩ := hk
  obtain ⟨e, he⟩ := hj
  have hlt : add_l (mul_l w k) j < mul_l w (succ_l k) := ⟨e,
    calc add_l (add_l (mul_l w k) j) (succ_l e)
        = add_l (mul_l w k) (add_l j (succ_l e)) := SecondOrderNumbers.add_assoc_l hℳ _ _ _
      _ = add_l (mul_l w k) w := congrArg (add_l (mul_l w k)) he
      _ = mul_l w (succ_l k) := (mul_succ_l hℳ w k).symm⟩
  have hle : succ_l k ≤ count := (le_iff_l hℳ _ _).mpr
    ⟨d, (SecondOrderNumbers.succ_add_l hℳ k d).trans
      ((add_succ_l hℳ k d).symm.trans hd)⟩
  exact lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_left hle (zero_le_l hℳ w))

/-- 副本平坦列与原块同局部列的可选列读取完全一致：界外零分支在两侧同时被排除，
界内列码由 A1 的块定位逐值搬运。 -/
theorem block_column_agree_l (hℳ : Theory.Models ℳ theory_m) {R C O L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {b w : num_l ℳ} (hb : relation_l L b w)
    {A l k blk count out j : num_l ℳ} (hk : SecondOrderOrder.lt_l k count)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) out)
    (hj : SecondOrderOrder.lt_l j w) (z : num_l ℳ) :
    relation_l O (value_l out (add_l (mul_l w k) j)) z ↔ relation_l O (value_l blk j) z := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hflt : add_l (mul_l w k) j < mul_l w count := flat_index_lt_l hℳ hk hj
  have hwc : relation_l L out (mul_l w count) := copies_width_l hℳ hR hL hb hy
  have hwb : relation_l L blk w := copy_width_l hℳ hC hL hblk hb
  rw [optional_rel_l hℳ hO hL hE hwc (add_l (mul_l w k) j) z,
    optional_rel_l hℳ hO hL hE hwb j z]
  constructor
  · rintro (⟨hle, _⟩ | ⟨_, a, ha, hz⟩)
    · exact absurd hflt (not_lt_of_ge hle)
    · exact Or.inr ⟨hj, a, (block_read_index_l hℳ hR hC hL hE hb hk hblk hy hj a).mp ha, hz⟩
  · rintro (⟨hle, _⟩ | ⟨_, a, ha, hz⟩)
    · exact absurd hj (not_lt_of_ge hle)
    · exact Or.inr ⟨hflt, a, (block_read_index_l hℳ hR hC hL hE hb hk hblk hy hj a).mpr ha, hz⟩

/-- 原条目图在副本平坦列与原块同局部列上逐内部行一致：两侧都按 `optional_m` 分解后
用上一条目搬运，条目自身的行读取因为列码相同而逐字相同。 -/
theorem block_entry_agree_l (hℳ : Theory.Models ℳ theory_m) {R C O L E J : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {b w : num_l ℳ} (hb : relation_l L b w)
    {A l k blk count out j r e : num_l ℳ} (hk : SecondOrderOrder.lt_l k count)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) out)
    (hj : SecondOrderOrder.lt_l j w) :
    relation_l J (value_l out (value_l (add_l (mul_l w k) j) r)) e ↔
      relation_l J (value_l blk (value_l j r)) e := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases (entry_rel_l hℳ hJ hO out (add_l (mul_l w k) j) r e).mp h with ⟨hz, he⟩ | ⟨c, hz, hc⟩
    · exact (entry_rel_l hℳ hJ hO blk j r e).mpr
        (Or.inl ⟨(block_column_agree_l hℳ hR hC hO hL hE hb hk hblk hy hj (zero_l ℳ)).mp hz, he⟩)
    · exact (entry_rel_l hℳ hJ hO blk j r e).mpr (Or.inr ⟨c,
        (block_column_agree_l hℳ hR hC hO hL hE hb hk hblk hy hj (succ_l c)).mp hz, hc⟩)
  · rcases (entry_rel_l hℳ hJ hO blk j r e).mp h with ⟨hz, he⟩ | ⟨c, hz, hc⟩
    · exact (entry_rel_l hℳ hJ hO out (add_l (mul_l w k) j) r e).mpr
        (Or.inl ⟨(block_column_agree_l hℳ hR hC hO hL hE hb hk hblk hy hj (zero_l ℳ)).mpr hz, he⟩)
    · exact (entry_rel_l hℳ hJ hO out (add_l (mul_l w k) j) r e).mpr (Or.inr ⟨c,
        (block_column_agree_l hℳ hR hC hO hL hE hb hk hblk hy hj (succ_l c)).mpr hz, hc⟩)

/-- `eligible_l` 的条目比较半边在第 `k` 份副本的两个局部列之间逐内部行一致：
两侧候选坐标同时存在且严格序相同。祖先成员半边与最大性半边不在此处。 -/
theorem block_compare_agree_l (hℳ : Theory.Models ℳ theory_m) {R C O L E J : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {b w : num_l ℳ} (hb : relation_l L b w)
    {A l k blk count out i j : num_l ℳ} (hk : SecondOrderOrder.lt_l k count)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) out)
    (hi : SecondOrderOrder.lt_l i w) (hj : SecondOrderOrder.lt_l j w) (r : num_l ℳ) :
    (∃ a b, relation_l J (value_l out (value_l (add_l (mul_l w k) i) (succ_l r))) (succ_l a) ∧
      relation_l J (value_l out (value_l (add_l (mul_l w k) j) (succ_l r))) (succ_l b) ∧
      SecondOrderOrder.lt_l a b) ↔
    (∃ a b, relation_l J (value_l blk (value_l i (succ_l r))) (succ_l a) ∧
      relation_l J (value_l blk (value_l j (succ_l r))) (succ_l b) ∧
      SecondOrderOrder.lt_l a b) := by
  constructor
  · rintro ⟨a, b, h1, h2, hab⟩
    refine ⟨a, b, (block_entry_agree_l hℳ hR hC hO hL hE hJ hb hk hblk hy hi).mp h1,
      (block_entry_agree_l hℳ hR hC hO hL hE hJ hb hk hblk hy hj).mp h2, hab⟩
  · rintro ⟨a, b, h1, h2, hab⟩
    refine ⟨a, b, (block_entry_agree_l hℳ hR hC hO hL hE hJ hb hk hblk hy hi).mpr h1,
      (block_entry_agree_l hℳ hR hC hO hL hE hJ hb hk hblk hy hj).mpr h2, hab⟩

#print axioms flat_index_lt_l
#print axioms block_column_agree_l
#print axioms block_entry_agree_l
#print axioms block_compare_agree_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlockEntry
