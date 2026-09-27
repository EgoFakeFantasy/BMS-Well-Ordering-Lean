import BMSConstructibleBridge.SecondOrderProgramParentZero
import BMSConstructibleBridge.SecondOrderProgramUniformParent
import BMSConstructibleBridge.SecondOrderProgramUniformParentLookup
import BMSConstructibleBridge.SecondOrderProgramCopies
import BMSConstructibleBridge.SecondOrderProgramCopiesShape
import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramCopyBlockShape
import BMSConstructibleBridge.SecondOrderProgramCopiesBlockEntry
import BMSConstructibleBridge.SecondOrderProgramEntry
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderProgramOptionalLookup
import BMSConstructibleBridge.SecondOrderProgramParentRelocation
import BMSConstructibleBridge.PrimitiveFormulas

/-!
# 副本段父平移的零行基例（弱化不变式的基）

`SecondOrderProgramCopiesBlockParentShift` 已说明强平移对应（含 `none ↔ none`）在第 `k ≥ 1`
份副本一般为假：`parent_zero_some_l` 的最大化搜索域是**全部** `i < t`，不限于本副本段，
故块内某列父为 `none` 时，更早副本列仍可能合格并把平坦父拉到 `< K`。
真正可作按行归纳不变式的是弱化形式：**平坦父只要落在本副本段 `[K, K+w)` 内，
就逐字等于局部块父平移 `K`**。本模块建立它的零行基例。

两支都不需要「更早候选不合格」这一额外假设：
* 正向由平坦最大性直接限制在区间 `(K+p, K+j)`，其中的候选必然形如 `K+q`（父列不小于 `K`），
  逐值搬回块内即得局部的最大性；
* 反向由 `p` 在块内最大给出 `K+p`，而一切更早副本候选都 `< K ≤ K+p`，被 `K+p` 自身支配。

全程只用 `entry_m` 在第零行的逐列一致 `block_entry_agree_l` 与内部数序，列号、次数、块宽、
偏移 `K = mul w k` 均可取任意内部非标准元素，不使用宿主 `Nat` 归纳，也不要求矩形性或外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlockParentZero

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramCopies (copies_m)
open SecondOrderProgramCopiesShape (copies_width_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramCopyBlockShape (copy_width_l)
open SecondOrderProgramCopiesBlockEntry (flat_index_lt_l block_entry_agree_l)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramParentZero (parent_zero_m parent_zero_some_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramUniformParentLookup (parent_zero_l)
open SecondOrderProgramParentRelocation (lt_add_left_l lt_of_add_lt_add_left_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 第零行候选合格性在第 `k` 份副本的段内列与原块同局部列之间逐值一致：两侧都只读取
`entry_m` 在第零行的坐标，`block_entry_agree_l` 的行参数可取 `zero`，故不需要任何后继行形状。 -/
theorem zero_eligible_agree_l (hℳ : Theory.Models ℳ theory_m)
    {R C O L E J : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {b w : num_l ℳ} (hb : relation_l L b w)
    {A l k blk count out i t : num_l ℳ} (hk : SecondOrderOrder.lt_l k count)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) out)
    (hi : SecondOrderOrder.lt_l i w) (ht : SecondOrderOrder.lt_l t w) :
    SecondOrderProgramParentZero.eligible_l J out (add_l (mul_l w k) t) (add_l (mul_l w k) i) ↔
      SecondOrderProgramParentZero.eligible_l J blk t i := by
  refine ⟨fun ⟨x, y, hx, ht₂, hxy⟩ => ⟨x, y, ?_, ?_, hxy⟩,
    fun ⟨x, y, hx, ht₂, hxy⟩ => ⟨x, y, ?_, ?_, hxy⟩⟩
  · exact (block_entry_agree_l hℳ hR hC hO hL hE hJ hb hk hblk hy hi).mp hx
  · exact (block_entry_agree_l hℳ hR hC hO hL hE hJ hb hk hblk hy ht).mp ht₂
  · exact (block_entry_agree_l hℳ hR hC hO hL hE hJ hb hk hblk hy hi).mpr hx
  · exact (block_entry_agree_l hℳ hR hC hO hL hE hJ hb hk hblk hy ht).mpr ht₂

/-- 弱化段内平移的零行基例：第 `k` 份副本块 `blk`（由 `copy_m` 产生）嵌入总输出 `out`
（由 `copies_m` 产生）时，两者在第零行的父输出在段 `[K, K+w)` 上逐值一致，
即 `parent(out, 0, K+j) = succ (K+p)` 当且仅当 `parent(blk, 0, j) = succ p`。
`j < w` 是唯一的列界；不需要「更早副本候选不合格」假设。 -/
theorem reloc_ge_zero_l (hℳ : Theory.Models ℳ theory_m)
    {R C O L E J P P0 : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hP0 : graph_semantics_l (graph_m parent_zero_m) P0)
    {b w : num_l ℳ} (hb : relation_l L b w)
    {A l k blk count out j p : num_l ℳ} (hk : SecondOrderOrder.lt_l k count)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) out)
    (hj : SecondOrderOrder.lt_l j w) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    relation_l P (value_l (value_l out (zero_l ℳ)) (add_l (mul_l w k) j))
        (succ_l (add_l (mul_l w k) p)) ↔
      relation_l P (value_l (value_l blk (zero_l ℳ)) j) (succ_l p) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hwc : relation_l L out (mul_l w count) := copies_width_l hℳ hR hL hb hy
  have hwb : relation_l L blk w := copy_width_l hℳ hC hL hblk hb
  have hflt : add_l (mul_l w k) j < mul_l w count := flat_index_lt_l hℳ hk hj
  have hel (i t : num_l ℳ) (hi : SecondOrderOrder.lt_l i w) (ht : SecondOrderOrder.lt_l t w) :
      SecondOrderProgramParentZero.eligible_l J out (add_l (mul_l w k) t) (add_l (mul_l w k) i) ↔
        SecondOrderProgramParentZero.eligible_l J blk t i :=
    zero_eligible_agree_l hℳ hR hC hO hL hE hJ hb hk hblk hy hi ht
  rw [parent_zero_l hℳ hP hP0 hL out (mul_l w count) (add_l (mul_l w k) j)
      (succ_l (add_l (mul_l w k) p)) hwc hflt,
    parent_zero_l hℳ hP hP0 hL blk w j (succ_l p) hwb hj,
    parent_zero_some_l hℳ hP0 hL hJ hwc (add_l (mul_l w k) j) (add_l (mul_l w k) p),
    parent_zero_some_l hℳ hP0 hL hJ hwb j p]
  constructor
  · rintro ⟨_, hKpj, ho, hmax⟩
    have hjw : j < w := hj
    have hpj : p < j := lt_of_add_lt_add_left_l hℳ hKpj
    refine ⟨hj, hpj, (hel p j (lt_trans hpj hjw) hj).mp ho, ?_⟩
    intro q' hpq hqj
    have h1 : p < q' := hpq
    have h2 : q' < j := hqj
    refine (hel q' j (lt_trans h2 hjw) hj).not.mp
      (hmax (add_l (mul_l w k) q') (lt_add_left_l hℳ h1) (lt_add_left_l hℳ h2))
  · rintro ⟨_, hpj, hb, hmax⟩
    have hjw : j < w := hj
    have hpj' : p < j := hpj
    have hpw : SecondOrderOrder.lt_l p w := lt_trans hpj' hjw
    refine ⟨hflt, lt_add_left_l hℳ hpj', (hel p j hpw hj).mpr hb, ?_⟩
    intro j' hKpj' hj'K
    have hKle : mul_l w k ≤ add_l (mul_l w k) p := (le_iff_l hℳ _ _).mpr ⟨p, rfl⟩
    obtain ⟨q', hq⟩ :=
      (le_iff_l hℳ (mul_l w k) j').mp (le_of_lt (lt_of_le_of_lt hKle hKpj'))
    subst hq
    have hpq : p < q' := lt_of_add_lt_add_left_l hℳ hKpj'
    have hqj : q' < j := lt_of_add_lt_add_left_l hℳ hj'K
    have hqw : SecondOrderOrder.lt_l q' w := lt_trans hqj hjw
    intro h
    exact (hmax _ hpq hqj) ((hel q' j hqw hj).mp h)

#print axioms zero_eligible_agree_l
#print axioms reloc_ge_zero_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlockParentZero
