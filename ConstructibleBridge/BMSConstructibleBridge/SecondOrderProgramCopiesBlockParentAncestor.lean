import BMSConstructibleBridge.SecondOrderProgramCopies
import BMSConstructibleBridge.SecondOrderProgramCopiesShape
import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramCopyBlockShape
import BMSConstructibleBridge.SecondOrderProgramCopiesBlockEntry
import BMSConstructibleBridge.SecondOrderProgramCopiesBlockParentZero
import BMSConstructibleBridge.SecondOrderProgramCopiesBlockParentShift
import BMSConstructibleBridge.SecondOrderProgramParentRelocationAncestorExit
import BMSConstructibleBridge.SecondOrderProgramEntry
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderProgramOptionalLookup
import BMSConstructibleBridge.SecondOrderProgramUniformParent
import BMSConstructibleBridge.SecondOrderProgramUniformParentLookup
import BMSConstructibleBridge.SecondOrderProgramUniformParentState
import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification
import BMSConstructibleBridge.SecondOrderProgramParentZero
import BMSConstructibleBridge.SecondOrderProgramAncestorStep
import BMSConstructibleBridge.SecondOrderProgramAncestorChain
import BMSConstructibleBridge.SecondOrderProgramAncestorMembership
import BMSConstructibleBridge.SecondOrderProgramListReverse
import BMSConstructibleBridge.SecondOrderProgramIteration

/-!
# 副本段弱化平移的按行归纳闭合（阶段 A5 终局）

`SecondOrderProgramCopiesBlockParentShift.reloc_ge_m` 给出可行不变式的正确形状：第 `r` 行上，
副本段列 `K + t`（`K = mul w k`、`t < w`）的平坦父若落在本段内，就逐字等于原块列 `t` 的父平移
`K`。本模块把它的两支接起来：

* 零行基例已由 `SecondOrderProgramCopiesBlockParentZero.reloc_ge_zero_l` 完成；
* 后继步需要 `parent_some_congr_l` 的候选合格性前提 `hagree`。`hagree` 的坐标比较半边来自
  `block_compare_agree_l`；祖先成员半边 `¬ M` 无法由任何逐列对齐假设得到（强 `none↔none`
  对第 `k ≥ 1` 份副本为假），只能由 `SecondOrderProgramParentRelocationAncestorExit.
  ancestor_exit_sync_l` 的出段同步给出——它只消费弱化对应与父列严格下降。

父列严格下降在这里是行参数任意的：零行经 `parent_zero_l` 转入 `parent_zero_some_l`，后继行经
`parent_succ_some_l`；行号为内部非标准元素时用 `predecessor_l` 在证明内部做一次分情形，
不做宿主 `Nat` 归纳。列越界时 `parent_past_end_l` 先反推列在长度内。

最后两支由实际公式 `reloc_ge_m` 经 `SecondOrderModel.induct_l` 缝合。`SecondOrderProgram
CopiesBlockParentShift.envSlots` 是私有定义，故此处按同一推送顺序重建同名装配子句；两者体相同，
`reloc_ge_syntax_l` 可在命题层直接复用（defeq）。全部列号、行号、块宽、副本下标与偏移
`K = mul w k` 均可取模型内部非标准元素，不要求矩形性或外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlockParentAncestor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramCopies (copies_m)
open SecondOrderProgramCopiesShape (copies_width_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramCopyBlockShape (copy_width_l)
open SecondOrderProgramCopiesBlockEntry (flat_index_lt_l block_compare_agree_l)
open SecondOrderProgramCopiesBlockParentZero (reloc_ge_zero_l)
open SecondOrderProgramCopiesBlockParentShift
  (reloc_ge_m reloc_ge_language_m reloc_ge_syntax_l parent_some_congr_l)
open SecondOrderProgramParentRelocationAncestorExit (ancestor_exit_sync_l)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorChain (chain_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramListReverse (reverse_m)
open SecondOrderProgramIteration (repeat_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramUniformParentLookup (parent_zero_l)
open SecondOrderProgramUniformParentState (parent_past_end_l)
open SecondOrderProgramUniformParentSpecification (eligible_l parent_succ_some_l)
open SecondOrderProgramParentZero (parent_zero_m parent_zero_some_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 除归纳行外的自由槽 `[父图, 平坦数组, 局部块, 块起点偏移, 块宽]`，与
`SecondOrderProgramCopiesBlockParentShift` 的私有上下文同形状、同推送顺序。 -/
private abbrev Δ : SortContext signature_m := [.set, .num, .num, .num, .num]

/-- 把五个自由槽 `[父图, out, blk, K, w]` 依次装入环境；归纳行由 `pushFree` 追加在头部。 -/
private def envSlots (P : set_l ℳ) (out blk K w : num_l ℳ) : Env ℳ [] Δ :=
  let η₀ := Env.pushFree (Env.empty (M := ℳ)) w
  let η₁ := Env.pushFree η₀ K
  let η₂ := Env.pushFree η₁ blk
  let η₃ := Env.pushFree η₂ out
  Env.pushFree η₃ P

/-- 原统一父程序每条真实父边的父列严格低于目标列，行号任意。零行先经 `parent_zero_l` 搬到
`parent_zero_m`，后继行直接用 `parent_succ_some_l` 的合取支；列越界由 `parent_past_end_l` 排除，
因为界外父输出恒为缺项而不可能是后继。 -/
private theorem parent_descends_l (hℳ : Theory.Models ℳ theory_m)
    {P P0 L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hP0 : graph_semantics_l (graph_m parent_zero_m) P0)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x n r : num_l ℳ} (hn : relation_l L x n) (k p : num_l ℳ)
    (hp : relation_l P (value_l (value_l x r) k) (succ_l p)) :
    SecondOrderOrder.lt_l p k := by
  letI := order_l hℳ
  have hkn : SecondOrderOrder.lt_l k n := by
    by_contra hkt
    exact absurd ((parent_past_end_l hℳ hP hL hn r k (succ_l p) (le_of_not_gt hkt)).mp hp)
      ((nonzero_l hℳ p).symm)
  rcases predecessor_l hℳ r with rfl | ⟨r', rfl⟩
  · rw [parent_zero_l hℳ hP hP0 hL x n k (succ_l p) hn hkn,
      parent_zero_some_l hℳ hP0 hL hJ hn k p] at hp
    exact hp.2.1
  · exact ((parent_succ_some_l hℳ hP hL hM hJ hn r' k p).mp hp).2.1

/-- 第 `k` 份副本的祖先成员半边在段列与原块列之间逐值同步：两侧父图同为 `parent_m`，只是把
参数状态换成 `out @ r` 与 `blk @ r`，故直接实例化 `ancestor_exit_sync_l`，其前提只有弱化平移
与上面的父列严格下降。 -/
theorem ancestor_sync_l (hℳ : Theory.Models ℳ theory_m)
    {R C O L E J P M : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (_hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {b w : num_l ℳ} (hb : relation_l L b w)
    {A l k blk count out r j : num_l ℳ} (_hk : SecondOrderOrder.lt_l k count)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) out)
    (hj : SecondOrderOrder.lt_l j w)
    (hpp : ∀ t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l out r) (add_l (mul_l w k) t))
          (succ_l (add_l (mul_l w k) q)) ↔
        relation_l P (value_l (value_l blk r) t) (succ_l q))
    (q : num_l ℳ) :
    ¬relation_l M (value_l (value_l (value_l out r) (add_l (mul_l w k) j)) (add_l (mul_l w k) q))
        (zero_l ℳ) ↔
      ¬relation_l M (value_l (value_l (value_l blk r) j) q) (zero_l ℳ) := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (repeat_m (step_m parent_m))
  obtain ⟨Ac, _, hAc⟩ := graph_total_l hℳ (chain_m parent_m)
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨P0, _, hP0⟩ := graph_total_l hℳ parent_zero_m
  have hwc : relation_l L out (mul_l w count) := copies_width_l hℳ hR hL hb hy
  have hwb : relation_l L blk w := copy_width_l hℳ hC hL hblk hb
  exact ancestor_exit_sync_l hℳ parent_m parent_m hP hP hS hS hL hE hAc hAc hT hM hM
    (value_l out r) (value_l blk r) (mul_l w k) w j hj
    (parent_descends_l hℳ hP hP0 hL hM hJ hwc) (parent_descends_l hℳ hP hP0 hL hM hJ hwb)
    (fun t q ht => hpp t ht q) q

/-- 第 `r` 行的候选合格性在段列与原块列之间逐值一致：祖先成员半边由 `ancestor_sync_l` 承担，
坐标比较半边由 `block_compare_agree_l` 承担。这是 `parent_some_congr_l` 所需的完整 `hagree`。 -/
theorem hagree_l (hℳ : Theory.Models ℳ theory_m)
    {R C O L E J P M : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {b w : num_l ℳ} (hb : relation_l L b w)
    {A l k blk count out r j : num_l ℳ} (hk : SecondOrderOrder.lt_l k count)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) out)
    (hj : SecondOrderOrder.lt_l j w)
    (hpp : ∀ t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l out r) (add_l (mul_l w k) t))
          (succ_l (add_l (mul_l w k) q)) ↔
        relation_l P (value_l (value_l blk r) t) (succ_l q))
    (q : num_l ℳ) (hqj : SecondOrderOrder.lt_l q j) :
    eligible_l M J out r (add_l (mul_l w k) j) (add_l (mul_l w k) q) ↔
      eligible_l M J blk r j q := by
  have hpw : SecondOrderOrder.lt_l q w :=
    SecondOrderOrder.trans_l hℳ hqj hj
  refine and_congr (ancestor_sync_l hℳ hR hC hO hL hE hJ hP hM hb hk hblk hy hj hpp q) ?_
  exact block_compare_agree_l hℳ hR hC hO hL hE hJ hb hk hblk hy hpw hj r

/-- A5 后继步：第 `r` 行的弱化平移给出第 `succ r` 行的弱化平移。父边的行是 `succ r`，
而 `hagree` 读取祖先与坐标的行分别是 `r` 与 `succ r`，与 `parent_some_congr_l` 的错位一致；
`eligible` 两半边都不涉及最大性搜索，最大性由该引理内部的 `parent_flat_to_local_l`
与 `parent_local_to_flat_l` 消费。 -/
theorem reloc_ge_succ_l (hℳ : Theory.Models ℳ theory_m)
    {R C O L E J P M : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {b w : num_l ℳ} (hb : relation_l L b w)
    {A l k blk count out : num_l ℳ} (hk : SecondOrderOrder.lt_l k count)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) out)
    (r : num_l ℳ)
    (hpp : ∀ t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l out r) (add_l (mul_l w k) t))
          (succ_l (add_l (mul_l w k) q)) ↔
        relation_l P (value_l (value_l blk r) t) (succ_l q)) :
    ∀ t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l out (succ_l r)) (add_l (mul_l w k) t))
          (succ_l (add_l (mul_l w k) q)) ↔
        relation_l P (value_l (value_l blk (succ_l r)) t) (succ_l q) := by
  have hwc : relation_l L out (mul_l w count) := copies_width_l hℳ hR hL hb hy
  have hwb : relation_l L blk w := copy_width_l hℳ hC hL hblk hb
  intro t ht q
  exact (parent_some_congr_l (k := k) (r := r) (j := t) hℳ hP hL hM hJ hwb hwc ht
    (flat_index_lt_l hℳ hk ht)
    (fun p hpt => hagree_l hℳ hR hC hO hL hE hJ hP hM hb hk hblk hy ht hpp p hpt) q).symm

/-- 副本段弱化平移对任意内部行成立：零行基例与上面的后继步由实际公式 `reloc_ge_m` 的
`SecondOrderModel.induct_l` 缝合。归纳只走该公式自身的自由变元形式，偏移、块宽、副本下标与
全部列号、行号都取模型内部元素，不使用宿主 `Nat` 归纳，也不要求外部标准性或矩形性。 -/
theorem reloc_ge_rows_l (hℳ : Theory.Models ℳ theory_m)
    {R C O L E J P M : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {b w : num_l ℳ} (hb : relation_l L b w)
    {A l k blk count out : num_l ℳ} (hk : SecondOrderOrder.lt_l k count)
    (hblk : relation_l C (value_l b (value_l A (value_l k l))) blk)
    (hy : relation_l R (value_l (value_l b (value_l A l)) count) out) :
    ∀ r : num_l ℳ, ∀ t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l out r) (add_l (mul_l w k) t))
          (succ_l (add_l (mul_l w k) q)) ↔
        relation_l P (value_l (value_l blk r) t) (succ_l q) := by
  intro r
  obtain ⟨P0, _, hP0⟩ := graph_total_l hℳ parent_zero_m
  refine induct_l hℳ reloc_ge_m reloc_ge_language_m
    (envSlots P out blk (mul_l w k) w)
    (fun e => ∀ t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l out e) (add_l (mul_l w k) t))
          (succ_l (add_l (mul_l w k) q)) ↔
        relation_l P (value_l (value_l blk e) t) (succ_l q))
    (reloc_ge_syntax_l P out blk (mul_l w k) w) ?_ ?_ r
  · intro t ht q
    exact reloc_ge_zero_l hℳ hR hC hO hL hE hJ hP hP0 hb hk hblk hy ht
  · intro f hf t ht q
    exact reloc_ge_succ_l hℳ hR hC hO hL hE hJ hP hM hb hk hblk hy f hf t ht q

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopiesBlockParentAncestor
