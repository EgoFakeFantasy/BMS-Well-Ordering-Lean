import BMSConstructibleBridge.SecondOrderProgramEntry
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderProgramListEntryBound
import BMSConstructibleBridge.SecondOrderProgramUniformParent
import BMSConstructibleBridge.SecondOrderProgramUniformParentLookup
import BMSConstructibleBridge.SecondOrderProgramUniformParentState
import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification
import BMSConstructibleBridge.SecondOrderProgramParentZero
import BMSConstructibleBridge.SecondOrderProgramAncestorChain
import BMSConstructibleBridge.SecondOrderProgramAncestorMembership
import BMSConstructibleBridge.SecondOrderProgramAncestorFinalBound

/-!
# 实际父图行数组的祖先指标严格下降（阶段 B2 第二块砖）

阶段 A 的祖先同步全部把"父边严格降列"当假设消费（`hdownx`、`hdowny`），且该下降在
`SecondOrderProgramCopiesBlockParentAncestor` 里是私有引理；固定外部行号的同款结论
（`SecondOrderProgramAncestorFinalBound.member_lt_l`）只覆盖外部参数化的父程序族。
本模块把两者合成并公开成秩下降砖需要的形状：对任意内部数组、任意内部行号与任意内部
目标列，实际统一父图的每个非零祖先指标都严格低于目标列。

证明组装完全走既有公共件：先把 A5 私有的按行下降重述为公共引理
`parent_descends_lt_l`（零行走 `parent_zero_l` 搬到 `parent_zero_some_l`，后继行走
`parent_succ_some_l`，行号为内部非标准元素时由 `predecessor_l` 在证明内部分情形，列越界
由 `parent_past_end_l` 排除）；再对行数组状态实例化公共的 `chain_below_l` 与
`member_nonzero_l`，祖先链每个界内条目都严格低于起始列。全部参数可取模型内部非标准
元素，不使用宿主 `Nat` 归纳、不要求外部标准性或矩形性，也不引入任何条件前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSegmentAncestorDescent

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramAncestorChain (chain_m)
open SecondOrderProgramAncestorMembership (member_m member_nonzero_l)
open SecondOrderProgramAncestorFinalBound (chain_below_l)
open SecondOrderProgramListEntryBound (below_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramUniformParentLookup (parent_zero_l)
open SecondOrderProgramUniformParentState (parent_past_end_l)
open SecondOrderProgramUniformParentSpecification (parent_succ_some_l)
open SecondOrderProgramParentZero (parent_zero_m parent_zero_some_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际统一父图每条真实父边都严格减小目标列号：数组、行号与列号全部允许内部非标准
元素。这是阶段 A 各模块以假设形式消费的 `hdown` 的公共无版本。 -/
theorem parent_descends_lt_l (hℳ : Theory.Models ℳ theory_m)
    {P P0 L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hP0 : graph_semantics_l (graph_m parent_zero_m) P0)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x n : num_l ℳ} (hn : relation_l L x n) (r k p : num_l ℳ)
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

/-- 实际统一父图的行数组祖先指标严格下降：任意内部数组 `x`、内部行 `r`、内部目标列
`t` 上，祖先成员查询非零 witnesses 的指标 `i` 必严格低于 `t`。行数组状态即 `x @ r`，
父边下降半边由上一条公共引理无条件提供，链界半边由 `chain_below_l` 承担。 -/
theorem segment_ancestor_lt_l (hℳ : Theory.Models ℳ theory_m)
    {P P0 L E J M Ac : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hP0 : graph_semantics_l (graph_m parent_zero_m) P0)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hAc : graph_semantics_l (graph_m (chain_m parent_m)) Ac)
    {x n r t i : num_l ℳ} (hn : relation_l L x n)
    (hi : ¬relation_l M (value_l (value_l (value_l x r) t) i) (zero_l ℳ)) :
    SecondOrderOrder.lt_l i t := by
  -- 行数组状态 `x @ r` 从目标列 `t` 出发的祖先链输出。
  obtain ⟨v, hv, _⟩ := function_of_semantics_l hℳ (chain_m parent_m) hAc
    (value_l (value_l (value_l x r) t) t)
  obtain ⟨len, hlen, _⟩ := function_of_semantics_l hℳ length_m hL v
  -- 成员非零当且仅当链的某个界内位置取值 `i`。
  obtain ⟨j, hj, hmem⟩ := (member_nonzero_l hℳ parent_m hM hAc hL hE hv hlen i).mp hi
  -- 行数组上的父边无条件严格降列，链的每个界内条目都严格低于起始列 `t`。
  have hbelow : below_l E v len t :=
    chain_below_l hℳ parent_m hAc hL hE hP
      (fun k p hp => parent_descends_lt_l hℳ hP hP0 hL hM hJ hn r k p hp) hv hlen
  exact hbelow j hj i hmem

#print axioms parent_descends_lt_l
#print axioms segment_ancestor_lt_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSegmentAncestorDescent
