import BMSConstructibleBridge.SecondOrderProgramExpansionSelected
import BMSConstructibleBridge.SecondOrderProgramSuccessCopyEntry
import BMSConstructibleBridge.SecondOrderProgramTrimEntryBelow

/-!
# 完整展开中任意副本的实际条目定位

成功正文中的条目位置经真实 `trim_m` 搬到完整 `expand_m` 输出。
条目只在被裁剪保留的内部行上保持；结论显式保留这个界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramTrimArray (trim_m)
open SecondOrderProgramTrimHeight (trim_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramUniformParent (parent_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 完整展开的第 `t` 个实际副本在保留行上的条目与局部复制块完全一致。 -/
theorem entry_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Q Last : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hQ : graph_semantics_l (graph_m copy_m) Q)
    (hLast : graph_semantics_l
      (graph_m SecondOrderProgramMaximalParentRow.last_column_m) Last)
    {x j p d k maximal b height y t row i : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (ht : SecondOrderOrder.lt_l t (succ_l k))
    (hi : SecondOrderOrder.lt_l i d) :
    ∃ v z l blk,
      relation_l S (value_l x (value_l k (value_l maximal p))) v ∧
      relation_l T v y ∧ relation_l Z v z ∧
      relation_l Last x l ∧
      relation_l Q
        (value_l b (value_l (value_l x (value_l maximal p)) (value_l t l))) blk ∧
      (∀ q, SecondOrderOrder.lt_l row z →
        (relation_l J
            (value_l y (value_l (add_l p (add_l (mul_l d t) i)) row)) q ↔
          relation_l J (value_l blk (value_l i row)) q)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨v, hv, htrim⟩ :=
    (SecondOrderProgramExpansionSelected.expand_some_l
      hℳ hX hW hP hI hS hT hmax hlast hparent k y).mp hy
  obtain ⟨z, hz, _⟩ :=
    function_of_semantics_l hℳ SecondOrderProgramTrimHeight.trim_m hZ v
  have hpj : SecondOrderOrder.lt_l p j :=
    SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hb
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hb hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  obtain ⟨l, blk, hl, hblk, hentry⟩ :=
    SecondOrderProgramSuccessCopyEntry.entry_l hℳ hS hB hL hE hD hJ hQ hLast
      hx.1 (Or.inr hpj) hd hb hv ht hi
  have hflat := SecondOrderProgramCopiesBlockEntry.flat_index_lt_l hℳ ht hi
  have hcol : add_l p (add_l (mul_l d t) i) < add_l p (mul_l d (succ_l k)) :=
    SecondOrderProgramParentRelocation.lt_add_left_l hℳ hflat
  refine ⟨v, z, l, blk, hv, htrim, hz, hl, hblk, ?_⟩
  intro q hrow
  exact (SecondOrderProgramTrimEntryBelow.entry_l hℳ hT hZ hJ hL hE hvr hz htrim
    hcol hrow q).symm.trans (hentry q)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyEntry
