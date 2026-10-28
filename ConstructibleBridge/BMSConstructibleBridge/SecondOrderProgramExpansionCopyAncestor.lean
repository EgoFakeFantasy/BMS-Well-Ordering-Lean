import BMSConstructibleBridge.SecondOrderProgramExpansionSelected
import BMSConstructibleBridge.SecondOrderProgramSuccessCopyAncestor
import BMSConstructibleBridge.SecondOrderProgramTrimParent

/-!
# 最终展开中任意副本的祖先对应

成功正文中的全局副本坐标先由 `SecondOrderProgramSuccessCopyAncestor` 处理，随后穿过
实际 `trim_m`。这里使用的正是完整 `expand_m` 图，而非未裁剪的中间输出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyAncestor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramTrimArray (trim_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 有最大父行的实际展开中，坏块祖先与任意副本的最终全局坐标祖先一致。 -/
theorem member_congr_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I B L E D J M : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x j p d k maximal b height y t row i q : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (ht : SecondOrderOrder.lt_l t (succ_l k))
    (hrow : SecondOrderOrder.lt_l row height)
    (hi : SecondOrderOrder.lt_l i d) (hq : SecondOrderOrder.lt_l q d) :
    (¬relation_l M (value_l (value_l (value_l b row) q) i) (zero_l ℳ) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d t) q)))
          (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ success_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ trim_m
  obtain ⟨v, hv, htrim⟩ :=
    (SecondOrderProgramExpansionSelected.expand_some_l
      hℳ hX hW hP hI hS hT hmax hlast hparent k y).mp hy
  have hpj : SecondOrderOrder.lt_l p j :=
    SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hb
  have hvr := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hb hbr hv
  have hsuccess := SecondOrderProgramSuccessCopyAncestor.member_congr_l
    hℳ hS hB hL hE hD hJ hM hx (Or.inr hpj) hd hb hv ht hrow hi hq
  have htrimmed := SecondOrderProgramTrimParent.member_l
    hℳ hT hM hL hE hvr htrim row (add_l p (add_l (mul_l d t) q))
      (add_l p (add_l (mul_l d t) i)) (zero_l ℳ)
  exact hsuccess.trans (not_congr htrimmed)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyAncestor
