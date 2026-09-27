import BMSConstructibleBridge.SecondOrderProgramExpansionCopyAncestor

/-!
# 最终展开的任意两个副本内祖先一致

两个实际副本分别与同一个实际坏块比较，从而得到任意内部副本编号之间的祖先等价。
这是 Hunter Lemma 2.5(ii) 的程序语义形态；不把副本编号限制为宿主自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionInsideCopies

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
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

/-- 完整展开输出中任意两份实际副本的同一对局部列具有相同祖先关系。 -/
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
    {x j p d k maximal b height y leftCopy rightCopy row i q : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (hleft : SecondOrderOrder.lt_l leftCopy (succ_l k))
    (hright : SecondOrderOrder.lt_l rightCopy (succ_l k))
    (hrow : SecondOrderOrder.lt_l row height)
    (hi : SecondOrderOrder.lt_l i d) (hq : SecondOrderOrder.lt_l q d) :
    (¬relation_l M
        (value_l (value_l (value_l y row)
          (add_l p (add_l (mul_l d leftCopy) q)))
          (add_l p (add_l (mul_l d leftCopy) i))) (zero_l ℳ) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row)
          (add_l p (add_l (mul_l d rightCopy) q)))
          (add_l p (add_l (mul_l d rightCopy) i))) (zero_l ℳ)) := by
  have h₁ := SecondOrderProgramExpansionCopyAncestor.member_congr_l
    hℳ hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparent hd hb hy
      hleft hrow hi hq
  have h₂ := SecondOrderProgramExpansionCopyAncestor.member_congr_l
    hℳ hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparent hd hb hy
      hright hrow hi hq
  exact h₁.symm.trans h₂

#print axioms member_congr_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionInsideCopies
