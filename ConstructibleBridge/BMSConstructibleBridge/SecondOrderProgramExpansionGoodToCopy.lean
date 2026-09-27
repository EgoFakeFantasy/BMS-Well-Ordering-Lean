import BMSConstructibleBridge.SecondOrderProgramExpansionPrefix
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorStructure
import BMSConstructibleBridge.SecondOrderProgramExpansionCopyBoundaryIteration

/-!
# 好前缀到副本的祖先对应：边界归约

完整展开已保留原非末列的祖先查询。若已证某个实际副本首列以零号副本首列为祖先，
则前缀内任一列到这两个首列的祖先关系一致。后向使用同一实际祖先链的可比性；
缺少的首列跨副本边界保留为显式前提，不能由副本内部对应替代。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodToCopy

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramArithmetic SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 若两个局部目标都经过各自的副本首列，首列上的好前缀对应可传给局部目标。 -/
theorem member_iff_of_two_roots_l (hℳ : Theory.Models ℳ theory_m)
    {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {y row good leftRoot rightRoot leftTarget rightTarget : num_l ℳ}
    (hgoodLeft : SecondOrderOrder.lt_l good leftRoot)
    (hgoodRight : SecondOrderOrder.lt_l good rightRoot)
    (hleftRoot : ¬relation_l M
      (value_l (value_l (value_l y row) leftTarget) leftRoot) (zero_l ℳ))
    (hrightRoot : ¬relation_l M
      (value_l (value_l (value_l y row) rightTarget) rightRoot) (zero_l ℳ))
    (hroot : (¬relation_l M
        (value_l (value_l (value_l y row) leftRoot) good) (zero_l ℳ)) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) rightRoot) good) (zero_l ℳ)) :
    (¬relation_l M
      (value_l (value_l (value_l y row) leftTarget) good) (zero_l ℳ)) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) rightTarget) good) (zero_l ℳ) := by
  constructor
  · intro hgoodTarget
    have hgoodAtRoot := SecondOrderProgramUniformAncestorStructure.comparable_l
      hℳ hM hgoodTarget hleftRoot hgoodLeft
    exact SecondOrderProgramUniformAncestorStructure.trans_l hℳ hM
      hrightRoot (hroot.mp hgoodAtRoot)
  · intro hgoodTarget
    have hgoodAtRoot := SecondOrderProgramUniformAncestorStructure.comparable_l
      hℳ hM hgoodTarget hrightRoot hgoodRight
    exact SecondOrderProgramUniformAncestorStructure.trans_l hℳ hM
      hleftRoot (hroot.mpr hgoodAtRoot)

/-- 跨副本首列祖先一旦建立，实际完整展开中好前缀到该首列的祖先即与原首列一致。 -/
theorem member_iff_of_root_l (hℳ : Theory.Models ℳ theory_m) {X M L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {x y j height k p d t row good : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hy : relation_l X (value_l x k) y)
    (hpj : SecondOrderOrder.lt_l p j)
    (hgood : SecondOrderOrder.lt_l good p)
    (hroot : ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (mul_l d t))) p) (zero_l ℳ)) :
    (¬relation_l M (value_l (value_l (value_l x row) p) good) (zero_l ℳ) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d t))) good) (zero_l ℳ)) := by
  have hprefix := not_congr (SecondOrderProgramExpansionPrefix.member_l
    hℳ hX hM hL hE hx hy hpj row good (zero_l ℳ))
  constructor
  · intro h
    exact SecondOrderProgramUniformAncestorStructure.trans_l hℳ hM hroot (hprefix.mp h)
  · intro h
    exact hprefix.mpr
      (SecondOrderProgramUniformAncestorStructure.comparable_l hℳ hM h hroot hgood)

/-- 只需逐对相邻首列的真实祖先边界，就能把好前缀对应传给每个较晚内部副本。 -/
theorem member_iff_of_adjacent_l (hℳ : Theory.Models ℳ theory_m) {X M L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {x y j height k p d row good s : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hy : relation_l X (value_l x k) y)
    (hpj : SecondOrderOrder.lt_l p j)
    (hgood : SecondOrderOrder.lt_l good p)
    (hadjacent : ∀ t, SecondOrderOrder.lt_l t k →
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
          (add_l p (mul_l d t))) (zero_l ℳ))
    (hs : SecondOrderOrder.lt_l s k) :
    (¬relation_l M (value_l (value_l (value_l x row) p) good) (zero_l ℳ) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l s)))) good)
          (zero_l ℳ)) := by
  exact member_iff_of_root_l hℳ hX hM hL hE hx hy hpj hgood
    (SecondOrderProgramExpansionCopyBoundaryIteration.first_to_l hℳ hM hadjacent hs)

#print axioms member_iff_of_root_l
#print axioms member_iff_of_adjacent_l
#print axioms member_iff_of_two_roots_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodToCopy
