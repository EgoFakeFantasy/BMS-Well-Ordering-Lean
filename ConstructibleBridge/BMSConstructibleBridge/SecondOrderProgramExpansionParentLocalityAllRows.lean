import BMSConstructibleBridge.SecondOrderProgramExpansionParentLocality
import BMSConstructibleBridge.SecondOrderProgramExpansionMaximalRootBound

/-!
# Hunter 2.5(iv) 的全部内部行版本

低行使用已闭合的有界归纳结果。高行若有某个低行不经过当前首列，则用低行
局部性；否则把较早父边截到当前首列，再降至最大父行，应用首列祖先界。
最终归纳对象仍是实际纯二阶行局部性公式，覆盖模型中的全部内部行号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionParentLocalityAllRows

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramExpansionEarlierParentCandidateCut
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际展开的每个副本在所有内部行满足父局部性；只对非首列目标作此断言。 -/
theorem all_rows_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
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
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal height y : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hsourceParent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l X (value_l x k) y) :
    ∀ copy, SecondOrderOrder.lt_l copy (succ_l k) →
      ∀ row, row_locality_l P y p (add_l p (mul_l d copy))
        (add_l p (mul_l d (succ_l copy))) row := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨bad, hbad, _⟩ := function_of_semantics_l hℳ bad_m hB
    (value_l x (value_l k (value_l maximal p)))
  obtain ⟨v, hv, htrim⟩ :=
    (SecondOrderProgramExpansionSelected.expand_some_l
      hℳ hX hW hP hI hS hT hmax hlast hsourceParent k y).mp hy
  obtain ⟨z, hz, _⟩ := function_of_semantics_l hℳ
    SecondOrderProgramTrimHeight.trim_m hZ v
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hsourceParent
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hbad
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hbad hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  have hyr := SecondOrderProgramTrimNormalized.rectangular_l hℳ hT hZ hL hE hvr hz htrim
  intro copy hcopy
  apply row_locality_all_of_strong_step_l hℳ P y p
    (add_l p (mul_l d copy)) (add_l p (mul_l d (succ_l copy)))
  intro row ih target hstart hfinish found hparent
  by_cases hrow : SecondOrderOrder.lt_l row maximal
  · exact SecondOrderProgramExpansionParentLocality.below_maximal_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hsourceParent hd hy copy hcopy row hrow
      target hstart hfinish found hparent
  · by_cases hbelow : ∀ s, SecondOrderOrder.lt_l s row →
        ¬relation_l M
          (value_l (value_l (value_l y s) target) (add_l p (mul_l d copy))) (zero_l ℳ)
    · by_cases hgood : SecondOrderOrder.lt_l found p
      · exact Or.inl hgood
      · right
        refine ⟨?_, SecondOrderOrder.trans_l hℳ
          (SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent) hfinish⟩
        intro hbefore
        obtain ⟨htarget, hrowTrim⟩ := SecondOrderProgramRectangularParent.target_bounds_l
          hℳ hP hJ hO hL hE hyr hparent
        obtain ⟨entry, hentry⟩ := SecondOrderProgramRectangularEntry.exists_l
          hℳ hJ hO hL hE hyr (SecondOrderOrder.trans_l hℳ hstart htarget) hrowTrim
        have hatRoot := SecondOrderProgramUniformAncestorBetween.member_between_l
          hℳ hM hJ hL hyr.1 htarget
          (SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hparent)
          hbefore hstart hentry hbelow
        have hmaxLe : maximal ≤ row := le_of_not_gt hrow
        have hatMax := SecondOrderProgramUniformAncestorRows.row_le_l
          hℳ hM hmaxLe hatRoot
        exact hgood (SecondOrderProgramExpansionMaximalRootBound.ancestor_in_good_at_maximal_l
          hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
          hx hmax hlast hsourceParent hd hbad hy hv htrim hz hcopy hatMax)
    · rcases parent_locality_of_not_all_lower_roots_l hℳ hP hM
        y p (add_l p (mul_l d copy)) (add_l p (mul_l d (succ_l copy)))
        row target found ih hbelow hstart hfinish hparent with hgood | ⟨hafter, hend⟩
      · exact Or.inl hgood
      · exact Or.inr ⟨fun h => SecondOrderOrder.irrefl_l hℳ _
          (SecondOrderOrder.trans_l hℳ hafter h), hend⟩

#print axioms all_rows_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionParentLocalityAllRows
