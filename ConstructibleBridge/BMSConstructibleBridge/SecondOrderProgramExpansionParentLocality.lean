import BMSConstructibleBridge.SecondOrderProgramExpansionEarlierParentCandidateCut
import BMSConstructibleBridge.SecondOrderProgramExpansionSelected

/-!
# 完整展开的模型内部父局部性

低于最大父行的部分由实际行局部性公式作内部强归纳。所有坏块、成功正文、
裁剪高度及输出长度见证均从原程序图取得，公共接口不再要求逐行归纳假设。
局部性只约束副本的非首列；首列的祖先界是后续高行证明的另一项义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionParentLocality

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

/-- Hunter 2.5(iv) 在最大父行以下成立，覆盖实际展开中的每个副本，含零号副本。
不假定内部行号为标准自然数，也不把低行局部性留作调用方前提。 -/
theorem below_maximal_l (hℳ : Theory.Models ℳ theory_m)
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
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l X (value_l x k) y) :
    ∀ copy, SecondOrderOrder.lt_l copy (succ_l k) →
      ∀ row, SecondOrderOrder.lt_l row maximal →
        row_locality_l P y p (add_l p (mul_l d copy))
          (add_l p (mul_l d (succ_l copy))) row := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨bad, hbad, _⟩ := function_of_semantics_l hℳ bad_m hB
    (value_l x (value_l k (value_l maximal p)))
  obtain ⟨v, hv, htrim⟩ :=
    (SecondOrderProgramExpansionSelected.expand_some_l
      hℳ hX hW hP hI hS hT hmax hlast hparent k y).mp hy
  obtain ⟨z, hz, _⟩ := function_of_semantics_l hℳ
    SecondOrderProgramTrimHeight.trim_m hZ v
  obtain ⟨n, hn, _⟩ := function_of_semantics_l hℳ length_m hL y
  intro copy hcopy
  by_cases hzero : copy = zero_l ℳ
  · subst copy
    intro row _
    simpa only [mul_zero_l hℳ, add_zero_l hℳ] using
      row_locality_at_prefix_l hℳ hP y p
        (add_l p (mul_l d (succ_l (zero_l ℳ)))) row
  · have hcopyPos : SecondOrderOrder.lt_l (zero_l ℳ) copy :=
      lt_of_le_of_ne (zero_le_l hℳ copy) (Ne.symm hzero)
    apply row_locality_below_of_strong_step_l hℳ P y p
      (add_l p (mul_l d copy)) (add_l p (mul_l d (succ_l copy))) maximal
    intro row hrow ih target hstart hfinish found hParent
    exact parent_locality_step_at_expansion_copy_interval_l hℳ
      hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparent hd hbad hy hv htrim hz hrow hcopyPos hcopy hn ih
      hstart hfinish hParent

#print axioms below_maximal_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionParentLocality
