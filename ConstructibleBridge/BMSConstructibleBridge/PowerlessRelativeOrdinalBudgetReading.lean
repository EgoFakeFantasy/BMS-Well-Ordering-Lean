import BMSConstructibleBridge.SecondOrderOrdinalBudgetFunction
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage

/-! # 规范预算的原成员读数与 Class 序数覆盖

原指标序数的成员关系与规范最小数前驱精确等价。因而 b<a 的任何有限
预算尾都属于 a 的零尾；每个预算值的 Class 身份来自已证明的原序数覆盖，
而不是从 raw 图、Class 可数性或某个未证明的统一历史假设推出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalBudgetReading

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open PowerlessBMSQuotientCoding
open SecondOrderOrdinalBudgetGraph SecondOrderOrdinalBudgetOrder
open SecondOrderOrdinalBudgetFunction (index_l)
open SecondOrderQuotient (type_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

variable (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
  {Q D R : set_l ℳ}
  (hQ : ∀ i j, SecondOrderPairing.relation_l Q i j ↔
    SecondOrderBisimulation.eq_l A.real A.real i j)
  (hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root)
  (hRel : SecondOrderRootOrdinalRelation.spec_l A.real Q D R)

include hQ hRel

theorem index_member_l (i n : num_l ℳ)
    (hi : SecondOrderModel.mem_l i D) (hn : SecondOrderModel.mem_l n D) :
    SecondOrderQuotient.mem_l hℳ (index_l hℳ A hD i hi) (index_l hℳ A hD n hn) ↔
      SecondOrderPairing.relation_l R i n := by
  constructor
  · rintro ⟨c, hc, hIC⟩
    exact (hRel i n).mpr ⟨hi, hn, c, hc, (hQ i c).mpr hIC⟩
  · intro hin
    obtain ⟨_, _, c, hc, hIC⟩ := (hRel i n).mp hin
    exact ⟨c, hc, (hQ i c).mp hIC⟩

variable {S G : set_l ℳ} {r : num_l ℳ}
  (hG : spec_l S r R G) (hS : ∀ a, SecondOrderDomain.wf_l S a)

theorem ordinal_l
    (hA : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ A))
    (hξ : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (base_l hℳ hS r))
    (n m : num_l ℳ) (hn : SecondOrderModel.mem_l n D) :
    SetTheory.Structure.IsOrdinal (quotient_l hℳ)
      (tail_l hℳ hG hS (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel) n m) := by
  have hTrans := SecondOrderRootOrdinalRelation.transitive_l hℳ A hA hQ hD hRel
  have hCompare := SecondOrderRootOrdinalRelation.compare_l hℳ A hA hQ hD hRel
  have hEnds (i j : num_l ℳ) (hij : SecondOrderPairing.relation_l R i j) :
      SecondOrderModel.mem_l i D ∧ SecondOrderModel.mem_l j D :=
    ⟨((hRel i j).mp hij).1, ((hRel i j).mp hij).2.1⟩
  exact SecondOrderOrdinalBudgetOrder.ordinal_l hℳ hG hS
    (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel)
    (hξ := hξ) (hTrans := hTrans) (hEnds := hEnds) (hCompare := hCompare) n m hn

theorem class_l (K : source_coding_l hℳ) {B : type_l hℳ}
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
      ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (hA : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ A))
    (hξ : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (base_l hℳ hS r))
    (n m : num_l ℳ) (hn : SecondOrderModel.mem_l n D) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B
      (tail_l hℳ hG hS (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel) n m) :=
  PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (ordinal_l hℳ A hQ hD hRel hG hS hA hξ n m hn)

/-- 严格较早的实际序数指标具有任意内部有限余量，不只两步。 -/
theorem earlier_l (i n : num_l ℳ)
    (hi : SecondOrderModel.mem_l i D) (hn : SecondOrderModel.mem_l n D)
    (hin : SecondOrderQuotient.mem_l hℳ (index_l hℳ A hD i hi) (index_l hℳ A hD n hn))
    (j m : num_l ℳ) :
    SecondOrderQuotient.mem_l hℳ
      (tail_l hℳ hG hS (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel) i j)
      (tail_l hℳ hG hS (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel) n m) :=
  SecondOrderOrdinalBudgetOrder.earlier_l hℳ hG hS
    (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel)
    ((index_member_l hℳ A hQ hD hRel i n hi hn).mp hin) j m

theorem empty_eq_base_l (n : num_l ℳ) (hn : SecondOrderModel.mem_l n D)
    (hEmpty : PowerlessRelativeHierarchySemantics.empty_l hℳ (index_l hℳ A hD n hn)) :
    tail_l hℳ hG hS (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel) n (zero_l ℳ) =
      base_l hℳ hS r := by
  apply SecondOrderOrdinalBudgetFinite.zero_eq_base_l hℳ hG hS
    (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel) n
  intro i hin
  have hi := ((hRel i n).mp hin).1
  exact hEmpty (index_l hℳ A hD i hi)
    ((index_member_l hℳ A hQ hD hRel i n hi hn).mpr hin)

#print axioms index_member_l
#print axioms class_l
#print axioms earlier_l
#print axioms empty_eq_base_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeOrdinalBudgetReading
