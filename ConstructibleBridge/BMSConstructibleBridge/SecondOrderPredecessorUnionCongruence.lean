import BMSConstructibleBridge.SecondOrderPredecessorUnionSemantics

/-! # 前驱并集的换码一致性

两套前驱索引不必相同。实际关系对应覆盖双方前驱，逐行商相等便足以保证
并集输出商相等；使用精确成员规格，不抽取一列 Type 层行选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorUnionCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private theorem forward_l (hℳ : Theory.Models ℳ theory_m)
    {R R' H H' G G' P P' W W' : set_l ℳ} {n m : num_l ℳ}
    (h : SecondOrderPredecessorUnion.spec_l R H n G P W)
    (h' : SecondOrderPredecessorUnion.spec_l R' H' m G' P' W')
    (hRows : SecondOrderPredecessorUnionSemantics.rows_wf_l R H n)
    (hRows' : SecondOrderPredecessorUnionSemantics.rows_wf_l R' H' m)
    (hMatch : ∀ i, relation_l R i n → ∃ j, relation_l R' j m ∧
      ∀ U V (hU : SecondOrderDomain.wf_l U (zero_l ℳ))
        (hV : SecondOrderDomain.wf_l V (zero_l ℳ)),
        SecondOrderSections.spec_l H i U → SecondOrderSections.spec_l H' j V →
        SecondOrderGraph.eq_l ⟨U, zero_l ℳ, hU⟩ ⟨V, zero_l ℳ, hV⟩)
    (Z : SecondOrderGraph.code_l ℳ)
    (hZ : SecondOrderGraph.mem_l Z (SecondOrderPredecessorUnionSemantics.code_l hℳ h hRows)) :
    SecondOrderGraph.mem_l Z (SecondOrderPredecessorUnionSemantics.code_l hℳ h' hRows') := by
  obtain ⟨i, Y, hi, hY, hRoot, hZY⟩ :=
    (SecondOrderPredecessorUnionSemantics.mem_l hℳ h hRows Z).mp hZ
  obtain ⟨j, hj, hEq⟩ := hMatch i hi
  obtain ⟨V, hV⟩ := SecondOrderSections.exists_l hℳ H' j
  have hYw : SecondOrderDomain.wf_l Y.real (zero_l ℳ) := hRoot ▸ Y.wf
  have hY0 : (⟨Y.real, zero_l ℳ, hYw⟩ : SecondOrderGraph.code_l ℳ) = Y := by
    cases Y
    cases hRoot
    rfl
  have hYV := hEq Y.real V hYw (hRows' j hj V hV) hY hV
  rw [hY0] at hYV
  exact (SecondOrderPredecessorUnionSemantics.mem_l hℳ h' hRows' Z).mpr
    ⟨j, ⟨V, zero_l ℳ, hRows' j hj V hV⟩, hj, hV, rfl,
      (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ Z) hYV).mp hZY⟩

theorem eq_l (hℳ : Theory.Models ℳ theory_m)
    {R R' H H' G G' P P' W W' : set_l ℳ} {n m : num_l ℳ}
    (h : SecondOrderPredecessorUnion.spec_l R H n G P W)
    (h' : SecondOrderPredecessorUnion.spec_l R' H' m G' P' W')
    (hRows : SecondOrderPredecessorUnionSemantics.rows_wf_l R H n)
    (hRows' : SecondOrderPredecessorUnionSemantics.rows_wf_l R' H' m)
    (I : set_l ℳ)
    (hForth : ∀ i, relation_l R i n → ∃ j, relation_l R' j m ∧ relation_l I i j)
    (hBack : ∀ j, relation_l R' j m → ∃ i, relation_l R i n ∧ relation_l I i j)
    (hEq : ∀ i j, relation_l I i j → relation_l R i n → relation_l R' j m →
      ∀ U V (hU : SecondOrderDomain.wf_l U (zero_l ℳ))
        (hV : SecondOrderDomain.wf_l V (zero_l ℳ)),
        SecondOrderSections.spec_l H i U → SecondOrderSections.spec_l H' j V →
        SecondOrderGraph.eq_l ⟨U, zero_l ℳ, hU⟩ ⟨V, zero_l ℳ, hV⟩) :
    SecondOrderGraph.eq_l (SecondOrderPredecessorUnionSemantics.code_l hℳ h hRows)
      (SecondOrderPredecessorUnionSemantics.code_l hℳ h' hRows') := by
  apply (SecondOrderGraph.ext_l hℳ _ _).mpr
  intro Z
  constructor
  · apply forward_l hℳ h h' hRows hRows' ?_ Z
    intro i hi
    obtain ⟨j, hj, hij⟩ := hForth i hi
    exact ⟨j, hj, hEq i j hij hi hj⟩
  · apply forward_l hℳ h' h hRows' hRows ?_ Z
    intro j hj
    obtain ⟨i, hi, hij⟩ := hBack j hj
    refine ⟨i, hi, ?_⟩
    intro V U hV hU hVj hUi
    exact SecondOrderGraph.symm_l hℳ (hEq i j hij hi hj U V hU hV hUi hVj)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorUnionCongruence
