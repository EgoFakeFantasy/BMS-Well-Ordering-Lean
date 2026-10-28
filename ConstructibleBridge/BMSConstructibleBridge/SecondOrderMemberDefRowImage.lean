import BMSConstructibleBridge.SecondOrderLegalMemberCollection
import BMSConstructibleBridge.SecondOrderMemberEnumeration

/-! # 原 Def 切片在实际母集枚举下的精确像

原切片按母根子节点收集成员，枚举却在全部内部数上有值。本模块
用原求值族的代表不变性处理非母根子节点，证明两种像完全相同。
结论读取原商全部对象，不限制于类内成员或宿主公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefRowImage

open Logic FirstOrder SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem image_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {A H Z : SecondOrderGraph.code_l ℳ} {a : num_l ℳ}
    {ha : relation_l A.real a A.root} {V E D Q R T F : set_l ℳ}
    (h : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F H)
    {U : SecondOrderQuotient.type_l hℳ}
    (hU : ∀ n y, ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      U (PowerlessBMSQuotientCoding.numberCode_l K n).val y ↔
        y = (SecondOrderMemberStructure.value_l hℳ A a ha n).val)
    (i : num_l ℳ)
    (hZ : ∀ X, SecondOrderGraph.mem_l X Z ↔ ∃ n, relation_l A.real n A.root ∧
      relation_l F i n ∧ SecondOrderBisimulation.eq_l X.real A.real X.root n) :
    ∀ y : SecondOrderQuotient.type_l hℳ,
      SecondOrderQuotient.mem_l hℳ y (SecondOrderQuotient.mk_l hℳ Z) ↔
        ∃ v, ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hℳ)
          U (PowerlessBMSQuotientCoding.numberCode_l K v).val y ∧ relation_l F i v := by
  have hRefl n : relation_l Q n n := (h.equality n n).mpr rfl
  have hQ : SecondOrderRelatedAssignments.respects_l Q Q := by
    intro n m n' m' hn hm
    have hn' := (h.equality n n').mp hn
    have hm' := (h.equality m m').mp hm
    rw [h.equality n m, h.equality n' m', hn', hm']
  have hR : SecondOrderRelatedAssignments.respects_l Q R := by
    intro n m n' m' hn hm
    have hn' := (h.equality n n').mp hn
    have hm' := (h.equality m m').mp hm
    rw [h.membership n m, h.membership n' m', hn', hm']
  intro y
  obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
  constructor
  · intro hy
    obtain ⟨n, hn, hFn, hYn⟩ := (hZ Y).mp hy
    have hValue : (SecondOrderMemberStructure.value_l hℳ A a ha n).val =
        SecondOrderQuotient.mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
      change SecondOrderQuotient.mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n) = _
      rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn]
    exact ⟨n, (hU n _).mpr (((SecondOrderQuotient.eq_iff_l hℳ Y
      (SecondOrderGraph.child_l hℳ A n hn)).mpr hYn).trans hValue.symm), hFn⟩
  · rintro ⟨v, hv, hFv⟩
    let m := SecondOrderMemberNormalizer.value_l A.real A.root a v
    have hm : relation_l A.real m A.root := SecondOrderMemberNormalizer.member_l A.real A.root a ha v
    have hValue : (SecondOrderMemberStructure.value_l hℳ A a ha v).val =
        (SecondOrderMemberStructure.value_l hℳ A a ha m).val := by
      change SecondOrderQuotient.mk_l hℳ (SecondOrderGraph.child_l hℳ A m hm) =
        SecondOrderQuotient.mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha m)
      rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha m hm]
    have hvm := (h.equality v m).mpr (Subtype.ext hValue)
    have hFm := (SecondOrderDefinableRespect.row_l hℳ h.powers D Q R T F
      hRefl hQ hR h.evaluation h.family i v m (h.domain v) (h.domain m) hvm).mp hFv
    have hYm : SecondOrderBisimulation.eq_l Y.real A.real Y.root m := by
      apply (SecondOrderQuotient.eq_iff_l hℳ Y (SecondOrderGraph.child_l hℳ A m hm)).mp
      exact (hU v _).mp hv
    exact (hZ Y).mpr ⟨m, hm, hFm, hYm⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefRowImage
