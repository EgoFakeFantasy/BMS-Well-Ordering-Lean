import BMSConstructibleBridge.SecondOrderFiniteDisjunctionFamily
import BMSConstructibleBridge.SecondOrderMemberDefRowImage

/-! # 全内部有限参数值域进入实际 Def

读取原 Def 的合法内部呈现，证明任意有效内部赋值的值域属于同一个 Def。
值域等式量化商中的全部对象，不仅比较母根子节点。长度无需外部标准；
但一般有限集合仍需先构造这样的实际赋值，不能把该编码义务删掉。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefFiniteAssignment

open Logic FirstOrder SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderSequenceSyntax (read_l)
open SecondOrderQuotient (mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem exists_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {A H : SecondOrderGraph.code_l ℳ} {a : num_l ℳ}
    {ha : relation_l A.real a A.root} {V E D Q R T F : set_l ℳ}
    (h : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F H)
    (l c : num_l ℳ) (hc : SecondOrderAssignmentSyntax.valid_l E c l) :
    ∃ Y : SecondOrderQuotient.type_l hℳ, mem_l hℳ Y (mk_l hℳ H) ∧
      ∀ x, mem_l hℳ x Y ↔ ∃ j y, SecondOrderOrder.lt_l j l ∧ read_l E c j y ∧
        x = (SecondOrderMemberStructure.value_l hℳ A a ha y).val := by
  obtain ⟨i, hi, hRow⟩ := SecondOrderFiniteDisjunctionFamily.exists_l hℳ
    h.formula_codes h.powers h.evaluation h.family l c hc
  obtain ⟨G, hG⟩ := SecondOrderSubsetLayer.exists_l hℳ A.real F A.root
  let Z := SecondOrderSubsetLayer.code_l hℳ A F G hG i
  have hZ := SecondOrderSubsetLayer.mem_l hℳ A F G hG i
  have hZH := (h.collection Z).mpr ⟨i, hi, hZ⟩
  obtain ⟨U, _, hU, _⟩ := SecondOrderMemberEnumeration.exists_l K A a ha
  have hU' n y : ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      U (PowerlessBMSQuotientCoding.numberCode_l K n).val y ↔
        y = (SecondOrderMemberStructure.value_l hℳ A a ha n).val := by
    simpa only [ThirdOrderSemantics.value_l, ThirdOrderSemantics.member_l,
      ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l,
      SecondOrderFunctionObjects.value_l, SecondOrderPairObjects.ordered_l,
      SecondOrderPairObjects.pair_l, SecondOrderQuotient.structure_l] using hU n y
  have hImage := SecondOrderMemberDefRowImage.image_l K h hU' i hZ
  refine ⟨mk_l hℳ Z, hZH, fun x => (hImage x).trans ?_⟩
  constructor
  · rintro ⟨v, hv, hFv⟩
    obtain ⟨_, j, y, hj, hy, hQ⟩ := (hRow v).mp hFv
    exact ⟨j, y, hj, hy, ((hU' v x).mp hv).trans
      (congrArg Subtype.val ((h.equality v y).mp hQ))⟩
  · rintro ⟨j, y, hj, hy, hx⟩
    exact ⟨y, (hU' y x).mpr hx, (hRow y).mpr
      ⟨h.domain y, j, y, hj, hy, (h.equality y y).mpr rfl⟩⟩

/-- 精确同值域即可传回实际 Def 成员，不额外要求待比较集合属于相对类。 -/
theorem member_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {A H : SecondOrderGraph.code_l ℳ} {a : num_l ℳ}
    {ha : relation_l A.real a A.root} {V E D Q R T F : set_l ℳ}
    (h : SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F H)
    (l c : num_l ℳ) (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    {Y : SecondOrderQuotient.type_l hℳ}
    (hY : ∀ x, mem_l hℳ x Y ↔ ∃ j y, SecondOrderOrder.lt_l j l ∧ read_l E c j y ∧
      x = (SecondOrderMemberStructure.value_l hℳ A a ha y).val) : mem_l hℳ Y (mk_l hℳ H) := by
  obtain ⟨Z, hZH, hZ⟩ := exists_l K h l c hc
  have hEq : Y = Z := SecondOrderQuotient.ext_l hℳ Y Z (fun x => (hY x).trans (hZ x).symm)
  exact hEq.symm ▸ hZH

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefFiniteAssignment
