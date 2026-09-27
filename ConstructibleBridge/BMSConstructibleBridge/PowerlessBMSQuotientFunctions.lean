import BMSConstructibleBridge.PowerlessBMSQuotientCoding
import BMSConstructibleBridge.SecondOrderRelationImage

/-!
# 从 Z₂ 二阶关系提升 quotient 上的全函数图

任意目标模型中由二阶关系实数给出的全函数，都能经根码像构造成 quotient 上的
`map_l`。构造逐成员使用关系像，不先收集整个 `ω × ω` 乘积，也不调用源 quotient
上的 Collection。该接口本身不证明零、后继、加法或乘法的关系前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientFunctions

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

private theorem ordered_iff_l (a b p : SecondOrderQuotient.type_l hM) :
    SecondOrderPairObjects.ordered_l hM a b p ↔
      ThirdOrderSemantics.ordered_l
        (ℳ := SecondOrderQuotient.structure_l hM) a b p := by
  rfl

/-- 任意目标数域上的全函数关系提升为 quotient 内部 ω 上的全函数图。 -/
theorem exists_map_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (S : SecondOrderModel.set_l M)
    (hTotal : ∀ a, ∃ b, SecondOrderPairing.relation_l S a b)
    (hUnique : ∀ a b c, SecondOrderPairing.relation_l S a b →
      SecondOrderPairing.relation_l S a c → b = c) :
    ∃ f : SecondOrderQuotient.type_l hM,
      ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM)
        f C.omega C.omega := by
  have hRoots (a b : SecondOrderModel.num_l M)
      (_ : SecondOrderPairing.relation_l S a b) :
      SecondOrderDomain.wf_l C.less a ∧ SecondOrderDomain.wf_l C.less b :=
    ⟨SecondOrderNaturalGraph.wf_l hM C.less C.less_spec a,
      SecondOrderNaturalGraph.wf_l hM C.less C.less_spec b⟩
  obtain ⟨f, hf⟩ := SecondOrderRelationImage.quotient_l hM C.less S hRoots
  refine ⟨f, ?_⟩
  constructor
  · intro p hp
    change SecondOrderQuotient.mem_l hM p f at hp
    obtain ⟨a, b, hab, hp⟩ := (hf p).mp hp
    refine ⟨(PowerlessBMSQuotientCoding.numberCode_l C a).val,
      (PowerlessBMSQuotientCoding.numberCode_l C b).val, ?_, ?_, ?_⟩
    · exact (PowerlessBMSQuotientCoding.numberCode_l C a).property
    · exact (PowerlessBMSQuotientCoding.numberCode_l C b).property
    · exact (ordered_iff_l _ _ _).mp hp
  · intro x hx
    change SecondOrderQuotient.mem_l hM x C.omega at hx
    let xNum : PowerlessArithmetic.num_l
      (ℳ := SecondOrderQuotient.structure_l hM) C.omega := ⟨x, hx⟩
    obtain ⟨a, ha⟩ := PowerlessBMSQuotientCoding.numberCode_surjective_l C xNum
    have hxa : (PowerlessBMSQuotientCoding.numberCode_l C a).val = x :=
      congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := hTotal a
    let yNum := PowerlessBMSQuotientCoding.numberCode_l C b
    have hy : SecondOrderQuotient.mem_l hM yNum.val C.omega := yNum.property
    obtain ⟨p, hpair⟩ := SecondOrderPairObjects.ordered_exists_l hM
      (PowerlessBMSQuotientCoding.numberCode_l C a).val yNum.val
    have hp : SecondOrderQuotient.mem_l hM p f := (hf p).mpr ⟨a, b, hb, hpair⟩
    have hValue : ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hM)
        f x yNum.val := by
      refine ⟨p, hp, ?_⟩
      rw [← hxa]
      exact (ordered_iff_l _ _ _).mp hpair
    refine ⟨yNum.val, ⟨hy, hValue⟩, ?_⟩
    intro z hz
    rcases hz with ⟨hzMem, q, hqMem, hqOrdered⟩
    change SecondOrderQuotient.mem_l hM z C.omega at hzMem
    change SecondOrderQuotient.mem_l hM q f at hqMem
    obtain ⟨a', b', ha'b', hqPair⟩ := (hf q).mp hqMem
    have hCoordinates := (SecondOrderPairObjects.ordered_eq_l hM hqPair
      ((ordered_iff_l _ _ _).mpr hqOrdered)).mp rfl
    have hCodeEq := hCoordinates.1.trans hxa.symm
    change SecondOrderQuotient.mk_l hM
      (SecondOrderNaturalGraph.code_l hM C.less C.less_spec a') =
        SecondOrderQuotient.mk_l hM
          (SecondOrderNaturalGraph.code_l hM C.less C.less_spec a) at hCodeEq
    have haEq : a' = a :=
      (SecondOrderNaturalNumbers.eq_l hM C.less C.less_spec a' a).mp
        ((SecondOrderQuotient.eq_iff_l hM _ _).mp hCodeEq)
    have ha'b : SecondOrderPairing.relation_l S a b' := by
      rw [← haEq]
      exact ha'b'
    have hbEq := hUnique a b' b ha'b hb
    have hzy : z = yNum.val := by
      change z = (PowerlessBMSQuotientCoding.numberCode_l C b).val
      rw [← hbEq]
      exact hCoordinates.2.symm
    exact hzy

#print axioms exists_map_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientFunctions
