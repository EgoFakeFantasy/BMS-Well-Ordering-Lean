import BMSConstructibleBridge.PowerlessRelativeClassPowerIteration
import BMSConstructibleBridge.PowerlessRelativeClassRelationReal

/-! # 指定原幂实数的实际 Class 表示

任意内部底数的完整幂图先由类内迭代取得，再通过原配数编码表示同一
原实数。底数和指数不要求外部标准；见证只在 Prop 中存在，不抽取
Type 层实数选择族。本模块不宣称截断源已满足完整 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPowersReal

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase

theorem graph_l (K : source_coding_l hℳ) {ω : type_l hℳ B}
    (hω : ω.val = K.omega) {i : SecondOrderModel.num_l ℳ}
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderPowers.spec_l i E) :
    ∃ F : type_l hℳ B, ∀ n m,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val
        (numberCode_l K n).val (numberCode_l K m).val ↔ SecondOrderPairing.relation_l E n m := by
  let number (n : SecondOrderModel.num_l ℳ) : type_l hℳ B :=
    ⟨(numberCode_l K n).val, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
      ω.property (by rw [hω]; exact (numberCode_l K n).property)⟩
  obtain ⟨_H, F, _hH, _hMultiply, _hIterate, hRead⟩ :=
    PowerlessRelativeClassPowerIteration.exists_l (hBase := hBase) K hE hω
      (ω := ω) (e := number (SecondOrderModel.zero_l ℳ)) (a := number i)
      (one := number (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))) rfl rfl rfl
  refine ⟨F, fun n m => ?_⟩
  refine (hRead n (numberCode_l K m).val).trans ⟨?_, ?_⟩
  · rintro ⟨j, hj, hEq⟩
    have hJM : m = j := numberCode_injective_l K (Subtype.ext hEq)
    exact hJM.symm ▸ hj
  · intro h
    exact ⟨m, h, rfl⟩

theorem represents_l (K : source_coding_l hℳ) {ω : type_l hℳ B}
    (hω : ω.val = K.omega) {i : SecondOrderModel.num_l ℳ}
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderPowers.spec_l i E) :
    ∃ U : type_l hℳ B, ∃ hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega,
      setRel_l K ⟨U.val, hU⟩ E := by
  obtain ⟨F, hF⟩ := graph_l (hBase := hBase) K hω hE
  exact PowerlessRelativeClassRelationReal.represents_l (hBase := hBase) K F E hF

theorem binary_exists_l (K : source_coding_l hℳ) {ω : type_l hℳ B}
    (hω : ω.val = K.omega) :
    ∃ E : SecondOrderModel.set_l ℳ, SecondOrderBinaryPowers.spec_l E ∧
      ∃ U : type_l hℳ B, ∃ hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega,
        setRel_l K ⟨U.val, hU⟩ E := by
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  obtain ⟨U, hU, hRep⟩ := represents_l (hBase := hBase) K hω hE
  exact ⟨E, hE, U, hU, hRep⟩

#print axioms graph_l
#print axioms represents_l
#print axioms binary_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPowersReal
