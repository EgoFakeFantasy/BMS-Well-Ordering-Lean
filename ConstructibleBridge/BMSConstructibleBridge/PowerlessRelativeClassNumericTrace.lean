import BMSConstructibleBridge.SecondOrderRelationBoolean
import BMSConstructibleBridge.SecondOrderQuotientNumericFunction
import BMSConstructibleBridge.SecondOrderFunctionRestriction
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives

/-! # 任意内部数函数的有限前段属于相对类

总图先在原商中构造，其内部有限限制属于既有 Seq(ω)，因此留在类中。
原函数实数、无限总图均不要求属于类。零一实例用于内部合法性检查表；
本定理不把全部有限前段收集为类内无限图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNumericTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l (K : source_coding_l hℳ) {ω : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderFunctions.function_l E) (n : SecondOrderModel.num_l ℳ) :
    ∃ f : type_l hℳ B,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val (numberCode_l K n).val K.omega ∧
      ∀ i j, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val (numberCode_l K i).val (numberCode_l K j).val ↔
        SecondOrderOrder.lt_l i n ∧ SecondOrderPairing.relation_l E i j := by
  obtain ⟨F, hF, hRead⟩ := SecondOrderQuotientNumericFunction.exists_l K hE
  obtain ⟨f, hf, hRestrict⟩ := SecondOrderFunctionRestriction.exists_l hℳ
    (S := (numberCode_l K n).val) hF
    (fun x hx => SecondOrderOmegaTransitive.member_l hℳ (k := (numberCode_l K n).val)
      K.omega_spec (numberCode_l K n).property hx)
  obtain ⟨S, hS, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (X := ω) hω
  have hfS : mem_l hℳ f S.val := (hS f).mpr
    ⟨(numberCode_l K n).val, hωEq.symm ▸ (numberCode_l K n).property, hωEq.symm ▸ hf⟩
  refine ⟨⟨f, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase S.property hfS⟩, hf, ?_⟩
  intro i j
  have hValue : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F
      (numberCode_l K i).val (numberCode_l K j).val ↔ SecondOrderPairing.relation_l E i j := by
    rw [hRead]
    constructor
    · rintro ⟨k, hk, hEq⟩
      have hjk : j = k := numberCode_injective_l K (Subtype.ext hEq)
      exact hjk.symm ▸ hk
    · exact fun h => ⟨j, h, rfl⟩
  exact (hRestrict _ _).trans (and_congr (numberCode_mem_iff_lt_l K i n) hValue)

theorem boolean_l (K : source_coding_l hℳ) {ω : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)
    (V : SecondOrderModel.set_l ℳ) (l n : SecondOrderModel.num_l ℳ) :
    ∃ f : type_l hℳ B,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val (numberCode_l K n).val K.omega ∧
      ∀ i j, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val (numberCode_l K i).val (numberCode_l K j).val ↔
        SecondOrderOrder.lt_l i n ∧
          ((SecondOrderPairing.relation_l V i l ∧ j = SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)) ∨
            (¬SecondOrderPairing.relation_l V i l ∧ j = SecondOrderModel.zero_l ℳ)) := by
  obtain ⟨E, hE, hSpec⟩ := SecondOrderRelationBoolean.exists_l hℳ V l
  obtain ⟨f, hf, hRead⟩ := exists_l K hω hωEq hE n
  exact ⟨f, hf, fun i j => (hRead i j).trans (and_congr Iff.rfl (hSpec i j))⟩

#print axioms exists_l
#print axioms boolean_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNumericTrace
