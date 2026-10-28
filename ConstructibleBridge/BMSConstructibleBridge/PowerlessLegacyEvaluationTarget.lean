import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionSpecification
import BMSConstructibleBridge.PowerlessRelativeClassEvaluationAtomicAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassInduction

/-! # 实际类内 Sat 的原内部数码分支接口

直接消费已经构造的 Sat 规格与合法性图。原四标签构造子经明确的
编码对应搬入类内，再把原子和 NAND 的读数搬回环境商。存在分支
保留实际类内更新图，供原头部前插的保持性证明使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationTarget

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

abbrev number_l (K : source_coding_l hℳ) (n : SecondOrderModel.num_l ℳ) : type_l hℳ B :=
  PowerlessRelativeClassInduction.number_l (hBase := hBase) K n

variable (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ P F R : type_l hℳ B}
  {W : SecondOrderModel.set_l ℳ} (hω : ω.val = K.omega)
  (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
  (hP : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) P.val K.omega K.omega)
  (hPair : PowerlessBMSQuotientPairingBounds.spec_l K P.val)

include hω he hP hPair

theorem constructor_l {tag : type_l hℳ B} {k i j n : SecondOrderModel.num_l ℳ}
    (hTag : tag.val = (numberCode_l K k).val)
    (hCode : SecondOrderTriangularConstructor.constructor_l k i j n) :
    PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e P tag
      (number_l (hBase := hBase) K i) (number_l (hBase := hBase) K j) (number_l (hBase := hBase) K n) := by
  have hRaw := (PowerlessBMSQuotientTriangularSyntax.constructor_l K hP hPair k i j n).mpr hCode
  change PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
    K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val P.val (numberCode_l K k).val
      (numberCode_l K i).val (numberCode_l K j).val (numberCode_l K n).val at hRaw
  apply PowerlessRelativeClassConstructorTotal.constructor_from_ambient_l K hω he hP hPair
  simpa only [hTag, number_l, PowerlessRelativeClassInduction.number_l] using hRaw

variable (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
    PowerlessRelationalCodeValidity.valid_l K W c l)
  (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
    ω A e t₁ t₂ t₃ P F R)

include hF hSat

omit hω he hP hPair hSat in
private theorem valid_l {n L : SecondOrderModel.num_l ℳ} (h : SecondOrderPairing.relation_l W n L) :
    value_l (ℳ := structure_l hℳ B hBase) F (number_l (hBase := hBase) K n) (number_l (hBase := hBase) K L) :=
  (PowerlessRelativeClassSatisfactionSpecification.validity_l K hF rfl rfl).mpr h

omit he hP hPair hF in
private theorem equations_l (n L : SecondOrderModel.num_l ℳ) {f : type_l hℳ B}
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f (number_l (hBase := hBase) K L) A) :
    ∀ a b : type_l hℳ B,
      (PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase)
        ω e P e a b (number_l (hBase := hBase) K n) →
        member_l (structure_l hℳ B hBase) a (number_l (hBase := hBase) K L) →
        member_l (structure_l hℳ B hBase) b (number_l (hBase := hBase) K L) →
        (value_l (ℳ := structure_l hℳ B hBase) R (number_l (hBase := hBase) K n) f ↔
          PowerlessEvaluationClause.member_l (ℳ := structure_l hℳ B hBase) f a b)) ∧
      (PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase)
        ω e P t₁ a b (number_l (hBase := hBase) K n) →
        member_l (structure_l hℳ B hBase) a (number_l (hBase := hBase) K L) →
        member_l (structure_l hℳ B hBase) b (number_l (hBase := hBase) K L) →
        (value_l (ℳ := structure_l hℳ B hBase) R (number_l (hBase := hBase) K n) f ↔
          PowerlessEvaluationClause.equal_l (ℳ := structure_l hℳ B hBase) f a b)) ∧
      (PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase)
        ω e P t₂ a b (number_l (hBase := hBase) K n) →
        value_l (ℳ := structure_l hℳ B hBase) F a (number_l (hBase := hBase) K L) →
        value_l (ℳ := structure_l hℳ B hBase) F b (number_l (hBase := hBase) K L) →
        (value_l (ℳ := structure_l hℳ B hBase) R (number_l (hBase := hBase) K n) f ↔
          ¬(value_l (ℳ := structure_l hℳ B hBase) R a f ∧
            value_l (ℳ := structure_l hℳ B hBase) R b f))) ∧
      (PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase)
        ω e P t₃ a b (number_l (hBase := hBase) K n) →
        member_l (structure_l hℳ B hBase) a (number_l (hBase := hBase) K L) →
        value_l (ℳ := structure_l hℳ B hBase) F b (number_l (hBase := hBase) K L) →
        (value_l (ℳ := structure_l hℳ B hBase) R (number_l (hBase := hBase) K n) f ↔
          PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := structure_l hℳ B hBase)
            ω A R f a b)) := by
  have hn : member_l (structure_l hℳ B hBase) (number_l (hBase := hBase) K n) ω := by
    change SecondOrderQuotient.mem_l hℳ (numberCode_l K n).val ω.val
    rw [hω]
    exact (numberCode_l K n).property
  have hL : member_l (structure_l hℳ B hBase) (number_l (hBase := hBase) K L) ω := by
    change SecondOrderQuotient.mem_l hℳ (numberCode_l K L).val ω.val
    rw [hω]
    exact (numberCode_l K L).property
  exact hSat.2.2 (number_l (hBase := hBase) K n) (number_l (hBase := hBase) K L) f hn hL hMap

omit hω hP hPair hF in
theorem zero_l (f : type_l hℳ B) :
    ¬value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val f.val := by
  intro h
  have h' : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val e.val f.val := he.symm ▸ h
  exact hSat.2.1 f ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R e f).mpr h')

omit hF in
theorem equality_l (ht₁ : t₁.val = (numberCode_l K (numeral_l ℳ 1)).val)
    {n i j L : SecondOrderModel.num_l ℳ} {f : type_l hℳ B}
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 1) i j n)
    (hi : SecondOrderOrder.lt_l i L) (hj : SecondOrderOrder.lt_l j L)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f (number_l (hBase := hBase) K L) A) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val (numberCode_l K n).val f.val ↔
      PowerlessEvaluationClause.equal_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        f.val (numberCode_l K i).val (numberCode_l K j).val := by
  have hEq := (equations_l K hω hSat n L hMap (number_l (hBase := hBase) K i) (number_l (hBase := hBase) K j)).2.1
    (constructor_l K hω he hP hPair ht₁ hCode)
    ((numberCode_mem_iff_lt_l K i L).mpr hi) ((numberCode_mem_iff_lt_l K j L).mpr hj)
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R (number_l (hBase := hBase) K n) f).symm.trans
    (hEq.trans (PowerlessRelativeClassEvaluationAtomicAbsolute.equality_l hMap))

omit hF in
theorem membership_l {n i j L : SecondOrderModel.num_l ℳ} {f : type_l hℳ B}
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 0) i j n)
    (hi : SecondOrderOrder.lt_l i L) (hj : SecondOrderOrder.lt_l j L)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f (number_l (hBase := hBase) K L) A) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val (numberCode_l K n).val f.val ↔
      PowerlessEvaluationClause.member_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        f.val (numberCode_l K i).val (numberCode_l K j).val := by
  have hEq := (equations_l K hω hSat n L hMap (number_l (hBase := hBase) K i) (number_l (hBase := hBase) K j)).1
    (constructor_l K hω he hP hPair he hCode)
    ((numberCode_mem_iff_lt_l K i L).mpr hi) ((numberCode_mem_iff_lt_l K j L).mpr hj)
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R (number_l (hBase := hBase) K n) f).symm.trans
    (hEq.trans (PowerlessRelativeClassEvaluationAtomicAbsolute.membership_l hMap))

theorem nand_l (ht₂ : t₂.val = (numberCode_l K (numeral_l ℳ 2)).val)
    {n a b L : SecondOrderModel.num_l ℳ} {f : type_l hℳ B}
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 2) a b n)
    (ha : SecondOrderPairing.relation_l W a L) (hb : SecondOrderPairing.relation_l W b L)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f (number_l (hBase := hBase) K L) A) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val (numberCode_l K n).val f.val ↔
      ¬(value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val (numberCode_l K a).val f.val ∧
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val (numberCode_l K b).val f.val) := by
  have hEq := (equations_l K hω hSat n L hMap (number_l (hBase := hBase) K a) (number_l (hBase := hBase) K b)).2.2.1
    (constructor_l K hω he hP hPair ht₂ hCode) (valid_l K hF ha) (valid_l K hF hb)
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R (number_l (hBase := hBase) K n) f).symm.trans
    (hEq.trans (not_congr (and_congr
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R (number_l (hBase := hBase) K a) f)
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R (number_l (hBase := hBase) K b) f))))

theorem existential_l (ht₃ : t₃.val = (numberCode_l K (numeral_l ℳ 3)).val)
    {n i b L : SecondOrderModel.num_l ℳ} {f : type_l hℳ B}
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 3) i b n)
    (hi : SecondOrderOrder.lt_l i L) (hb : SecondOrderPairing.relation_l W b L)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f (number_l (hBase := hBase) K L) A) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val (numberCode_l K n).val f.val ↔
      PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := structure_l hℳ B hBase)
        ω A R f (number_l (hBase := hBase) K i) (number_l (hBase := hBase) K b) := by
  have hEq := (equations_l K hω hSat n L hMap (number_l (hBase := hBase) K i) (number_l (hBase := hBase) K b)).2.2.2
    (constructor_l K hω he hP hPair ht₃ hCode) ((numberCode_mem_iff_lt_l K i L).mpr hi) (valid_l K hF hb)
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R (number_l (hBase := hBase) K n) f).symm.trans hEq

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationTarget
