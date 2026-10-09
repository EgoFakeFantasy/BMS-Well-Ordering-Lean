import BMSConstructibleBridge.PowerlessSatisfactionSpecification
import BMSConstructibleBridge.PowerlessBMSQuotientTriangularSyntax
import BMSConstructibleBridge.PowerlessRelationalCodeValidity

/-! # 完整原商 Sat 的内部数码分支

背景为原 Z₂ 模型，消费原纯隶属语言中的完整 Sat 规格。构造子和
合法性均读取同一内部编码 K；赋值是任意原商有限图，不要求属于
Class 或某个可构造层。存在分支保留全部原商更新图，不改为有界
检查器。这是原旧码求值保持归纳的中间接口，不是最终良序推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRawTarget

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

variable (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ P F R : type_l hℳ}
  (hω : ω = K.omega) (he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
  (hP : map_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) P K.omega K.omega)
  (hPair : PowerlessBMSQuotientPairingBounds.spec_l K P)

include hω he hP hPair

/-- 直接读取原商构造子，不经过 Class 的加法绝对性。 -/
theorem constructor_l {tag : type_l hℳ} {k i j n : SecondOrderModel.num_l ℳ}
    (hTag : tag = (numberCode_l K k).val)
    (hCode : SecondOrderTriangularConstructor.constructor_l k i j n) :
    PowerlessFormulaConstructor.constructor_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) ω e P tag
      (numberCode_l K i).val (numberCode_l K j).val (numberCode_l K n).val := by
  subst ω
  subst e
  subst tag
  exact (PowerlessBMSQuotientTriangularSyntax.constructor_l K hP hPair k i j n).mpr hCode

variable (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := (SecondOrderQuotient.structure_l hℳ))
  ω A e t₁ t₂ t₃ P F R)

include hSat

omit hω hP hPair in
theorem zero_l (f : type_l hℳ) :
    ¬value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) R (numberCode_l K (SecondOrderModel.zero_l ℳ)).val f :=
  he ▸ hSat.2.1 f

theorem equality_l (ht₁ : t₁ = (numberCode_l K (numeral_l ℳ 1)).val)
    {n i j L : SecondOrderModel.num_l ℳ} {f : type_l hℳ}
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 1) i j n)
    (hi : SecondOrderOrder.lt_l i L) (hj : SecondOrderOrder.lt_l j L)
    (hMap : map_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) f (numberCode_l K L).val A) :
    value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) R (numberCode_l K n).val f ↔
      PowerlessEvaluationClause.equal_l (ℳ := (SecondOrderQuotient.structure_l hℳ))
        f (numberCode_l K i).val (numberCode_l K j).val :=
  (hSat.2.2 (numberCode_l K n).val (numberCode_l K L).val f
    (hω.symm ▸ (numberCode_l K n).property) (hω.symm ▸ (numberCode_l K L).property)
    hMap (numberCode_l K i).val (numberCode_l K j).val).2.1
      (constructor_l K hω he hP hPair ht₁ hCode)
      ((numberCode_mem_iff_lt_l K i L).mpr hi) ((numberCode_mem_iff_lt_l K j L).mpr hj)

theorem membership_l {n i j L : SecondOrderModel.num_l ℳ} {f : type_l hℳ}
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 0) i j n)
    (hi : SecondOrderOrder.lt_l i L) (hj : SecondOrderOrder.lt_l j L)
    (hMap : map_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) f (numberCode_l K L).val A) :
    value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) R (numberCode_l K n).val f ↔
      PowerlessEvaluationClause.member_l (ℳ := (SecondOrderQuotient.structure_l hℳ))
        f (numberCode_l K i).val (numberCode_l K j).val :=
  (hSat.2.2 (numberCode_l K n).val (numberCode_l K L).val f
    (hω.symm ▸ (numberCode_l K n).property) (hω.symm ▸ (numberCode_l K L).property)
    hMap (numberCode_l K i).val (numberCode_l K j).val).1
      (constructor_l K hω he hP hPair he hCode)
      ((numberCode_mem_iff_lt_l K i L).mpr hi) ((numberCode_mem_iff_lt_l K j L).mpr hj)

variable {W : SecondOrderModel.set_l ℳ}
  (hF : ∀ c l, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) F c l ↔ PowerlessRelationalCodeValidity.valid_l K W c l)

include hF

theorem nand_l (ht₂ : t₂ = (numberCode_l K (numeral_l ℳ 2)).val)
    {n a b L : SecondOrderModel.num_l ℳ} {f : type_l hℳ}
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 2) a b n)
    (ha : SecondOrderPairing.relation_l W a L) (hb : SecondOrderPairing.relation_l W b L)
    (hMap : map_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) f (numberCode_l K L).val A) :
    value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) R (numberCode_l K n).val f ↔
      ¬(value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) R (numberCode_l K a).val f ∧
        value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) R (numberCode_l K b).val f) :=
  (hSat.2.2 (numberCode_l K n).val (numberCode_l K L).val f
    (hω.symm ▸ (numberCode_l K n).property) (hω.symm ▸ (numberCode_l K L).property)
    hMap (numberCode_l K a).val (numberCode_l K b).val).2.2.1
      (constructor_l K hω he hP hPair ht₂ hCode)
      ((hF _ _).mpr ⟨a, L, rfl, rfl, ha⟩) ((hF _ _).mpr ⟨b, L, rfl, rfl, hb⟩)

theorem existential_l (ht₃ : t₃ = (numberCode_l K (numeral_l ℳ 3)).val)
    {n i b L : SecondOrderModel.num_l ℳ} {f : type_l hℳ}
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 3) i b n)
    (hi : SecondOrderOrder.lt_l i L) (hb : SecondOrderPairing.relation_l W b L)
    (hMap : map_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) f (numberCode_l K L).val A) :
    value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) R (numberCode_l K n).val f ↔
      PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := (SecondOrderQuotient.structure_l hℳ))
        ω A R f (numberCode_l K i).val (numberCode_l K b).val :=
  (hSat.2.2 (numberCode_l K n).val (numberCode_l K L).val f
    (hω.symm ▸ (numberCode_l K n).property) (hω.symm ▸ (numberCode_l K L).property)
    hMap (numberCode_l K i).val (numberCode_l K b).val).2.2.2
      (constructor_l K hω he hP hPair ht₃ hCode)
      ((numberCode_mem_iff_lt_l K i L).mpr hi) ((hF _ _).mpr ⟨b, L, rfl, rfl, hb⟩)

#print axioms constructor_l
#print axioms zero_l
#print axioms equality_l
#print axioms membership_l
#print axioms nand_l
#print axioms existential_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRawTarget
