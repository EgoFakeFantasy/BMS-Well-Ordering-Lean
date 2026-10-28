import BMSConstructibleBridge.PowerlessLegacyAssignmentFrontInsert
import BMSConstructibleBridge.PowerlessLegacyEvaluationTarget

/-! # 原头部存在量词至指定槽存在量词的求值保持

正向对任意给定旧赋值构造实际更新图；反向先用函数定义域唯一性
对齐长度，再由环境枚举的满射取原数值代表。子式保持性明确覆盖
全部正确前插码及全部表示该码的类内赋值，不只覆盖某个所选表示。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationExistential

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessLegacyAssignmentSyntax (link_l)
open PowerlessLegacyEvaluationTarget (number_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

theorem equation_l (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ P F S : type_l hℳ B}
    {W E D Q R T : SecondOrderModel.set_l ℳ}
    (hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω) (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hP : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) P.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K P.val)
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K W c l)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
      ω A e t₁ t₂ t₃ P F S)
    (ht₃ : t₃.val = (numberCode_l K (numeral_l ℳ 3)).val)
    (hE : SecondOrderBinaryPowers.spec_l E) (hD : ∀ v, SecondOrderModel.mem_l v D)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)
    {l c L z p a q : SecondOrderModel.num_l ℳ} {U : SecondOrderQuotient.type_l hℳ}
    {f : type_l hℳ B} (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hLength : SecondOrderOrder.lt_l l L)
    (hLink : link_l K E c l L z U f.val)
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val)
    (hOnto : ∀ y, member_l (SecondOrderQuotient.structure_l hℳ) y A.val →
      ∃ v, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val y)
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 3) l a q)
    (ha : SecondOrderPairing.relation_l W a L)
    (hf : map_l (ℳ := structure_l hℳ B hBase) f (number_l (hBase := hBase) K L) A)
    (hChild : ∀ d : SecondOrderModel.num_l ℳ, ∀ g : type_l hℳ B,
      SecondOrderAssignmentSyntax.valid_l E d (SecondOrderModel.succ_l l) →
      map_l (ℳ := structure_l hℳ B hBase) g (number_l (hBase := hBase) K L) A →
      link_l K E d (SecondOrderModel.succ_l l) L z U g.val →
      (SecondOrderPairing.relation_l T p (SecondOrderPairing.value_l (SecondOrderModel.succ_l l) d) ↔
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K a).val g.val)) :
    SecondOrderPairing.relation_l T (SecondOrderEvaluationEquations.node_l 4 p)
      (SecondOrderPairing.value_l l c) ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K q).val f.val := by
  have hTarget := PowerlessLegacyEvaluationTarget.existential_l (hBase := hBase)
    K hω he hP hPair hF hSat ht₃ hCode hLength ha hf
  refine (SecondOrderEvaluationEquations.existential_l hℳ E D Q R T hT l c p hc).trans
    (Iff.trans ?_ hTarget.symm)
  constructor
  · rintro ⟨v, d, _, hd, hValue⟩
    obtain ⟨x, hx, _⟩ := hU.2 _ (numberCode_l K v).property
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hx.1⟩
    obtain ⟨g, hg, hUpdate, hNewLink⟩ := PowerlessLegacyAssignmentFrontInsert.exists_l
      (hBase := hBase) K hΩ hω hE hc hd hLength hf hLink hU (x := x') hx.2
    have hChildValue := (hChild d g hd.1 hg hNewLink).mp hValue
    have hLω : member_l (structure_l hℳ B hBase) (number_l (hBase := hBase) K L) ω := by
      change SecondOrderQuotient.mem_l hℳ (numberCode_l K L).val ω.val
      rw [hω]
      exact (numberCode_l K L).property
    exact ⟨number_l (hBase := hBase) K L, hLω, hf,
      (numberCode_mem_iff_lt_l K l L).mpr hLength, x', hx.1, g, hg, hUpdate,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) S
        (number_l (hBase := hBase) K a) g).mpr hChildValue⟩
  · rintro ⟨m, _, hfm, _, x, hx, g, hg, hUpdate, hValue⟩
    have hDomain := PowerlessRelativeClassFunctionProperties.domain_unique_l hfm hf
    subst m
    obtain ⟨v, hv⟩ := hOnto x.val hx
    obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l v hc
    have hNewLink := PowerlessLegacyAssignmentUpdateReading.prepend_l (hBase := hBase)
      K hω hd hLength hf hg hUpdate hLink hU hv
    exact ⟨v, d, hD v, hd, (hChild d g hd.1 hg hNewLink).mpr
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) S
        (number_l (hBase := hBase) K a) g).mp hValue)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationExistential
