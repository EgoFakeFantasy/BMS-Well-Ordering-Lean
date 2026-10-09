import BMSConstructibleBridge.PowerlessFormulaValiditySpecification
import BMSConstructibleBridge.PowerlessRelativeClassValueCoordinates

/-! # 给定合法性图的全原商规格

类内图的坐标闭包和查询自带的 ω 守卫分别处理两个方向。由此保留调用者
的原 F，而非重新选择具有较强规格的另一张图；再接同一编码的实际 V。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassValidityAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  {ω e N T t₁ t₂ t₃ F : type_l hℳ B}

theorem spec_l
    (hF : PowerlessFormulaValiditySpecification.spec_l (𝒩 := structure_l hℳ B hBase) ω e N T t₁ t₂ t₃ F) :
    PowerlessFormulaValiditySpecification.spec_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val N.val T.val t₁.val t₂.val t₃.val F.val := by
  intro c l
  constructor
  · intro hValue
    obtain ⟨hc, hl⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase F hValue
    let c' : type_l hℳ B := ⟨c, hc⟩
    let l' : type_l hℳ B := ⟨l, hl⟩
    exact (PowerlessFormulaValiditySpecification.query_absolute_l (hBase := hBase) ω e N T t₁ t₂ t₃ c' l').mp
      ((hF c' l').mp ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F c' l').mpr hValue))
  · intro hQuery
    let c' : type_l hℳ B := ⟨c, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hQuery.1⟩
    let l' : type_l hℳ B := ⟨l, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hQuery.2.1⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F c' l').mp
      ((hF c' l').mpr ((PowerlessFormulaValiditySpecification.query_absolute_l
        (hBase := hBase) ω e N T t₁ t₂ t₃ c' l').mpr hQuery))

theorem reading_l (K : source_coding_l hℳ)
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)
    (he : e.val = PowerlessFormulaValidityReading.code_l K (SecondOrderModel.zero_l ℳ))
    (ht : PowerlessEvaluationTags.tags_l (ℳ := structure_l hℳ B hBase) e t₁ t₂ t₃)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N.val)
    (hF : PowerlessFormulaValiditySpecification.spec_l (𝒩 := structure_l hℳ B hBase) ω e N T t₁ t₂ t₃ F) :
    ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l := by
  intro c l
  exact (spec_l hF c l).trans
    (PowerlessRelativeClassValidity.query_iff_l K hω hωEq he ht hT hSpec hV hN c l)

#print axioms spec_l
#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassValidityAbsolute
