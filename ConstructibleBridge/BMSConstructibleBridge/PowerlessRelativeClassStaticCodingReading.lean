import BMSConstructibleBridge.PowerlessRelativeClassTriangularSpecification
import BMSConstructibleBridge.PowerlessRelativeClassValidityAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassSequenceAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassSyntaxReading
import BMSConstructibleBridge.PowerlessSatisfactionExistenceSyntax

/-! # 固定编码下的原静态包读数

给定同一 K 及类内 ω 与 K.omega 的实际相等，把原纯静态规格中的零码、
三个标签、完整 Seq(ω,ω)、三角图和合法性图读回原商。全部结论仍关于
给定的 e、标签、N、T、F；不重新选择编码或替换任何图。

合法性读数对每个满足原内部三角合法性规格的实数 V 及全部 raw 坐标成立，
不只核验外部标准数码。这里只提取静态包接口，不构造共同界或 Sat 图，
也不宣称对象推导终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassStaticCodingReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

/-- 固定 K 的静态包给出原商上的完整数码、序列、配对及合法性读数。 -/
theorem reading_l (K : source_coding_l hℳ) {ω e t₁ t₂ t₃ T N F : type_l hℳ B}
    (hωEq : ω.val = K.omega)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := structure_l hℳ B hBase)
      ω e t₁ t₂ t₃ T N F) :
    e.val = code_l K (numeral_l ℳ 0) ∧
      t₁.val = code_l K (numeral_l ℳ 1) ∧
        t₂.val = code_l K (numeral_l ℳ 2) ∧
          t₃.val = code_l K (numeral_l ℳ 3) ∧
            PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
              K.omega K.omega N.val ∧
            map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega ∧
            PowerlessBMSQuotientPairingBounds.spec_l K T.val ∧
              ∀ V : SecondOrderModel.set_l ℳ, SecondOrderTriangularFormulaSyntax.spec_l V →
                ∀ c L, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c L ↔
                  PowerlessRelationalCodeValidity.valid_l K V c L := by
  have hω : omega_l (ℳ := structure_l hℳ B hBase) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr
      (hωEq.symm ▸ K.omega_spec)
  have he : e.val = code_l K (numeral_l ℳ 0) :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false
      ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp hStatic.1.1 x)
      (PowerlessBMSQuotientSuccessor.zero_l K x))
  have ht := PowerlessRelativeClassSyntaxReading.tags_l K he hStatic.1
  have hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N.val := by
    simpa only [hωEq] using PowerlessRelativeClassSequenceAbsolute.spec_l hω hStatic.2.2.2.1
  have hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega := by
    simpa only [ThirdOrderSemantics.map_l, ThirdOrderSemantics.member_l, ThirdOrderSemantics.value_l,
      ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l, SecondOrderQuotient.structure_l,
      SecondOrderFunctionObjects.map_l, SecondOrderFunctionObjects.value_l,
      SecondOrderPairObjects.ordered_l, SecondOrderPairObjects.pair_l, hωEq]
      using (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) T ω ω).mp hStatic.2.1.1
  have hPair := PowerlessRelativeClassTriangularSpecification.spec_l
    (N := N) K hωEq he hN hStatic.2.1
  refine ⟨he, ht.1, ht.2.1, ht.2.2, hN, hT, hPair, ?_⟩
  intro V hV
  exact PowerlessRelativeClassValidityAbsolute.reading_l K hω hωEq he hStatic.1
    hT hPair hV hN hStatic.2.2.2.2

#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassStaticCodingReading
