import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseCodingReading
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseDefImage
import BMSConstructibleBridge.PowerlessMemberDefImageRawReading

/-! # 同一坍缩映射下局部原非空 Def 的读回

指定 U 的像 V 保留真实传递性、闭包与全部内部赋值覆盖。原静态图
和旧翻译图的数码读数沿同一个 H 运输，再将全部 raw 查询行族识别
为原 Def。Sat 输入须关于实际统一函数 G 的同一个输出；不预供
目标 Def、Class 资格或完整源模型，也不将此局部读回称为弱凝聚。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseDefReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}


/-- 全部候选行的完整规格给出同一个 D 的原非空 Def，而非其某个子族。 -/
theorem nonempty_l (K : source_coding_l hℳ) {I W T H U V : type_l hℳ}
    (hI : ∃ x, mem_l hℳ x I) (hT : ∃ x, mem_l hℳ x T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) W)
    (hIW : subset_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) I W)
    (hReflect : PowerlessRelativeFiniteHullClosure.pair_matrix_reflection_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) I W)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := (SecondOrderQuotient.structure_l hℳ)) I)
    (hU : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := (SecondOrderQuotient.structure_l hℳ)) U)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) U)
    (hUI : mem_l hℳ U I) (hUV : SecondOrderFunctionObjects.value_l hℳ H U V)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hω : mem_l hℳ K.omega I) (hωU : mem_l hℳ K.omega U)
    (P₀ F₀ C₀ : PowerlessMemberStructure.type_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) I)
    (P F C : PowerlessMemberStructure.type_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) T)
    (hP : PowerlessMemberCollapseTransport.relation_l H P₀ P)
    (hF : PowerlessMemberCollapseTransport.relation_l H F₀ F)
    (hC : PowerlessMemberCollapseTransport.relation_l H C₀ C)
    (hP₀ : PowerlessBMSQuotientPairingBounds.spec_l K P₀.val)
    (hF₀ : ∀ A : SecondOrderModel.set_l ℳ, SecondOrderTriangularFormulaSyntax.spec_l A →
      ∀ c L, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) F₀.val c L ↔ PowerlessRelationalCodeValidity.valid_l K A c L)
    {E : SecondOrderModel.set_l ℳ}
    (hC₀ : ∀ n s, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) C₀.val (numberCode_l K n).val (numberCode_l K s).val ↔
      SecondOrderPairing.relation_l E n s)
    (hE : SecondOrderLegacyFormulaTranslation.spec_l E)
    {e t₁ t₂ t₃ N G A D : type_l hℳ}
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := (SecondOrderQuotient.structure_l hℳ))
      K.omega e t₁ t₂ t₃ P.val N F.val)
    (hEvaluation : ∀ R, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) G A R →
      PowerlessSatisfactionSpecification.spec_l (𝒩 := (SecondOrderQuotient.structure_l hℳ))
        K.omega A e t₁ t₂ t₃ P.val F.val R)
    (hAV : mem_l hℳ A V)
    (hImage : PowerlessMemberDefImageBounded.holds_l (𝒩 := (SecondOrderQuotient.structure_l hℳ))
      K.omega e N C.val V G A D)
    (hA : ∃ x, mem_l hℳ x A) : SecondOrderMemberDef.nonempty_l hℳ A D := by
  obtain ⟨he, ht₁, ht₂, ht₃, hN, hPairMap, hPair, hValid⟩ :=
    PowerlessRelativeMembershipCollapseCodingReading.reading_l K hI hT hH hW hIW
      hReflect hClosed.1 hωI P₀ F₀ P F hP hF hP₀ hF₀ hStatic
  have hNumeric := PowerlessRelativeMembershipCollapseValues.numeric_l K
    hI hT hH hW hIW hReflect hClosed.1 hωI C₀ C hC
  have hTranslation : ∀ n s, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) C.val
      (numberCode_l K n).val (numberCode_l K s).val ↔ SecondOrderPairing.relation_l E n s :=
    fun n s => (hNumeric n s).symm.trans (hC₀ n s)
  obtain ⟨R, S, Q, J, L, _, _, _, _, _, hG, _, hData, hRows⟩ :=
    PowerlessRelativeMembershipCollapseDefImage.collapse_rows_l K
      hH hClosed hU hTrans hUI hUV hωI hω hωU hAV hImage hA
  exact PowerlessMemberDefImageRawReading.identify_l K rfl he ht₁ ht₂ ht₃
    hN hPairMap hPair hValid hTranslation hE (hEvaluation R hG) hData hA hRows

#print axioms nonempty_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseDefReading
