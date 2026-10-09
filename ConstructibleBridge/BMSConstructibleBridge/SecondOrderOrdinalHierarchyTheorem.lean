import BMSConstructibleBridge.SecondOrderOrdinalStrongHierarchy
import BMSConstructibleBridge.SecondOrderRootPresentationFormula
import BMSConstructibleBridge.SecondOrderGraphOrdinalFormula

/-! # 实际商序数上的强闭合历史在原 Z₂ 中可推导

对象句输入任意有效序数图根和任意传递零根基图，输出同一模型内的规范
相等图、代表域、前驱关系及强历史。递归条件已由输入序数证明，不再作为
附加前提。这仍不是相对类满足完整源公理的证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalHierarchyTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

def sentence_m : Sentence signature_m :=
  .forallE .set <| .forallE .num <| .forallE .set <| .imp
    (GraphTranslation.domain_m (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
    .imp (SecondOrderGraphOrdinalFormula.formula_m (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
    .imp (GraphTranslation.domain_m (.bvar .here) (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (SecondOrderGraphTransitivityFormula.formula_m (.bvar .here) (Term.app (σ := signature_m) .zero .nil)) <|
    .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .conj
      (SecondOrderRootPresentationFormula.formula_m
        (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)))
      (SecondOrderRelativeHierarchyStrongFormula.formula_m
        (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there .here)) (.bvar .here))

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  intro A r B hA hα hB hBase
  let η := (((Env.empty (M := ℳ)).pushBound A).pushBound r).pushBound B
  have hA' : SecondOrderDomain.wf_l A r := (SecondOrderInterpretation.domain_l _ _ _).mp hA
  have hα' := (SecondOrderGraphOrdinalFormula.formula_l hℳ η
    (.bvar (.there (.there .here))) (.bvar (.there .here)) hA').mp hα
  have hB' : SecondOrderDomain.wf_l B (zero_l ℳ) := (SecondOrderInterpretation.domain_l _ _ _).mp hB
  have hBase' := (SecondOrderGraphTransitivityFormula.formula_l hℳ η (.bvar .here)
    (Term.app (σ := signature_m) .zero .nil) hB').mp hBase
  obtain ⟨Q, D, R, S, hPresentation, hHistory⟩ := SecondOrderOrdinalStrongHierarchy.exists_l hℳ ⟨A, r, hA'⟩ hα' B hB' hBase'
  let ξ := (((η.pushBound Q).pushBound D).pushBound R).pushBound S
  refine ⟨Q, D, R, S, ?_, ?_⟩
  · exact (SecondOrderRootPresentationFormula.formula_l ξ
      (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.bvar (.there (.there (.there (.there (.there .here))))))
      (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)) hA').mpr hPresentation
  · exact (SecondOrderRelativeHierarchyStrongTheorem.formula_l hℳ ξ
      (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there .here)) (.bvar .here) hB').mpr hHistory

theorem derives_m : Derives theory_m [] sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => models_l hℳ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalHierarchyTheorem
