import BMSConstructibleBridge.SecondOrderRelativeHierarchyClosedFormula
import BMSConstructibleBridge.SecondOrderRelativeHierarchyTheorem

/-! # 原 Z₂ 正式证明闭合相对历史存在

对象句同时要求阶段规格、内部良基、传递与单调。基图的传递性和前驱关系
的三个条件明列于前提，不隐藏完整 Collection；本结论仍非 BMS 最终句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyClosedTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderWellFoundedRecursionTheorem (wellFounded_m transitive_m irreflexive_m)

set_option autoImplicit false

universe u

def sentence_m : Sentence signature_m :=
  .forallE .set <| .forallE .set <| .imp
    (GraphTranslation.domain_m (.bvar (.there .here)) (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (SecondOrderGraphTransitivityFormula.formula_m (.bvar (.there .here))
      (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (wellFounded_m (.bvar .here)) <| .imp (transitive_m (.bvar .here)) <|
    .imp (irreflexive_m (.bvar .here)) <| .existsE .set <|
      SecondOrderRelativeHierarchyClosedFormula.formula_m
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  intro B R hB hBase hWf hTrans hIrrefl
  have hB' : SecondOrderDomain.wf_l B (zero_l ℳ) :=
    (SecondOrderInterpretation.domain_l _ _ _).mp hB
  have hBase' := (SecondOrderGraphTransitivityFormula.formula_l hℳ
    ((Env.empty (M := ℳ)).pushBound B |>.pushBound R) (.bvar (.there .here))
    (Term.app (σ := signature_m) .zero .nil) hB').mp hBase
  have hWf' := (SecondOrderWellFoundedRecursionTheorem.wellFounded_formula_l _ _).mp hWf
  have hTrans' := (SecondOrderWellFoundedRecursionTheorem.transitive_formula_l _ _).mp hTrans
  have hIrrefl' := (SecondOrderWellFoundedRecursionTheorem.irreflexive_formula_l _ _).mp hIrrefl
  obtain ⟨S, hS⟩ := SecondOrderRelativeHierarchy.exists_l hℳ B R hWf' hTrans' hIrrefl'
  refine ⟨S, ?_, ?_, ?_⟩
  · apply (SecondOrderRelativeHierarchyHistoryFormula.formula_l hℳ _ _ _ _).mpr
    intro n W hW
    exact ⟨SecondOrderRelativeHierarchy.rows_wf_l hℳ hB' hWf' hS n W hW, hS n W hW⟩
  · apply (SecondOrderRelativeHierarchyClosedFormula.transitive_formula_l hℳ _ _).mpr
    exact SecondOrderRelativeHierarchyTransitivity.transitive_l hℳ hB' hBase' hWf' hS
  · apply (SecondOrderRelativeHierarchyClosedFormula.monotone_formula_l hℳ _ _ _).mpr
    exact SecondOrderRelativeHierarchyMonotonicity.monotone_l hℳ hB' hBase' hWf' hS

theorem derives_m : Derives theory_m [] sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => models_l hℳ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyClosedTheorem
