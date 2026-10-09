import BMSConstructibleBridge.SecondOrderRelativeHierarchyHistoryFormula
import BMSConstructibleBridge.SecondOrderWellFoundedRecursionTheorem

/-! # 相对层次历史在原 Z₂ 中的正式推导

原对象句量化基图及内部前驱关系；在基根内部良基及关系内部良基、传递、
非自返的前提下，得到一个编码所有阶段的实数历史。每行满足三类阶段正文
且根内部良基。这不是相对层次的收集／反射结论，更不是 BMS 最终句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderWellFoundedRecursionTheorem (wellFounded_m transitive_m irreflexive_m)

set_option autoImplicit false

universe u

def sentence_m : Sentence signature_m :=
  .forallE .set <| .forallE .set <| .imp
    (GraphTranslation.domain_m (.bvar (.there .here)) (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (wellFounded_m (.bvar .here)) <| .imp (transitive_m (.bvar .here)) <|
    .imp (irreflexive_m (.bvar .here)) <| .existsE .set <|
      SecondOrderRelativeHierarchyHistoryFormula.formula_m
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  intro B R hB hWf hTrans hIrrefl
  have hB' : SecondOrderDomain.wf_l B (zero_l ℳ) :=
    (SecondOrderInterpretation.domain_l _ _ _).mp hB
  have hWf' := (SecondOrderWellFoundedRecursionTheorem.wellFounded_formula_l _ _).mp hWf
  have hTrans' := (SecondOrderWellFoundedRecursionTheorem.transitive_formula_l _ _).mp hTrans
  have hIrrefl' := (SecondOrderWellFoundedRecursionTheorem.irreflexive_formula_l _ _).mp hIrrefl
  obtain ⟨S, hS⟩ := SecondOrderRelativeHierarchy.exists_l hℳ B R hWf' hTrans' hIrrefl'
  refine ⟨S, ?_⟩
  apply (SecondOrderRelativeHierarchyHistoryFormula.formula_l hℳ _ _ _ _).mpr
  intro n W hW
  exact ⟨SecondOrderRelativeHierarchy.rows_wf_l hℳ hB' hWf' hS n W hW, hS n W hW⟩

theorem derives_m : Derives theory_m [] sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => models_l hℳ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyTheorem
