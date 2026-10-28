import BMSConstructibleBridge.SecondOrderRelativeHierarchyMonotonicityStep
import BMSConstructibleBridge.SecondOrderRelativeHierarchyTransitivity

/-! # 相对层次的内部单调性

对实际“每个前驱行包含于当前行”公式作内部良基归纳。图根证书由同一历史
的良基性给出；索引覆盖模型所有数，不借助外部良基性或逐行选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyMonotonicity

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderRelativeHierarchyMonotonicityStep (rows_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def rows_m : Formula signature_m [] [.num, .set, .set] :=
  .forallE .num <| .forallE .set <| .forallE .set <| .imp
    (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there (.there .here))) (.fvar .here)) <|
    .imp (SecondOrderSections.formula_m (.fvar (.there .here)) (.bvar (.there .here))
      (.bvar (.there (.there .here)))) <|
    .imp (SecondOrderSections.formula_m (.fvar (.there .here)) (.bvar .here) (.fvar .here)) <|
    .imp (GraphTranslation.domain_m (.bvar (.there .here)) (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (GraphTranslation.domain_m (.bvar .here) (Term.app (σ := signature_m) .zero .nil))
      (SecondOrderGraphSubsetFormula.formula_m (.bvar (.there .here)) (.bvar .here)
        (Term.app (σ := signature_m) .zero .nil) (Term.app (σ := signature_m) .zero .nil))

theorem pure_m : language_m rows_m = true := by
  have hEdge : language_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set])
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there (.there .here))) (.fvar .here)) = true := rfl
  have hU := SecondOrderSections.pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set])
    (.fvar (.there .here)) (.bvar (.there .here)) (.bvar (.there (.there .here))) rfl rfl rfl
  have hW := SecondOrderSections.pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set])
    (.fvar (.there .here)) (.bvar .here) (.fvar .here) rfl rfl rfl
  have hUD := GraphTranslation.domain_pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set])
    (.bvar (.there .here)) (Term.app (σ := signature_m) .zero .nil) rfl rfl
  have hWD := GraphTranslation.domain_pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set])
    (.bvar .here) (Term.app (σ := signature_m) .zero .nil) rfl rfl
  have hSubset := SecondOrderGraphSubsetFormula.pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set])
    (.bvar (.there .here)) (.bvar .here) (Term.app (σ := signature_m) .zero .nil)
    (Term.app (σ := signature_m) .zero .nil) rfl rfl rfl rfl
  exact SecondOrderFormulaArguments.forall_pure_m .num _
    (SecondOrderFormulaArguments.forall_pure_m .set _
      (SecondOrderFormulaArguments.forall_pure_m .set _
        (SecondOrderFormulaArguments.imp_pure_m _ _ hEdge
          (SecondOrderFormulaArguments.imp_pure_m _ _ hU
            (SecondOrderFormulaArguments.imp_pure_m _ _ hW
              (SecondOrderFormulaArguments.imp_pure_m _ _ hUD
                (SecondOrderFormulaArguments.imp_pure_m _ _ hWD hSubset)))))))

theorem formula_l (hℳ : Theory.Models ℳ theory_m) (R S : set_l ℳ) (n : num_l ℳ) :
    rows_m.satisfies ((((Env.empty (M := ℳ)).pushFree R).pushFree S).pushFree n) ↔ rows_l R S n := by
  constructor
  · intro h i hi U W hU hW hUi hWn
    let η := ((((Env.empty (M := ℳ)).pushFree R).pushFree S).pushFree n).pushBound i |>.pushBound U |>.pushBound W
    have hi' : (GraphSyntax.edge_m (.fvar (.there (.there .here)))
        (.bvar (.there (.there .here))) (.fvar .here)).satisfies η :=
      (SecondOrderPairing.edge_l η (.fvar (.there (.there .here)))
        (.bvar (.there (.there .here))) (.fvar .here)).mpr hi
    have hUi' := (SecondOrderSections.formula_l η (.fvar (.there .here))
      (.bvar (.there .here)) (.bvar (.there (.there .here)))).mpr hUi
    have hWn' := (SecondOrderSections.formula_l η (.fvar (.there .here)) (.bvar .here) (.fvar .here)).mpr hWn
    have hU' := (SecondOrderInterpretation.domain_l η (.bvar (.there .here))
      (Term.app (σ := signature_m) .zero .nil)).mpr hU
    have hW' := (SecondOrderInterpretation.domain_l η (.bvar .here)
      (Term.app (σ := signature_m) .zero .nil)).mpr hW
    exact (SecondOrderGraphSubsetFormula.formula_l hℳ η (.bvar (.there .here)) (.bvar .here)
      (Term.app (σ := signature_m) .zero .nil) (Term.app (σ := signature_m) .zero .nil) hU hW).mp
      (h i U W hi' hUi' hWn' hU' hW')
  · intro h i U W hi hUi hWn hU hW
    let η := ((((Env.empty (M := ℳ)).pushFree R).pushFree S).pushFree n).pushBound i |>.pushBound U |>.pushBound W
    have hi' : relation_l R i n :=
      (SecondOrderPairing.edge_l η (.fvar (.there (.there .here)))
        (.bvar (.there (.there .here))) (.fvar .here)).mp hi
    have hUi' := (SecondOrderSections.formula_l η (.fvar (.there .here))
      (.bvar (.there .here)) (.bvar (.there (.there .here)))).mp hUi
    have hWn' := (SecondOrderSections.formula_l η (.fvar (.there .here)) (.bvar .here) (.fvar .here)).mp hWn
    have hU' := (SecondOrderInterpretation.domain_l η (.bvar (.there .here))
      (Term.app (σ := signature_m) .zero .nil)).mp hU
    have hW' := (SecondOrderInterpretation.domain_l η (.bvar .here)
      (Term.app (σ := signature_m) .zero .nil)).mp hW
    exact (SecondOrderGraphSubsetFormula.formula_l hℳ η (.bvar (.there .here)) (.bvar .here)
      (Term.app (σ := signature_m) .zero .nil) (Term.app (σ := signature_m) .zero .nil) hU' hW').mpr
      (h i hi' U W hU' hW' hUi' hWn')

theorem monotone_l (hℳ : Theory.Models ℳ theory_m) {B R S : set_l ℳ}
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n) (hS : SecondOrderRelativeHierarchy.spec_l B R S) :
    ∀ n, rows_l R S n := by
  intro n
  apply (formula_l hℳ R S n).mp
  apply SecondOrderWellFoundedInduction.induction_l hℳ rows_m pure_m
    (((Env.empty (M := ℳ)).pushFree R).pushFree S) R ?_ n (hWf n)
  intro k _ hPast
  apply (formula_l hℳ R S k).mpr
  apply SecondOrderRelativeHierarchyMonotonicityStep.step_l hℳ
  · intro i _ Y hY
    exact SecondOrderRelativeHierarchy.rows_wf_l hℳ hB hWf hS i Y hY
  · intro i _ Y hYw hY
    exact SecondOrderRelativeHierarchyTransitivity.transitive_l hℳ hB hBase hWf hS i Y hY hYw
  · intro i hi
    exact (formula_l hℳ R S i).mp (hPast i hi)
  · exact hS k

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyMonotonicity
