import BMSConstructibleBridge.SecondOrderRelativeHierarchyClosure
import BMSConstructibleBridge.SecondOrderGraphTransitivityFormula

/-! # 所有内部相对阶段的传递性

对实际行传递性公式作内部良基归纳，调用已验证的三类归纳步。参数和行
均来自同一模型，所有索引包括非标准数；没有对模型序数作外部递归。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyTransitivity

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def rows_m : Formula signature_m [] [.num, .set] :=
  .forallE .set <| .imp
    (SecondOrderSections.formula_m (.fvar (.there .here)) (.bvar .here) (.fvar .here)) <|
    .imp (GraphTranslation.domain_m (.bvar .here) (Term.app (σ := signature_m) .zero .nil))
      (SecondOrderGraphTransitivityFormula.formula_m (.bvar .here) (Term.app (σ := signature_m) .zero .nil))

theorem pure_m : language_m rows_m = true := by
  have hSection := SecondOrderSections.pure_m (Γ := [.set]) (Δ := [.num, .set])
    (.fvar (.there .here)) (.bvar .here) (.fvar .here) rfl rfl rfl
  have hDomain := GraphTranslation.domain_pure_m (Γ := [.set]) (Δ := [.num, .set])
    (.bvar .here) (Term.app (σ := signature_m) .zero .nil) rfl rfl
  have hTrans := SecondOrderGraphTransitivityFormula.pure_m (Γ := [.set]) (Δ := [.num, .set])
    (.bvar .here) (Term.app (σ := signature_m) .zero .nil) rfl rfl
  exact SecondOrderFormulaArguments.forall_pure_m .set _
    (SecondOrderFormulaArguments.imp_pure_m _ _ hSection
      (SecondOrderFormulaArguments.imp_pure_m _ _ hDomain hTrans))

theorem formula_l (hℳ : Theory.Models ℳ theory_m) (S : set_l ℳ) (n : num_l ℳ) :
    rows_m.satisfies (((Env.empty (M := ℳ)).pushFree S).pushFree n) ↔
      ∀ W, SecondOrderSections.spec_l S n W → ∀ hW : SecondOrderDomain.wf_l W (zero_l ℳ),
        SecondOrderTransitiveSuperset.transitive_l ⟨W, zero_l ℳ, hW⟩ := by
  constructor
  · intro h W hRow hW
    let η := (((Env.empty (M := ℳ)).pushFree S).pushFree n).pushBound W
    have hRow' := (SecondOrderSections.formula_l η (.fvar (.there .here))
      (.bvar .here) (.fvar .here)).mpr hRow
    have hW' := (SecondOrderInterpretation.domain_l η (.bvar .here)
      (Term.app (σ := signature_m) .zero .nil)).mpr hW
    exact (SecondOrderGraphTransitivityFormula.formula_l hℳ η (.bvar .here)
      (Term.app (σ := signature_m) .zero .nil) hW).mp (h W hRow' hW')
  · intro h W hRow hW
    let η := (((Env.empty (M := ℳ)).pushFree S).pushFree n).pushBound W
    have hRow' := (SecondOrderSections.formula_l η (.fvar (.there .here))
      (.bvar .here) (.fvar .here)).mp hRow
    have hW' := (SecondOrderInterpretation.domain_l η (.bvar .here)
      (Term.app (σ := signature_m) .zero .nil)).mp hW
    exact (SecondOrderGraphTransitivityFormula.formula_l hℳ η (.bvar .here)
      (Term.app (σ := signature_m) .zero .nil) hW').mpr (h W hRow' hW')

theorem transitive_l (hℳ : Theory.Models ℳ theory_m) {B R S : set_l ℳ}
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n) (hS : SecondOrderRelativeHierarchy.spec_l B R S) :
    ∀ n W, SecondOrderSections.spec_l S n W → ∀ hW : SecondOrderDomain.wf_l W (zero_l ℳ),
      SecondOrderTransitiveSuperset.transitive_l ⟨W, zero_l ℳ, hW⟩ := by
  intro n
  apply (formula_l hℳ S n).mp
  apply SecondOrderWellFoundedInduction.induction_l hℳ rows_m pure_m
    ((Env.empty (M := ℳ)).pushFree S) R ?_ n (hWf n)
  intro k _ hPast
  apply (formula_l hℳ S k).mpr
  intro W hRow hW
  apply SecondOrderRelativeHierarchyClosure.step_l hℳ hB hBase _ _ (hS k W hRow) hW
  · intro i _ Y hY
    exact SecondOrderRelativeHierarchy.rows_wf_l hℳ hB hWf hS i Y hY
  · intro i hi Y hYw hY
    exact (formula_l hℳ S i).mp (hPast i hi) Y hY hYw

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyTransitivity
