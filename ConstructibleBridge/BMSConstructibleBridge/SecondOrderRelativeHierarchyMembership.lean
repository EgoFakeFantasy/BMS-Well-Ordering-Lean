import BMSConstructibleBridge.SecondOrderRelativeHierarchyMembershipStep
import BMSConstructibleBridge.SecondOrderRelativeHierarchyTransitivity

/-! # 内部前驱阶段的强包含

原子隶属公式而非子集公式用于内部良基归纳。前驱共同上界下的可比性明列
为前提，不能将任意部分序的极限阶段误当成线序极限。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyMembership

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderRelativeHierarchyMembershipStep (rows_l comparable_l)

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
      (GraphTranslation.atom_m GraphSyntax.mem_m (.bvar (.there .here)) (.bvar .here)
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
  have hMem := GraphTranslation.atom_pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set])
    GraphSyntax.mem_m (.bvar (.there .here)) (.bvar .here) (Term.app (σ := signature_m) .zero .nil)
    (Term.app (σ := signature_m) .zero .nil)
    (pure_language_m GraphSyntax.mem_matrix_m GraphSyntax.mem_matrix_pure_m) rfl rfl rfl rfl
  exact SecondOrderFormulaArguments.forall_pure_m .num _
    (SecondOrderFormulaArguments.forall_pure_m .set _
      (SecondOrderFormulaArguments.forall_pure_m .set _
        (SecondOrderFormulaArguments.imp_pure_m _ _ hEdge
          (SecondOrderFormulaArguments.imp_pure_m _ _ hU
            (SecondOrderFormulaArguments.imp_pure_m _ _ hW
              (SecondOrderFormulaArguments.imp_pure_m _ _ hUD
                (SecondOrderFormulaArguments.imp_pure_m _ _ hWD hMem)))))))

theorem formula_l (R S : set_l ℳ) (n : num_l ℳ) :
    rows_m.satisfies ((((Env.empty (M := ℳ)).pushFree R).pushFree S).pushFree n) ↔ rows_l R S n := by
  simp only [rows_m, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderSections.formula_l,
    SecondOrderInterpretation.domain_l, SecondOrderInterpretation.mem_l, Term.eval]
  constructor
  · intro h i hi U W hU hW hUi hWn
    exact h i U W hi hUi hWn hU hW
  · intro h i U W hi hUi hWn hU hW
    exact h i hi U W hU hW hUi hWn

theorem member_l (hℳ : Theory.Models ℳ theory_m) {B R S : set_l ℳ}
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n) (hCompare : comparable_l R)
    (hS : SecondOrderRelativeHierarchy.spec_l B R S) : ∀ n, rows_l R S n := by
  intro n
  apply (formula_l R S n).mp
  apply SecondOrderWellFoundedInduction.induction_l hℳ rows_m pure_m
    (((Env.empty (M := ℳ)).pushFree R).pushFree S) R ?_ n (hWf n)
  intro k _ hPast
  apply (formula_l R S k).mpr
  apply SecondOrderRelativeHierarchyMembershipStep.step_l hℳ hCompare
  · intro i _ Y hY
    exact SecondOrderRelativeHierarchy.rows_wf_l hℳ hB hWf hS i Y hY
  · intro i _ Y hYw hY
    exact SecondOrderRelativeHierarchyTransitivity.transitive_l hℳ hB hBase hWf hS i Y hY hYw
  · intro i hi
    exact (formula_l R S i).mp (hPast i hi)
  · exact hS k

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyMembership
