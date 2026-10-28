import BMSConstructibleBridge.SecondOrderRelativeHierarchyAgreementStep

/-! # 原 Z₂ 内部归纳得到两套历史的商一致性

归纳正文是实际二阶公式，遍历全部配对索引与两套历史的行实数。关系良基
仅指原模型内无下降链；不使用宿主自然数或宿主序数归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyAgreement

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderRelativeHierarchyAgreementStep (rows_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def rows_m : Formula signature_m [] [.num, .set, .set, .set] :=
  .forallE .num <| .forallE .set <| .forallE .set <| .imp
    (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there (.there .here)))) <|
    .imp (SecondOrderSections.formula_m (.fvar (.there (.there .here)))
      (.bvar (.there .here)) (.fvar .here)) <|
    .imp (SecondOrderSections.formula_m (.fvar (.there (.there (.there .here))))
      (.bvar .here) (.bvar (.there (.there .here)))) <|
    .imp (GraphTranslation.domain_m (.bvar (.there .here)) (Term.app (σ := signature_m) .zero .nil)) <|
    .imp (GraphTranslation.domain_m (.bvar .here) (Term.app (σ := signature_m) .zero .nil))
      (GraphTranslation.atom_m GraphSyntax.eq_m (.bvar (.there .here)) (.bvar .here)
        (Term.app (σ := signature_m) .zero .nil) (Term.app (σ := signature_m) .zero .nil))

theorem pure_m : language_m rows_m = true := by
  have hEdge : language_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set, .set])
      (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there (.there .here)))) = true := rfl
  have hU := SecondOrderSections.pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set, .set])
    (.fvar (.there (.there .here))) (.bvar (.there .here)) (.fvar .here) rfl rfl rfl
  have hV := SecondOrderSections.pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set, .set])
    (.fvar (.there (.there (.there .here)))) (.bvar .here) (.bvar (.there (.there .here))) rfl rfl rfl
  have hUD := GraphTranslation.domain_pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set, .set])
    (.bvar (.there .here)) (Term.app (σ := signature_m) .zero .nil) rfl rfl
  have hVD := GraphTranslation.domain_pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set, .set])
    (.bvar .here) (Term.app (σ := signature_m) .zero .nil) rfl rfl
  have hEq := GraphTranslation.atom_pure_m (Γ := [.set, .set, .num]) (Δ := [.num, .set, .set, .set])
    GraphSyntax.eq_m (.bvar (.there .here)) (.bvar .here) (Term.app (σ := signature_m) .zero .nil)
    (Term.app (σ := signature_m) .zero .nil)
    (pure_language_m GraphSyntax.matrix_m GraphSyntax.matrix_pure_m) rfl rfl rfl rfl
  exact SecondOrderFormulaArguments.forall_pure_m .num _
    (SecondOrderFormulaArguments.forall_pure_m .set _
      (SecondOrderFormulaArguments.forall_pure_m .set _
        (SecondOrderFormulaArguments.imp_pure_m _ _ hEdge
          (SecondOrderFormulaArguments.imp_pure_m _ _ hU
            (SecondOrderFormulaArguments.imp_pure_m _ _ hV
              (SecondOrderFormulaArguments.imp_pure_m _ _ hUD
                (SecondOrderFormulaArguments.imp_pure_m _ _ hVD hEq)))))))

theorem formula_l (I S T : set_l ℳ) (n : num_l ℳ) :
    rows_m.satisfies (((((Env.empty (M := ℳ)).pushFree T).pushFree S).pushFree I).pushFree n) ↔
      rows_l I S T n := by
  simp only [rows_m, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderSections.formula_l,
    SecondOrderInterpretation.domain_l, SecondOrderInterpretation.eq_l, Term.eval]
  constructor
  · intro h m hnm U V hU hV hUn hVm
    exact h m U V hnm hUn hVm hU hV
  · intro h m U V hnm hUn hVm hU hV
    exact h m hnm U V hU hV hUn hVm

def formula_m {Γ Δ : SortContext signature_m} (I S T : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  SecondOrderFormulaArguments.formula_m rows_m (.cons n (.cons I (.cons S (.cons T .nil))))

theorem formula_arguments_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (I S T : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num) :
    (formula_m I S T n).satisfies η ↔ rows_l (I.eval η) (S.eval η) (T.eval η) (n.eval η) := by
  rw [formula_m, SecondOrderFormulaArguments.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l η
      (Automation.RelationalTranslation.argumentsSubstitution (.cons n (.cons I (.cons S (.cons T .nil))))) =
      ((((Env.empty (M := ℳ)).pushFree (T.eval η)).pushFree (S.eval η)).pushFree (I.eval η)).pushFree (n.eval η) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      rcases v with _ | _ | _ | _ | v
      all_goals first | rfl | nomatch v
  rw [hEnv]
  exact formula_l _ _ _ _

theorem agree_l (hℳ : Theory.Models ℳ theory_m) {B B' R R' I S T : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {hB' : SecondOrderDomain.wf_l B' (zero_l ℳ)}
    (hBB' : SecondOrderGraph.eq_l ⟨B, zero_l ℳ, hB⟩ ⟨B', zero_l ℳ, hB'⟩)
    (hI : SecondOrderPredecessorCorrespondence.spec_l R R' I)
    (hAsymm : ∀ a b, relation_l R' a b → ¬relation_l R' b a)
    (hS : SecondOrderRelativeHierarchyStrongTheorem.spec_l B R S hB)
    (hT : SecondOrderRelativeHierarchyStrongTheorem.spec_l B' R' T hB')
    (hWf : ∀ n, SecondOrderDomain.wf_l R n) : ∀ n, rows_l I S T n := by
  intro n
  apply (formula_l I S T n).mp
  apply SecondOrderWellFoundedInduction.induction_l hℳ rows_m pure_m
    ((((Env.empty (M := ℳ)).pushFree T).pushFree S).pushFree I) R ?_ n (hWf n)
  intro k _ hPast
  apply (formula_l I S T k).mpr
  exact SecondOrderRelativeHierarchyAgreementStep.step_l hℳ hBB' hI hAsymm hS hT
    (fun i hi => (formula_l I S T i).mp (hPast i hi))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyAgreement
