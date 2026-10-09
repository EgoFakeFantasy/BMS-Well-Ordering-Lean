import BMSConstructibleBridge.SecondOrderRelativeHierarchy

/-! # 相对层次历史的对象公式

一个公开历史实数编码全部阶段；对任意阶段数及该阶段的实际行，正文同时
断言阶段规格与零根内部无链。量化覆盖模型所有数和所有实数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyHistoryFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def stage_m {Γ Δ : SortContext signature_m} (B R S : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) (W : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  SecondOrderFormulaArguments.formula_m SecondOrderRelativeHierarchyFormula.formula_m
    (.cons W (.cons n (.cons S (.cons R (.cons B .nil)))))

theorem stage_pure_m {Γ Δ : SortContext signature_m} (B R S : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) (W : Term signature_m Γ Δ .set)
    (hB : pure_term_m B = true) (hR : pure_term_m R = true) (hS : pure_term_m S = true)
    (hn : pure_term_m n = true) (hW : pure_term_m W = true) : language_m (stage_m B R S n W) = true := by
  apply SecondOrderFormulaArguments.pure_m _ _ SecondOrderRelativeHierarchyFormula.pure_m
  simp only [pure_args_m, hB, hR, hS, hn, hW]
  rfl

theorem stage_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B R S : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) (W : Term signature_m Γ Δ .set) :
    (stage_m B R S n W).satisfies η ↔ SecondOrderRelativeHierarchyStep.spec_l
      (B.eval η) (R.eval η) (S.eval η) (n.eval η) (W.eval η) := by
  rw [stage_m, SecondOrderFormulaArguments.formula_l, SecondOrderRelativeHierarchyFormula.formula_l hℳ]
  rfl

def formula_m {Γ Δ : SortContext signature_m} (B R S : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .forallE .num <| .forallE .set <| .imp
    (SecondOrderSections.formula_m (S.weakenBound sort_m.num |>.weakenBound sort_m.set)
      (.bvar .here) (.bvar (.there .here))) <|
    .conj (GraphTranslation.domain_m (.bvar .here) (Term.app (σ := signature_m) .zero .nil))
      (stage_m (B.weakenBound sort_m.num |>.weakenBound sort_m.set)
        (R.weakenBound sort_m.num |>.weakenBound sort_m.set)
        (S.weakenBound sort_m.num |>.weakenBound sort_m.set) (.bvar (.there .here)) (.bvar .here))

theorem pure_m {Γ Δ : SortContext signature_m} (B R S : Term signature_m Γ Δ .set)
    (hB : pure_term_m B = true) (hR : pure_term_m R = true) (hS : pure_term_m S = true) :
    language_m (formula_m B R S) = true := by
  have hTwice (t : Term signature_m Γ Δ .set) (ht : pure_term_m t = true) :
      pure_term_m (t.weakenBound sort_m.num |>.weakenBound sort_m.set) = true :=
    (SecondOrderSubstitution.term_weaken_m (t.weakenBound sort_m.num) sort_m.set).trans
      ((SecondOrderSubstitution.term_weaken_m t sort_m.num).trans ht)
  have hSection := SecondOrderSections.pure_m
    (S.weakenBound sort_m.num |>.weakenBound sort_m.set) (.bvar .here)
    (.bvar (.there .here)) (hTwice S hS) rfl rfl
  have hDomain := GraphTranslation.domain_pure_m (Γ := .set :: .num :: Γ) (Δ := Δ)
    (.bvar .here) (Term.app (σ := signature_m) .zero .nil) rfl rfl
  have hStage := stage_pure_m
    (B.weakenBound sort_m.num |>.weakenBound sort_m.set)
    (R.weakenBound sort_m.num |>.weakenBound sort_m.set)
    (S.weakenBound sort_m.num |>.weakenBound sort_m.set) (.bvar (.there .here)) (.bvar .here)
    (hTwice B hB) (hTwice R hR) (hTwice S hS) rfl rfl
  exact SecondOrderFormulaArguments.forall_pure_m .num _
    (SecondOrderFormulaArguments.forall_pure_m .set _
      (SecondOrderFormulaArguments.imp_pure_m _ _ hSection
        (SecondOrderFormulaArguments.conj_pure_m _ _ hDomain hStage)))

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B R S : Term signature_m Γ Δ .set) :
    (formula_m B R S).satisfies η ↔ ∀ n W, SecondOrderSections.spec_l (S.eval η) n W →
      SecondOrderDomain.wf_l W (zero_l ℳ) ∧
        SecondOrderRelativeHierarchyStep.spec_l (B.eval η) (R.eval η) (S.eval η) n W := by
  simp only [formula_m, Formula.satisfies, SecondOrderSections.formula_l,
    SecondOrderInterpretation.domain_l, stage_formula_l hℳ, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyHistoryFormula
