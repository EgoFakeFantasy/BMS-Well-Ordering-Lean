import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedReplay

/-!
# ZFC 基础逻辑公理的对象层回放

本模块把外部 Hilbert 基础公理的 quotation 直接回放到对象层逻辑公理码。
这里不调用 checked 布尔谓词的可靠性，也不引入新的证明谓词。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

/-! ## 七个命题模式 -/

/-! ### 有限见证的对象层回放 -/

/-- 两个闭 quotation 项的嵌套存在见证回放。 -/
theorem fs_zfc_support_raw_exists_two_of_substituted
    (body : SetFormula)
    (leftId rightId : FreeVarId)
    (leftCode rightCode : SetTerm)
    (hLeft : GodelQuotation.Numbered.CodeBoundary leftCode)
    (hRight : GodelQuotation.Numbered.CodeBoundary rightCode)
    (hDistinct : leftId ≠ rightId)
    (hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set rightId rightCode
          (Formula.substituteFree SetSort.set leftId leftCode body))) :
    Derives fs_zfc_support_raw_theory [] (
      ∃ₘ[SetSort.set, leftId],
        ∃ₘ[SetSort.set, rightId], body) := by
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := leftCode) leftId
  change Derives fs_zfc_support_raw_theory [] (
    Formula.existsE SetSort.set
      (Formula.substituteFree SetSort.set leftId leftCode
        (Formula.closeFreeAt SetSort.set rightId 0 body)))
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set leftId rightId 0 leftCode body
    hDistinct hLeft.1.2 (by
      rw [hLeft.2]
      exact List.not_mem_nil)]
  exact FirstOrder.Derives.exists_intro_substituted
    (witness := rightCode) rightId hInstance

/-- 三个闭 quotation 项的嵌套存在见证回放。 -/
theorem fs_zfc_support_raw_exists_three_of_substituted
    (body : SetFormula)
    (leftId middleId rightId : FreeVarId)
    (leftCode middleCode rightCode : SetTerm)
    (hLeft : GodelQuotation.Numbered.CodeBoundary leftCode)
    (hMiddle : GodelQuotation.Numbered.CodeBoundary middleCode)
    (hRight : GodelQuotation.Numbered.CodeBoundary rightCode)
    (hLeftMiddle : leftId ≠ middleId)
    (hMiddleRight : middleId ≠ rightId)
    (hLeftRight : leftId ≠ rightId)
    (hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set rightId rightCode
          (Formula.substituteFree SetSort.set middleId middleCode
            (Formula.substituteFree SetSort.set leftId leftCode body)))) :
    Derives fs_zfc_support_raw_theory [] (
      ∃ₘ[SetSort.set, leftId],
        ∃ₘ[SetSort.set, middleId],
          ∃ₘ[SetSort.set, rightId], body) := by
  have hRightInstance :=
    FirstOrder.Derives.exists_intro_substituted
      (T := fs_zfc_support_raw_theory)
      (Γ := []) (witness := rightCode) rightId hInstance
  have hMiddleComm :
      Formula.closeFreeAt SetSort.set rightId 0
          (Formula.substituteFree SetSort.set middleId middleCode
            (Formula.substituteFree SetSort.set leftId leftCode body)) =
        Formula.substituteFree SetSort.set middleId middleCode
          (Formula.closeFreeAt SetSort.set rightId 0
            (Formula.substituteFree SetSort.set leftId leftCode body)) :=
    Formula.closeFreeAt_substituteFree_comm
      SetSort.set middleId rightId 0 middleCode
      (Formula.substituteFree SetSort.set leftId leftCode body)
      hMiddleRight hMiddle.1.2 (by
        rw [hMiddle.2]
        exact List.not_mem_nil)
  have hMiddleSubstitute :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set middleId middleCode
          (∃ₘ[SetSort.set, rightId],
            Formula.substituteFree SetSort.set leftId leftCode body)) := by
    change Derives fs_zfc_support_raw_theory [] (
      Formula.existsE SetSort.set
        (Formula.substituteFree SetSort.set middleId middleCode
          (Formula.closeFreeAt SetSort.set rightId 0
            (Formula.substituteFree SetSort.set leftId leftCode body))))
    rw [← hMiddleComm]
    exact hRightInstance
  have hMiddleInstance :=
    FirstOrder.Derives.exists_intro_substituted
      (T := fs_zfc_support_raw_theory)
      (Γ := []) (witness := middleCode) middleId hMiddleSubstitute
  have hLeftCommRight :
      Formula.closeFreeAt SetSort.set rightId 0
          (Formula.substituteFree SetSort.set leftId leftCode body) =
        Formula.substituteFree SetSort.set leftId leftCode
          (Formula.closeFreeAt SetSort.set rightId 0 body) :=
    Formula.closeFreeAt_substituteFree_comm
      SetSort.set leftId rightId 0 leftCode body
      hLeftRight
      hLeft.1.2 (by
        rw [hLeft.2]
        exact List.not_mem_nil)
  have hLeftCommMiddle :
      Formula.closeFreeAt SetSort.set middleId 0
          (Formula.substituteFree SetSort.set leftId leftCode
            (∃ₘ[SetSort.set, rightId], body)) =
        Formula.substituteFree SetSort.set leftId leftCode
          (Formula.closeFreeAt SetSort.set middleId 0
            (∃ₘ[SetSort.set, rightId], body)) :=
    Formula.closeFreeAt_substituteFree_comm
      SetSort.set leftId middleId 0 leftCode
      (∃ₘ[SetSort.set, rightId], body)
      hLeftMiddle hLeft.1.2 (by
        rw [hLeft.2]
        exact List.not_mem_nil)
  have hLeftSubstitute :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set leftId leftCode
          (∃ₘ[SetSort.set, middleId],
            ∃ₘ[SetSort.set, rightId], body)) := by
    change Derives fs_zfc_support_raw_theory [] (
      Formula.substituteFree SetSort.set leftId leftCode
        (Formula.existsE SetSort.set
          (Formula.closeFreeAt SetSort.set middleId 0
            (Formula.existsE SetSort.set
              (Formula.closeFreeAt SetSort.set rightId 0 body)))))
    simp only [Formula.substituteFree]
    rw [← hLeftCommMiddle]
    simp only [Formula.substituteFree]
    rw [← hLeftCommRight]
    exact hMiddleInstance
  exact FirstOrder.Derives.exists_intro_substituted
    (witness := leftCode) leftId hLeftSubstitute

/-- 一个闭 quotation 项的单个存在见证回放。 -/
theorem fs_zfc_support_raw_exists_one_of_substituted
    (body : SetFormula)
    (id : FreeVarId)
    (code : SetTerm)
    (hCode : GodelQuotation.Numbered.CodeBoundary code)
    (hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set id code body)) :
    Derives fs_zfc_support_raw_theory [] (
      ∃ₘ[SetSort.set, id], body) :=
  FirstOrder.Derives.exists_intro_substituted
    (witness := code) id hInstance

theorem fs_zfc_support_raw_self_implication_axiom_code_exists
    {formula : SetFormula}
    (hFormula : Formula.Admissible formula) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp formula (Formula.imp formula formula)) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  rcases GodelQuotation.Numbered.quote?_exists hFormula with
    ⟨formulaCode, hFormulaQuote⟩
  have hFormulaBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hFormulaQuote
  have hFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(formulaCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hFormulaQuote)
  let code : SetTerm :=
    self_implication_axiom_code_term formulaCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      self_implication_axiom_code_term_admissible
        formulaCode hFormulaBoundary.1
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hFormulaBoundary.2]
  have hFormulaCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth formulaCode =
        formulaCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth formulaCode
      hFormulaBoundary.1.2 (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 403 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 403 depth code hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hFormulaSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement formulaCode =
        formulaCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement formulaCode (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hCodeSubstituteTerm :
      Term.substituteFree SetSort.set 403 formulaCode code =
        code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 403 formulaCode code (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        propositional_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hSelfDefinition :=
    FirstOrder.Derives.conjElimLeft
      (FirstOrder.Derives.conjElimRight hDefinition)
  have hSelfInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hSelfDefinition
  have hSelfIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ SelfImpAxiomsₘ) ↔ₘ
          self_implication_axiom_condition code) := by
    simpa [code, self_implication_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hCodeOpen, hCodeClose,
      hFormulaCloseAt,
      self_implication_axiom_set_term] using hSelfInstance
  let body : SetFormula :=
    formula_codeₘ(x#403) ∧ₘ
      (code ≐ₘ self_implication_axiom_code_term (x#403))
  have hBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        formula_codeₘ(formulaCode) ∧ₘ
          (code ≐ₘ self_implication_axiom_code_term formulaCode)) := by
    apply FirstOrder.Derives.conjIntro
    · exact hFormulaCode
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code
  have hBodySubstitute :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 403 formulaCode body) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable, code,
      hFormulaSubstituteTerm, hCodeSubstituteTerm] using hBodyActual
  have hConditionBody :=
    fs_zfc_support_raw_exists_one_of_substituted
      body 403 formulaCode hFormulaBoundary hBodySubstitute
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        self_implication_axiom_condition code) := by
    simpa [self_implication_axiom_condition, body, code,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hFormulaCloseAt, hCodeClose] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ SelfImpAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft hSelfIff hCondition
  have hBaseAdmissible :
      Formula.Admissible (base_logical_axiom_condition code) :=
    base_logical_axiom_condition_admissible code hCode
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        base_logical_axiom_condition code) := by
    simpa [base_logical_axiom_condition] using
      (FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroLeft
          hMember))
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hFormulaHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort formula) =
        some formulaCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hFormulaQuote
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp formula (Formula.imp formula formula)) =
        some code := by
    simp [code, GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, hFormulaHilbertQuote]
  exact ⟨code, hWholeQuote, hLogical⟩

theorem fs_zfc_support_raw_implication_distribution_axiom_code_exists
    {antecedent middle consequent : SetFormula}
    (hAntecedent : Formula.Admissible antecedent)
    (hMiddle : Formula.Admissible middle)
    (hConsequent : Formula.Admissible consequent) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp
            (Formula.imp antecedent
              (Formula.imp middle consequent))
            (Formula.imp
              (Formula.imp antecedent middle)
              (Formula.imp antecedent consequent))) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  rcases GodelQuotation.Numbered.quote?_exists hAntecedent with
    ⟨antecedentCode, hAntecedentQuote⟩
  rcases GodelQuotation.Numbered.quote?_exists hMiddle with
    ⟨middleCode, hMiddleQuote⟩
  rcases GodelQuotation.Numbered.quote?_exists hConsequent with
    ⟨consequentCode, hConsequentQuote⟩
  have hAntecedentBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hAntecedentQuote
  have hMiddleBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hMiddleQuote
  have hConsequentBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hConsequentQuote
  have hAntecedentFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(antecedentCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hAntecedentQuote)
  have hMiddleFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(middleCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hMiddleQuote)
  have hConsequentFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(consequentCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hConsequentQuote)
  let code : SetTerm :=
    implication_distribution_axiom_code_term
      antecedentCode middleCode consequentCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      implication_distribution_axiom_code_term_admissible
        antecedentCode middleCode consequentCode
        hAntecedentBoundary.1
        hMiddleBoundary.1
        hConsequentBoundary.1
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hAntecedentBoundary.2, hMiddleBoundary.2,
      hConsequentBoundary.2]
  have hAntecedentClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 400 depth antecedentCode =
        antecedentCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 400 depth antecedentCode
      hAntecedentBoundary.1.2 (by
        rw [hAntecedentBoundary.2]
        exact List.not_mem_nil)
  have hAntecedentCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth antecedentCode =
        antecedentCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth antecedentCode
      hAntecedentBoundary.1.2 (by
        rw [hAntecedentBoundary.2]
        exact List.not_mem_nil)
  have hMiddleClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 401 depth middleCode =
        middleCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 401 depth middleCode
      hMiddleBoundary.1.2 (by
        rw [hMiddleBoundary.2]
        exact List.not_mem_nil)
  have hMiddleCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth middleCode =
        middleCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth middleCode
      hMiddleBoundary.1.2 (by
        rw [hMiddleBoundary.2]
        exact List.not_mem_nil)
  have hConsequentClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 402 depth consequentCode =
        consequentCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 402 depth consequentCode
      hConsequentBoundary.1.2 (by
        rw [hConsequentBoundary.2]
        exact List.not_mem_nil)
  have hConsequentCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth consequentCode =
        consequentCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth consequentCode
      hConsequentBoundary.1.2 (by
        rw [hConsequentBoundary.2]
        exact List.not_mem_nil)
  have hCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 0 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 depth code hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hAntecedentSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement antecedentCode =
        antecedentCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement antecedentCode (by
        rw [hAntecedentBoundary.2]
        exact List.not_mem_nil)
  have hMiddleSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement middleCode =
        middleCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement middleCode (by
        rw [hMiddleBoundary.2]
        exact List.not_mem_nil)
  have hConsequentSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement consequentCode =
        consequentCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement consequentCode (by
        rw [hConsequentBoundary.2]
        exact List.not_mem_nil)
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        propositional_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hImplicationDefinition :=
    FirstOrder.Derives.conjElimLeft hDefinition
  have hImplicationInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hImplicationDefinition
  have hImplicationIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ ImpDistribAxiomsₘ) ↔ₘ
          implication_distribution_axiom_condition code) := by
    simpa [code, implication_distribution_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hCodeOpen, hCodeClose,
      hAntecedentCloseAt, hMiddleCloseAt,
      hConsequentCloseAt,
      implication_distribution_axiom_set_term] using
      hImplicationInstance
  let body : SetFormula :=
    (((formula_codeₘ(x#400) ∧ₘ
        formula_codeₘ(x#401)) ∧ₘ
        formula_codeₘ(x#402)) ∧ₘ
      (code ≐ₘ
        implication_distribution_axiom_code_term
          (x#400) (x#401) (x#402)))
  have hBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        (((formula_codeₘ(antecedentCode) ∧ₘ
            formula_codeₘ(middleCode)) ∧ₘ
            formula_codeₘ(consequentCode)) ∧ₘ
          (code ≐ₘ
            implication_distribution_axiom_code_term
              antecedentCode middleCode consequentCode))) := by
    apply FirstOrder.Derives.conjIntro
    · apply FirstOrder.Derives.conjIntro
      · apply FirstOrder.Derives.conjIntro
        · exact hAntecedentFormulaCode
        · exact hMiddleFormulaCode
      · exact hConsequentFormulaCode
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code
  have hBody402 :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 402
          consequentCode
          (Formula.substituteFree SetSort.set 401
            middleCode
            (Formula.substituteFree SetSort.set 400
              antecedentCode body))) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable, code,
      hCodeClosed, hAntecedentSubstituteTerm,
      hMiddleSubstituteTerm,
      hConsequentSubstituteTerm] using
      hBodyActual
  have hConditionBody :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 400],
          ∃ₘ[SetSort.set, 401],
            ∃ₘ[SetSort.set, 402], body) :=
    fs_zfc_support_raw_exists_three_of_substituted
      body 400 401 402
      antecedentCode middleCode consequentCode
      hAntecedentBoundary hMiddleBoundary hConsequentBoundary
      (by decide) (by decide) (by decide) hBody402
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        implication_distribution_axiom_condition code) := by
    simpa [implication_distribution_axiom_condition, body, code] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ ImpDistribAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft
      hImplicationIff hCondition
  have hBaseAdmissible :
      Formula.Admissible (base_logical_axiom_condition code) :=
    base_logical_axiom_condition_admissible code hCode
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        base_logical_axiom_condition code) :=
    FirstOrder.Derives.disjIntroLeft hMember
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hAntecedentHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort antecedent) =
        some antecedentCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hAntecedentQuote
  have hMiddleHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort middle) =
        some middleCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hMiddleQuote
  have hConsequentHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort consequent) =
        some consequentCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hConsequentQuote
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp
            (Formula.imp antecedent
              (Formula.imp middle consequent))
            (Formula.imp
              (Formula.imp antecedent middle)
              (Formula.imp antecedent consequent))) =
        some code := by
    simp [code, GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize,
      hAntecedentHilbertQuote,
      hMiddleHilbertQuote,
      hConsequentHilbertQuote]
  exact ⟨code, hWholeQuote, hLogical⟩

theorem fs_zfc_support_raw_weakening_axiom_code_exists
    {formula extra : SetFormula}
    (hFormula : Formula.Admissible formula)
    (hExtra : Formula.Admissible extra) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp formula (Formula.imp extra formula)) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  rcases GodelQuotation.Numbered.quote?_exists hFormula with
    ⟨formulaCode, hFormulaQuote⟩
  rcases GodelQuotation.Numbered.quote?_exists hExtra with
    ⟨extraCode, hExtraQuote⟩
  have hFormulaBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hFormulaQuote
  have hExtraBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hExtraQuote
  have hFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(formulaCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hFormulaQuote)
  have hExtraCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(extraCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hExtraQuote)
  let code : SetTerm :=
    weakening_axiom_code_term formulaCode extraCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      weakening_axiom_code_term_admissible
        formulaCode extraCode hFormulaBoundary.1 hExtraBoundary.1
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hFormulaBoundary.2, hExtraBoundary.2]
  have hFormulaCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth formulaCode =
        formulaCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth formulaCode
      hFormulaBoundary.1.2 (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hExtraCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth extraCode =
        extraCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth extraCode
      hExtraBoundary.1.2 (by
        rw [hExtraBoundary.2]
        exact List.not_mem_nil)
  have hCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 0 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 depth code hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hFormulaSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement formulaCode =
        formulaCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement formulaCode (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hExtraSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement extraCode =
        extraCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement extraCode (by
        rw [hExtraBoundary.2]
        exact List.not_mem_nil)
  have hCodeSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code =
        code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement code (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        propositional_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hWeakeningDefinition :=
    FirstOrder.Derives.conjElimLeft
      (FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.conjElimRight hDefinition))
  have hWeakeningInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hWeakeningDefinition
  have hWeakeningIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ WeakeningAxiomsₘ) ↔ₘ
          weakening_axiom_condition code) := by
    simpa [code, weakening_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hCodeOpen, hCodeClose,
      hFormulaCloseAt, hExtraCloseAt,
      weakening_axiom_set_term] using
      hWeakeningInstance
  let body : SetFormula :=
    ((formula_codeₘ(x#404) ∧ₘ
        formula_codeₘ(x#405)) ∧ₘ
      (code ≐ₘ weakening_axiom_code_term
        (x#404) (x#405)))
  have hBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        ((formula_codeₘ(formulaCode) ∧ₘ
            formula_codeₘ(extraCode)) ∧ₘ
          (code ≐ₘ weakening_axiom_code_term
            formulaCode extraCode))) := by
    apply FirstOrder.Derives.conjIntro
    · apply FirstOrder.Derives.conjIntro
      · exact hFormulaCode
      · exact hExtraCode
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code
  have hBodyInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 405 extraCode
          (Formula.substituteFree SetSort.set 404 formulaCode body)) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable, code,
      hCodeClosed, hFormulaSubstituteTerm,
      hExtraSubstituteTerm, hCodeSubstituteTerm] using
      hBodyActual
  have hConditionBody :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 404],
          ∃ₘ[SetSort.set, 405], body) :=
    fs_zfc_support_raw_exists_two_of_substituted
      body 404 405 formulaCode extraCode
      hFormulaBoundary hExtraBoundary
      (by decide) hBodyInstance
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        weakening_axiom_condition code) := by
    simpa [weakening_axiom_condition, body, code] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ WeakeningAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft hWeakeningIff hCondition
  have hBaseAdmissible :
      Formula.Admissible (base_logical_axiom_condition code) :=
    base_logical_axiom_condition_admissible code hCode
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        base_logical_axiom_condition code) := by
    simpa [base_logical_axiom_condition] using
      (FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.disjIntroLeft
            hMember)))
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hFormulaHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort formula) =
        some formulaCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hFormulaQuote
  have hExtraHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort extra) =
        some extraCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hExtraQuote
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp formula (Formula.imp extra formula)) =
        some code := by
    simp [code, GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, hFormulaHilbertQuote,
      hExtraHilbertQuote]
  exact ⟨code, hWholeQuote, hLogical⟩

theorem fs_zfc_support_raw_explosion_axiom_code_exists
    {formula conclusion : SetFormula}
    (hFormula : Formula.Admissible formula)
    (hConclusion : Formula.Admissible conclusion) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp (Formula.neg formula)
            (Formula.imp formula conclusion)) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  rcases GodelQuotation.Numbered.quote?_exists hFormula with
    ⟨formulaCode, hFormulaQuote⟩
  rcases GodelQuotation.Numbered.quote?_exists hConclusion with
    ⟨conclusionCode, hConclusionQuote⟩
  have hFormulaBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hFormulaQuote
  have hConclusionBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hConclusionQuote
  have hFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(formulaCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hFormulaQuote)
  have hConclusionCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(conclusionCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hConclusionQuote)
  let code : SetTerm :=
    explosion_axiom_code_term formulaCode conclusionCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      explosion_axiom_code_term_admissible
        formulaCode conclusionCode
        hFormulaBoundary.1 hConclusionBoundary.1
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hFormulaBoundary.2, hConclusionBoundary.2]
  have hFormulaCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth formulaCode =
        formulaCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth formulaCode
      hFormulaBoundary.1.2 (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hConclusionCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth conclusionCode =
        conclusionCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth conclusionCode
      hConclusionBoundary.1.2 (by
        rw [hConclusionBoundary.2]
        exact List.not_mem_nil)
  have hCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 0 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 depth code hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hFormulaSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement formulaCode =
        formulaCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement formulaCode (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hConclusionSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement conclusionCode =
        conclusionCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement conclusionCode (by
        rw [hConclusionBoundary.2]
        exact List.not_mem_nil)
  have hCodeSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code =
        code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement code (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        propositional_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hExplosionDefinition :=
    FirstOrder.Derives.conjElimLeft
      (FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight hDefinition)))))
  have hExplosionInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hExplosionDefinition
  have hExplosionIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ ExplosionAxiomsₘ) ↔ₘ
          explosion_axiom_condition code) := by
    simpa [code, explosion_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hCodeOpen, hCodeClose,
      hFormulaCloseAt, hConclusionCloseAt,
      explosion_axiom_set_term] using
      hExplosionInstance
  let body : SetFormula :=
    ((formula_codeₘ(x#409) ∧ₘ
        formula_codeₘ(x#410)) ∧ₘ
      (code ≐ₘ explosion_axiom_code_term
        (x#409) (x#410)))
  have hBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        ((formula_codeₘ(formulaCode) ∧ₘ
            formula_codeₘ(conclusionCode)) ∧ₘ
          (code ≐ₘ explosion_axiom_code_term
            formulaCode conclusionCode))) := by
    apply FirstOrder.Derives.conjIntro
    · apply FirstOrder.Derives.conjIntro
      · exact hFormulaCode
      · exact hConclusionCode
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code
  have hBodyInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 410 conclusionCode
          (Formula.substituteFree SetSort.set 409 formulaCode body)) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable, code,
      hCodeClosed, hFormulaSubstituteTerm,
      hConclusionSubstituteTerm, hCodeSubstituteTerm] using
      hBodyActual
  have hConditionBody :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 409],
          ∃ₘ[SetSort.set, 410], body) :=
    fs_zfc_support_raw_exists_two_of_substituted
      body 409 410 formulaCode conclusionCode
      hFormulaBoundary hConclusionBoundary
      (by decide) hBodyInstance
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        explosion_axiom_condition code) := by
    simpa [explosion_axiom_condition, body, code] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ ExplosionAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft hExplosionIff hCondition
  have hBaseAdmissible :
      Formula.Admissible (base_logical_axiom_condition code) :=
    base_logical_axiom_condition_admissible code hCode
  let tail11 : SetFormula :=
    (code ∈ₘ EqualitySubstAxiomsₘ) ∨ₘ
      (code ∈ₘ EqualityReflAxiomsₘ)
  let tail10 : SetFormula :=
    (code ∈ₘ VacuousForallAxiomsₘ) ∨ₘ tail11
  let tail9 : SetFormula :=
    (code ∈ₘ ForallDistribAxiomsₘ) ∨ₘ tail10
  let tail8 : SetFormula :=
    (code ∈ₘ SpecializationAxiomsₘ) ∨ₘ tail9
  let tail7 : SetFormula :=
    (code ∈ₘ CaseAnalysisAxiomsₘ) ∨ₘ tail8
  let tail6 : SetFormula :=
    (code ∈ₘ ExplosionAxiomsₘ) ∨ₘ tail7
  let tail5 : SetFormula :=
    (code ∈ₘ ClassicalAxiomsₘ) ∨ₘ tail6
  let tail4 : SetFormula :=
    (code ∈ₘ ContradictionAxiomsₘ) ∨ₘ tail5
  let tail3 : SetFormula :=
    (code ∈ₘ WeakeningAxiomsₘ) ∨ₘ tail4
  let tail2 : SetFormula :=
    (code ∈ₘ SelfImpAxiomsₘ) ∨ₘ tail3
  let tail1 : SetFormula :=
    (code ∈ₘ ImpDistribAxiomsₘ) ∨ₘ tail2
  have hTail7Admissible :
      Formula.Admissible tail7 := by
    simpa [tail7, tail8, tail9, tail10, tail11] using
      Formula.Admissible.disj_right
        (Formula.Admissible.disj_right
          (Formula.Admissible.disj_right
            (Formula.Admissible.disj_right
              (Formula.Admissible.disj_right
                (Formula.Admissible.disj_right hBaseAdmissible)))))
  have hTail6 :
      Derives fs_zfc_support_raw_theory [] tail6 := by
    dsimp [tail6]
    exact FirstOrder.Derives.disjIntroLeft hMember
  have hTail5 :
      Derives fs_zfc_support_raw_theory [] tail5 := by
    dsimp [tail5]
    exact FirstOrder.Derives.disjIntroRight hTail6
  have hTail4 :
      Derives fs_zfc_support_raw_theory [] tail4 := by
    dsimp [tail4]
    exact FirstOrder.Derives.disjIntroRight hTail5
  have hTail3 :
      Derives fs_zfc_support_raw_theory [] tail3 := by
    dsimp [tail3]
    exact FirstOrder.Derives.disjIntroRight hTail4
  have hTail2 :
      Derives fs_zfc_support_raw_theory [] tail2 := by
    dsimp [tail2]
    exact FirstOrder.Derives.disjIntroRight hTail3
  have hTail1 :
      Derives fs_zfc_support_raw_theory [] tail1 := by
    dsimp [tail1]
    exact FirstOrder.Derives.disjIntroRight hTail2
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        base_logical_axiom_condition code) := by
    simpa [base_logical_axiom_condition, tail1, tail2, tail3,
      tail4, tail5, tail6, tail7, tail8, tail9, tail10, tail11] using
      hTail1
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hFormulaHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort formula) =
        some formulaCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hFormulaQuote
  have hConclusionHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort conclusion) =
        some conclusionCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hConclusionQuote
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp (Formula.neg formula)
            (Formula.imp formula conclusion)) =
        some code := by
    simp [code, GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, hFormulaHilbertQuote,
      hConclusionHilbertQuote]
  exact ⟨code, hWholeQuote, hLogical⟩

theorem fs_zfc_support_raw_classical_axiom_code_exists
    {formula : SetFormula}
    (hFormula : Formula.Admissible formula) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp (Formula.imp (Formula.neg formula) formula)
            formula) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  rcases GodelQuotation.Numbered.quote?_exists hFormula with
    ⟨formulaCode, hFormulaQuote⟩
  have hFormulaBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hFormulaQuote
  have hFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(formulaCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hFormulaQuote)
  let code : SetTerm :=
    classical_axiom_code_term formulaCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      classical_axiom_code_term_admissible
        formulaCode hFormulaBoundary.1
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hFormulaBoundary.2]
  have hFormulaCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth formulaCode =
        formulaCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth formulaCode
      hFormulaBoundary.1.2 (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 0 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 depth code hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hFormulaSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement formulaCode =
        formulaCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement formulaCode (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hCodeSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code =
        code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement code (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        propositional_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hClassicalDefinition :=
    FirstOrder.Derives.conjElimLeft
      (FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight hDefinition))))
  have hClassicalInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hClassicalDefinition
  have hClassicalIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ ClassicalAxiomsₘ) ↔ₘ
          classical_axiom_condition code) := by
    simpa [code, classical_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hCodeOpen, hCodeClose,
      hFormulaCloseAt,
      classical_axiom_set_term] using
      hClassicalInstance
  let body : SetFormula :=
    formula_codeₘ(x#408) ∧ₘ
      (code ≐ₘ classical_axiom_code_term (x#408))
  have hBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        formula_codeₘ(formulaCode) ∧ₘ
          (code ≐ₘ classical_axiom_code_term formulaCode)) := by
    apply FirstOrder.Derives.conjIntro
    · exact hFormulaCode
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code
  have hBodySubstitute :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 408 formulaCode body) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable, code,
      hFormulaSubstituteTerm, hCodeSubstituteTerm] using hBodyActual
  have hConditionBody :=
    fs_zfc_support_raw_exists_one_of_substituted
      body 408 formulaCode hFormulaBoundary hBodySubstitute
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        classical_axiom_condition code) := by
    simpa [classical_axiom_condition, body, code,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hFormulaCloseAt, hCodeClose] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ ClassicalAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft hClassicalIff hCondition
  have hBaseAdmissible :
      Formula.Admissible (base_logical_axiom_condition code) :=
    base_logical_axiom_condition_admissible code hCode
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        base_logical_axiom_condition code) := by
    simpa [base_logical_axiom_condition] using
      (FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.disjIntroRight
            (FirstOrder.Derives.disjIntroRight
              (FirstOrder.Derives.disjIntroLeft
                hMember)))))
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hFormulaHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort formula) =
        some formulaCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hFormulaQuote
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp (Formula.imp (Formula.neg formula) formula)
            formula) =
        some code := by
    simp [code, GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, hFormulaHilbertQuote]
  exact ⟨code, hWholeQuote, hLogical⟩

theorem fs_zfc_support_raw_contradiction_axiom_code_exists
    {formula conclusion : SetFormula}
    (hFormula : Formula.Admissible formula)
    (hConclusion : Formula.Admissible conclusion) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp formula
            (Formula.imp (Formula.neg formula) conclusion)) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  rcases GodelQuotation.Numbered.quote?_exists hFormula with
    ⟨formulaCode, hFormulaQuote⟩
  rcases GodelQuotation.Numbered.quote?_exists hConclusion with
    ⟨conclusionCode, hConclusionQuote⟩
  have hFormulaBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hFormulaQuote
  have hConclusionBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hConclusionQuote
  have hFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(formulaCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hFormulaQuote)
  have hConclusionCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(conclusionCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hConclusionQuote)
  let code : SetTerm :=
    contradiction_axiom_code_term formulaCode conclusionCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      contradiction_axiom_code_term_admissible
        formulaCode conclusionCode
        hFormulaBoundary.1 hConclusionBoundary.1
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hFormulaBoundary.2, hConclusionBoundary.2]
  have hFormulaCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth formulaCode =
        formulaCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth formulaCode
      hFormulaBoundary.1.2 (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hConclusionCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth conclusionCode =
        conclusionCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth conclusionCode
      hConclusionBoundary.1.2 (by
        rw [hConclusionBoundary.2]
        exact List.not_mem_nil)
  have hCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 0 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 depth code hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hFormulaSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement formulaCode =
        formulaCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement formulaCode (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hConclusionSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement conclusionCode =
        conclusionCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement conclusionCode (by
        rw [hConclusionBoundary.2]
        exact List.not_mem_nil)
  have hCodeSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code =
        code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement code (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        propositional_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hContradictionDefinition :=
    FirstOrder.Derives.conjElimLeft
      (FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hDefinition)))
  have hContradictionInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hContradictionDefinition
  have hContradictionIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ ContradictionAxiomsₘ) ↔ₘ
          contradiction_axiom_condition code) := by
    simpa [code, contradiction_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hCodeOpen, hCodeClose,
      hFormulaCloseAt, hConclusionCloseAt,
      contradiction_axiom_set_term] using
      hContradictionInstance
  let body : SetFormula :=
    ((formula_codeₘ(x#406) ∧ₘ
        formula_codeₘ(x#407)) ∧ₘ
      (code ≐ₘ contradiction_axiom_code_term
        (x#406) (x#407)))
  have hBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        ((formula_codeₘ(formulaCode) ∧ₘ
            formula_codeₘ(conclusionCode)) ∧ₘ
          (code ≐ₘ contradiction_axiom_code_term
            formulaCode conclusionCode))) := by
    apply FirstOrder.Derives.conjIntro
    · apply FirstOrder.Derives.conjIntro
      · exact hFormulaCode
      · exact hConclusionCode
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code
  have hBodyInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 407 conclusionCode
          (Formula.substituteFree SetSort.set 406 formulaCode body)) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable, code,
      hCodeClosed, hFormulaSubstituteTerm,
      hConclusionSubstituteTerm, hCodeSubstituteTerm] using
      hBodyActual
  have hConditionBody :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 406],
          ∃ₘ[SetSort.set, 407], body) :=
    fs_zfc_support_raw_exists_two_of_substituted
      body 406 407 formulaCode conclusionCode
      hFormulaBoundary hConclusionBoundary
      (by decide) hBodyInstance
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        contradiction_axiom_condition code) := by
    simpa [contradiction_axiom_condition, body, code] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ ContradictionAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft hContradictionIff hCondition
  have hBaseAdmissible :
      Formula.Admissible (base_logical_axiom_condition code) :=
    base_logical_axiom_condition_admissible code hCode
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        base_logical_axiom_condition code) := by
    simpa [base_logical_axiom_condition] using
      (FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.disjIntroRight
            (FirstOrder.Derives.disjIntroLeft
              hMember))))
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hFormulaHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort formula) =
        some formulaCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hFormulaQuote
  have hConclusionHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort conclusion) =
        some conclusionCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hConclusionQuote
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp formula
            (Formula.imp (Formula.neg formula) conclusion)) =
        some code := by
    simp [code, GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, hFormulaHilbertQuote,
      hConclusionHilbertQuote]
  exact ⟨code, hWholeQuote, hLogical⟩

theorem fs_zfc_support_raw_case_analysis_axiom_code_exists
    {formula conclusion : SetFormula}
    (hFormula : Formula.Admissible formula)
    (hConclusion : Formula.Admissible conclusion) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp
            (Formula.imp formula conclusion)
            (Formula.imp
              (Formula.imp (Formula.neg formula) conclusion)
              conclusion)) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  rcases GodelQuotation.Numbered.quote?_exists hFormula with
    ⟨formulaCode, hFormulaQuote⟩
  rcases GodelQuotation.Numbered.quote?_exists hConclusion with
    ⟨conclusionCode, hConclusionQuote⟩
  have hFormulaBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hFormulaQuote
  have hConclusionBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hConclusionQuote
  have hFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(formulaCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hFormulaQuote)
  have hConclusionCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(conclusionCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code
        hConclusionQuote)
  let code : SetTerm :=
    case_analysis_axiom_code_term formulaCode conclusionCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      case_analysis_axiom_code_term_admissible
        formulaCode conclusionCode
        hFormulaBoundary.1 hConclusionBoundary.1
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hFormulaBoundary.2, hConclusionBoundary.2]
  have hFormulaCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth formulaCode =
        formulaCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth formulaCode
      hFormulaBoundary.1.2 (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hConclusionCloseAt (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth conclusionCode =
        conclusionCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth conclusionCode
      hConclusionBoundary.1.2 (by
        rw [hConclusionBoundary.2]
        exact List.not_mem_nil)
  have hCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 0 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 0 depth code hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hFormulaSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement formulaCode =
        formulaCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement formulaCode (by
        rw [hFormulaBoundary.2]
        exact List.not_mem_nil)
  have hConclusionSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement conclusionCode =
        conclusionCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement conclusionCode (by
        rw [hConclusionBoundary.2]
        exact List.not_mem_nil)
  have hCodeSubstituteTerm (id : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code =
        code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement code (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        propositional_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hCaseDefinition :=
    FirstOrder.Derives.conjElimRight
      (FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight hDefinition)))))
  have hCaseInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hCaseDefinition
  have hCaseIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ CaseAnalysisAxiomsₘ) ↔ₘ
          case_analysis_axiom_condition code) := by
    simpa [code, case_analysis_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hCodeOpen, hCodeClose,
      hFormulaCloseAt, hConclusionCloseAt,
      case_analysis_axiom_set_term] using
      hCaseInstance
  let body : SetFormula :=
    ((formula_codeₘ(x#411) ∧ₘ
        formula_codeₘ(x#412)) ∧ₘ
      (code ≐ₘ case_analysis_axiom_code_term
        (x#411) (x#412)))
  have hBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        ((formula_codeₘ(formulaCode) ∧ₘ
            formula_codeₘ(conclusionCode)) ∧ₘ
          (code ≐ₘ case_analysis_axiom_code_term
            formulaCode conclusionCode))) := by
    apply FirstOrder.Derives.conjIntro
    · apply FirstOrder.Derives.conjIntro
      · exact hFormulaCode
      · exact hConclusionCode
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code
  have hBodyInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 412 conclusionCode
          (Formula.substituteFree SetSort.set 411 formulaCode body)) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable, code,
      hCodeClosed, hFormulaSubstituteTerm,
      hConclusionSubstituteTerm, hCodeSubstituteTerm] using
      hBodyActual
  have hConditionBody :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 411],
          ∃ₘ[SetSort.set, 412], body) :=
    fs_zfc_support_raw_exists_two_of_substituted
      body 411 412 formulaCode conclusionCode
      hFormulaBoundary hConclusionBoundary
      (by decide) hBodyInstance
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        case_analysis_axiom_condition code) := by
    simpa [case_analysis_axiom_condition, body, code] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ CaseAnalysisAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft hCaseIff hCondition
  have hBaseAdmissible :
      Formula.Admissible (base_logical_axiom_condition code) :=
    base_logical_axiom_condition_admissible code hCode
  let tail11 : SetFormula :=
    (code ∈ₘ EqualitySubstAxiomsₘ) ∨ₘ
      (code ∈ₘ EqualityReflAxiomsₘ)
  let tail10 : SetFormula :=
    (code ∈ₘ VacuousForallAxiomsₘ) ∨ₘ tail11
  let tail9 : SetFormula :=
    (code ∈ₘ ForallDistribAxiomsₘ) ∨ₘ tail10
  let tail8 : SetFormula :=
    (code ∈ₘ SpecializationAxiomsₘ) ∨ₘ tail9
  let tail7 : SetFormula :=
    (code ∈ₘ CaseAnalysisAxiomsₘ) ∨ₘ tail8
  let tail6 : SetFormula :=
    (code ∈ₘ ExplosionAxiomsₘ) ∨ₘ tail7
  let tail5 : SetFormula :=
    (code ∈ₘ ClassicalAxiomsₘ) ∨ₘ tail6
  let tail4 : SetFormula :=
    (code ∈ₘ ContradictionAxiomsₘ) ∨ₘ tail5
  let tail3 : SetFormula :=
    (code ∈ₘ WeakeningAxiomsₘ) ∨ₘ tail4
  let tail2 : SetFormula :=
    (code ∈ₘ SelfImpAxiomsₘ) ∨ₘ tail3
  let tail1 : SetFormula :=
    (code ∈ₘ ImpDistribAxiomsₘ) ∨ₘ tail2
  have hRight1 :=
    Formula.Admissible.disj_right hBaseAdmissible
  have hRight2 :=
    Formula.Admissible.disj_right hRight1
  have hRight3 :=
    Formula.Admissible.disj_right hRight2
  have hRight4 :=
    Formula.Admissible.disj_right hRight3
  have hRight5 :=
    Formula.Admissible.disj_right hRight4
  have hRight6 :=
    Formula.Admissible.disj_right hRight5
  have hRight7 :=
    Formula.Admissible.disj_right hRight6
  have hTail8Admissible :
      Formula.Admissible tail8 := by
    simpa [tail8, tail9, tail10, tail11] using
      hRight7
  have hTail7 :
      Derives fs_zfc_support_raw_theory [] tail7 := by
    dsimp [tail7]
    exact FirstOrder.Derives.disjIntroLeft hMember
  have hTail6 :
      Derives fs_zfc_support_raw_theory [] tail6 := by
    dsimp [tail6]
    exact FirstOrder.Derives.disjIntroRight hTail7
  have hTail5 :
      Derives fs_zfc_support_raw_theory [] tail5 := by
    dsimp [tail5]
    exact FirstOrder.Derives.disjIntroRight hTail6
  have hTail4 :
      Derives fs_zfc_support_raw_theory [] tail4 := by
    dsimp [tail4]
    exact FirstOrder.Derives.disjIntroRight hTail5
  have hTail3 :
      Derives fs_zfc_support_raw_theory [] tail3 := by
    dsimp [tail3]
    exact FirstOrder.Derives.disjIntroRight hTail4
  have hTail2 :
      Derives fs_zfc_support_raw_theory [] tail2 := by
    dsimp [tail2]
    exact FirstOrder.Derives.disjIntroRight hTail3
  have hTail1 :
      Derives fs_zfc_support_raw_theory [] tail1 := by
    dsimp [tail1]
    exact FirstOrder.Derives.disjIntroRight hTail2
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        base_logical_axiom_condition code) := by
    simpa [base_logical_axiom_condition, tail1, tail2, tail3,
      tail4, tail5, tail6, tail7, tail8, tail9, tail10, tail11] using
      hTail1
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hFormulaHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort formula) =
        some formulaCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hFormulaQuote
  have hConclusionHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort conclusion) =
        some conclusionCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using
      hConclusionQuote
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp
            (Formula.imp formula conclusion)
            (Formula.imp
              (Formula.imp (Formula.neg formula) conclusion)
              conclusion)) =
        some code := by
    simp [code, GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, hFormulaHilbertQuote,
      hConclusionHilbertQuote]
  exact ⟨code, hWholeQuote, hLogical⟩

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
