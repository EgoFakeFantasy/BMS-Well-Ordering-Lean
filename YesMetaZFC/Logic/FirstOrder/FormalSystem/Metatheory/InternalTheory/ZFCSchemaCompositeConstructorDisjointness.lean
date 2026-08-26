import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaAtomicConstructorDisjointness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemSymbolWitnessBound
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.LogicalHead

/-
# ZFC schema 复合公式构造子的互斥

本模块只提供复合构造子之间的对象层互斥原语，用于规范公式 shift 行的
构造分支选择。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

/-- 否定码与全称码不可能相等：第二 token 分别是否定符号和全称符号。 -/
theorem fs_zfc_support_raw_negation_ne_universal_branch
    {Γ : Context signature}
    (negationBody boundVariable universalBody : SetTerm)
    (hNegationBody : Term.Admissible negationBody SetSort.set)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hUniversalBody : Term.Admissible universalBody SetSort.set)
    (hNegationBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        negationBody ∈ₘ FormulaCodeₘ)
    (hBoundVariableMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        boundVariable ∈ₘ VarSymₘ)
    (hUniversalBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        universalBody ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        neg_codeₘ(negationBody) ≐ₘ
          forall_codeₘ(boundVariable, universalBody)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hUniversalBodyCodeString :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        universalBody ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            (gq_formula_code_member_implies_code_string
              universalBody hUniversalBody))
      hUniversalBodyMember
  have hNegationOpening :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.theory_weaken
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_godel_quotation hFormula)
        (gq_negation_formula_opening_inversion
          (Γ := Γ) negationBody hNegationBody))
      hNegationBodyMember
  have hUniversalOpeningBase :=
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      (gq_universal_formula_opening_inversion
        boundVariable universalBody
        (hBoundVariable :=
          Term.check_admissible_complete hBoundVariable)
        (hBody :=
          Term.check_admissible_complete hUniversalBody))
  have hUniversalOpening :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        hUniversalOpeningBase)
      (FirstOrder.Derives.conjIntro
        hBoundVariableMember hUniversalBodyCodeString)
  have hUniversalPoint :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hUniversalOpening
  have hEqualityPoint :=
    gq_point_inversion_of_equality_of_theory
      neg_codeₘ(negationBody)
      (forall_codeₘ(boundVariable, universalBody))
      (numₘ(1))
      (numₘ(Numbered.logical_token .universal))
      hEquality hUniversalPoint
      (hLeft := Term.check_admissible_complete <|
        negation_formula_code_term_admissible
          negationBody hNegationBody)
      (hRight := Term.check_admissible_complete <|
        universal_formula_code_term_admissible
          boundVariable universalBody
          hBoundVariable hUniversalBody)
  have hTokenEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(Numbered.logical_token .negation) ≐ₘ
          numₘ(Numbered.logical_token .universal) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <|
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight hNegationOpening)
      (FirstOrder.Derives.conjElimRight hEqualityPoint)
  exact fs_zfc_support_raw_falsum_of_numeral_equality
      (by native_decide) hTokenEquality

/-!
蕴含码与全称码不可能相等。
蕴含左正文的开头若在零位出现左括号，则比较总码的第 1 位；
若只在一位出现左括号，则比较第 2 位，并通过变量符号零位的有限
token 条件排除绑定变量编码等于左括号。
-/
theorem fs_zfc_support_raw_implication_ne_universal_branch
    {Γ : Context signature}
    (implicationLeft implicationRight boundVariable universalBody : SetTerm)
    (hImplicationLeft : Term.Admissible implicationLeft SetSort.set)
    (hImplicationRight : Term.Admissible implicationRight SetSort.set)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hUniversalBody : Term.Admissible universalBody SetSort.set)
    (hImplicationLeftMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        implicationLeft ∈ₘ FormulaCodeₘ)
    (hImplicationRightMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        implicationRight ∈ₘ FormulaCodeₘ)
    (hBoundVariableMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        boundVariable ∈ₘ VarSymₘ)
    (hUniversalBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        universalBody ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        imp_codeₘ(implicationLeft, implicationRight) ≐ₘ
          forall_codeₘ(boundVariable, universalBody)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hUniversalBodyCodeString :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        universalBody ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          (gq_formula_code_member_implies_code_string
            universalBody hUniversalBody))
      hUniversalBodyMember
  have hUniversalOpeningBase :=
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      (gq_universal_formula_opening_inversion
        boundVariable universalBody
        (hBoundVariable :=
          Term.check_admissible_complete hBoundVariable)
        (hBody :=
          Term.check_admissible_complete hUniversalBody))
  have hUniversalOpening :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        hUniversalOpeningBase)
      (FirstOrder.Derives.conjIntro
        hBoundVariableMember hUniversalBodyCodeString)
  have hUniversalPointOne :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ((numₘ(1) ∈ₘ
            domₘ(forall_codeₘ(boundVariable, universalBody))) ∧ₘ
          ((forall_codeₘ(boundVariable, universalBody) ·ₘ
              numₘ(1)) ≐ₘ
            numₘ(Numbered.logical_token .universal))) :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hUniversalOpening
  have hUniversalPointTwo :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ((numₘ(2) ∈ₘ
            domₘ(forall_codeₘ(boundVariable, universalBody))) ∧ₘ
          ((forall_codeₘ(boundVariable, universalBody) ·ₘ
              numₘ(2)) ≐ₘ
            (boundVariable ·ₘ numₘ(0)))) :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight hUniversalOpening
  have hImplicationOpening :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          (gq_formula_code_member_implies_opening
            implicationLeft hImplicationLeft))
      hImplicationLeftMember
  unfold formula_code_left_opening_condition at hImplicationOpening
  have hImplicationLeftFinite :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      implicationLeft hImplicationLeft hImplicationLeftMember
  have hImplicationRightFinite :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      implicationRight hImplicationRight hImplicationRightMember
  apply FirstOrder.Derives.disjElim hImplicationOpening
  · let Δ : Context signature :=
      (((numₘ(0) ∈ₘ domₘ(implicationLeft)) ∧ₘ
        ((implicationLeft ·ₘ numₘ(0)) ≐ₘ
          numₘ(Numbered.logical_token .leftParenthesis)))) :: Γ
    have hLeftPoint :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          ((numₘ(0) ∈ₘ domₘ(implicationLeft)) ∧ₘ
            ((implicationLeft ·ₘ numₘ(0)) ≐ₘ
              numₘ(Numbered.logical_token .leftParenthesis))) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hShift :=
      gq_implication_formula_left_point_at_standard_offset_of_theory
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ)
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_godel_quotation hFormula)
        implicationLeft implicationRight 0
        (FirstOrder.Derives.context_weaken_cons
          hImplicationLeftFinite)
        (FirstOrder.Derives.context_weaken_cons
          hImplicationRightFinite)
        (FirstOrder.Derives.conjElimLeft hLeftPoint)
        (hLeft := Term.check_admissible_complete
          hImplicationLeft)
        (hRight := Term.check_admissible_complete
          hImplicationRight)
    have hImplicationPointOne :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          ((numₘ(1) ∈ₘ
              domₘ(imp_codeₘ(implicationLeft, implicationRight))) ∧ₘ
            ((imp_codeₘ(implicationLeft, implicationRight) ·ₘ
                numₘ(1)) ≐ₘ
              numₘ(Numbered.logical_token
                .leftParenthesis))) :=
      FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjElimLeft hShift)
        (Metatheory.Derives.equality_trans
          (FirstOrder.Derives.conjElimRight hShift)
          (FirstOrder.Derives.conjElimRight hLeftPoint))
    have hEqualityPointOne :=
      gq_point_inversion_of_equality_of_theory
        (imp_codeₘ(implicationLeft, implicationRight))
        (forall_codeₘ(boundVariable, universalBody))
        (numₘ(1))
        (numₘ(Numbered.logical_token .universal))
        hEquality hUniversalPointOne
        (hLeft := Term.check_admissible_complete <|
          implication_formula_code_term_admissible
            implicationLeft implicationRight
            hImplicationLeft hImplicationRight)
        (hRight := Term.check_admissible_complete <|
          universal_formula_code_term_admissible
            boundVariable universalBody
            hBoundVariable hUniversalBody)
    have hTokenEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(Numbered.logical_token
            .leftParenthesis) ≐ₘ
            numₘ(Numbered.logical_token .universal) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm <|
          FirstOrder.Derives.conjElimRight
            hImplicationPointOne)
        (FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.context_weaken_cons
            hEqualityPointOne))
    exact fs_zfc_support_raw_falsum_of_numeral_equality
      (by native_decide)
      hTokenEquality
  · let Δ : Context signature :=
      (((numₘ(1) ∈ₘ domₘ(implicationLeft)) ∧ₘ
        ((implicationLeft ·ₘ numₘ(1)) ≐ₘ
          numₘ(Numbered.logical_token .leftParenthesis)))) :: Γ
    have hLeftPoint :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          ((numₘ(1) ∈ₘ domₘ(implicationLeft)) ∧ₘ
            ((implicationLeft ·ₘ numₘ(1)) ≐ₘ
              numₘ(Numbered.logical_token .leftParenthesis))) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hShift :=
      gq_implication_formula_left_point_at_standard_offset_of_theory
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ)
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_godel_quotation hFormula)
        implicationLeft implicationRight 1
        (FirstOrder.Derives.context_weaken_cons
          hImplicationLeftFinite)
        (FirstOrder.Derives.context_weaken_cons
          hImplicationRightFinite)
        (FirstOrder.Derives.conjElimLeft hLeftPoint)
        (hLeft := Term.check_admissible_complete
          hImplicationLeft)
        (hRight := Term.check_admissible_complete
          hImplicationRight)
    have hImplicationPointTwo :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          ((numₘ(2) ∈ₘ
              domₘ(imp_codeₘ(implicationLeft, implicationRight))) ∧ₘ
            ((imp_codeₘ(implicationLeft, implicationRight) ·ₘ
                numₘ(2)) ≐ₘ
              numₘ(Numbered.logical_token
                .leftParenthesis))) :=
      FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjElimLeft hShift)
        (Metatheory.Derives.equality_trans
          (FirstOrder.Derives.conjElimRight hShift)
          (FirstOrder.Derives.conjElimRight hLeftPoint))
    have hEqualityPointTwo :=
      gq_point_inversion_of_equality_of_theory
        (imp_codeₘ(implicationLeft, implicationRight))
        (forall_codeₘ(boundVariable, universalBody))
        (numₘ(2))
        (boundVariable ·ₘ numₘ(0))
        hEquality
        (FirstOrder.Derives.conjIntro
          (FirstOrder.Derives.conjElimLeft
            hUniversalPointTwo)
          (FirstOrder.Derives.conjElimRight
            hUniversalPointTwo))
        (hLeft := Term.check_admissible_complete <|
          implication_formula_code_term_admissible
            implicationLeft implicationRight
            hImplicationLeft hImplicationRight)
        (hRight := Term.check_admissible_complete <|
          universal_formula_code_term_admissible
            boundVariable universalBody
            hBoundVariable hUniversalBody)
    have hVariableValue :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (boundVariable ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis) :=
      Metatheory.Derives.equality_symm <|
        Metatheory.Derives.equality_trans
          (Metatheory.Derives.equality_symm <|
            FirstOrder.Derives.conjElimRight
              hImplicationPointTwo)
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.context_weaken_cons
              hEqualityPointTwo))
    have hVariableCondition :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_variable_token_condition
            (numₘ(Numbered.logical_token
              .leftParenthesis)) := by
      exact
        gq_variable_symbol_zero_value_implies_token_condition_of_theory
          (T := fs_zfc_support_raw_theory)
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_standard_sequence_semantics
              hFormula)
          (fun _ hFormula =>
            fs_zfc_support_raw_theory_sentence hFormula)
          boundVariable
          (Numbered.logical_token .leftParenthesis)
          hBoundVariable
          (FirstOrder.Derives.context_weaken_cons
            hBoundVariableMember)
          hVariableValue
    have hVariableConditionNot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          ¬ₘ fs_variable_token_condition
            (numₘ(Numbered.logical_token
              .leftParenthesis)) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          (gq_fs_variable_token_condition_not
            (Numbered.logical_token .leftParenthesis)
            (by native_decide))
    exact FirstOrder.Derives.negElim
      hVariableCondition hVariableConditionNot

/-!
否定规范序列不能伪装成蕴含码。

这里把 Gödel quotation 层的 checked slice rejection 提升到 ZFC raw
支持理论；调用者只需提供两个候选正文的 `FormulaCodeₘ` 成员和规范
序列的有限公式码证书。
-/
theorem fs_zfc_support_raw_standard_negation_ne_implication_branch
    {Γ : Context signature}
    (bodyTokens : List Nat)
    (implicationLeft implicationRight : SetTerm)
    (hLeft : Term.Admissible implicationLeft SetSort.set)
    (hRight : Term.Admissible implicationRight SetSort.set)
    (hTokens :
      GodelQuotation.FSFormulaTokens
        (GodelQuotation.Numbered.negation_tokens bodyTokens))
    (hImplicationLeftMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        implicationLeft ∈ₘ FormulaCodeₘ)
    (hImplicationRightMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        implicationRight ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence
          (GodelQuotation.Numbered.negation_tokens bodyTokens) ≐ₘ
        imp_codeₘ(implicationLeft, implicationRight)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let condition : SetFormula :=
    (((implicationLeft ∈ₘ FormulaCodeₘ) ∧ₘ
        (implicationRight ∈ₘ FormulaCodeₘ)) ∧ₘ
      (standard_token_sequence
        (GodelQuotation.Numbered.negation_tokens bodyTokens) ≐ₘ
        imp_codeₘ(implicationLeft, implicationRight)))
  have hConditionAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] condition := by
    dsimp only [condition]
    exact FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        hImplicationLeftMember hImplicationRightMember)
      hEquality
  have hLeftCheck :
      Term.CheckCertificate implicationLeft SetSort.set :=
    Term.check_admissible_complete hLeft
  have hRightCheck :
      Term.CheckCertificate implicationRight SetSort.set :=
    Term.check_admissible_complete hRight
  have hRejectGodel :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        condition ⟶ₘ Formula.falsum := by
    simpa only [condition] using
      (GodelQuotation.gq_standard_negation_tokens_implication_equality_rejection
        bodyTokens implicationLeft implicationRight
        (hLeft := hLeftCheck) (hRight := hRightCheck)
        hTokens)
  have hRejectZfc :
      ⊢ₘ[fs_zfc_support_raw_theory]
        condition ⟶ₘ Formula.falsum :=
    fs_zfc_support_raw_derives_of_godel_quotation hRejectGodel
  have hRejectZfcAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        condition ⟶ₘ Formula.falsum :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hRejectZfc
  exact FirstOrder.Derives.impElim hRejectZfcAt hConditionAt

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
