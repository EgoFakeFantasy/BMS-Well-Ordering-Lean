import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.Freshness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaShape

/-!
# 复合公式码的开头反演

本模块只恢复复合公式构造结果的固定开头。正文仍保持为任意对象内公式码，
因此这些接口可直接用于标准 token 行的有限 parser 拒绝，而不要求先把正文
提取回 Lean 宿主语法树。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 公式码成员在任意局部上下文中给出有限序列条件。 -/
theorem gq_formula_code_member_implies_finite_sequence
    {Γ : Context signature}
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      finite_sequence_condition code := by
  have hCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_formula_code_member_implies_code_string
          code hCode))
      hMember
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (gq_weaken_standard_sequence
      (code_string_member_implies_finite_sequence_at
          code hCode)))
    hCodeString

/-- 项码谓词在任意局部上下文中给出有限序列条件。 -/
theorem gq_term_code_implies_finite_sequence
    {Γ : Context signature}
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hPredicate :
      Γ ⊢ₘ[godel_quotation_theory]
        term_codeₘ(code)) :
    Γ ⊢ₘ[godel_quotation_theory]
      finite_sequence_condition code := by
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_term_code_definition_instance
          code hCode))
      hPredicate
  have hCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_term_code_member_implies_code_string
          code hCode))
      hMember
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (gq_weaken_standard_sequence
        (code_string_member_implies_finite_sequence_at
          code hCode)))
    hCodeString

/--
四段左结合拼接保留第一段的已知点。
该机械接口统一承担否定与后续谓词应用开头反演中的拼接传播。
-/
theorem gq_four_part_left_point
    {Γ : Context signature}
    (first second third fourth index value : SetTerm)
    (hFirstFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first)
    (hSecondFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition second)
    (hThirdFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition third)
    (hFourthFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition fourth)
    (hIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        index ∈ₘ domₘ(first))
    (hValue :
      Γ ⊢ₘ[godel_quotation_theory]
        (first ·ₘ index) ≐ₘ value)
    (hFirst : Term.CheckCertificate first SetSort.set := by
      prove_term_check)
    (hSecond : Term.CheckCertificate second SetSort.set := by
      prove_term_check)
    (hThird : Term.CheckCertificate third SetSort.set := by
      prove_term_check)
    (hFourth : Term.CheckCertificate fourth SetSort.set := by
      prove_term_check)
    (hIndexTerm : Term.CheckCertificate index SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((index ∈ₘ
          domₘ(((first ⌢ₘ second) ⌢ₘ third) ⌢ₘ fourth)) ∧ₘ
        ((((first ⌢ₘ second) ⌢ₘ third) ⌢ₘ fourth) ·ₘ index) ≐ₘ
          value) := by
  let firstStage := first ⌢ₘ second
  let secondStage := firstStage ⌢ₘ third
  have hFirstPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((index ∈ₘ domₘ(firstStage)) ∧ₘ
          ((firstStage ·ₘ index) ≐ₘ value)) := by
    simpa [firstStage] using
      gq_concatenation_left_point
        first second index value
        hFirstFinite hSecondFinite hIndex hValue
  have hFirstStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition firstStage := by
    simpa [firstStage] using
      gq_concatenation_finite
        first second hFirstFinite hSecondFinite
  have hSecondPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((index ∈ₘ domₘ(secondStage)) ∧ₘ
          ((secondStage ·ₘ index) ≐ₘ value)) := by
    simpa [secondStage] using
      gq_concatenation_left_point
        firstStage third index value
        hFirstStageFinite hThirdFinite
        (FirstOrder.Derives.conjElimLeft hFirstPoint)
        (FirstOrder.Derives.conjElimRight hFirstPoint)
  have hSecondStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition secondStage := by
    simpa [secondStage] using
      gq_concatenation_finite
        firstStage third
        hFirstStageFinite hThirdFinite
  simpa [firstStage, secondStage] using
    gq_concatenation_left_point
      secondStage fourth index value
      hSecondStageFinite hFourthFinite
      (FirstOrder.Derives.conjElimLeft hSecondPoint)
      (FirstOrder.Derives.conjElimRight hSecondPoint)

/-- 否定构造结果的前两个 token 必为左括号与否定符号。 -/
theorem gq_negation_formula_opening_inversion
    {Γ : Context signature}
    (body : SetTerm)
    (hBody : Term.Admissible body SetSort.set) :
    Γ ⊢ₘ[godel_quotation_theory]
      (body ∈ₘ FormulaCodeₘ) ⟶ₘ
        (((numₘ(0) ∈ₘ domₘ(neg_codeₘ(body))) ∧ₘ
            ((neg_codeₘ(body) ·ₘ numₘ(0)) ≐ₘ
              numₘ(Numbered.logical_token
                .leftParenthesis))) ∧ₘ
          ((numₘ(1) ∈ₘ domₘ(neg_codeₘ(body))) ∧ₘ
            ((neg_codeₘ(body) ·ₘ numₘ(1)) ≐ₘ
              numₘ(Numbered.logical_token
                .negation)))) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let negationSymbol :=
    logical_symbol_code_term .negation
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let rawCode :=
    ((leftParenthesis ⌢ₘ negationSymbol) ⌢ₘ body) ⌢ₘ
      rightParenthesis
  let membership : SetFormula :=
    body ∈ₘ FormulaCodeₘ
  let Δ : Context signature := membership :: Γ
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hBody formula_code_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  have hMember :
      Δ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.assumption
      (by simp [Δ, membership])
  have hBodyFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body :=
    gq_formula_code_member_implies_finite_sequence
      body hBody hMember
  have hLeftFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .leftParenthesis
  have hNegationFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition negationSymbol := by
    simpa [negationSymbol] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .negation
  have hRightFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .rightParenthesis
  have hLeftPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(leftParenthesis)) ∧ₘ
          ((leftParenthesis ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
    simpa [leftParenthesis] using
      gq_standard_token_sequence_point_inversion
        leftParenthesis
        [Numbered.logical_token .leftParenthesis]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp)
          (logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis))
        (by simp)
  have hNegationPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(negationSymbol)) ∧ₘ
          ((negationSymbol ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .negation))) := by
    simpa [negationSymbol] using
      gq_standard_token_sequence_point_inversion
        negationSymbol
        [Numbered.logical_token .negation]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp)
          (logical_symbol_code_eq_standard_token_sequence
            .negation))
        (by simp)
  have hRawZero :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(rawCode)) ∧ₘ
          ((rawCode ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
    simpa [rawCode] using
      gq_four_part_left_point
        leftParenthesis negationSymbol body
        rightParenthesis
        (numₘ(0))
        (numₘ(Numbered.logical_token
          .leftParenthesis))
        hLeftFinite hNegationFinite hBodyFinite hRightFinite
        (FirstOrder.Derives.conjElimLeft hLeftPoint)
        (FirstOrder.Derives.conjElimRight hLeftPoint)
  have hPrefixFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          (leftParenthesis ⌢ₘ negationSymbol) := by
    exact gq_concatenation_finite
      leftParenthesis negationSymbol
      hLeftFinite hNegationFinite
  have hPrefixOneRaw :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1) ∈ₘ
            domₘ(leftParenthesis ⌢ₘ negationSymbol)) ∧ₘ
          (((leftParenthesis ⌢ₘ negationSymbol) ·ₘ
              numₘ(1)) ≐ₘ
            (negationSymbol ·ₘ numₘ(0)))) := by
    simpa using
      gq_concatenation_right_zero_at_standard_length
        leftParenthesis negationSymbol
        [Numbered.logical_token .leftParenthesis]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp)
          (logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis))
        hNegationFinite
        (FirstOrder.Derives.conjElimLeft hNegationPoint)
  have hPrefixOne :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1) ∈ₘ
            domₘ(leftParenthesis ⌢ₘ negationSymbol)) ∧ₘ
          (((leftParenthesis ⌢ₘ negationSymbol) ·ₘ
              numₘ(1)) ≐ₘ
            numₘ(Numbered.logical_token
              .negation))) :=
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjElimLeft hPrefixOneRaw)
      (Metatheory.Derives.equality_trans
        (FirstOrder.Derives.conjElimRight hPrefixOneRaw)
        (FirstOrder.Derives.conjElimRight hNegationPoint))
  have hRawOne :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1) ∈ₘ domₘ(rawCode)) ∧ₘ
          ((rawCode ·ₘ numₘ(1)) ≐ₘ
            numₘ(Numbered.logical_token
              .negation))) := by
    let bodyStage :=
      (leftParenthesis ⌢ₘ negationSymbol) ⌢ₘ body
    have hBodyStageFinite :
        Δ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition bodyStage := by
      simpa [bodyStage] using
        gq_concatenation_finite
          (leftParenthesis ⌢ₘ negationSymbol)
          body hPrefixFinite hBodyFinite
    have hBodyStagePoint :
        Δ ⊢ₘ[godel_quotation_theory]
          ((numₘ(1) ∈ₘ domₘ(bodyStage)) ∧ₘ
            ((bodyStage ·ₘ numₘ(1)) ≐ₘ
              numₘ(Numbered.logical_token
                .negation))) := by
      simpa [bodyStage] using
        gq_concatenation_left_point
          (leftParenthesis ⌢ₘ negationSymbol)
          body (numₘ(1))
          (numₘ(Numbered.logical_token .negation))
          hPrefixFinite hBodyFinite
          (FirstOrder.Derives.conjElimLeft hPrefixOne)
          (FirstOrder.Derives.conjElimRight hPrefixOne)
    simpa [rawCode, bodyStage] using
      gq_concatenation_left_point
        bodyStage rightParenthesis
        (numₘ(1))
        (numₘ(Numbered.logical_token .negation))
        hBodyStageFinite hRightFinite
        (FirstOrder.Derives.conjElimLeft hBodyStagePoint)
        (FirstOrder.Derives.conjElimRight hBodyStagePoint)
  have hCodeRaw :
      Δ ⊢ₘ[godel_quotation_theory]
        neg_codeₘ(body) ≐ₘ rawCode := by
    have hDefinition :
        Δ ⊢ₘ[godel_quotation_theory]
          negation_formula_code_definition_instance
            body (neg_codeₘ(body)) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp)
        (gq_weaken_formula_constructor
          (negation_formula_code_definition_instance_derives
            body (neg_codeₘ(body))
            hBody
            (negation_formula_code_term_admissible
              body hBody)))
    have hReflexive :
        Δ ⊢ₘ[godel_quotation_theory]
          neg_codeₘ(body) ≐ₘ neg_codeₘ(body) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp)
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (neg_codeₘ(body)))
    simpa [rawCode, leftParenthesis,
      negationSymbol, rightParenthesis,
      negation_formula_code_definition_instance,
      negation_formula_string_term] using
      FirstOrder.Derives.iffElimRight
        hDefinition hReflexive
  have hCodeZero :=
    gq_point_inversion_of_equality
      (neg_codeₘ(body)) rawCode
      (numₘ(0))
      (numₘ(Numbered.logical_token
        .leftParenthesis))
      hCodeRaw hRawZero
  have hCodeOne :=
    gq_point_inversion_of_equality
      (neg_codeₘ(body)) rawCode
      (numₘ(1))
      (numₘ(Numbered.logical_token
        .negation))
      hCodeRaw hRawOne
  exact FirstOrder.Derives.conjIntro
    hCodeZero hCodeOne

/-- 蕴含构造结果的首 token 必为左括号。 -/
theorem gq_implication_formula_opening_inversion
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((left ∈ₘ FormulaCodeₘ) ∧ₘ
        (right ∈ₘ FormulaCodeₘ)) ⟶ₘ
          ((numₘ(0) ∈ₘ
              domₘ(imp_codeₘ(left, right))) ∧ₘ
            ((imp_codeₘ(left, right) ·ₘ numₘ(0)) ≐ₘ
              numₘ(Numbered.logical_token
                .leftParenthesis))) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let implicationSymbol :=
    logical_symbol_code_term .implication
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let rawCode :=
    (((leftParenthesis ⌢ₘ left) ⌢ₘ
        implicationSymbol) ⌢ₘ right) ⌢ₘ
      rightParenthesis
  let precondition : SetFormula :=
    (left ∈ₘ FormulaCodeₘ) ∧ₘ
      (right ∈ₘ FormulaCodeₘ)
  let Δ : Context signature := precondition :: Γ
  have hPreconditionAdmissible :
      Formula.Admissible precondition := by
    simpa [precondition] using
      Formula.Admissible.conj
        (membership_formula_admissible
          hLeft formula_code_set_term_admissible)
        (membership_formula_admissible
          hRight formula_code_set_term_admissible)
  nd_apply FirstOrder.Derives.impIntro
  have hPrecondition :
      Δ ⊢ₘ[godel_quotation_theory]
        precondition :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
  have hLeftMember :
      Δ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.conjElimLeft hPrecondition
  have hRightMember :
      Δ ⊢ₘ[godel_quotation_theory]
        right ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.conjElimRight hPrecondition
  have hLeftFinite :=
    gq_formula_code_member_implies_finite_sequence
      left hLeft hLeftMember
  have hRightFinite :=
    gq_formula_code_member_implies_finite_sequence
      right hRight hRightMember
  have hLeftParenthesisFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .leftParenthesis
  have hImplicationFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition implicationSymbol := by
    simpa [implicationSymbol] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .implication
  have hRightParenthesisFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .rightParenthesis
  have hLeftParenthesisPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(leftParenthesis)) ∧ₘ
          ((leftParenthesis ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
    simpa [leftParenthesis] using
      gq_standard_token_sequence_point_inversion
        leftParenthesis
        [Numbered.logical_token .leftParenthesis]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp)
          (logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis))
        (by simp)
  have hFirstStageFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          (leftParenthesis ⌢ₘ left) :=
    gq_concatenation_finite
      leftParenthesis left
      hLeftParenthesisFinite hLeftFinite
  have hFirstStagePoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ
            domₘ(leftParenthesis ⌢ₘ left)) ∧ₘ
          (((leftParenthesis ⌢ₘ left) ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) :=
    gq_concatenation_left_point
      leftParenthesis left (numₘ(0))
      (numₘ(Numbered.logical_token .leftParenthesis))
      hLeftParenthesisFinite hLeftFinite
      (FirstOrder.Derives.conjElimLeft
        hLeftParenthesisPoint)
      (FirstOrder.Derives.conjElimRight
        hLeftParenthesisPoint)
  have hSecondStageFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          ((leftParenthesis ⌢ₘ left) ⌢ₘ
            implicationSymbol) :=
    gq_concatenation_finite
      (leftParenthesis ⌢ₘ left)
      implicationSymbol
      hFirstStageFinite hImplicationFinite
  have hSecondStagePoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ
            domₘ((leftParenthesis ⌢ₘ left) ⌢ₘ
              implicationSymbol)) ∧ₘ
          ((((leftParenthesis ⌢ₘ left) ⌢ₘ
              implicationSymbol) ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) :=
    gq_concatenation_left_point
      (leftParenthesis ⌢ₘ left)
      implicationSymbol (numₘ(0))
      (numₘ(Numbered.logical_token .leftParenthesis))
      hFirstStageFinite hImplicationFinite
      (FirstOrder.Derives.conjElimLeft hFirstStagePoint)
      (FirstOrder.Derives.conjElimRight hFirstStagePoint)
  have hThirdStageFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          (((leftParenthesis ⌢ₘ left) ⌢ₘ
            implicationSymbol) ⌢ₘ right) :=
    gq_concatenation_finite
      ((leftParenthesis ⌢ₘ left) ⌢ₘ
        implicationSymbol)
      right hSecondStageFinite hRightFinite
  have hThirdStagePoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ
            domₘ(((leftParenthesis ⌢ₘ left) ⌢ₘ
              implicationSymbol) ⌢ₘ right)) ∧ₘ
          (((((leftParenthesis ⌢ₘ left) ⌢ₘ
              implicationSymbol) ⌢ₘ right) ·ₘ
                numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) :=
    gq_concatenation_left_point
      ((leftParenthesis ⌢ₘ left) ⌢ₘ
        implicationSymbol)
      right (numₘ(0))
      (numₘ(Numbered.logical_token .leftParenthesis))
      hSecondStageFinite hRightFinite
      (FirstOrder.Derives.conjElimLeft hSecondStagePoint)
      (FirstOrder.Derives.conjElimRight hSecondStagePoint)
  have hRawPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(rawCode)) ∧ₘ
          ((rawCode ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
    simpa [rawCode] using
      gq_concatenation_left_point
        (((leftParenthesis ⌢ₘ left) ⌢ₘ
          implicationSymbol) ⌢ₘ right)
        rightParenthesis (numₘ(0))
        (numₘ(Numbered.logical_token .leftParenthesis))
        hThirdStageFinite hRightParenthesisFinite
        (FirstOrder.Derives.conjElimLeft hThirdStagePoint)
        (FirstOrder.Derives.conjElimRight hThirdStagePoint)
  have hCodeRaw :
      Δ ⊢ₘ[godel_quotation_theory]
        imp_codeₘ(left, right) ≐ₘ rawCode := by
    have hDefinition :
        Δ ⊢ₘ[godel_quotation_theory]
          implication_formula_code_definition_instance
            left right (imp_codeₘ(left, right)) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp)
        (gq_weaken_formula_constructor
          (implication_formula_code_definition_instance_derives
            left right (imp_codeₘ(left, right))
            hLeft hRight
            (implication_formula_code_term_admissible
              left right hLeft hRight)))
    have hReflexive :
        Δ ⊢ₘ[godel_quotation_theory]
          imp_codeₘ(left, right) ≐ₘ
            imp_codeₘ(left, right) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp)
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (imp_codeₘ(left, right)))
    simpa [rawCode, leftParenthesis,
      implicationSymbol, rightParenthesis,
      implication_formula_code_definition_instance,
      implication_formula_string_term] using
      FirstOrder.Derives.iffElimRight
        hDefinition hReflexive
  exact gq_point_inversion_of_equality
    (imp_codeₘ(left, right)) rawCode
    (numₘ(0))
    (numₘ(Numbered.logical_token
      .leftParenthesis))
    hCodeRaw hRawPoint

/-! ## 原子公式码的开头反演 -/

/--
二元原子构造只要关系符号本身是有限序列，首 token 就固定为左括号。
该接口统一覆盖等式与隶属原子，不展开关系符号的具体编号。
-/
theorem gq_binary_atomic_formula_opening_inversion
    {Γ : Context signature}
    (relation left right : SetTerm)
    (hRelation : Term.Admissible relation SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hRelationFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition relation) :
    Γ ⊢ₘ[godel_quotation_theory]
      (term_codeₘ(left) ∧ₘ term_codeₘ(right)) ⟶ₘ
        ((numₘ(0) ∈ₘ
            domₘ(binary_atomic_formula_code_term
              relation left right)) ∧ₘ
          ((binary_atomic_formula_code_term
              relation left right ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let precondition : SetFormula :=
    term_codeₘ(left) ∧ₘ term_codeₘ(right)
  let Δ : Context signature := precondition :: Γ
  have hPreconditionAdmissible :
      Formula.Admissible precondition := by
    simpa [precondition] using
      Formula.Admissible.conj
        (by prove_admissible)
        (by prove_admissible)
  nd_apply FirstOrder.Derives.impIntro
  have hPrecondition :
      Δ ⊢ₘ[godel_quotation_theory]
        precondition :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
  have hLeftFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    gq_term_code_implies_finite_sequence
      left hLeft
      (FirstOrder.Derives.conjElimLeft
        hPrecondition)
  have hRightFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right :=
    gq_term_code_implies_finite_sequence
      right hRight
      (FirstOrder.Derives.conjElimRight
        hPrecondition)
  have hRelationFiniteΔ :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition relation :=
    FirstOrder.Derives.context_weaken_cons
      hRelationFinite
  have hLeftParenthesisFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .leftParenthesis
  have hRightParenthesisFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .rightParenthesis
  have hLeftParenthesisPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(leftParenthesis)) ∧ₘ
          ((leftParenthesis ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
    simpa [leftParenthesis] using
      gq_standard_token_sequence_point_inversion
        leftParenthesis
        [Numbered.logical_token .leftParenthesis]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp)
          (logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis))
        (by simp)
  have hPrefixPoint :=
    gq_four_part_left_point
      leftParenthesis left relation right
      (numₘ(0))
      (numₘ(Numbered.logical_token
        .leftParenthesis))
      hLeftParenthesisFinite hLeftFinite
      hRelationFiniteΔ hRightFinite
      (FirstOrder.Derives.conjElimLeft
        hLeftParenthesisPoint)
      (FirstOrder.Derives.conjElimRight
        hLeftParenthesisPoint)
  have hPrefixFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          (((leftParenthesis ⌢ₘ left) ⌢ₘ relation) ⌢ₘ
            right) := by
    exact gq_concatenation_finite
      ((leftParenthesis ⌢ₘ left) ⌢ₘ relation)
      right
      (gq_concatenation_finite
        (leftParenthesis ⌢ₘ left) relation
        (gq_concatenation_finite
          leftParenthesis left
          hLeftParenthesisFinite hLeftFinite)
        hRelationFiniteΔ)
      hRightFinite
  simpa [leftParenthesis, rightParenthesis,
    binary_atomic_formula_code_term] using
    gq_concatenation_left_point
      (((leftParenthesis ⌢ₘ left) ⌢ₘ relation) ⌢ₘ
        right)
      rightParenthesis (numₘ(0))
      (numₘ(Numbered.logical_token .leftParenthesis))
      hPrefixFinite hRightParenthesisFinite
      (FirstOrder.Derives.conjElimLeft hPrefixPoint)
      (FirstOrder.Derives.conjElimRight hPrefixPoint)

/-- 等式原子编码的首 token 必为左括号。 -/
theorem gq_equality_formula_opening_inversion
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Γ ⊢ₘ[godel_quotation_theory]
      (term_codeₘ(left) ∧ₘ term_codeₘ(right)) ⟶ₘ
        ((numₘ(0) ∈ₘ
            domₘ(equality_atomic_formula_code_term
              left right)) ∧ₘ
          ((equality_atomic_formula_code_term
              left right ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
  simpa [equality_atomic_formula_code_term] using
    gq_binary_atomic_formula_opening_inversion
      (Γ := Γ)
      equality_symbol_code_term left right
      (logical_symbol_code_term_admissible .equality)
      hLeft hRight
      (by
        simpa [equality_symbol_code_term] using
          gq_logical_symbol_code_finite_sequence
            (Γ := Γ) .equality)

/-- 隶属原子编码的首 token 必为左括号。 -/
theorem gq_membership_formula_opening_inversion
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Γ ⊢ₘ[godel_quotation_theory]
      (term_codeₘ(left) ∧ₘ term_codeₘ(right)) ⟶ₘ
        ((numₘ(0) ∈ₘ
            domₘ(membership_atomic_formula_code_term
              left right)) ∧ₘ
          ((membership_atomic_formula_code_term
              left right ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
  simpa [membership_atomic_formula_code_term] using
    gq_binary_atomic_formula_opening_inversion
      (Γ := Γ)
      membership_symbol_code_term left right
      membership_symbol_code_term_admissible
      hLeft hRight
      (gq_finite_sequence_of_eq_standard_token_sequence
        membership_symbol_code_term
        [Numbered.membership_token]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp)
          membership_symbol_code_eq_standard_token_sequence))

/-! ## 标准 token 序列的固定点拒绝 -/

/--
若构造码在某位置的固定 token 与标准输入在同一位置的具体 token 不同，则对象层
直接推出矛盾。该接口只比较两个有限 numeral，不依赖语义解释。
-/
theorem gq_standard_token_sequence_falsum_of_point_mismatch
    {Γ : Context signature}
    (tokens : List Nat)
    (constructor : SetTerm)
    (index actual expected : Nat)
    (hGet : tokens[index]? = some actual)
    (hNe : actual ≠ expected)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ constructor)
    (hConstructorPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(index) ∈ₘ domₘ(constructor)) ∧ₘ
          ((constructor ·ₘ numₘ(index)) ≐ₘ
            numₘ(expected))))
    (hConstructor :
      Term.CheckCertificate constructor SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let standardCode := standard_token_sequence tokens
  have hStandardExpected :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(index) ∈ₘ domₘ(standardCode)) ∧ₘ
          ((standardCode ·ₘ numₘ(index)) ≐ₘ
            numₘ(expected))) := by
    simpa [standardCode] using
      gq_point_inversion_of_equality
        standardCode constructor
        (numₘ(index)) (numₘ(expected))
        (by simpa [standardCode] using hEquality)
        hConstructorPoint
  have hStandardActual :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(index) ∈ₘ domₘ(standardCode)) ∧ₘ
          ((standardCode ·ₘ numₘ(index)) ≐ₘ
            numₘ(actual))) := by
    simpa [standardCode] using
      gq_standard_token_sequence_point_inversion
        standardCode tokens
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp)
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) standardCode))
        hGet
  have hNumeralEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(actual) ≐ₘ numₘ(expected) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        (FirstOrder.Derives.conjElimRight
          hStandardActual))
      (FirstOrder.Derives.conjElimRight
        hStandardExpected)
  exact FirstOrder.Derives.negElim
    hNumeralEquality
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (gq_weaken_standard_sequence
        (standard_sequence_finite_numeral_ne hNe)))

/--
任意 Gödel quotation 理论扩张中的固定点 token mismatch checked replay。
-/
theorem gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
    {T : SetTheory} {Γ : Context signature}
    (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (tokens : List Nat)
    (constructor : SetTerm)
    (index actual expected : Nat)
    (hGet : tokens[index]? = some actual)
    (hNe : actual ≠ expected)
    (hEquality :
      Γ ⊢ₘ[T]
        standard_token_sequence tokens ≐ₘ constructor)
    (hConstructorPoint :
      Γ ⊢ₘ[T]
        ((numₘ(index) ∈ₘ domₘ(constructor)) ∧ₘ
          ((constructor ·ₘ numₘ(index)) ≐ₘ
            numₘ(expected))))
    (hConstructor :
      Term.CheckCertificate constructor SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[T]
      Formula.falsum := by
  let Δ : Context signature :=
    (standard_token_sequence tokens ≐ₘ constructor) ::
      (((numₘ(index) ∈ₘ domₘ(constructor)) ∧ₘ
        ((constructor ·ₘ numₘ(index)) ≐ₘ
          numₘ(expected)))) :: []
  have hEqualityAt :
      Δ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ constructor :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hConstructorPointAt :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(index) ∈ₘ domₘ(constructor)) ∧ₘ
          ((constructor ·ₘ numₘ(index)) ≐ₘ
            numₘ(expected))) :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hFalsum :=
    gq_standard_token_sequence_falsum_of_point_mismatch
      tokens constructor index actual expected
      hGet hNe hEqualityAt hConstructorPointAt
      (hConstructor := hConstructor)
  apply FirstOrder.Derives.multi_cut
    (T := T) (Γ := Γ) (premises := Δ)
  · intro formula hFormula
    simp [Δ] at hFormula
    rcases hFormula with rfl | rfl
    · exact hEquality
    · exact hConstructorPoint
  · exact
      (FirstOrder.Derives.theory_weaken
        hTheory hFalsum).context_weaken_append

/--
若标准输入在某位置不是构造码要求的固定 token，则对象层直接推出矛盾。

与具体 mismatch 版本相比，本接口同时覆盖该位置超出输入长度的情形；后者只用
标准序列定义域等于输入长度以及有限 numeral 的成员否定。
-/
theorem gq_standard_token_sequence_falsum_of_point_not_expected
    {Γ : Context signature}
    (tokens : List Nat)
    (constructor : SetTerm)
    (index expected : Nat)
    (hNotExpected :
      tokens[index]? ≠ some expected)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ constructor)
    (hConstructorPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(index) ∈ₘ domₘ(constructor)) ∧ₘ
          ((constructor ·ₘ numₘ(index)) ≐ₘ
            numₘ(expected))))
    (hConstructor :
      Term.CheckCertificate constructor SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  cases hGet : tokens[index]? with
  | some actual =>
      have hNe : actual ≠ expected := by
        intro hEquality
        subst actual
        exact hNotExpected hGet
      exact
        gq_standard_token_sequence_falsum_of_point_mismatch
          tokens constructor index actual expected
          hGet hNe hEquality hConstructorPoint
  | none =>
      let standardCode : SetTerm :=
        standard_token_sequence tokens
      have hStandardPoint :
          Γ ⊢ₘ[godel_quotation_theory]
            ((numₘ(index) ∈ₘ domₘ(standardCode)) ∧ₘ
              ((standardCode ·ₘ numₘ(index)) ≐ₘ
                numₘ(expected))) := by
        simpa [standardCode] using
          gq_point_inversion_of_equality
            standardCode constructor
            (numₘ(index)) (numₘ(expected))
            (by simpa [standardCode] using hEquality)
            hConstructorPoint
      have hNotLt : ¬ index < tokens.length := by
        intro hLt
        have hSome :
            tokens[index]? = some tokens[index] :=
          List.getElem?_eq_getElem hLt
        rw [hGet] at hSome
        contradiction
      have hNotMember :
          Derives godel_quotation_theory [] (
            ¬ₘ (numₘ(index) ∈ₘ
              numₘ(tokens.length))) :=
        gq_weaken_standard_sequence
          (standard_sequence_finite_numeral_not_mem_of_not_lt
            index tokens.length hNotLt)
      have hDomain :
          Derives godel_quotation_theory [] (
            domₘ(standardCode) ≐ₘ
              numₘ(tokens.length)) := by
        simpa [standardCode] using
          gq_weaken_standard_sequence
            (standard_token_sequence_domain_eq_length tokens)
      have hMemberAtLength :
          Γ ⊢ₘ[godel_quotation_theory]
            numₘ(index) ∈ₘ numₘ(tokens.length) :=
        FirstOrder.Derives.iffElimRight
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp)
            (membership_right_iff_of_equality
              (numₘ(index))
              (domₘ(standardCode))
              (numₘ(tokens.length))
              (finite_numeral_term_admissible index)
              (domain_term_admissible standardCode
                (by
                  simpa [standardCode] using
                    standard_token_sequence_admissible tokens))
              (finite_numeral_term_admissible tokens.length)
              hDomain))
          (FirstOrder.Derives.conjElimLeft hStandardPoint)
      exact FirstOrder.Derives.negElim
        hMemberAtLength
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp)
          hNotMember)

/-- 标准输入首 token 不是左括号时，否定生成分支不可能成立。 -/
theorem
    gq_standard_token_sequence_negation_falsum_of_first_mismatch
    {Γ : Context signature}
    (tokens : List Nat)
    (body : SetTerm)
    (hBody : Term.Admissible body SetSort.set)
    (actual : Nat)
    (hGet : tokens[0]? = some actual)
    (hNe :
      actual ≠
        Numbered.logical_token .leftParenthesis)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          neg_codeₘ(body)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hOpening :=
    FirstOrder.Derives.impElim
      (gq_negation_formula_opening_inversion
        (Γ := Γ) body hBody)
      hBodyMember
  exact
    gq_standard_token_sequence_falsum_of_point_mismatch
      tokens (neg_codeₘ(body))
      0 actual
      (Numbered.logical_token .leftParenthesis)
      hGet hNe hEquality
      (FirstOrder.Derives.conjElimLeft hOpening)

/-- 标准输入第二个 token 不是否定符号时，否定生成分支不可能成立。 -/
theorem
    gq_standard_token_sequence_negation_falsum_of_second_mismatch
    {Γ : Context signature}
    (tokens : List Nat)
    (body : SetTerm)
    (hBody : Term.Admissible body SetSort.set)
    (actual : Nat)
    (hGet : tokens[1]? = some actual)
    (hNe :
      actual ≠ Numbered.logical_token .negation)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          neg_codeₘ(body)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hOpening :=
    FirstOrder.Derives.impElim
      (gq_negation_formula_opening_inversion
        (Γ := Γ) body hBody)
      hBodyMember
  exact
    gq_standard_token_sequence_falsum_of_point_mismatch
      tokens (neg_codeₘ(body))
      1 actual
      (Numbered.logical_token .negation)
      hGet hNe hEquality
      (FirstOrder.Derives.conjElimRight hOpening)

/-- 标准输入首 token 不是左括号时，蕴含生成分支不可能成立。 -/
theorem
    gq_standard_token_sequence_implication_falsum_of_first_mismatch
    {Γ : Context signature}
    (tokens : List Nat)
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (actual : Nat)
    (hGet : tokens[0]? = some actual)
    (hNe :
      actual ≠
        Numbered.logical_token .leftParenthesis)
    (hLeftMember :
      Γ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[godel_quotation_theory]
        right ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hOpening :=
    FirstOrder.Derives.impElim
      (gq_implication_formula_opening_inversion
        (Γ := Γ) left right hLeft hRight)
      (FirstOrder.Derives.conjIntro
        hLeftMember hRightMember)
  exact
    gq_standard_token_sequence_falsum_of_point_mismatch
      tokens (imp_codeₘ(left, right))
      0 actual
      (Numbered.logical_token .leftParenthesis)
      hGet hNe hEquality hOpening

/-- 标准输入首 token 不是左括号时，全称生成分支不可能成立。 -/
theorem
    gq_standard_token_sequence_universal_falsum_of_first_mismatch
    {Γ : Context signature}
    (tokens : List Nat)
    (boundVariable body : SetTerm)
    (hBoundVariable :
      Term.Admissible boundVariable SetSort.set)
    (hBody : Term.Admissible body SetSort.set)
    (actual : Nat)
    (hGet : tokens[0]? = some actual)
    (hNe :
      actual ≠
        Numbered.logical_token .leftParenthesis)
    (hBoundVariableMember :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ∈ₘ VarSymₘ)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(boundVariable, body)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hBodyCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_formula_code_member_implies_code_string
          body hBody))
      hBodyMember
  have hOpening :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_universal_formula_opening_inversion
          boundVariable body))
      (FirstOrder.Derives.conjIntro
        hBoundVariableMember hBodyCodeString)
  exact
    gq_standard_token_sequence_falsum_of_point_mismatch
      tokens (forall_codeₘ(boundVariable, body))
      0 actual
      (Numbered.logical_token .leftParenthesis)
      hGet hNe hEquality
      (FirstOrder.Derives.conjElimLeft hOpening)

/-- 标准输入第二个 token 不是全称符号时，全称生成分支不可能成立。 -/
theorem
    gq_standard_token_sequence_universal_falsum_of_second_mismatch
    {Γ : Context signature}
    (tokens : List Nat)
    (boundVariable body : SetTerm)
    (hBoundVariable :
      Term.Admissible boundVariable SetSort.set)
    (hBody : Term.Admissible body SetSort.set)
    (actual : Nat)
    (hGet : tokens[1]? = some actual)
    (hNe :
      actual ≠ Numbered.logical_token .universal)
    (hBoundVariableMember :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ∈ₘ VarSymₘ)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(boundVariable, body)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hBodyCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_formula_code_member_implies_code_string
          body hBody))
      hBodyMember
  have hOpening :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_universal_formula_opening_inversion
          boundVariable body))
      (FirstOrder.Derives.conjIntro
        hBoundVariableMember hBodyCodeString)
  exact
    gq_standard_token_sequence_falsum_of_point_mismatch
      tokens (forall_codeₘ(boundVariable, body))
      1 actual
      (Numbered.logical_token .universal)
      hGet hNe hEquality
      (FirstOrder.Derives.conjElimLeft
        (FirstOrder.Derives.conjElimRight hOpening))

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
