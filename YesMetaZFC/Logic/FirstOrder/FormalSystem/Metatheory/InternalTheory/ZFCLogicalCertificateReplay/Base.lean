import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCertifiedProofReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCFormulaBinderReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCQuantifierAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay

/-!
# checked 逻辑基础证书的对象层公共组件

本模块只建立 decoder 与对象公式码之间的精确桥梁。成功解码的自然数既确定一条
规范 token 序列，也确定该序列所编码的 Hilbert 核公式；对象层重放同时保留这两
部分信息，不经过会遗失 payload 的 `HilbertLogicalAxiom`。
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
open Rosser

set_option autoImplicit false

namespace CertifiedProof

/-- 右结合字段合取的对象层回放。 -/
theorem fs_zfc_support_raw_logical_conjunction_of_list
    {fields : List SetFormula}
    (hFields :
      ∀ field, field ∈ fields →
        Derives fs_zfc_support_raw_theory [] field) :
    Derives fs_zfc_support_raw_theory [] (
      logical_certificate_conjunction fields) := by
  induction fields with
  | nil =>
      simpa [logical_certificate_conjunction] using
        (FirstOrder.Derives.truthIntro :
          Derives fs_zfc_support_raw_theory [] Formula.truth)
  | cons field fields ih =>
      cases fields with
      | nil =>
          simpa [logical_certificate_conjunction] using
            hFields field (by simp)
      | cons next rest =>
          simp only [logical_certificate_conjunction]
          apply FirstOrder.Derives.conjIntro
          · exact hFields field (by simp)
          · apply ih
            intro item hItem
            exact hFields item (by simp [hItem])

/-- 自由支持为空的项在任意自由变量替换下保持不变。 -/
theorem fs_zfc_support_raw_closed_term_substitute
    {term : SetTerm}
    (hClosed : Term.freeSupport term = [])
    (id : FreeVarId) (replacement : SetTerm) :
    Term.substituteFree SetSort.set id replacement term = term :=
  Term.substituteFree_eq_self_of_not_mem
    SetSort.set id replacement term (by
      rw [hClosed]
      exact List.not_mem_nil)

/-- 总化公式 quotation 保持 Hilbert 否定构造。 -/
theorem fs_zfc_formula_code_term_neg
    (formula : SetFormula)
    (hFormula : Formula.Admissible formula) :
    fs_zfc_formula_code_term (Formula.neg formula) =
      neg_codeₘ(fs_zfc_formula_code_term formula) := by
  rcases GodelQuotation.Numbered.quote?_exists hFormula with
    ⟨code, hQuote⟩
  have hNegQuote := Rosser.quote_negation_code hQuote
  simp [fs_zfc_formula_code_term, hQuote, hNegQuote]

/-- 总化公式 quotation 保持 Hilbert 蕴含构造。 -/
theorem fs_zfc_formula_code_term_imp
    (left right : SetFormula)
    (hLeft : Formula.Admissible left)
    (hRight : Formula.Admissible right) :
    fs_zfc_formula_code_term (Formula.imp left right) =
      imp_codeₘ(
        fs_zfc_formula_code_term left,
        fs_zfc_formula_code_term right) := by
  rcases GodelQuotation.Numbered.quote?_exists hLeft with
    ⟨leftCode, hLeftQuote⟩
  rcases GodelQuotation.Numbered.quote?_exists hRight with
    ⟨rightCode, hRightQuote⟩
  have hImpQuote :=
    Rosser.quote_implication_code hLeftQuote hRightQuote
  simp [fs_zfc_formula_code_term, hLeftQuote,
    hRightQuote, hImpQuote]

/-! ## 自由变量等式的规范 quotation -/

theorem fs_zfc_formula_code_term_fvar_equality_reflexivity
    (identifier : FreeVarId) :
    fs_zfc_formula_code_term
        (Formula.equal
          (Term.var (.fvar SetSort.set identifier))
          (Term.var (.fvar SetSort.set identifier))) =
      eq_codeₘ(
        var_codeₘ(numₘ(2 * identifier)),
        var_codeₘ(numₘ(2 * identifier))) := by
  unfold fs_zfc_formula_code_term
  simp [GodelQuotation.Numbered.quote?,
    GodelQuotation.Numbered.quote_with?,
    GodelQuotation.Numbered.quote_hilbert_with?,
    GodelQuotation.Numbered.quote_term_with?,
    GodelQuotation.Numbered.named_variable_code,
    Formula.hilbertize,
    GodelQuotation.free_name]

theorem fs_zfc_support_raw_equality_code_term_congr_of_equalities
    (left₁ left₂ right₁ right₂ : SetTerm)
    (hLeft₁ : Term.Admissible left₁ SetSort.set)
    (hLeft₂ : Term.Admissible left₂ SetSort.set)
    (hRight₁ : Term.Admissible right₁ SetSort.set)
    (hRight₂ : Term.Admissible right₂ SetSort.set)
    (hLeftEquality :
      Derives fs_zfc_support_raw_theory [] (left₁ ≐ₘ left₂))
    (hRightEquality :
      Derives fs_zfc_support_raw_theory [] (right₁ ≐ₘ right₂)) :
    Derives fs_zfc_support_raw_theory [] (
      eq_codeₘ(left₁, right₁) ≐ₘ
        eq_codeₘ(left₂, right₂)) := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    (fun left right => eq_codeₘ(left, right))
    (fun left right hLeft hRight =>
      equality_formula_code_term_admissible
        left right hLeft hRight)
    (by intros; simp [Term.substituteFree])
    left₁ left₂ right₁ right₂
    hLeft₁ hLeft₂ hRight₁ hRight₂
    hLeftEquality hRightEquality

theorem fs_zfc_formula_code_term_equal_of_quote
    (left right leftCode rightCode : SetTerm)
    (hLeftQuote :
      GodelQuotation.Numbered.quote_term_with?
        GodelQuotation.free_name [] left =
        some leftCode)
    (hRightQuote :
      GodelQuotation.Numbered.quote_term_with?
        GodelQuotation.free_name [] right =
        some rightCode) :
    fs_zfc_formula_code_term (Formula.equal left right) =
      eq_codeₘ(leftCode, rightCode) := by
  unfold fs_zfc_formula_code_term
  simp [GodelQuotation.Numbered.quote?,
    GodelQuotation.Numbered.quote_with?,
    GodelQuotation.Numbered.quote_hilbert_with?,

    Formula.hilbertize,
    hLeftQuote, hRightQuote]

theorem fs_zfc_support_raw_variable_code_term_numeral_mul
    (number : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      var_codeₘ(numₘ(2 * number)) ≐ₘ
        var_codeₘ(numₘ(2) *ₘ numₘ(number))) := by
  have hMultiplication :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(2 * number) ≐ₘ
          (numₘ(2) *ₘ numₘ(number))) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_finite_numeral_multiplication
        2 number)
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    (fun term => var_codeₘ(term))
    (fun term hTerm =>
      variable_code_term_admissible term hTerm)
    (by intros; simp [Term.substituteFree])
    (numₘ(2 * number))
    (numₘ(2) *ₘ numₘ(number))
    (finite_numeral_term_admissible (2 * number))
    (natural_multiplication_term_admissible
      (numₘ(2)) (numₘ(number))
      (finite_numeral_term_admissible 2)
      (finite_numeral_term_admissible number))
    hMultiplication

/-! ## canonical 全称闭包的总化公式码接口 -/

/--
总化 quotation 直接保持一次 canonical 全称闭包。

该接口隐藏 quotation witness，只暴露 transcript replay 真正需要的三个规范码项。
-/
theorem fs_zfc_support_raw_canonical_forall_closure_code_term
    {formula : SetFormula}
    (eigen : FreeVarId)
    (hFormula : Formula.Admissible formula) :
    Derives fs_zfc_support_raw_theory [] (
      canonical_forall_closure_code_condition
        (fs_zfc_formula_code_term formula)
        (var_codeₘ(numₘ(2 * eigen)))
        (fs_zfc_formula_code_term
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set eigen 0 formula)))) := by
  rcases
      fs_zfc_support_raw_canonical_forall_closure_condition_of_quotation
        eigen hFormula with
    ⟨sourceCode, variableCode, targetCode,
      hSourceQuote, hVariableQuote, hTargetQuote, hClosure⟩
  have hSourceCode :
      sourceCode = fs_zfc_formula_code_term formula := by
    simp [fs_zfc_formula_code_term, hSourceQuote]
  have hVariableCode :
      variableCode =
        var_codeₘ(numₘ(2 * eigen)) := by
    symm
    simpa [GodelQuotation.Numbered.quote_term_with?,
      GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using hVariableQuote
  have hTargetCode :
      targetCode =
        fs_zfc_formula_code_term
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set eigen 0 formula)) := by
    simp [fs_zfc_formula_code_term, hTargetQuote]
  subst sourceCode
  subst variableCode
  subst targetCode
  exact hClosure

/-! ## canonical 全称打开的总化公式码接口 -/

/--
总化 quotation 直接保持一次 canonical 全称打开。

该接口与闭包接口共用同一组规范码项；transcript 只需按方向排列三项。
-/
theorem fs_zfc_support_raw_canonical_forall_open_code_term
    {formula : SetFormula}
    (eigen : FreeVarId)
    (hFormula : Formula.Admissible formula) :
    Derives fs_zfc_support_raw_theory [] (
      canonical_forall_open_code_condition
        (fs_zfc_formula_code_term
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set eigen 0 formula)))
        (var_codeₘ(numₘ(2 * eigen)))
        (fs_zfc_formula_code_term formula)) := by
  rcases
      fs_zfc_support_raw_canonical_forall_open_condition_of_quotation
        eigen hFormula with
    ⟨sourceCode, variableCode, targetCode,
      hSourceQuote, hVariableQuote, hTargetQuote, hOpen⟩
  have hSourceCode :
      sourceCode = fs_zfc_formula_code_term formula := by
    simp [fs_zfc_formula_code_term, hSourceQuote]
  have hVariableCode :
      variableCode =
        var_codeₘ(numₘ(2 * eigen)) := by
    symm
    simpa [GodelQuotation.Numbered.quote_term_with?,
      GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using hVariableQuote
  have hTargetCode :
      targetCode =
        fs_zfc_formula_code_term
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set eigen 0 formula)) := by
    simp [fs_zfc_formula_code_term, hTargetQuote]
  subst sourceCode
  subst variableCode
  subst targetCode
  exact hOpen

/-! ## 七个命题构造的 quotation 同态 -/

theorem fs_zfc_formula_code_term_implication_distribution
    (antecedent middle consequent : SetFormula)
    (hAntecedent : Formula.Admissible antecedent)
    (hMiddle : Formula.Admissible middle)
    (hConsequent : Formula.Admissible consequent) :
    fs_zfc_formula_code_term
        (Formula.imp
          (Formula.imp antecedent (Formula.imp middle consequent))
          (Formula.imp
            (Formula.imp antecedent middle)
            (Formula.imp antecedent consequent))) =
      implication_distribution_axiom_code_term
        (fs_zfc_formula_code_term antecedent)
        (fs_zfc_formula_code_term middle)
        (fs_zfc_formula_code_term consequent) := by
  have hMiddleConsequent :=
    Formula.Admissible.imp hMiddle hConsequent
  have hAntecedentMiddleConsequent :=
    Formula.Admissible.imp hAntecedent hMiddleConsequent
  have hAntecedentMiddle :=
    Formula.Admissible.imp hAntecedent hMiddle
  have hAntecedentConsequent :=
    Formula.Admissible.imp hAntecedent hConsequent
  have hRight :=
    Formula.Admissible.imp
      hAntecedentMiddle hAntecedentConsequent
  rw [fs_zfc_formula_code_term_imp
    _ _ hAntecedentMiddleConsequent hRight]
  rw [fs_zfc_formula_code_term_imp
    _ _ hAntecedent hMiddleConsequent]
  rw [fs_zfc_formula_code_term_imp _ _ hMiddle hConsequent]
  rw [fs_zfc_formula_code_term_imp
    _ _ hAntecedentMiddle hAntecedentConsequent]
  rw [fs_zfc_formula_code_term_imp _ _ hAntecedent hMiddle]
  rw [fs_zfc_formula_code_term_imp _ _ hAntecedent hConsequent]

theorem fs_zfc_formula_code_term_self_implication
    (formula : SetFormula)
    (hFormula : Formula.Admissible formula) :
    fs_zfc_formula_code_term
        (Formula.imp formula (Formula.imp formula formula)) =
      self_implication_axiom_code_term
        (fs_zfc_formula_code_term formula) := by
  have hInner := Formula.Admissible.imp hFormula hFormula
  rw [fs_zfc_formula_code_term_imp _ _ hFormula hInner]
  rw [fs_zfc_formula_code_term_imp _ _ hFormula hFormula]

theorem fs_zfc_formula_code_term_weakening
    (formula extra : SetFormula)
    (hFormula : Formula.Admissible formula)
    (hExtra : Formula.Admissible extra) :
    fs_zfc_formula_code_term
        (Formula.imp formula (Formula.imp extra formula)) =
      weakening_axiom_code_term
        (fs_zfc_formula_code_term formula)
        (fs_zfc_formula_code_term extra) := by
  have hInner := Formula.Admissible.imp hExtra hFormula
  rw [fs_zfc_formula_code_term_imp _ _ hFormula hInner]
  rw [fs_zfc_formula_code_term_imp _ _ hExtra hFormula]

theorem fs_zfc_formula_code_term_contradiction
    (formula conclusion : SetFormula)
    (hFormula : Formula.Admissible formula)
    (hConclusion : Formula.Admissible conclusion) :
    fs_zfc_formula_code_term
        (Formula.imp formula
          (Formula.imp (Formula.neg formula) conclusion)) =
      contradiction_axiom_code_term
        (fs_zfc_formula_code_term formula)
        (fs_zfc_formula_code_term conclusion) := by
  have hNeg := Formula.Admissible.neg hFormula
  have hInner := Formula.Admissible.imp hNeg hConclusion
  rw [fs_zfc_formula_code_term_imp _ _ hFormula hInner]
  rw [fs_zfc_formula_code_term_imp _ _ hNeg hConclusion]
  rw [fs_zfc_formula_code_term_neg _ hFormula]

theorem fs_zfc_formula_code_term_classical
    (formula : SetFormula)
    (hFormula : Formula.Admissible formula) :
    fs_zfc_formula_code_term
        (Formula.imp
          (Formula.imp (Formula.neg formula) formula)
          formula) =
      classical_axiom_code_term
        (fs_zfc_formula_code_term formula) := by
  have hNeg := Formula.Admissible.neg hFormula
  have hInner := Formula.Admissible.imp hNeg hFormula
  rw [fs_zfc_formula_code_term_imp _ _ hInner hFormula]
  rw [fs_zfc_formula_code_term_imp _ _ hNeg hFormula]
  rw [fs_zfc_formula_code_term_neg _ hFormula]

theorem fs_zfc_formula_code_term_explosion
    (formula conclusion : SetFormula)
    (hFormula : Formula.Admissible formula)
    (hConclusion : Formula.Admissible conclusion) :
    fs_zfc_formula_code_term
        (Formula.imp (Formula.neg formula)
          (Formula.imp formula conclusion)) =
      explosion_axiom_code_term
        (fs_zfc_formula_code_term formula)
        (fs_zfc_formula_code_term conclusion) := by
  have hNeg := Formula.Admissible.neg hFormula
  have hInner := Formula.Admissible.imp hFormula hConclusion
  rw [fs_zfc_formula_code_term_imp _ _ hNeg hInner]
  rw [fs_zfc_formula_code_term_neg _ hFormula]
  rw [fs_zfc_formula_code_term_imp _ _ hFormula hConclusion]

theorem fs_zfc_formula_code_term_case_analysis
    (formula conclusion : SetFormula)
    (hFormula : Formula.Admissible formula)
    (hConclusion : Formula.Admissible conclusion) :
    fs_zfc_formula_code_term
        (Formula.imp
          (Formula.imp formula conclusion)
          (Formula.imp
            (Formula.imp (Formula.neg formula) conclusion)
            conclusion)) =
      case_analysis_axiom_code_term
        (fs_zfc_formula_code_term formula)
        (fs_zfc_formula_code_term conclusion) := by
  have hPositive := Formula.Admissible.imp hFormula hConclusion
  have hNeg := Formula.Admissible.neg hFormula
  have hNegative := Formula.Admissible.imp hNeg hConclusion
  have hRight := Formula.Admissible.imp hNegative hConclusion
  rw [fs_zfc_formula_code_term_imp _ _ hPositive hRight]
  rw [fs_zfc_formula_code_term_imp _ _ hFormula hConclusion]
  rw [fs_zfc_formula_code_term_imp _ _ hNegative hConclusion]
  rw [fs_zfc_formula_code_term_imp _ _ hNeg hConclusion]
  rw [fs_zfc_formula_code_term_neg _ hFormula]

/-- 标准 token 序列在对象层的定义域正好是外部列表长度。 -/
theorem fs_zfc_support_raw_standard_token_sequence_domain
    (tokens : List Nat) :
    Derives fs_zfc_support_raw_theory [] (
      domₘ(standard_token_sequence tokens) ≐ₘ
        numₘ(tokens.length)) :=
  fs_zfc_support_raw_derives_of_standard_sequence
    (standard_token_sequence_domain_eq_length tokens)

/-- 标准 token 序列的具体位置仍是闭的可用对象项。 -/
theorem fs_zfc_standard_token_sequence_apply_code_boundary
    (tokens : List Nat) (index : Nat) :
    GodelQuotation.Numbered.CodeBoundary
      (standard_token_sequence tokens ·ₘ numₘ(index)) := by
  refine ⟨function_application_term_admissible
      (standard_token_sequence tokens) (numₘ(index))
      (standard_token_sequence_admissible tokens)
      (finite_numeral_term_admissible index), ?_⟩
  simp [Term.freeSupport, Term.freeSupportList,
    standard_token_sequence_freeSupport_nil,
    finite_numeral_term_freeSupport]

/-- 自然数证书值与对象 Gödel 配对项精确对齐。 -/
theorem fs_zfc_support_raw_logical_certificate_pair_eq
    {certificate tag payload : Nat}
    (hCertificate :
      certificate = godel_pair_value tag payload) :
    Derives fs_zfc_support_raw_theory [] (
      numₘ(certificate) ≐ₘ
        godel_pairₘ(⟨numₘ(tag), numₘ(payload)⟩ₘ)) := by
  have hPair :=
    Metatheory.Derives.equality_symm
      (fs_zfc_support_raw_godel_pair_value_eq tag payload)
  simpa [hCertificate] using hPair

/-- 三字段 payload 的嵌套自然数配对精确对应嵌套对象配对项。 -/
theorem fs_zfc_support_raw_logical_certificate_nested_pair_eq
    {payload first second third : Nat}
    (hPayload :
      payload =
        godel_pair_value first
          (godel_pair_value second third)) :
    Derives fs_zfc_support_raw_theory [] (
      numₘ(payload) ≐ₘ
        godel_pairₘ(⟨numₘ(first),
          godel_pairₘ(⟨numₘ(second), numₘ(third)⟩ₘ)⟩ₘ)) := by
  have hInner :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(godel_pair_value second third) ≐ₘ
          godel_pairₘ(⟨numₘ(second), numₘ(third)⟩ₘ)) :=
    fs_zfc_support_raw_logical_certificate_pair_eq
      (certificate := godel_pair_value second third)
      (tag := second) (payload := third) rfl
  have hOuter :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(payload) ≐ₘ
          godel_pairₘ(⟨numₘ(first),
            numₘ(godel_pair_value second third)⟩ₘ)) :=
    fs_zfc_support_raw_logical_certificate_pair_eq hPayload
  have hInnerTerm :
      Term.Admissible
        (godel_pairₘ(⟨numₘ(second), numₘ(third)⟩ₘ))
        SetSort.set :=
    godel_pairing_term_admissible _ <|
      ordered_pair_term_admissible _ _
        (finite_numeral_term_admissible second)
        (finite_numeral_term_admissible third)
  have hCongruence :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairₘ(⟨numₘ(first),
          numₘ(godel_pair_value second third)⟩ₘ) ≐ₘ
        godel_pairₘ(⟨numₘ(first),
          godel_pairₘ(⟨numₘ(second), numₘ(third)⟩ₘ)⟩ₘ)) :=
    godel_pairing_term_congr_of_equalities
      (numₘ(first)) (numₘ(first))
      (numₘ(godel_pair_value second third))
      (godel_pairₘ(⟨numₘ(second), numₘ(third)⟩ₘ))
      (finite_numeral_term_admissible first)
      (finite_numeral_term_admissible first)
      (finite_numeral_term_admissible
        (godel_pair_value second third))
      hInnerTerm
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(first)))
      hInner
  exact Metatheory.Derives.equality_trans hOuter hCongruence

/--
成功解码的单个公式字段同时满足公式码条件与精确自然数序列编码条件。

这里使用总化 quotation 项作为公式码见证；decoder 出口的 re-quote 检查保证它与
原 token 串对象相等，因此没有额外的“任意可解析串即公式码”假设。
-/
theorem fs_zfc_support_raw_logical_formula_payload_component_of_decode
    {code : Nat} {formula : SetFormula}
    (traceId indexId : FreeVarId)
    (hIds : traceId ≠ indexId)
    (hDecode :
      fs_formula_token_code_decode code =
        some formula) :
    Derives fs_zfc_support_raw_theory [] (
      logical_formula_payload_component_condition_with_ids
        (fs_zfc_formula_code_term formula)
        (numₘ(code)) traceId indexId) := by
  have hFormula :
      Formula.Admissible formula :=
    fs_formula_token_code_decode_admissible hDecode
  have hTokens :
      GodelQuotation.Numbered.quote_tokens? formula =
        some (nat_sequence_decode code) :=
    fs_formula_token_code_decode_quote_tokens hDecode
  have hFormulaCode :
      Derives fs_zfc_support_raw_theory [] (
        formula_codeₘ(fs_zfc_formula_code_term formula)) :=
    fs_zfc_support_raw_formula_code_term_is_formula_code hFormula
  have hCodeEquality :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_formula_code_term formula ≐ₘ
          standard_token_sequence (nat_sequence_decode code)) := by
    simpa [certified_row_tokens, hTokens] using
      ProofT.ZFC.formula_code_eq_tokens
        fs_zfc_support_raw_contains_godel_quotation
        hFormula
  have hStandardCondition :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (standard_token_sequence (nat_sequence_decode code))
          (numₘ(code)) traceId indexId) := by
    simpa [nat_sequence_code_value_decode] using
      fs_zfc_support_raw_nat_sequence_code_condition_with_ids
        (nat_sequence_decode code) traceId indexId hIds
  have hStandardBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (standard_token_sequence (nat_sequence_decode code)) :=
    ⟨standard_token_sequence_admissible (nat_sequence_decode code),
      standard_token_sequence_freeSupport_nil
        (nat_sequence_decode code)⟩
  have hCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary (numₘ(code)) :=
    ⟨finite_numeral_term_admissible code,
      finite_numeral_term_freeSupport code⟩
  have hStandardReplay :
      Derives fs_zfc_support_raw_theory [] (
        fs_formula_replay_condition
          (standard_token_sequence (nat_sequence_decode code))) :=
    fs_zfc_support_raw_quote_tokens_replay hFormula hTokens
  have hReplayTransport :=
    fs_formula_replay_condition_iff_of_equality
      (fs_zfc_formula_code_term formula)
      (standard_token_sequence (nat_sequence_decode code))
      (fs_zfc_formula_code_term_code_boundary formula).1
      hStandardBoundary.1 hCodeEquality
  have hFormulaReplay :
      Derives fs_zfc_support_raw_theory [] (
        fs_formula_replay_condition
          (fs_zfc_formula_code_term formula)) :=
    FirstOrder.Derives.iffElimLeft
      hReplayTransport hStandardReplay
  have hTransport :=
    fs_zfc_support_raw_nat_sequence_code_condition_with_ids_iff_of_sequence_equality
      (fs_zfc_formula_code_term formula)
      (standard_token_sequence (nat_sequence_decode code))
      (numₘ(code)) traceId indexId
      (fs_zfc_formula_code_term_code_boundary formula)
      hStandardBoundary hCodeBoundary hCodeEquality
  have hSequenceCode :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (fs_zfc_formula_code_term formula)
          (numₘ(code)) traceId indexId) :=
    FirstOrder.Derives.iffElimLeft
      hTransport hStandardCondition
  exact FirstOrder.Derives.conjIntro
    (FirstOrder.Derives.conjIntro
      hFormulaCode hFormulaReplay)
    hSequenceCode

/--
成功解码的公式字段可直接放到标准 payload 序列的指定位置。

这里同时运输数值代码条件；公式码见证本身不变，因此不会丢失 decoder 的规范
re-quote 信息。
-/
theorem fs_zfc_support_raw_logical_formula_payload_component_of_decode_at
    {codes : List Nat} {index code : Nat}
    {formula : SetFormula}
    (traceId indexId : FreeVarId)
    (hIds : traceId ≠ indexId)
    (hGet : codes[index]? = some code)
    (hDecode :
      fs_formula_token_code_decode code =
        some formula) :
    Derives fs_zfc_support_raw_theory [] (
      logical_formula_payload_component_condition_with_ids
        (fs_zfc_formula_code_term formula)
        (standard_token_sequence codes ·ₘ numₘ(index))
        traceId indexId) := by
  have hComponent :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode
      traceId indexId hIds hDecode
  have hFormulaFields :=
    FirstOrder.Derives.conjElimLeft hComponent
  have hNumericCode :=
    FirstOrder.Derives.conjElimRight hComponent
  have hApplication :
      Derives fs_zfc_support_raw_theory [] (
        (standard_token_sequence codes ·ₘ numₘ(index)) ≐ₘ
          numₘ(code)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_apply_getElem? codes hGet)
  have hTransport :=
    fs_zfc_support_raw_nat_sequence_code_condition_with_ids_iff_of_code_equality
      (fs_zfc_formula_code_term formula)
      (standard_token_sequence codes ·ₘ numₘ(index))
      (numₘ(code)) traceId indexId
      (fs_zfc_formula_code_term_code_boundary formula)
      (fs_zfc_standard_token_sequence_apply_code_boundary
        codes index)
      ⟨finite_numeral_term_admissible code,
        finite_numeral_term_freeSupport code⟩
      hApplication
  have hAt :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (fs_zfc_formula_code_term formula)
          (standard_token_sequence codes ·ₘ numₘ(index))
          traceId indexId) :=
    FirstOrder.Derives.iffElimLeft
      hTransport hNumericCode
  exact FirstOrder.Derives.conjIntro
    hFormulaFields hAt

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
