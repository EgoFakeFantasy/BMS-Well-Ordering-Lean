import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SequenceInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.Symbol
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.Opening
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FlattenBound
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SequenceBound

/-!
# 单 token 头应用码的公共反演

本模块处理统一形状
`((head ⌢ leftParenthesis) ⌢ body) ⌢ rightParenthesis`。函数应用和谓词应用只需
分别提供头部 singleton 的标准码等式；总长度、正文切片、末位和宿主列表重组
均由此公共层承担。
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

/-- 单 token 头、左右括号与有限正文构成的统一应用码。 -/
abbrev headed_application_code_term
    (head body : SetTerm) : SetTerm :=
  (((head ⌢ₘ left_parenthesis_symbol_code_term) ⌢ₘ
      body) ⌢ₘ
    right_parenthesis_symbol_code_term)

/--
统一应用码的零位保留单 token 头的唯一值。

该接口只要求头部已有 singleton 标准码等式，并要求正文是有限序列；左右括号的
有限性由公共符号码定理内部提供。
-/
theorem gq_headed_application_head_point
    {Γ : Context signature}
    (head body : SetTerm) (headToken : Nat)
    (hHeadEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        head ≐ₘ standard_token_sequence [headToken])
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hHead : Term.CheckCertificate head SetSort.set := by
      prove_term_check)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((numₘ(0) ∈ₘ
          domₘ(headed_application_code_term head body)) ∧ₘ
        ((headed_application_code_term head body ·ₘ numₘ(0)) ≐ₘ
          numₘ(headToken))) := by
  let leftParenthesis : SetTerm :=
    left_parenthesis_symbol_code_term
  let rightParenthesis : SetTerm :=
    right_parenthesis_symbol_code_term
  have hHeadFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition head :=
    gq_finite_sequence_of_eq_standard_token_sequence
      head [headToken] hHeadEquality
  have hHeadPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(head)) ∧ₘ
          ((head ·ₘ numₘ(0)) ≐ₘ numₘ(headToken))) :=
    gq_standard_token_sequence_point_inversion
      head [headToken] hHeadEquality (by simp)
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  simpa [headed_application_code_term,
    leftParenthesis, rightParenthesis] using
      gq_four_part_left_point
        head leftParenthesis body rightParenthesis
        (numₘ(0)) (numₘ(headToken))
        hHeadFinite hLeftFinite hBodyFinite hRightFinite
        (FirstOrder.Derives.conjElimLeft hHeadPoint)
        (FirstOrder.Derives.conjElimRight hHeadPoint)
        (hFirst := hHead) (hThird := hBody)

/-- 任意 Gödel quotation 理论扩张中的统一应用头 token checked replay。 -/
theorem gq_headed_application_head_point_of_theory
    {T : SetTheory} {Γ : Context signature}
    (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (head body : SetTerm) (headToken : Nat)
    (hHeadEquality :
      Γ ⊢ₘ[T]
        head ≐ₘ standard_token_sequence [headToken])
    (hBodyFinite :
      Γ ⊢ₘ[T]
        finite_sequence_condition body)
    (hHead : Term.CheckCertificate head SetSort.set := by
      prove_term_check)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T]
      ((numₘ(0) ∈ₘ
          domₘ(headed_application_code_term head body)) ∧ₘ
        ((headed_application_code_term head body ·ₘ numₘ(0)) ≐ₘ
          numₘ(headToken))) := by
  let Δ : Context signature :=
    (head ≐ₘ standard_token_sequence [headToken]) ::
      finite_sequence_condition body :: []
  have hHeadEqualityAt :
      Δ ⊢ₘ[godel_quotation_theory]
        head ≐ₘ standard_token_sequence [headToken] :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hBodyFiniteAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hPoint :=
    gq_headed_application_head_point
      head body headToken hHeadEqualityAt hBodyFiniteAt
      (hHead := hHead) (hBody := hBody)
  apply FirstOrder.Derives.multi_cut
    (T := T) (Γ := Γ) (premises := Δ)
  · intro formula hFormula
    simp [Δ] at hFormula
    rcases hFormula with rfl | rfl
    · exact hHeadEquality
    · exact hBodyFinite
  · exact
      (FirstOrder.Derives.theory_weaken
        hTheory hPoint).context_weaken_append

/--
头部定义域为 `1` 时，统一应用码是有限序列，且正文定义域严格落在整码定义域
中。
-/
theorem gq_headed_application_finite_and_body_domain_member
    {Γ : Context signature}
    (head body : SetTerm)
    (hHead : Term.Admissible head SetSort.set)
    (hBody : Term.Admissible body SetSort.set)
    (hHeadFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition head)
    (hHeadDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(head) ≐ₘ numₘ(1))
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body) :
    Γ ⊢ₘ[godel_quotation_theory]
      (finite_sequence_condition
          (headed_application_code_term head body) ∧ₘ
        (finite_sequence_condition body ∧ₘ
          (domₘ(body) ∈ₘ
            domₘ(headed_application_code_term
              head body)))) := by
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let prefixCode : SetTerm :=
    head ⌢ₘ leftParenthesis
  let middle : SetTerm :=
    prefixCode ⌢ₘ body
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        head leftParenthesis
        hHeadFinite hLeftFinite
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ numₘ(2) := by
    simpa [prefixCode] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        head leftParenthesis 1 1
        hHeadFinite hLeftFinite
        hHeadDomain hLeftDomain
  have hBodyInMiddle :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ∈ₘ domₘ(middle) := by
    simpa [middle] using
      gq_concatenation_right_domain_member_of_positive_left_length
        prefixCode body 1
        hPrefixFinite hBodyFinite hPrefixDomain
  have hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle := by
    simpa [middle] using
      gq_concatenation_finite
        prefixCode body hPrefixFinite hBodyFinite
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hBodyInWhole :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ∈ₘ
          domₘ(middle ⌢ₘ rightParenthesis) :=
    gq_concatenation_left_domain_member
      middle rightParenthesis
      (domₘ(body))
      hMiddleFinite hRightFinite hBodyInMiddle
  have hWholeFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          (middle ⌢ₘ rightParenthesis) :=
    gq_concatenation_finite
      middle rightParenthesis
      hMiddleFinite hRightFinite
  simpa [leftParenthesis, prefixCode, middle,
    rightParenthesis, headed_application_code_term] using
    FirstOrder.Derives.conjIntro hWholeFinite <|
      FirstOrder.Derives.conjIntro
        hBodyFinite hBodyInWhole

/--
有限族任一外部 numeral 位置的片段都严格短于以其 flatten 为正文的统一应用码。

证明先使用 flatten 的逐片段长度上界，再与正文严格落在整码定义域中的事实做
对象自然数 `≤`-`<` 传递。
-/
theorem gq_headed_application_family_piece_domain_member
    {Γ : Context signature}
    (head arguments : SetTerm)
    (familyLength argumentIndex : Nat)
    (hHead : Term.Admissible head SetSort.set)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hHeadFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition head)
    (hHeadDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(head) ≐ₘ numₘ(1))
    (hFamily :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition arguments)
    (hDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(arguments) ≐ₘ
          numₘ(familyLength))
    (hArgumentIndex :
      argumentIndex < familyLength) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(arguments ·ₘ numₘ(argumentIndex)) ∈ₘ
        domₘ(headed_application_code_term
          head (flattenₘ(arguments))) := by
  let body : SetTerm :=
    flattenₘ(arguments)
  let code : SetTerm :=
    headed_application_code_term head body
  have hFlattenSpec :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_flatten_spec
          arguments body :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <| by
            simpa [body] using
              finite_sequence_flatten_term_spec_derives
                arguments hArguments)
      hFamily
  have hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body :=
    FirstOrder.Derives.conjElimLeft hFlattenSpec
  have hStructure :
      Γ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition code ∧ₘ
          (finite_sequence_condition body ∧ₘ
            (domₘ(body) ∈ₘ domₘ(code)))) := by
    simpa [body, code] using
      gq_headed_application_finite_and_body_domain_member
        (Γ := Γ)
        head (flattenₘ(arguments))
        hHead
        (finite_sequence_flatten_term_admissible
          arguments hArguments)
        hHeadFinite hHeadDomain
        (by simpa [body] using hBodyFinite)
  have hCodeFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition code :=
    FirstOrder.Derives.conjElimLeft hStructure
  have hBodyInCode :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ∈ₘ domₘ(code) :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight hStructure
  have hArgumentLeBody :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(arguments ·ₘ numₘ(argumentIndex)) ∈ₘ
          Sₘ(domₘ(body)) := by
    simpa [body] using
      gq_flatten_numeral_point_domain_le
        (Γ := Γ)
        arguments familyLength argumentIndex
        hArguments hFamily hDomain hArgumentIndex
  have hArgumentDomain :
      Term.Admissible
        (domₘ(arguments ·ₘ
          numₘ(argumentIndex))) SetSort.set :=
    domain_term_admissible
      (arguments ·ₘ numₘ(argumentIndex))
      (function_application_term_admissible
        arguments (numₘ(argumentIndex))
        hArguments
        (finite_numeral_term_admissible
          argumentIndex))
  have hBodyDomain :
      Term.Admissible
        (domₘ(body)) SetSort.set :=
    domain_term_admissible body
      (by
        simpa [body] using
          finite_sequence_flatten_term_admissible
            arguments hArguments)
  have hCodeDomain :
      Term.Admissible
        (domₘ(code)) SetSort.set :=
    domain_term_admissible code
      (by
        simpa [body, code] using
          finite_sequence_concatenation_term_admissible
            (((head ⌢ₘ
                left_parenthesis_symbol_code_term) ⌢ₘ
              flattenₘ(arguments)))
            right_parenthesis_symbol_code_term
            (finite_sequence_concatenation_term_admissible
              (head ⌢ₘ
                left_parenthesis_symbol_code_term)
              (flattenₘ(arguments))
              (finite_sequence_concatenation_term_admissible
                head left_parenthesis_symbol_code_term
                hHead
                (logical_symbol_code_term_admissible
                  .leftParenthesis))
              (finite_sequence_flatten_term_admissible
                arguments hArguments))
            (logical_symbol_code_term_admissible
              .rightParenthesis))
  have hBodyOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ∈ₘ ωₘ := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hBodyFinite
  have hCodeOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ∈ₘ ωₘ := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hCodeFinite
  simpa [body, code] using
    gq_natural_le_lt_transitivity
      (Γ := Γ)
      (domₘ(arguments ·ₘ numₘ(argumentIndex)))
      (domₘ(body))
      (domₘ(code))
      hArgumentDomain hBodyDomain hCodeDomain
      hBodyOmega hCodeOmega
      hArgumentLeBody hBodyInCode

/-- 统一应用码的定义域长度为固定前缀 `2`、正文长度与末尾 `1` 之和。 -/
theorem gq_headed_application_domain_eq_of_body_domain
    {Γ : Context signature}
    (head body : SetTerm)
    (bodyLength : Nat)
    (hHead : Term.Admissible head SetSort.set)
    (hBody : Term.Admissible body SetSort.set)
    (hHeadFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition head)
    (hHeadDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(head) ≐ₘ numₘ(1))
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength)) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(headed_application_code_term head body) ≐ₘ
        numₘ(2 + bodyLength + 1) := by
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let prefixCode : SetTerm :=
    head ⌢ₘ leftParenthesis
  let middle : SetTerm :=
    prefixCode ⌢ₘ body
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        head leftParenthesis
        hHeadFinite hLeftFinite
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ numₘ(2) := by
    simpa [prefixCode] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        head leftParenthesis 1 1
        hHeadFinite hLeftFinite
        hHeadDomain hLeftDomain
  have hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle := by
    simpa [middle] using
      gq_concatenation_finite
        prefixCode body hPrefixFinite hBodyFinite
  have hMiddleDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(middle) ≐ₘ
          numₘ(2 + bodyLength) := by
    simpa [middle] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        prefixCode body 2 bodyLength
        hPrefixFinite hBodyFinite
        hPrefixDomain hBodyDomain
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(rightParenthesis) ≐ₘ numₘ(1) := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .rightParenthesis
  simpa [leftParenthesis, prefixCode, middle,
    rightParenthesis, headed_application_code_term] using
    gq_concatenation_domain_eq_numeral_lengths_of_theory
      (fun _ hAxiom => hAxiom)
      middle rightParenthesis
      (2 + bodyLength) 1
      hMiddleFinite hRightFinite
      hMiddleDomain hRightDomain

/-- 标准输入长度与统一应用码长度不相符时，对象层推出矛盾。 -/
theorem gq_headed_application_standard_falsum_of_length_ne
    {Γ : Context signature}
    (head body : SetTerm)
    (tokens : List Nat)
    (bodyLength : Nat)
    (hHead : Term.Admissible head SetSort.set)
    (hBody : Term.Admissible body SetSort.set)
    (hHeadFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition head)
    (hHeadDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(head) ≐ₘ numₘ(1))
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          headed_application_code_term head body)
    (hLength :
      tokens.length ≠ 2 + bodyLength + 1) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let code : SetTerm :=
    headed_application_code_term head body
  have hCodeDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(tokens.length) :=
    gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
      (fun _ hAxiom => hAxiom)
      code tokens
      (Metatheory.Derives.equality_symm hEquality)
  have hConstructorDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ
          numₘ(2 + bodyLength + 1) := by
    simpa [code] using
      gq_headed_application_domain_eq_of_body_domain
        (Γ := Γ) head body bodyLength
        hHead hBody
        hHeadFinite hHeadDomain
        hBodyFinite hBodyDomain
  have hNumeralEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(tokens.length) ≐ₘ
          numₘ(2 + bodyLength + 1) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hCodeDomain)
      hConstructorDomain
  have hNotEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        ¬ₘ (numₘ(tokens.length) ≐ₘ
          numₘ(2 + bodyLength + 1)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_ne
            hLength
  exact FirstOrder.Derives.negElim
    hNumeralEquality hNotEquality

/-- 已知正文定义域时，从标准整串等式恢复固定二 token 前缀后的正文切片。 -/
theorem gq_headed_application_body_eq_standard_slice
    {Γ : Context signature}
    (headToken : Nat)
    (head body : SetTerm)
    (tokens : List Nat)
    (bodyLength : Nat)
    (hHead : Term.Admissible head SetSort.set)
    (hBody : Term.Admissible body SetSort.set)
    (hHeadEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        head ≐ₘ standard_token_sequence [headToken])
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          headed_application_code_term head body)
    (hSliceBound :
      2 + bodyLength ≤ tokens.length) :
    Γ ⊢ₘ[godel_quotation_theory]
      body ≐ₘ
        standard_token_sequence
          ((tokens.drop 2).take bodyLength) := by
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let prefixCode : SetTerm :=
    head ⌢ₘ leftParenthesis
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  let prefixTokens : List Nat :=
    [headToken,
      Numbered.logical_token .leftParenthesis]
  have hLeftEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ
          standard_token_sequence
            [Numbered.logical_token
              .leftParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [leftParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis
  have hPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence prefixTokens := by
    simpa [prefixCode, prefixTokens] using
      gq_concatenation_eq_standard_token_sequence
        [headToken]
        [Numbered.logical_token
          .leftParenthesis]
        head leftParenthesis
        hHeadEquality hLeftEquality
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  simpa [prefixCode, rightParenthesis, prefixTokens,
    headed_application_code_term] using
    gq_concatenation_middle_eq_standard_slice_of_domain
      prefixCode body rightParenthesis
      prefixTokens tokens bodyLength
      hPrefixEquality hBodyFinite hRightFinite
      hBodyDomain hEquality
      (by simpa [prefixTokens] using hSliceBound)
      (hPrefix := by prove_term_check)
      (hBody := by prove_term_check)
      (hSuffix := by prove_term_check)

/--
统一应用正文切片反演只依赖 GQ 理论。

四个对象前提在 GQ 临时上下文中进行有限 replay，再通过 `multi_cut` 回放到任意
扩张理论；不要求调用方把局部事实提升为理论公理。
-/
theorem gq_headed_application_body_eq_standard_slice_of_theory
    {T : Theory signature}
    {Γ : Context signature}
    (hTheory :
      ∀ formula,
        godel_quotation_theory formula →
          T formula)
    (headToken : Nat)
    (head body : SetTerm)
    (tokens : List Nat)
    (bodyLength : Nat)
    (hHeadEquality :
      Γ ⊢ₘ[T]
        head ≐ₘ standard_token_sequence [headToken])
    (hBodyFinite :
      Γ ⊢ₘ[T]
        finite_sequence_condition body)
    (hBodyDomain :
      Γ ⊢ₘ[T]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hEquality :
      Γ ⊢ₘ[T]
        standard_token_sequence tokens ≐ₘ
          headed_application_code_term head body)
    (hSliceBound :
      2 + bodyLength ≤ tokens.length)
    (hHeadCheck :
      Term.CheckCertificate head SetSort.set := by
        prove_term_check)
    (hBodyCheck :
      Term.CheckCertificate body SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[T]
      body ≐ₘ
        standard_token_sequence
          ((tokens.drop 2).take bodyLength) := by
  let Δ : Context signature := [
    (head ≐ₘ standard_token_sequence [headToken]),
    finite_sequence_condition body,
    (domₘ(body) ≐ₘ numₘ(bodyLength)),
    (standard_token_sequence tokens ≐ₘ
      headed_application_code_term head body)]
  have hCodeCheck :
      Term.CheckCertificate
        (headed_application_code_term head body)
        SetSort.set := by
    prove_term_check
  have hHeadEqualityAt :
      Δ ⊢ₘ[godel_quotation_theory]
        head ≐ₘ standard_token_sequence [headToken] :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          hHeadCheck.admissible
          (standard_token_sequence_admissible
            [headToken])))
  have hBodyFiniteAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (finite_sequence_condition_admissible
          body hBodyCheck.admissible))
  have hBodyDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (domain_term_admissible
            body hBodyCheck.admissible)
          (finite_numeral_term_admissible
            bodyLength)))
  have hEqualityAt :
      Δ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          headed_application_code_term head body :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (standard_token_sequence_admissible tokens)
          hCodeCheck.admissible))
  have hBody :
      Δ ⊢ₘ[godel_quotation_theory]
        body ≐ₘ
          standard_token_sequence
            ((tokens.drop 2).take bodyLength) :=
    gq_headed_application_body_eq_standard_slice
      headToken head body tokens bodyLength
      hHeadCheck.admissible hBodyCheck.admissible
      hHeadEqualityAt hBodyFiniteAt
      hBodyDomainAt hEqualityAt hSliceBound
  apply FirstOrder.Derives.multi_cut
    (T := T) (Γ := Γ) (premises := Δ)
  · intro formula hFormula
    simp [Δ] at hFormula
    rcases hFormula with
      rfl | rfl | rfl | rfl
    · exact hHeadEquality
    · exact hBodyFinite
    · exact hBodyDomain
    · exact hEquality
  · exact
      (FirstOrder.Derives.theory_weaken
        hTheory hBody).context_weaken_append

/-- 统一应用码在正文之后的下一位置必为右括号。 -/
theorem gq_headed_application_right_parenthesis_point
    {Γ : Context signature}
    (head body : SetTerm)
    (bodyLength : Nat)
    (hHead : Term.Admissible head SetSort.set)
    (hBody : Term.Admissible body SetSort.set)
    (hHeadFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition head)
    (hHeadDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(head) ≐ₘ numₘ(1))
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength)) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((numₘ(2 + bodyLength) ∈ₘ
          domₘ(headed_application_code_term
            head body)) ∧ₘ
        ((headed_application_code_term head body ·ₘ
            numₘ(2 + bodyLength)) ≐ₘ
          numₘ(Numbered.logical_token
            .rightParenthesis))) := by
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let prefixCode : SetTerm :=
    head ⌢ₘ leftParenthesis
  let middle : SetTerm :=
    prefixCode ⌢ₘ body
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        head leftParenthesis
        hHeadFinite hLeftFinite
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ numₘ(2) := by
    simpa [prefixCode] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        head leftParenthesis 1 1
        hHeadFinite hLeftFinite
        hHeadDomain hLeftDomain
  have hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle := by
    simpa [middle] using
      gq_concatenation_finite
        prefixCode body hPrefixFinite hBodyFinite
  have hMiddleDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(middle) ≐ₘ
          numₘ(2 + bodyLength) := by
    simpa [middle] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        prefixCode body 2 bodyLength
        hPrefixFinite hBodyFinite
        hPrefixDomain hBodyDomain
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRightPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(rightParenthesis)) ∧ₘ
          ((rightParenthesis ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .rightParenthesis))) := by
    simpa [rightParenthesis] using
      gq_standard_token_sequence_point_inversion
        rightParenthesis
        [Numbered.logical_token .rightParenthesis]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            logical_symbol_code_eq_standard_token_sequence
              .rightParenthesis)
        (by simp)
  have hRaw :=
    gq_concatenation_right_point_at_numeral_offset
      middle rightParenthesis
      (2 + bodyLength) 0
      hMiddleFinite hRightFinite hMiddleDomain
      (FirstOrder.Derives.conjElimLeft
        hRightPoint)
  simpa [leftParenthesis, prefixCode, middle,
    rightParenthesis, headed_application_code_term] using
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjElimLeft hRaw)
      (Metatheory.Derives.equality_trans
        (FirstOrder.Derives.conjElimRight hRaw)
        (FirstOrder.Derives.conjElimRight
          hRightPoint))

/-- 标准输入末位不是右括号时，不可能等于统一应用码。 -/
theorem gq_headed_application_standard_falsum_of_last_not_right
    {Γ : Context signature}
    (head body : SetTerm)
    (tokens : List Nat)
    (bodyLength : Nat)
    (hHead : Term.Admissible head SetSort.set)
    (hBody : Term.Admissible body SetSort.set)
    (hHeadFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition head)
    (hHeadDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(head) ≐ₘ numₘ(1))
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          headed_application_code_term head body)
    (hLast :
      tokens[2 + bodyLength]? ≠
        some (Numbered.logical_token
          .rightParenthesis)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum :=
  gq_standard_token_sequence_falsum_of_point_not_expected
    tokens
    (headed_application_code_term head body)
    (2 + bodyLength)
    (Numbered.logical_token .rightParenthesis)
    hLast hEquality
    (gq_headed_application_right_parenthesis_point
      head body bodyLength
      hHead hBody
      hHeadFinite hHeadDomain
      hBodyFinite hBodyDomain)

/-- 固定头、括号、正文切片和总长度唯一重组出宿主应用 token 串。 -/
theorem fs_headed_application_tokens_eq_of_slice
    (tokens bodyTokens : List Nat)
    (headToken : Nat)
    (hLength :
      tokens.length =
        2 + bodyTokens.length + 1)
    (hHead :
      tokens[0]? = some headToken)
    (hLeft :
      tokens[1]? =
        some (Numbered.logical_token
          .leftParenthesis))
    (hBody :
      bodyTokens =
        (tokens.drop 2).take bodyTokens.length)
    (hRight :
      tokens[2 + bodyTokens.length]? =
        some (Numbered.logical_token
          .rightParenthesis)) :
    [headToken,
        Numbered.logical_token .leftParenthesis] ++
      bodyTokens ++
        [Numbered.logical_token .rightParenthesis] =
      tokens := by
  cases tokens with
  | nil =>
      simp at hHead
  | cons head tail =>
      simp at hHead
      subst head
      cases tail with
      | nil =>
          simp at hLeft
      | cons left rest =>
          simp at hLeft
          subst left
          have hRestLength :
              rest.length =
                bodyTokens.length + 1 := by
            simp only [List.length_cons] at hLength
            omega
          have hBody' :
              bodyTokens =
                rest.take bodyTokens.length := by
            simpa using hBody
          have hRight' :
              rest[bodyTokens.length]? =
                some (Numbered.logical_token
                  .rightParenthesis) := by
            simpa only [
              show 2 + bodyTokens.length =
                bodyTokens.length + 2 by omega,
              List.getElem?_cons_succ] using hRight
          have hIndex :
              bodyTokens.length < rest.length := by
            omega
          have hGet :=
            List.getElem?_eq_getElem hIndex
          rw [hRight'] at hGet
          have hValue :
              rest[bodyTokens.length] =
                Numbered.logical_token
                  .rightParenthesis :=
            Option.some.inj hGet.symm
          have hRest :
              rest =
                rest.take bodyTokens.length ++
                  [Numbered.logical_token
                    .rightParenthesis] := by
            calc
              rest =
                  rest.take
                    (bodyTokens.length + 1) := by
                rw [← hRestLength, List.take_length]
              _ =
                  rest.take bodyTokens.length ++
                    [rest[bodyTokens.length]] :=
                List.take_succ_eq_append_getElem hIndex
              _ =
                  rest.take bodyTokens.length ++
                    [Numbered.logical_token
                      .rightParenthesis] := by
                rw [hValue]
          simp only [List.cons_append,
            List.nil_append]
          rw [hRest, ← hBody']

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
