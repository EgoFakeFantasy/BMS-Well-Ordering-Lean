import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalPropositionalMismatchRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.CodeTransport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.LogicalPropositionalFailure

/-!
# 命题基础逻辑证书的失败适配

本模块只把宿主 checker 已给出的失败视图压到相应对象分支的否定，不扩展成功
反演层。对象 payload 与行内容的恢复均调用既有通用拒绝定理。
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

/-- 固定 binder 基址下 tag 0--6 的标准对象分支。 -/
def fs_zfc_logical_propositional_certificate_branch_with_base
    (formulaCode certificate : SetTerm)
    (base : FreeVarId) : Nat → SetFormula
  | 0 =>
      logical_ternary_base_certificate_condition_with_ids
        0 implication_distribution_axiom_code_term
        formulaCode certificate
        base (base + 1) (base + 2) (base + 3) (base + 4)
        (base + 40) (base + 41)
  | 1 =>
      logical_unary_base_certificate_condition_with_ids
        1 self_implication_axiom_code_term
        formulaCode certificate
        (base + 5) (base + 6) (base + 7)
        (base + 40) (base + 41)
  | 2 =>
      logical_binary_base_certificate_condition_with_ids
        2 weakening_axiom_code_term formulaCode certificate
        (base + 8) (base + 9) (base + 10) (base + 11)
        (base + 40) (base + 41)
  | 3 =>
      logical_binary_base_certificate_condition_with_ids
        3 contradiction_axiom_code_term formulaCode certificate
        (base + 12) (base + 13) (base + 14) (base + 15)
        (base + 40) (base + 41)
  | 4 =>
      logical_unary_base_certificate_condition_with_ids
        4 classical_axiom_code_term formulaCode certificate
        (base + 16) (base + 17) (base + 18)
        (base + 40) (base + 41)
  | 5 =>
      logical_binary_base_certificate_condition_with_ids
        5 explosion_axiom_code_term formulaCode certificate
        (base + 19) (base + 20) (base + 21) (base + 22)
        (base + 40) (base + 41)
  | 6 =>
      logical_binary_base_certificate_condition_with_ids
        6 case_analysis_axiom_code_term formulaCode certificate
        (base + 23) (base + 24) (base + 25) (base + 26)
        (base + 40) (base + 41)
  | _ => Formula.falsum

/-- 固定 binder 基址下，当前命题公理分支实际使用的保留编号。 -/
def fs_zfc_logical_propositional_reserved_ids_with_base
    (base : FreeVarId) : Nat → List FreeVarId
  | 0 => [base, base + 1, base + 2, base + 3, base + 4, base + 40, base + 41]
  | 1 => [base + 5, base + 6, base + 7, base + 40, base + 41]
  | 2 => [base + 8, base + 9, base + 10, base + 11, base + 40, base + 41]
  | 3 => [base + 12, base + 13, base + 14, base + 15, base + 40, base + 41]
  | 4 => [base + 16, base + 17, base + 18, base + 40, base + 41]
  | 5 => [base + 19, base + 20, base + 21, base + 22, base + 40, base + 41]
  | 6 => [base + 23, base + 24, base + 25, base + 26, base + 40, base + 41]
  | _ => []

/-- 候选公式码唯一性与当前标准行互异时，该对象分支为假。 -/
theorem fs_zfc_support_raw_logical_branch_neg_of_candidate_ne
    (condition : SetFormula)
    (formulaCode : SetTerm)
    (row expectedTokens : List Nat)
    (hExpected :
      Derives fs_zfc_support_raw_theory [] (
        condition ⟶ₘ
          formulaCode ≐ₘ standard_token_sequence expectedTokens))
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence row))
    (hRowNe : row ≠ expectedTokens) :
    Derives fs_zfc_support_raw_theory [] (¬ₘ condition) := by
  have hCondition :
      Formula.Admissible condition :=
    Formula.Admissible.imp_left hExpected.admissible
  apply FirstOrder.Derives.negIntro
    (hBodyCheck := Formula.check_admissible_complete hCondition)
  let Γ : Context signature := [condition]
  have hConditionAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hCondition)
  have hFormulaExpected :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        formulaCode ≐ₘ standard_token_sequence expectedTokens :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hExpected)
      hConditionAt
  have hFormulaToRowAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        formulaCode ≐ₘ standard_token_sequence row :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hFormulaToRow
  have hRowsEqual :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence row ≐ₘ
          standard_token_sequence expectedTokens :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hFormulaToRowAt)
      hFormulaExpected
  exact FirstOrder.Derives.negElim hRowsEqual <|
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_standard_sequence <|
          standard_token_sequence_ne hRowNe

/-- 具名一元 payload 唯一给出可解码的候选标准公式码。 -/
theorem
    fs_zfc_support_raw_logical_unary_base_certificate_candidate_of_named_payload
    (raw tag freeBase : Nat)
    (component expected : SetFormula)
    (tokenConstructor : List Nat → List Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId componentId traceId indexId : FreeVarId)
    (hTraceFresh : traceId ∉ [payloadId, sequenceId, componentId])
    (hIndexFresh : indexId ∉ [payloadId, sequenceId, componentId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ term, Term.Admissible term SetSort.set →
        Term.Admissible (constructor term) SetSort.set)
    (hConstructorSupport :
      ∀ term freeVariable,
        freeVariable ∈ Term.freeSupport (constructor term) →
          freeVariable ∈ Term.freeSupport term)
    (hConstructorSubstitute :
      ∀ parameter replacement term,
        Term.substituteFree SetSort.set parameter replacement
            (constructor term) =
          constructor
            (Term.substituteFree SetSort.set parameter replacement term))
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, componentId, traceId, indexId]
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (certificate ≐ₘ numₘ(raw)))
    (hPayload :
      fs_named_formula_payload_decode freeBase
          (godel_unpair_value raw).2 =
        some [component])
    (hExpectedDecode :
      ∀ tokens,
        fs_named_hilbert_tokens_decode_with_env freeBase [] tokens =
          some component →
        fs_named_hilbert_tokens_decode_with_env freeBase []
            (tokenConstructor tokens) =
          some expected)
    (hConstructorStandard :
      ∀ tokens,
        Derives fs_zfc_support_raw_theory [] (
          constructor (standard_token_sequence tokens) ≐ₘ
            standard_token_sequence (tokenConstructor tokens))) :
    ∃ expectedTokens,
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] expectedTokens =
        some expected ∧
      Derives fs_zfc_support_raw_theory [] (
        logical_unary_base_certificate_condition_with_ids
            tag constructor formulaCode certificate
            payloadId sequenceId componentId traceId indexId ⟶ₘ
          formulaCode ≐ₘ standard_token_sequence expectedTokens) := by
  rcases fs_named_formula_payload_decode_one hPayload with
    ⟨componentCode, hCodes, hComponentCode⟩
  let tokens := nat_sequence_decode componentCode
  let expectedTokens := tokenConstructor tokens
  have hComponent :
      fs_named_hilbert_tokens_decode_with_env freeBase [] tokens =
        some component := by
    simpa [tokens, fs_named_formula_token_code_decode] using hComponentCode
  refine ⟨expectedTokens, ?_, ?_⟩
  · simpa [expectedTokens] using hExpectedDecode tokens hComponent
  · exact
      fs_zfc_support_raw_logical_unary_base_certificate_eq_standard_imp
        raw tag componentCode expectedTokens constructor
        formulaCode certificate
        payloadId sequenceId componentId traceId indexId
        hTraceFresh hIndexFresh hTraceNeIndex
        hConstructorAdmissible hConstructorSupport hConstructorSubstitute
        hFormulaCode hCertificate hReservedFresh hCertificateCode
        (by simp [hCodes])
        (by
          simpa [tokens, expectedTokens] using hConstructorStandard tokens)

/-- 具名一元 payload 的公式错配适配。 -/
theorem
    fs_zfc_support_raw_logical_unary_base_certificate_neg_of_named_mismatch
    (raw tag freeBase : Nat)
    (row : List Nat)
    (formula component expected : SetFormula)
    (tokenConstructor : List Nat → List Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId componentId traceId indexId : FreeVarId)
    (hTraceFresh : traceId ∉ [payloadId, sequenceId, componentId])
    (hIndexFresh : indexId ∉ [payloadId, sequenceId, componentId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ term, Term.Admissible term SetSort.set →
        Term.Admissible (constructor term) SetSort.set)
    (hConstructorSupport :
      ∀ term freeVariable,
        freeVariable ∈ Term.freeSupport (constructor term) →
          freeVariable ∈ Term.freeSupport term)
    (hConstructorSubstitute :
      ∀ parameter replacement term,
        Term.substituteFree SetSort.set parameter replacement
            (constructor term) =
          constructor
            (Term.substituteFree SetSort.set parameter replacement term))
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, componentId, traceId, indexId]
        [formulaCode, certificate])
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence row))
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (certificate ≐ₘ numₘ(raw)))
    (hRowDecode :
      fs_named_hilbert_tokens_decode_with_env freeBase [] row =
        some formula)
    (hPayload :
      fs_named_formula_payload_decode freeBase
          (godel_unpair_value raw).2 =
        some [component])
    (hExpectedDecode :
      ∀ tokens,
        fs_named_hilbert_tokens_decode_with_env freeBase [] tokens =
          some component →
        fs_named_hilbert_tokens_decode_with_env freeBase []
            (tokenConstructor tokens) =
          some expected)
    (hConstructorStandard :
      ∀ tokens,
        Derives fs_zfc_support_raw_theory [] (
          constructor (standard_token_sequence tokens) ≐ₘ
            standard_token_sequence (tokenConstructor tokens)))
    (hMismatch : formula ≠ expected) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_unary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId componentId traceId indexId) := by
  rcases
      fs_zfc_support_raw_logical_unary_base_certificate_candidate_of_named_payload
        raw tag freeBase component expected tokenConstructor constructor
        formulaCode certificate
        payloadId sequenceId componentId traceId indexId
        hTraceFresh hIndexFresh hTraceNeIndex
        hConstructorAdmissible hConstructorSupport hConstructorSubstitute
        hFormulaCode hCertificate hReservedFresh hCertificateCode hPayload
        hExpectedDecode hConstructorStandard with
    ⟨expectedTokens, hExpectedDecode, hExpected⟩
  have hRowNe : row ≠ expectedTokens := by
    intro hEquality
    rw [hEquality] at hRowDecode
    apply hMismatch
    exact Option.some.inj <| hRowDecode.symm.trans hExpectedDecode
  exact
    fs_zfc_support_raw_logical_branch_neg_of_candidate_ne
      (logical_unary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId componentId traceId indexId)
      formulaCode row expectedTokens hExpected hFormulaToRow hRowNe

/-- tag 0 的成功 payload 唯一给出可解码的蕴含分配候选公式码。 -/
theorem
    fs_zfc_support_raw_logical_implication_distribution_base_certificate_candidate_of_named_payload
    (raw freeBase : Nat)
    (antecedent middle consequent : SetFormula)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId antecedentId middleId consequentId traceId indexId :
      FreeVarId)
    (hTraceFresh :
      traceId ∉
        [payloadId, sequenceId, antecedentId, middleId, consequentId])
    (hIndexFresh :
      indexId ∉
        [payloadId, sequenceId, antecedentId, middleId, consequentId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, antecedentId, middleId, consequentId,
          traceId, indexId]
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (certificate ≐ₘ numₘ(raw)))
    (hPayload :
      fs_named_formula_payload_decode freeBase
          (godel_unpair_value raw).2 =
        some [antecedent, middle, consequent]) :
    ∃ expectedTokens,
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] expectedTokens =
        some
          (Formula.imp
            (Formula.imp antecedent (Formula.imp middle consequent))
            (Formula.imp
              (Formula.imp antecedent middle)
              (Formula.imp antecedent consequent))) ∧
      Derives fs_zfc_support_raw_theory [] (
        logical_ternary_base_certificate_condition_with_ids
            0 implication_distribution_axiom_code_term
            formulaCode certificate
            payloadId sequenceId antecedentId middleId consequentId
            traceId indexId ⟶ₘ
          formulaCode ≐ₘ standard_token_sequence expectedTokens) := by
  rcases fs_named_formula_payload_decode_three hPayload with
    ⟨antecedentCode, middleCode, consequentCode, hCodes,
      hAntecedentCode, hMiddleCode, hConsequentCode⟩
  let antecedentTokens := nat_sequence_decode antecedentCode
  let middleTokens := nat_sequence_decode middleCode
  let consequentTokens := nat_sequence_decode consequentCode
  let expectedTokens :=
    fs_implication_distribution_axiom_tokens
      antecedentTokens middleTokens consequentTokens
  have hAntecedent :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] antecedentTokens =
        some antecedent := by
    simpa [antecedentTokens, fs_named_formula_token_code_decode] using
      hAntecedentCode
  have hMiddle :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] middleTokens =
        some middle := by
    simpa [middleTokens, fs_named_formula_token_code_decode] using
      hMiddleCode
  have hConsequent :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] consequentTokens =
        some consequent := by
    simpa [consequentTokens, fs_named_formula_token_code_decode] using
      hConsequentCode
  have hMiddleConsequent :=
    fs_named_hilbert_tokens_decode_with_env_implication
      freeBase [] hMiddle hConsequent
  have hLeft :=
    fs_named_hilbert_tokens_decode_with_env_implication
      freeBase [] hAntecedent hMiddleConsequent
  have hAntecedentMiddle :=
    fs_named_hilbert_tokens_decode_with_env_implication
      freeBase [] hAntecedent hMiddle
  have hAntecedentConsequent :=
    fs_named_hilbert_tokens_decode_with_env_implication
      freeBase [] hAntecedent hConsequent
  have hRight :=
    fs_named_hilbert_tokens_decode_with_env_implication
      freeBase [] hAntecedentMiddle hAntecedentConsequent
  have hExpected :=
    fs_named_hilbert_tokens_decode_with_env_implication
      freeBase [] hLeft hRight
  refine ⟨expectedTokens, ?_, ?_⟩
  · simpa [expectedTokens,
      fs_implication_distribution_axiom_tokens] using hExpected
  · exact
    fs_zfc_support_raw_logical_ternary_base_certificate_eq_standard_imp
      raw 0 antecedentCode middleCode consequentCode expectedTokens
      implication_distribution_axiom_code_term formulaCode certificate
      payloadId sequenceId antecedentId middleId consequentId traceId indexId
      hTraceFresh hIndexFresh hTraceNeIndex
      implication_distribution_axiom_code_term_admissible
      (by
        intro first second third freeVariable hMember
        simp [Term.freeSupport,
          Term.freeSupportList] at hMember
        rcases hMember with
          hMember | hMember | hMember | hMember | hMember | hMember | hMember
        · exact Or.inl hMember
        · exact Or.inr (Or.inl hMember)
        · exact Or.inr (Or.inr hMember)
        · exact Or.inl hMember
        · exact Or.inr (Or.inl hMember)
        · exact Or.inl hMember
        · exact Or.inr (Or.inr hMember))
      (by
        intro Γ firstLeft firstRight secondLeft secondRight
          thirdLeft thirdRight hFirstLeft hFirstRight hSecondLeft
          hSecondRight hThirdLeft hThirdRight hFirst hSecond hThird
        have hImp
            (left₁ left₂ right₁ right₂ : SetTerm)
            (hLeft₁ : Term.Admissible left₁ SetSort.set)
            (hLeft₂ : Term.Admissible left₂ SetSort.set)
            (hRight₁ : Term.Admissible right₁ SetSort.set)
            (hRight₂ : Term.Admissible right₂ SetSort.set)
            (hLeft : Γ ⊢ₘ[fs_zfc_support_raw_theory] left₁ ≐ₘ left₂)
            (hRight : Γ ⊢ₘ[fs_zfc_support_raw_theory] right₁ ≐ₘ right₂) :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              imp_codeₘ(left₁, right₁) ≐ₘ
                imp_codeₘ(left₂, right₂) :=
          canonical_implication_code_term_congr_of_equalities
            (T := fs_zfc_support_raw_theory) (Γ := Γ)
            left₁ left₂ right₁ right₂
            hLeft₁ hLeft₂ hRight₁ hRight₂ hLeft hRight
        have hSecondThird :=
          hImp secondLeft secondRight thirdLeft thirdRight
            hSecondLeft hSecondRight hThirdLeft hThirdRight hSecond hThird
        have hLeft :=
          hImp firstLeft firstRight
            (imp_codeₘ(secondLeft, thirdLeft))
            (imp_codeₘ(secondRight, thirdRight))
            hFirstLeft hFirstRight
            (implication_formula_code_term_admissible
              secondLeft thirdLeft hSecondLeft hThirdLeft)
            (implication_formula_code_term_admissible
              secondRight thirdRight hSecondRight hThirdRight)
            hFirst hSecondThird
        have hFirstSecond :=
          hImp firstLeft firstRight secondLeft secondRight
            hFirstLeft hFirstRight hSecondLeft hSecondRight hFirst hSecond
        have hFirstThird :=
          hImp firstLeft firstRight thirdLeft thirdRight
            hFirstLeft hFirstRight hThirdLeft hThirdRight hFirst hThird
        have hRight :=
          hImp
            (imp_codeₘ(firstLeft, secondLeft))
            (imp_codeₘ(firstRight, secondRight))
            (imp_codeₘ(firstLeft, thirdLeft))
            (imp_codeₘ(firstRight, thirdRight))
            (implication_formula_code_term_admissible
              firstLeft secondLeft hFirstLeft hSecondLeft)
            (implication_formula_code_term_admissible
              firstRight secondRight hFirstRight hSecondRight)
            (implication_formula_code_term_admissible
              firstLeft thirdLeft hFirstLeft hThirdLeft)
            (implication_formula_code_term_admissible
              firstRight thirdRight hFirstRight hThirdRight)
            hFirstSecond hFirstThird
        exact hImp _ _ _ _
          (implication_formula_code_term_admissible _ _
            hFirstLeft
            (implication_formula_code_term_admissible _ _
              hSecondLeft hThirdLeft))
          (implication_formula_code_term_admissible _ _
            hFirstRight
            (implication_formula_code_term_admissible _ _
              hSecondRight hThirdRight))
          (implication_formula_code_term_admissible _ _
            (implication_formula_code_term_admissible _ _
              hFirstLeft hSecondLeft)
            (implication_formula_code_term_admissible _ _
              hFirstLeft hThirdLeft))
          (implication_formula_code_term_admissible _ _
            (implication_formula_code_term_admissible _ _
              hFirstRight hSecondRight)
            (implication_formula_code_term_admissible _ _
              hFirstRight hThirdRight))
          hLeft hRight)
      hFormulaCode hCertificate hReservedFresh hCertificateCode
      (by simp [hCodes])
      (by
        simpa [antecedentTokens, middleTokens, consequentTokens,
          expectedTokens] using
          fs_zfc_support_raw_implication_distribution_axiom_code_eq_standard
            antecedentTokens middleTokens consequentTokens)

/-- tag 0 候选公式与当前标准行错配时，导出对应分支的对象层否定。 -/
theorem
    fs_zfc_support_raw_logical_implication_distribution_base_certificate_neg_of_mismatch
    (raw freeBase : Nat)
    (row : List Nat)
    (formula antecedent middle consequent : SetFormula)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId antecedentId middleId consequentId traceId indexId :
      FreeVarId)
    (hTraceFresh :
      traceId ∉
        [payloadId, sequenceId, antecedentId, middleId, consequentId])
    (hIndexFresh :
      indexId ∉
        [payloadId, sequenceId, antecedentId, middleId, consequentId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, antecedentId, middleId, consequentId,
          traceId, indexId]
        [formulaCode, certificate])
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence row))
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (certificate ≐ₘ numₘ(raw)))
    (hRowDecode :
      fs_named_hilbert_tokens_decode_with_env freeBase [] row =
        some formula)
    (hPayload :
      fs_named_formula_payload_decode freeBase
          (godel_unpair_value raw).2 =
        some [antecedent, middle, consequent])
    (hMismatch :
      formula ≠
        Formula.imp
          (Formula.imp antecedent (Formula.imp middle consequent))
          (Formula.imp
            (Formula.imp antecedent middle)
            (Formula.imp antecedent consequent))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_ternary_base_certificate_condition_with_ids
        0 implication_distribution_axiom_code_term
        formulaCode certificate
        payloadId sequenceId antecedentId middleId consequentId
        traceId indexId) := by
  rcases
      fs_zfc_support_raw_logical_implication_distribution_base_certificate_candidate_of_named_payload
        raw freeBase antecedent middle consequent formulaCode certificate
        payloadId sequenceId antecedentId middleId consequentId traceId indexId
        hTraceFresh hIndexFresh hTraceNeIndex
        hFormulaCode hCertificate hReservedFresh hCertificateCode hPayload with
    ⟨expectedTokens, hExpectedDecode, hExpected⟩
  have hRowNe : row ≠ expectedTokens := by
    intro hEquality
    rw [hEquality] at hRowDecode
    apply hMismatch
    exact Option.some.inj <| hRowDecode.symm.trans hExpectedDecode
  exact
    fs_zfc_support_raw_logical_branch_neg_of_candidate_ne
      (logical_ternary_base_certificate_condition_with_ids
        0 implication_distribution_axiom_code_term
        formulaCode certificate
        payloadId sequenceId antecedentId middleId consequentId
        traceId indexId)
      formulaCode row expectedTokens hExpected hFormulaToRow hRowNe

/-- tag 0--6 的 payload 失败否定当前标准对象分支。 -/
theorem fs_zfc_support_raw_logical_propositional_branch_neg_of_payload_failure
    (raw freeBase : Nat)
    (formulaCode certificate : SetTerm)
    (base : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        (fs_zfc_logical_propositional_reserved_ids_with_base
          base (godel_unpair_value raw).1)
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (certificate ≐ₘ numₘ(raw)))
    (hTagBound : (godel_unpair_value raw).1 ≤ 6)
    (hFailure :
      FSNamedFormulaPayloadArityFailure freeBase
        (godel_unpair_value raw).2
        (fs_logical_propositional_payload_arity
          (godel_unpair_value raw).1)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_logical_propositional_certificate_branch_with_base
        formulaCode certificate base (godel_unpair_value raw).1) := by
  have hTraceIndex : base + 40 ≠ base + 41 :=
    Nat.ne_of_lt <| Nat.add_lt_add_left (by decide : 40 < 41) base
  have hCases :
      (godel_unpair_value raw).1 = 0 ∨
      (godel_unpair_value raw).1 = 1 ∨
      (godel_unpair_value raw).1 = 2 ∨
      (godel_unpair_value raw).1 = 3 ∨
      (godel_unpair_value raw).1 = 4 ∨
      (godel_unpair_value raw).1 = 5 ∨
      (godel_unpair_value raw).1 = 6 := by omega
  rcases hCases with h | h | h | h | h | h | h
  · rw [h] at hFailure hReservedFresh ⊢
    exact fs_zfc_support_raw_logical_ternary_base_certificate_neg_of_payload_failure
      raw 0 freeBase implication_distribution_axiom_code_term
      formulaCode certificate
      base (base + 1) (base + 2) (base + 3) (base + 4)
      (base + 40) (base + 41)
      (by simp) (by simp) hTraceIndex
      implication_distribution_axiom_code_term_admissible
      (by
        intro first second third freeVariable hMember
        simpa [implication_distribution_axiom_code_term,
          Term.freeSupport, Term.freeSupportList, or_assoc,
          or_left_comm, or_comm] using hMember)
      hFormulaCode hCertificate hReservedFresh hCertificateCode
      (by simpa [fs_logical_propositional_payload_arity] using hFailure)
  · rw [h] at hFailure hReservedFresh ⊢
    exact fs_zfc_support_raw_logical_unary_base_certificate_neg_of_payload_failure
      raw 1 freeBase self_implication_axiom_code_term
      formulaCode certificate
      (base + 5) (base + 6) (base + 7)
      (base + 40) (base + 41)
      (by simp) (by simp) hTraceIndex
      self_implication_axiom_code_term_admissible
      (by
        intro term freeVariable hMember
        simpa [Term.freeSupport, Term.freeSupportList] using hMember)
      hFormulaCode hCertificate hReservedFresh hCertificateCode
      (by simpa [fs_logical_propositional_payload_arity] using hFailure)
  all_goals
    rw [h] at hFailure hReservedFresh ⊢
  · exact fs_zfc_support_raw_logical_binary_base_certificate_neg_of_payload_failure
      raw 2 freeBase weakening_axiom_code_term formulaCode certificate
      (base + 8) (base + 9) (base + 10) (base + 11)
      (base + 40) (base + 41)
      (by simp) (by simp) hTraceIndex weakening_axiom_code_term_admissible
      (by
        intro left right freeVariable hMember
        simpa [weakening_axiom_code_term,
          Term.freeSupport, Term.freeSupportList, or_assoc,
          or_left_comm, or_comm] using hMember)
      hFormulaCode hCertificate hReservedFresh hCertificateCode
      (by simpa [fs_logical_propositional_payload_arity] using hFailure)
  · exact fs_zfc_support_raw_logical_binary_base_certificate_neg_of_payload_failure
      raw 3 freeBase contradiction_axiom_code_term formulaCode certificate
      (base + 12) (base + 13) (base + 14) (base + 15)
      (base + 40) (base + 41)
      (by simp) (by simp) hTraceIndex
      contradiction_axiom_code_term_admissible
      (by
        intro left right freeVariable hMember
        simpa [Term.freeSupport, Term.freeSupportList] using hMember)
      hFormulaCode hCertificate hReservedFresh hCertificateCode
      (by simpa [fs_logical_propositional_payload_arity] using hFailure)
  · exact fs_zfc_support_raw_logical_unary_base_certificate_neg_of_payload_failure
      raw 4 freeBase classical_axiom_code_term formulaCode certificate
      (base + 16) (base + 17) (base + 18)
      (base + 40) (base + 41)
      (by simp) (by simp) hTraceIndex classical_axiom_code_term_admissible
      (by
        intro term freeVariable hMember
        simpa only [classical_axiom_code_term, Term.freeSupport,
          Term.freeSupportList, List.mem_append, or_self,
          or_assoc, List.not_mem_nil, or_false] using hMember)
      hFormulaCode hCertificate hReservedFresh hCertificateCode
      (by simpa [fs_logical_propositional_payload_arity] using hFailure)
  · exact fs_zfc_support_raw_logical_binary_base_certificate_neg_of_payload_failure
      raw 5 freeBase explosion_axiom_code_term formulaCode certificate
      (base + 19) (base + 20) (base + 21) (base + 22)
      (base + 40) (base + 41)
      (by simp) (by simp) hTraceIndex explosion_axiom_code_term_admissible
      (by
        intro left right freeVariable hMember
        simpa [Term.freeSupport, Term.freeSupportList] using hMember)
      hFormulaCode hCertificate hReservedFresh hCertificateCode
      (by simpa [fs_logical_propositional_payload_arity] using hFailure)
  · exact fs_zfc_support_raw_logical_binary_base_certificate_neg_of_payload_failure
      raw 6 freeBase case_analysis_axiom_code_term formulaCode certificate
      (base + 23) (base + 24) (base + 25) (base + 26)
      (base + 40) (base + 41)
      (by simp) (by simp) hTraceIndex case_analysis_axiom_code_term_admissible
      (by
        intro left right freeVariable hMember
        simpa [case_analysis_axiom_code_term,
          Term.freeSupport, Term.freeSupportList, or_assoc,
          or_left_comm, or_comm] using hMember)
      hFormulaCode hCertificate hReservedFresh hCertificateCode
      (by simpa [fs_logical_propositional_payload_arity] using hFailure)

/--
命题 checker 的失败视图要么直接否定当前分支，要么给出唯一候选公式码。

右侧候选同时保留宿主公式错配；终局适配器可在闭包前向折叠后消费它。
-/
theorem fs_zfc_support_raw_logical_propositional_branch_neg_or_candidate_of_failure
    (raw freeBase : Nat) (formula : SetFormula)
    (formulaCode certificate : SetTerm) (base : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        (fs_zfc_logical_propositional_reserved_ids_with_base
          base (godel_unpair_value raw).1)
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (certificate ≐ₘ numₘ(raw)))
    (hTagBound : (godel_unpair_value raw).1 ≤ 6)
    (hFailure :
      FSLogicalPropositionalCheckFailureView freeBase formula
        (godel_unpair_value raw).2 (godel_unpair_value raw).1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_logical_propositional_certificate_branch_with_base
        formulaCode certificate base (godel_unpair_value raw).1) ∨
    ∃ expectedTokens expected,
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] expectedTokens =
        some expected ∧
      formula ≠ expected ∧
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_logical_propositional_certificate_branch_with_base
            formulaCode certificate base (godel_unpair_value raw).1 ⟶ₘ
          formulaCode ≐ₘ standard_token_sequence expectedTokens) := by
  generalize hPayloadCode :
      (godel_unpair_value raw).2 = payload at hFailure ⊢
  generalize hTagCode :
      (godel_unpair_value raw).1 = tag at hFailure hTagBound ⊢
  have hReservedFreshAtTag :
      ReservedIdsFresh
        (fs_zfc_logical_propositional_reserved_ids_with_base base tag)
        [formulaCode, certificate] := by
    simpa [hTagCode] using hReservedFresh
  have hTraceIndex : base + 40 ≠ base + 41 :=
    Nat.ne_of_lt <| Nat.add_lt_add_left (by decide : 40 < 41) base
  cases hFailure with
  | payload_failure h =>
      exact Or.inl <| by
        simpa [hTagCode] using
          fs_zfc_support_raw_logical_propositional_branch_neg_of_payload_failure
            raw freeBase formulaCode certificate base hFormulaCode hCertificate
            hReservedFresh hCertificateCode
            (by simpa [hTagCode] using hTagBound)
            (by simpa [hPayloadCode, hTagCode] using h)
  | implication_distribution_mismatch antecedent middle consequent hPayload hMismatch =>
      rcases
          fs_zfc_support_raw_logical_implication_distribution_base_certificate_candidate_of_named_payload
            raw freeBase antecedent middle consequent formulaCode certificate
            base (base + 1) (base + 2) (base + 3) (base + 4)
            (base + 40) (base + 41) (by simp) (by simp) hTraceIndex
            hFormulaCode hCertificate hReservedFreshAtTag hCertificateCode
            (by simpa [hPayloadCode] using hPayload) with
        ⟨expectedTokens, hExpectedDecode, hExpected⟩
      exact Or.inr ⟨expectedTokens, _, hExpectedDecode, hMismatch, by
        simpa [hTagCode,
          fs_zfc_logical_propositional_certificate_branch_with_base] using
          hExpected⟩
  | self_implication_mismatch body hPayload hMismatch =>
      rcases
          fs_zfc_support_raw_logical_unary_base_certificate_candidate_of_named_payload
            raw 1 freeBase body (.imp body (.imp body body))
            fs_self_implication_axiom_tokens self_implication_axiom_code_term
            formulaCode certificate
            (base + 5) (base + 6) (base + 7) (base + 40) (base + 41)
            (by simp) (by simp) hTraceIndex
            self_implication_axiom_code_term_admissible
            (by
              intro term freeVariable hMember
              simpa [self_implication_axiom_code_term, Term.freeSupport,
                Term.freeSupportList, or_assoc, or_left_comm, or_comm] using
                hMember)
            (by
              intros
              simp [self_implication_axiom_code_term, Term.substituteFree])
            hFormulaCode hCertificate hReservedFreshAtTag hCertificateCode
            (by simpa [hPayloadCode] using hPayload)
            (by
              intro tokens h
              exact fs_named_hilbert_tokens_decode_with_env_implication
                freeBase [] h <|
                  fs_named_hilbert_tokens_decode_with_env_implication
                    freeBase [] h h)
            fs_zfc_support_raw_self_implication_axiom_code_eq_standard with
        ⟨expectedTokens, hExpectedDecode, hExpected⟩
      exact Or.inr ⟨expectedTokens, _, hExpectedDecode, hMismatch, by
        simpa [hTagCode,
          fs_zfc_logical_propositional_certificate_branch_with_base] using
          hExpected⟩
  | weakening_mismatch body extra hPayload hMismatch =>
      rcases
          fs_zfc_support_raw_logical_binary_base_certificate_candidate_of_named_payload
            raw 2 freeBase body extra (.imp body (.imp extra body))
            fs_weakening_axiom_tokens weakening_axiom_code_term
            formulaCode certificate
            (base + 8) (base + 9) (base + 10) (base + 11)
            (base + 40) (base + 41)
            (by simp) (by simp) hTraceIndex
            weakening_axiom_code_term_admissible
            (by
              intro left right freeVariable hMember
              simpa [weakening_axiom_code_term, Term.freeSupport,
                Term.freeSupportList, or_assoc, or_left_comm, or_comm] using
                hMember)
            (by intros; simp [weakening_axiom_code_term, Term.substituteFree])
            hFormulaCode hCertificate hReservedFreshAtTag hCertificateCode
            (by simpa [hPayloadCode] using hPayload)
            (by
              intro leftTokens rightTokens hLeft hRight
              exact fs_named_hilbert_tokens_decode_with_env_implication
                freeBase [] hLeft <|
                  fs_named_hilbert_tokens_decode_with_env_implication
                    freeBase [] hRight hLeft)
            fs_zfc_support_raw_weakening_axiom_code_eq_standard with
        ⟨expectedTokens, hExpectedDecode, hExpected⟩
      exact Or.inr ⟨expectedTokens, _, hExpectedDecode, hMismatch, by
        simpa [hTagCode,
          fs_zfc_logical_propositional_certificate_branch_with_base] using
          hExpected⟩
  | contradiction_mismatch body conclusion hPayload hMismatch =>
      rcases
          fs_zfc_support_raw_logical_binary_base_certificate_candidate_of_named_payload
            raw 3 freeBase body conclusion
            (.imp body (.imp (.neg body) conclusion))
            fs_contradiction_axiom_tokens contradiction_axiom_code_term
            formulaCode certificate
            (base + 12) (base + 13) (base + 14) (base + 15)
            (base + 40) (base + 41)
            (by simp) (by simp) hTraceIndex
            contradiction_axiom_code_term_admissible
            (by
              intro left right freeVariable hMember
              simpa [contradiction_axiom_code_term, Term.freeSupport,
                Term.freeSupportList, or_assoc, or_left_comm, or_comm] using
                hMember)
            (by
              intros
              simp [contradiction_axiom_code_term, Term.substituteFree])
            hFormulaCode hCertificate hReservedFreshAtTag hCertificateCode
            (by simpa [hPayloadCode] using hPayload)
            (by
              intro leftTokens rightTokens hLeft hRight
              exact fs_named_hilbert_tokens_decode_with_env_implication
                freeBase [] hLeft <|
                  fs_named_hilbert_tokens_decode_with_env_implication
                    freeBase []
                    (fs_named_hilbert_tokens_decode_with_env_negation
                      freeBase [] hLeft)
                    hRight)
            fs_zfc_support_raw_contradiction_axiom_code_eq_standard with
        ⟨expectedTokens, hExpectedDecode, hExpected⟩
      exact Or.inr ⟨expectedTokens, _, hExpectedDecode, hMismatch, by
        simpa [hTagCode,
          fs_zfc_logical_propositional_certificate_branch_with_base] using
          hExpected⟩
  | classical_mismatch body hPayload hMismatch =>
      rcases
          fs_zfc_support_raw_logical_unary_base_certificate_candidate_of_named_payload
            raw 4 freeBase body
            (.imp (.imp (.neg body) body) body)
            fs_classical_axiom_tokens classical_axiom_code_term
            formulaCode certificate
            (base + 16) (base + 17) (base + 18)
            (base + 40) (base + 41)
            (by simp) (by simp) hTraceIndex
            classical_axiom_code_term_admissible
            (by
              intro term freeVariable hMember
              simpa [classical_axiom_code_term, Term.freeSupport,
                Term.freeSupportList, or_assoc, or_left_comm, or_comm] using
                hMember)
            (by intros; simp [classical_axiom_code_term, Term.substituteFree])
            hFormulaCode hCertificate hReservedFreshAtTag hCertificateCode
            (by simpa [hPayloadCode] using hPayload)
            (by
              intro tokens h
              exact fs_named_hilbert_tokens_decode_with_env_implication
                freeBase []
                (fs_named_hilbert_tokens_decode_with_env_implication
                  freeBase []
                  (fs_named_hilbert_tokens_decode_with_env_negation
                    freeBase [] h)
                  h)
                h)
            fs_zfc_support_raw_classical_axiom_code_eq_standard with
        ⟨expectedTokens, hExpectedDecode, hExpected⟩
      exact Or.inr ⟨expectedTokens, _, hExpectedDecode, hMismatch, by
        simpa [hTagCode,
          fs_zfc_logical_propositional_certificate_branch_with_base] using
          hExpected⟩
  | explosion_mismatch body conclusion hPayload hMismatch =>
      rcases
          fs_zfc_support_raw_logical_binary_base_certificate_candidate_of_named_payload
            raw 5 freeBase body conclusion
            (.imp (.neg body) (.imp body conclusion))
            fs_explosion_axiom_tokens explosion_axiom_code_term
            formulaCode certificate
            (base + 19) (base + 20) (base + 21) (base + 22)
            (base + 40) (base + 41)
            (by simp) (by simp) hTraceIndex
            explosion_axiom_code_term_admissible
            (by
              intro left right freeVariable hMember
              simpa [explosion_axiom_code_term, Term.freeSupport,
                Term.freeSupportList, or_assoc, or_left_comm, or_comm] using
                hMember)
            (by intros; simp [explosion_axiom_code_term, Term.substituteFree])
            hFormulaCode hCertificate hReservedFreshAtTag hCertificateCode
            (by simpa [hPayloadCode] using hPayload)
            (by
              intro leftTokens rightTokens hLeft hRight
              exact fs_named_hilbert_tokens_decode_with_env_implication
                freeBase []
                (fs_named_hilbert_tokens_decode_with_env_negation
                  freeBase [] hLeft)
                (fs_named_hilbert_tokens_decode_with_env_implication
                  freeBase [] hLeft hRight))
            fs_zfc_support_raw_explosion_axiom_code_eq_standard with
        ⟨expectedTokens, hExpectedDecode, hExpected⟩
      exact Or.inr ⟨expectedTokens, _, hExpectedDecode, hMismatch, by
        simpa [hTagCode,
          fs_zfc_logical_propositional_certificate_branch_with_base] using
          hExpected⟩
  | case_analysis_mismatch body conclusion hPayload hMismatch =>
      rcases
          fs_zfc_support_raw_logical_binary_base_certificate_candidate_of_named_payload
            raw 6 freeBase body conclusion
            (.imp (.imp body conclusion)
              (.imp (.imp (.neg body) conclusion) conclusion))
            fs_case_analysis_axiom_tokens case_analysis_axiom_code_term
            formulaCode certificate
            (base + 23) (base + 24) (base + 25) (base + 26)
            (base + 40) (base + 41)
            (by simp) (by simp) hTraceIndex
            case_analysis_axiom_code_term_admissible
            (by
              intro left right freeVariable hMember
              simpa [case_analysis_axiom_code_term, Term.freeSupport,
                Term.freeSupportList, or_assoc, or_left_comm, or_comm] using
                hMember)
            (by
              intros
              simp [case_analysis_axiom_code_term, Term.substituteFree])
            hFormulaCode hCertificate hReservedFreshAtTag hCertificateCode
            (by simpa [hPayloadCode] using hPayload)
            (by
              intro leftTokens rightTokens hLeft hRight
              exact fs_named_hilbert_tokens_decode_with_env_implication
                freeBase []
                (fs_named_hilbert_tokens_decode_with_env_implication
                  freeBase [] hLeft hRight)
                (fs_named_hilbert_tokens_decode_with_env_implication
                  freeBase []
                  (fs_named_hilbert_tokens_decode_with_env_implication
                    freeBase []
                    (fs_named_hilbert_tokens_decode_with_env_negation
                      freeBase [] hLeft)
                    hRight)
                  hRight))
            fs_zfc_support_raw_case_analysis_axiom_code_eq_standard with
        ⟨expectedTokens, hExpectedDecode, hExpected⟩
      exact Or.inr ⟨expectedTokens, _, hExpectedDecode, hMismatch, by
        simpa [hTagCode,
          fs_zfc_logical_propositional_certificate_branch_with_base] using
          hExpected⟩

/-- 候选分支与当前标准行错配时，恢复原有的命题分支否定接口。 -/
theorem fs_zfc_support_raw_logical_propositional_branch_neg_of_failure
    (raw freeBase : Nat) (row : List Nat) (formula : SetFormula)
    (formulaCode certificate : SetTerm) (base : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        (fs_zfc_logical_propositional_reserved_ids_with_base
          base (godel_unpair_value raw).1)
        [formulaCode, certificate])
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence row))
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (certificate ≐ₘ numₘ(raw)))
    (hRowDecode :
      fs_named_hilbert_tokens_decode_with_env freeBase [] row = some formula)
    (hTagBound : (godel_unpair_value raw).1 ≤ 6)
    (hFailure :
      FSLogicalPropositionalCheckFailureView freeBase formula
        (godel_unpair_value raw).2 (godel_unpair_value raw).1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_logical_propositional_certificate_branch_with_base
        formulaCode certificate base (godel_unpair_value raw).1) := by
  rcases
      fs_zfc_support_raw_logical_propositional_branch_neg_or_candidate_of_failure
        raw freeBase formula formulaCode certificate base
        hFormulaCode hCertificate hReservedFresh
        hCertificateCode hTagBound hFailure with
    hNeg | ⟨expectedTokens, expected, hExpectedDecode, hMismatch, hExpected⟩
  · exact hNeg
  · have hRowNe : row ≠ expectedTokens := by
      intro hEquality
      rw [hEquality] at hRowDecode
      apply hMismatch
      exact Option.some.inj <| hRowDecode.symm.trans hExpectedDecode
    exact
      fs_zfc_support_raw_logical_branch_neg_of_candidate_ne
        (fs_zfc_logical_propositional_certificate_branch_with_base
          formulaCode certificate base (godel_unpair_value raw).1)
        formulaCode row expectedTokens hExpected hFormulaToRow hRowNe

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
