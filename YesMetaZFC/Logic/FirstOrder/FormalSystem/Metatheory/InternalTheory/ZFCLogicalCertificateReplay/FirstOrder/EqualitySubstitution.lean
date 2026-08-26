import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Base
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCEqAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.LogicalFirstOrderInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence.Freshness

/-!
# checked 逻辑证书的等式替换分支

本模块回放 tag 10。替换规格由成功 quotation 的对象层
`code_substitution_spec` 直接提供；payload 序列、公式字段和最终公式码仍全部
进入同一个精确证书条件。
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

theorem fs_zfc_support_raw_logical_equality_substitution_certificate_of_decode
    (payload certificate leftId rightId bodyCode : Nat)
    (body : SetFormula)
    (formulaCode resultCode certificateTerm : SetTerm)
    (payloadId sequenceId bodyId resultId traceId indexId : FreeVarId)
    (hAssignmentIds :
      ([payloadId, sequenceId, bodyId, resultId]).Nodup)
    (hTraceFresh :
      traceId ∉ [payloadId, sequenceId, bodyId, resultId])
    (hIndexFresh :
      indexId ∉ [payloadId, sequenceId, bodyId, resultId])
    (hIds : traceId ≠ indexId)
    (hReservedFresh :
      ReservedIdsFresh [310, 311, 320, 321, 322]
        [x#payloadId, x#sequenceId, x#bodyId, x#resultId])
    (hCertificate :
      certificate = godel_pair_value 10 payload)
    (hPayload :
      payload = nat_sequence_code_value [leftId, rightId, bodyCode])
    (hBody :
      fs_formula_token_code_decode bodyCode = some body)
    (hNoQuantifier :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ quantifier_occurs_condition
          (var_codeₘ(numₘ(2 * leftId)))
          (fs_zfc_formula_code_term body)))
    (hSubstitutable :
      Derives fs_zfc_support_raw_theory [] (
        substitutableₘ(
          var_codeₘ(numₘ(2 * leftId)),
          var_codeₘ(numₘ(2 * rightId)),
          fs_zfc_formula_code_term body)))
    (hSubstitution :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          (fs_zfc_formula_code_term body)
          (var_codeₘ(numₘ(2 * leftId)))
          (var_codeₘ(numₘ(2 * rightId)))
          resultCode))
    (hFormulaCode :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          imp_codeₘ(
            eq_codeₘ(
              var_codeₘ(numₘ(2 * leftId)),
              var_codeₘ(numₘ(2 * rightId))),
            imp_codeₘ(fs_zfc_formula_code_term body, resultCode))))
    (hResultBoundary :
      GodelQuotation.Numbered.CodeBoundary resultCode)
    (hFormulaBoundary :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hCertificateBoundary :
      GodelQuotation.Numbered.CodeBoundary certificateTerm)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate))) :
    Derives fs_zfc_support_raw_theory [] (
      logical_equality_substitution_certificate_condition_with_ids
        formulaCode certificateTerm
        payloadId sequenceId bodyId resultId traceId indexId) := by
  have hBodyAdmissible :
      Formula.Admissible body :=
    fs_formula_token_code_decode_admissible hBody
  have hCertificateField :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ
          godel_pairₘ(⟨numₘ(10), numₘ(payload)⟩ₘ)) :=
    Metatheory.Derives.equality_trans hCertificateCode
      (fs_zfc_support_raw_logical_certificate_pair_eq hCertificate)
  have hPayloadValue :
      nat_sequence_code_value [leftId, rightId, bodyCode] = payload :=
    hPayload.symm
  have hSequenceField :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (standard_token_sequence [leftId, rightId, bodyCode])
          (numₘ(payload)) traceId indexId) := by
    simpa [hPayloadValue] using
      fs_zfc_support_raw_nat_sequence_code_condition_with_ids
        [leftId, rightId, bodyCode] traceId indexId hIds
  have hDomainField :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(standard_token_sequence [leftId, rightId, bodyCode]) ≐ₘ
          numₘ(3)) := by
    simpa using
      fs_zfc_support_raw_standard_token_sequence_domain
        [leftId, rightId, bodyCode]
  have hBodyField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term body)
          (standard_token_sequence [leftId, rightId, bodyCode] ·ₘ
            numₘ(2)) traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode_at
      traceId indexId hIds (by simp) hBody
  have hFormulaAndSubstitution :
      Derives fs_zfc_support_raw_theory [] (
          formulaCode ≐ₘ
            imp_codeₘ(
              eq_codeₘ(
                var_codeₘ(numₘ(2) *ₘ
                  (standard_token_sequence
                    [leftId, rightId, bodyCode] ·ₘ numₘ(0))),
                var_codeₘ(numₘ(2) *ₘ
                  (standard_token_sequence
                    [leftId, rightId, bodyCode] ·ₘ numₘ(1)))),
              imp_codeₘ(fs_zfc_formula_code_term body, resultCode))) ∧
        Derives fs_zfc_support_raw_theory [] (
          code_substitution_spec
            (fs_zfc_formula_code_term body)
            (var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(0))))
            (var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(1))))
            resultCode) ∧
        Derives fs_zfc_support_raw_theory [] (
          var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(0))) ≐ₘ
            var_codeₘ(numₘ(2 * leftId))) ∧
        Derives fs_zfc_support_raw_theory [] (
          var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(1))) ≐ₘ
            var_codeₘ(numₘ(2 * rightId))) := by
    have hLeftApplication :
        Derives fs_zfc_support_raw_theory [] (
          standard_token_sequence [leftId, rightId, bodyCode] ·ₘ numₘ(0) ≐ₘ
            numₘ(leftId)) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_apply_getElem? [leftId, rightId, bodyCode]
          (by simp))
    have hRightApplication :
        Derives fs_zfc_support_raw_theory [] (
          standard_token_sequence [leftId, rightId, bodyCode] ·ₘ numₘ(1) ≐ₘ
            numₘ(rightId)) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_apply_getElem? [leftId, rightId, bodyCode]
          (by simp))
    have hLeftVariableBase :
        Derives fs_zfc_support_raw_theory [] (
          var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(0))) ≐ₘ
            var_codeₘ(numₘ(2) *ₘ numₘ(leftId))) :=
      Metatheory.Derives.unary_term_constructor_congr_of_equality
        (fun term => var_codeₘ(numₘ(2) *ₘ term))
        (fun term hTerm =>
          variable_code_term_admissible
            (numₘ(2) *ₘ term)
            (natural_multiplication_term_admissible
              (numₘ(2)) term
              (finite_numeral_term_admissible 2) hTerm))
        (by intros; simp [Term.substituteFree, finite_numeral_term])
        (standard_token_sequence [leftId, rightId, bodyCode] ·ₘ numₘ(0))
        (numₘ(leftId))
        (fs_zfc_standard_token_sequence_apply_code_boundary
          [leftId, rightId, bodyCode] 0).1
        (finite_numeral_term_admissible leftId)
        hLeftApplication
    have hLeftVariable :
        Derives fs_zfc_support_raw_theory [] (
          var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(0))) ≐ₘ
            var_codeₘ(numₘ(2 * leftId))) :=
      Metatheory.Derives.equality_trans
        hLeftVariableBase
        (Metatheory.Derives.equality_symm
          (fs_zfc_support_raw_variable_code_term_numeral_mul leftId))
    have hRightVariableBase :
        Derives fs_zfc_support_raw_theory [] (
          var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(1))) ≐ₘ
            var_codeₘ(numₘ(2) *ₘ numₘ(rightId))) :=
      Metatheory.Derives.unary_term_constructor_congr_of_equality
        (fun term => var_codeₘ(numₘ(2) *ₘ term))
        (fun term hTerm =>
          variable_code_term_admissible
            (numₘ(2) *ₘ term)
            (natural_multiplication_term_admissible
              (numₘ(2)) term
              (finite_numeral_term_admissible 2) hTerm))
        (by intros; simp [Term.substituteFree, finite_numeral_term])
        (standard_token_sequence [leftId, rightId, bodyCode] ·ₘ numₘ(1))
        (numₘ(rightId))
        (fs_zfc_standard_token_sequence_apply_code_boundary
          [leftId, rightId, bodyCode] 1).1
        (finite_numeral_term_admissible rightId)
        hRightApplication
    have hRightVariable :
        Derives fs_zfc_support_raw_theory [] (
          var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(1))) ≐ₘ
            var_codeₘ(numₘ(2 * rightId))) :=
      Metatheory.Derives.equality_trans
        hRightVariableBase
        (Metatheory.Derives.equality_symm
          (fs_zfc_support_raw_variable_code_term_numeral_mul rightId))
    have hEqualityCode :
        Derives fs_zfc_support_raw_theory [] (
          eq_codeₘ(
            var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(0))),
            var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(1)))) ≐ₘ
          eq_codeₘ(
            var_codeₘ(numₘ(2 * leftId)),
            var_codeₘ(numₘ(2 * rightId)))) :=
      fs_zfc_support_raw_equality_code_term_congr_of_equalities
        (var_codeₘ(numₘ(2) *ₘ
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(0))))
        (var_codeₘ(numₘ(2 * leftId)))
        (var_codeₘ(numₘ(2) *ₘ
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(1))))
        (var_codeₘ(numₘ(2 * rightId)))
        (variable_code_term_admissible _ <|
          natural_multiplication_term_admissible
            (numₘ(2))
            (standard_token_sequence
              [leftId, rightId, bodyCode] ·ₘ numₘ(0))
            (finite_numeral_term_admissible 2)
            (function_application_term_admissible _ _
              (standard_token_sequence_admissible _)
              (finite_numeral_term_admissible 0)))
        (variable_code_term_admissible
          (numₘ(2 * leftId))
          (finite_numeral_term_admissible (2 * leftId)))
        (variable_code_term_admissible _ <|
          natural_multiplication_term_admissible
            (numₘ(2))
            (standard_token_sequence
              [leftId, rightId, bodyCode] ·ₘ numₘ(1))
            (finite_numeral_term_admissible 2)
            (function_application_term_admissible _ _
              (standard_token_sequence_admissible _)
              (finite_numeral_term_admissible 1)))
        (variable_code_term_admissible
          (numₘ(2 * rightId))
          (finite_numeral_term_admissible (2 * rightId)))
        hLeftVariable hRightVariable
    have hFormulaCode' :
        Derives fs_zfc_support_raw_theory [] (
          formulaCode ≐ₘ
            imp_codeₘ(
              eq_codeₘ(
                var_codeₘ(numₘ(2 * leftId)),
                var_codeₘ(numₘ(2 * rightId))),
              imp_codeₘ(fs_zfc_formula_code_term body, resultCode))) :=
      hFormulaCode
    have hSequenceZero :
        Term.Admissible
          (standard_token_sequence [leftId, rightId, bodyCode] ·ₘ
            numₘ(0)) SetSort.set :=
      (fs_zfc_standard_token_sequence_apply_code_boundary
        [leftId, rightId, bodyCode] 0).1
    have hSequenceOne :
        Term.Admissible
          (standard_token_sequence [leftId, rightId, bodyCode] ·ₘ
            numₘ(1)) SetSort.set :=
      (fs_zfc_standard_token_sequence_apply_code_boundary
        [leftId, rightId, bodyCode] 1).1
    have hVariableZero :
        Term.Admissible
          (var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence
              [leftId, rightId, bodyCode] ·ₘ numₘ(0))))
          SetSort.set :=
      variable_code_term_admissible _ <|
        natural_multiplication_term_admissible
          (numₘ(2))
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(0))
          (finite_numeral_term_admissible 2) hSequenceZero
    have hVariableOne :
        Term.Admissible
          (var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence
              [leftId, rightId, bodyCode] ·ₘ numₘ(1))))
          SetSort.set :=
      variable_code_term_admissible _ <|
        natural_multiplication_term_admissible
          (numₘ(2))
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(1))
          (finite_numeral_term_admissible 2) hSequenceOne
    have hInner :=
      Metatheory.Derives.binary_term_constructor_congr_of_equalities
        (fun left right => imp_codeₘ(left, right))
        (fun left right hLeft hRight =>
          implication_formula_code_term_admissible
            left right hLeft hRight)
        (by intros; simp [Term.substituteFree])
        (eq_codeₘ(
          var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence
              [leftId, rightId, bodyCode] ·ₘ numₘ(0))),
          var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence
              [leftId, rightId, bodyCode] ·ₘ numₘ(1)))))
        (eq_codeₘ(
          var_codeₘ(numₘ(2 * leftId)),
          var_codeₘ(numₘ(2 * rightId))))
        (imp_codeₘ(fs_zfc_formula_code_term body, resultCode))
        (imp_codeₘ(fs_zfc_formula_code_term body, resultCode))
        (equality_formula_code_term_admissible _ _
          hVariableZero hVariableOne)
        (equality_formula_code_term_admissible _ _
          (variable_code_term_admissible
            (numₘ(2 * leftId))
            (finite_numeral_term_admissible (2 * leftId)))
          (variable_code_term_admissible
            (numₘ(2 * rightId))
            (finite_numeral_term_admissible (2 * rightId))))
        (implication_formula_code_term_admissible _ _
          (fs_zfc_formula_code_term_admissible body)
          hResultBoundary.1)
        (implication_formula_code_term_admissible _ _
          (fs_zfc_formula_code_term_admissible body)
          hResultBoundary.1)
        hEqualityCode
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (imp_codeₘ(fs_zfc_formula_code_term body, resultCode))
          (hTermCheck :=
            Term.check_certificate_of_admissible
              (implication_formula_code_term_admissible _ _
                (fs_zfc_formula_code_term_admissible body)
                hResultBoundary.1)))
    have hSubstitutionField :
        Derives fs_zfc_support_raw_theory [] (
          code_substitution_spec
            (fs_zfc_formula_code_term body)
            (var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(0))))
            (var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(1))))
            resultCode) := by
      have hBodyBoundary :=
        fs_zfc_formula_code_term_code_boundary body
      have hLeftNumeralBoundary :
          GodelQuotation.Numbered.CodeBoundary
            (var_codeₘ(numₘ(2 * leftId))) := by
        refine ⟨variable_code_term_admissible
            (numₘ(2 * leftId))
            (finite_numeral_term_admissible (2 * leftId)), ?_⟩
        simp [Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport]
      have hRightNumeralBoundary :
          GodelQuotation.Numbered.CodeBoundary
            (var_codeₘ(numₘ(2 * rightId))) := by
        refine ⟨variable_code_term_admissible
            (numₘ(2 * rightId))
            (finite_numeral_term_admissible (2 * rightId)), ?_⟩
        simp [Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport]
      have hLeftSequenceBoundary :
          GodelQuotation.Numbered.CodeBoundary
            (var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(0)))) := by
        refine ⟨hVariableZero, ?_⟩
        simp [Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport]
      have hRightSequenceBoundary :
          GodelQuotation.Numbered.CodeBoundary
            (var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence
                [leftId, rightId, bodyCode] ·ₘ numₘ(1)))) := by
        refine ⟨hVariableOne, ?_⟩
        simp [Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport]
      have hBodyRefl :
          Derives fs_zfc_support_raw_theory [] (
            fs_zfc_formula_code_term body ≐ₘ
              fs_zfc_formula_code_term body) :=
        FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (fs_zfc_formula_code_term body)
          (hTermCheck := hBodyBoundary.check_certificate)
      have hResultRefl :
          Derives fs_zfc_support_raw_theory [] (
            resultCode ≐ₘ resultCode) :=
        FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) resultCode
          (hTermCheck := hResultBoundary.check_certificate)
      exact GodelQuotation.code_substitution_spec_congr_of_code_equalities
        (fs_zfc_formula_code_term body)
        (fs_zfc_formula_code_term body)
        (var_codeₘ(numₘ(2 * leftId)))
        (var_codeₘ(numₘ(2) *ₘ
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(0))))
        (var_codeₘ(numₘ(2 * rightId)))
        (var_codeₘ(numₘ(2) *ₘ
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(1))))
        resultCode resultCode
        hBodyBoundary hBodyBoundary
        hLeftNumeralBoundary hLeftSequenceBoundary
        hRightNumeralBoundary hRightSequenceBoundary
        hResultBoundary hResultBoundary
        hBodyRefl
        (Metatheory.Derives.equality_symm hLeftVariable)
        (Metatheory.Derives.equality_symm hRightVariable)
        hResultRefl hSubstitution
    exact ⟨
      Metatheory.Derives.equality_trans
        hFormulaCode' (Metatheory.Derives.equality_symm hInner),
      hSubstitutionField, hLeftVariable, hRightVariable⟩
  have hFormulaField := hFormulaAndSubstitution.1
  have hSubstitutionField := hFormulaAndSubstitution.2.1
  have hLeftVariable := hFormulaAndSubstitution.2.2.1
  have hRightVariable := hFormulaAndSubstitution.2.2.2
  have hBodyBoundary :=
    fs_zfc_formula_code_term_code_boundary body
  have hLeftNumeralBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (var_codeₘ(numₘ(2 * leftId))) :=
    ⟨variable_code_term_admissible _
        (finite_numeral_term_admissible _),
      by simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]⟩
  have hRightNumeralBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (var_codeₘ(numₘ(2 * rightId))) :=
    ⟨variable_code_term_admissible _
        (finite_numeral_term_admissible _),
      by simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]⟩
  have hLeftSequenceBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (var_codeₘ(numₘ(2) *ₘ
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(0)))) := by
    refine ⟨variable_code_term_admissible _ <|
        natural_multiplication_term_admissible
          (numₘ(2)) _
          (finite_numeral_term_admissible 2)
          (fs_zfc_standard_token_sequence_apply_code_boundary
            [leftId, rightId, bodyCode] 0).1, ?_⟩
    simp [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport]
  have hRightSequenceBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (var_codeₘ(numₘ(2) *ₘ
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(1)))) := by
    refine ⟨variable_code_term_admissible _ <|
        natural_multiplication_term_admissible
          (numₘ(2)) _
          (finite_numeral_term_admissible 2)
          (fs_zfc_standard_token_sequence_apply_code_boundary
            [leftId, rightId, bodyCode] 1).1, ?_⟩
    simp [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport]
  have hNoQuantifierField :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ quantifier_occurs_condition
          (var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence
              [leftId, rightId, bodyCode] ·ₘ numₘ(0))))
          (fs_zfc_formula_code_term body)) :=
    GodelQuotation.not_quantifier_occurs_congr_variable_code
      _ _ _ hLeftSequenceBoundary hLeftNumeralBoundary
      hBodyBoundary hLeftVariable hNoQuantifier
  have hSubstitutableLeft :
      Derives fs_zfc_support_raw_theory [] (
        substitutableₘ(
          var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence
              [leftId, rightId, bodyCode] ·ₘ numₘ(0))),
          var_codeₘ(numₘ(2 * rightId)),
          fs_zfc_formula_code_term body)) := by
    let transport : SetFormula :=
      substitutableₘ(x#493,
        var_codeₘ(numₘ(2 * rightId)),
        fs_zfc_formula_code_term body)
    have hTransport :=
      FirstOrder.Derives.eq_subst_m
        (sort := SetSort.set) (eigen := 493)
        (left := var_codeₘ(numₘ(2 * leftId)))
        (right := var_codeₘ(numₘ(2) *ₘ
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(0))))
        (body := transport)
        (Metatheory.Derives.equality_symm hLeftVariable)
        (by
          simpa [transport, Formula.substituteFree,
            Term.substituteFree, set_variable,
            GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
              hLeftNumeralBoundary,
            GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
              hRightNumeralBoundary,
            GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
              hBodyBoundary] using hSubstitutable)
    simpa [transport, Formula.substituteFree,
      Term.substituteFree, set_variable,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hLeftSequenceBoundary,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hRightNumeralBoundary,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hBodyBoundary] using hTransport
  have hSubstitutableField :
      Derives fs_zfc_support_raw_theory [] (
        substitutableₘ(
          var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence
              [leftId, rightId, bodyCode] ·ₘ numₘ(0))),
          var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence
              [leftId, rightId, bodyCode] ·ₘ numₘ(1))),
          fs_zfc_formula_code_term body)) := by
    let transport : SetFormula :=
      substitutableₘ(
        var_codeₘ(numₘ(2) *ₘ
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(0))),
        x#493, fs_zfc_formula_code_term body)
    have hTransport :=
      FirstOrder.Derives.eq_subst_m
        (sort := SetSort.set) (eigen := 493)
        (left := var_codeₘ(numₘ(2 * rightId)))
        (right := var_codeₘ(numₘ(2) *ₘ
          (standard_token_sequence
            [leftId, rightId, bodyCode] ·ₘ numₘ(1))))
        (body := transport)
        (Metatheory.Derives.equality_symm hRightVariable)
        (by
          simpa [transport, Formula.substituteFree,
            Term.substituteFree, set_variable,
            GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
              hLeftSequenceBoundary,
            GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
              hRightNumeralBoundary,
            GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
              hBodyBoundary] using hSubstitutableLeft)
    simpa [transport, Formula.substituteFree,
      Term.substituteFree, set_variable,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hLeftSequenceBoundary,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hRightSequenceBoundary,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hBodyBoundary] using hTransport
  let template
      (payloadTerm sequenceTerm bodyTerm resultTerm : SetTerm) :
      SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(10), payloadTerm⟩ₘ),
      nat_sequence_code_condition_with_ids
        sequenceTerm payloadTerm traceId indexId,
      domₘ(sequenceTerm) ≐ₘ numₘ(3),
      logical_formula_payload_component_condition_with_ids
        bodyTerm (sequenceTerm ·ₘ numₘ(2))
        traceId indexId,
      ¬ₘ quantifier_occurs_condition
        (var_codeₘ(numₘ(2) *ₘ
          (sequenceTerm ·ₘ numₘ(0)))) bodyTerm,
      substitutableₘ(
        var_codeₘ(numₘ(2) *ₘ
          (sequenceTerm ·ₘ numₘ(0))),
        var_codeₘ(numₘ(2) *ₘ
          (sequenceTerm ·ₘ numₘ(1))),
        bodyTerm),
      code_substitution_spec
        bodyTerm
        (var_codeₘ(numₘ(2) *ₘ
          (sequenceTerm ·ₘ numₘ(0))))
        (var_codeₘ(numₘ(2) *ₘ
          (sequenceTerm ·ₘ numₘ(1))))
        resultTerm,
      formulaCode ≐ₘ
        imp_codeₘ(
          eq_codeₘ(
            var_codeₘ(numₘ(2) *ₘ
              (sequenceTerm ·ₘ numₘ(0))),
            var_codeₘ(numₘ(2) *ₘ
              (sequenceTerm ·ₘ numₘ(1)))),
          imp_codeₘ(bodyTerm, resultTerm))]
  let bodyCondition : SetFormula :=
    template
      (x#payloadId) (x#sequenceId) (x#bodyId) (x#resultId)
  let actualBody : SetFormula :=
    template
      (numₘ(payload))
      (standard_token_sequence [leftId, rightId, bodyCode])
      (fs_zfc_formula_code_term body) resultCode
  have hActualBody :
      Derives fs_zfc_support_raw_theory [] actualBody := by
    dsimp [actualBody, template]
    apply fs_zfc_support_raw_logical_conjunction_of_list
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateField
    · exact hSequenceField
    · exact hDomainField
    · exact hBodyField
    · exact hNoQuantifierField
    · exact hSubstitutableField
    · exact hSubstitutionField
    · exact hFormulaField
  have hReservedFreshBase :
      ReservedIdsFresh [310, 311]
        [x#payloadId, x#sequenceId, x#bodyId, x#resultId] := by
    intro term hTerm reserved hReserved
    apply hReservedFresh term hTerm reserved
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hReserved ⊢
    rcases hReserved with rfl | rfl <;> simp
  have hPayloadCheck :
      Term.CheckCertificate (numₘ(payload)) SetSort.set :=
    Term.check_certificate_of_admissible
      (finite_numeral_term_admissible payload)
  have hSequenceCheck :
      Term.CheckCertificate
        (standard_token_sequence [leftId, rightId, bodyCode]) SetSort.set :=
    Term.check_certificate_of_admissible
      (standard_token_sequence_admissible
        [leftId, rightId, bodyCode])
  have hBodyCheck :
      Term.CheckCertificate
        (fs_zfc_formula_code_term body) SetSort.set :=
    Term.check_certificate_of_admissible
      (fs_zfc_formula_code_term_admissible body)
  have hResultCheck :
      Term.CheckCertificate resultCode SetSort.set := by
    exact Term.check_certificate_of_admissible hResultBoundary.1
  have hPayloadFree :
      Term.freeSupport (numₘ(payload)) = [] :=
    finite_numeral_term_freeSupport payload
  have hSequenceFree :
      Term.freeSupport
        (standard_token_sequence [leftId, rightId, bodyCode]) = [] :=
    standard_token_sequence_freeSupport_nil _
  have hBodyFree :
      Term.freeSupport (fs_zfc_formula_code_term body) = [] :=
    (fs_zfc_formula_code_term_code_boundary body).2
  have hFormulaCodeFree :
      Term.freeSupport formulaCode = [] :=
    hFormulaBoundary.2
  have hCertificateTermFree :
      Term.freeSupport certificateTerm = [] :=
    hCertificateBoundary.2
  have hResultFree :
      Term.freeSupport resultCode = [] := by
    exact hResultBoundary.2
  have hPayloadSubstitute
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (numₘ(payload)) =
        numₘ(payload) :=
    fs_zfc_support_raw_closed_term_substitute
      hPayloadFree id replacement
  have hSequenceSubstitute
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (standard_token_sequence [leftId, rightId, bodyCode]) =
        standard_token_sequence [leftId, rightId, bodyCode] :=
    fs_zfc_support_raw_closed_term_substitute
      hSequenceFree id replacement
  have hBodySubstitute
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (fs_zfc_formula_code_term body) =
        fs_zfc_formula_code_term body :=
    fs_zfc_support_raw_closed_term_substitute
      hBodyFree id replacement
  have hResultSubstitute
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement resultCode =
        resultCode :=
    fs_zfc_support_raw_closed_term_substitute
      hResultFree id replacement
  have hFormulaCodeSubstitute
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement formulaCode =
        formulaCode :=
    fs_zfc_support_raw_closed_term_substitute
      hFormulaCodeFree id replacement
  have hCertificateTermSubstitute
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement certificateTerm =
        certificateTerm :=
    fs_zfc_support_raw_closed_term_substitute
      hCertificateTermFree id replacement
  have hNumeralSubstitute
      (value : Nat) (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (numₘ(value)) =
        numₘ(value) :=
    fs_zfc_support_raw_closed_term_substitute
      (finite_numeral_term_freeSupport value) id replacement
  have hTemplateSubstitute
      (sourceId : FreeVarId)
      (replacement payloadTerm sequenceTerm bodyTerm resultTerm
        payloadResult sequenceResult bodyResult resultResult : SetTerm)
      (hSourceNeTrace : sourceId ≠ traceId)
      (hSourceNeIndex : sourceId ≠ indexId)
      (hSourceCanonicalFresh : sourceId ∉ [320, 321, 322])
      (hReplacementCheck :
        Term.CheckCertificate replacement SetSort.set)
      (hReplacementFree :
        Term.freeSupport replacement = [])
      (hSequenceTermCheck :
        Term.CheckCertificate sequenceTerm SetSort.set)
      (hBodyTermCheck :
        Term.CheckCertificate bodyTerm SetSort.set)
      (hResultTermCheck :
        Term.CheckCertificate resultTerm SetSort.set)
      (hTermsFresh :
        ReservedIdsFresh [310, 311]
          [replacement, payloadTerm, sequenceTerm, bodyTerm, resultTerm])
      (hPayloadTerm :
        Term.substituteFree SetSort.set sourceId replacement payloadTerm =
          payloadResult)
      (hSequenceTerm :
        Term.substituteFree SetSort.set sourceId replacement sequenceTerm =
          sequenceResult)
      (hBodyTerm :
        Term.substituteFree SetSort.set sourceId replacement bodyTerm =
          bodyResult)
      (hResultTerm :
        Term.substituteFree SetSort.set sourceId replacement resultTerm =
          resultResult) :
      Formula.substituteFree SetSort.set sourceId replacement
          (template payloadTerm sequenceTerm bodyTerm resultTerm) =
        template payloadResult sequenceResult bodyResult resultResult := by
    have hReplacementFresh (id : FreeVarId) :
        (SetSort.set, id) ∉ Term.freeSupport replacement := by
      rw [hReplacementFree]
      exact List.not_mem_nil
    have hSequenceCondition :=
      nat_sequence_code_condition_with_ids_substitute_closed
        sequenceTerm payloadTerm replacement
        sequenceResult payloadResult
        sourceId traceId indexId
        hSourceNeTrace hSourceNeIndex
        hReplacementCheck.admissible.2
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hSequenceTerm hPayloadTerm
    have hSequenceAt (value : Nat) :
        Term.substituteFree SetSort.set sourceId replacement
            (sequenceTerm ·ₘ numₘ(value)) =
          sequenceResult ·ₘ numₘ(value) := by
      simp [Term.substituteFree, hSequenceTerm,
        hNumeralSubstitute value sourceId replacement]
    have hBodyCondition :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        bodyTerm (sequenceTerm ·ₘ numₘ(2)) replacement
        bodyResult (sequenceResult ·ₘ numₘ(2))
        sourceId traceId indexId
        hSourceNeTrace hSourceNeIndex
        hReplacementCheck.admissible.2
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hBodyTerm (hSequenceAt 2)
    have hQuantifierCondition :=
      quantifier_occurs_condition_substituteFree
        sourceId replacement
        (var_codeₘ(numₘ(2) *ₘ
          (sequenceTerm ·ₘ numₘ(0)))) bodyTerm
        (var_codeₘ(numₘ(2) *ₘ
          (sequenceResult ·ₘ numₘ(0)))) bodyResult
        hSourceCanonicalFresh hReplacementCheck.admissible
        (fun id _ => hReplacementFresh id)
        (by
          simp [Term.substituteFree, hSequenceAt,
            hNumeralSubstitute])
        hBodyTerm
    have hSequenceAtAdmissible (value : Nat) :
        Term.Admissible
          (sequenceTerm ·ₘ numₘ(value)) SetSort.set :=
      function_application_term_admissible
        sequenceTerm (numₘ(value))
        hSequenceTermCheck.admissible
        (finite_numeral_term_admissible value)
    have hVariableAtCheck (value : Nat) :
        Term.CheckCertificate
          (var_codeₘ(numₘ(2) *ₘ
            (sequenceTerm ·ₘ numₘ(value)))) SetSort.set :=
      Term.check_certificate_of_admissible <|
        variable_code_term_admissible _ <|
          natural_multiplication_term_admissible
            (numₘ(2)) (sequenceTerm ·ₘ numₘ(value))
            (finite_numeral_term_admissible 2)
            (hSequenceAtAdmissible value)
    have hSequenceFresh
        (reserved : FreeVarId)
        (hReserved : reserved ∈ [310, 311]) :
        (SetSort.set, reserved) ∉ Term.freeSupport sequenceTerm :=
      hTermsFresh sequenceTerm (by simp) reserved hReserved
    have hSpecificationFresh :
        ReservedIdsFresh [310, 311] [
          replacement,
          bodyTerm,
          var_codeₘ(numₘ(2) *ₘ
            (sequenceTerm ·ₘ numₘ(0))),
          var_codeₘ(numₘ(2) *ₘ
            (sequenceTerm ·ₘ numₘ(1))),
          resultTerm] := by
      intro term hTerm reserved hReserved
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
      rcases hTerm with hReplacement | hBody | hBound |
        hReplacementCode | hResult
      · exact hTermsFresh term
          (by simp [hReplacement]) reserved hReserved
      · exact hTermsFresh term
          (by simp [hBody]) reserved hReserved
      · subst term
        simpa [Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport] using
          hSequenceFresh reserved hReserved
      · subst term
        simpa [Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport] using
          hSequenceFresh reserved hReserved
      · exact hTermsFresh term
          (by simp [hResult]) reserved hReserved
    have hSubstitutionCondition :=
      GodelQuotation.code_substitution_spec_substituteFree
        sourceId replacement bodyTerm
        (var_codeₘ(numₘ(2) *ₘ
          (sequenceTerm ·ₘ numₘ(0))))
        (var_codeₘ(numₘ(2) *ₘ
          (sequenceTerm ·ₘ numₘ(1))))
        resultTerm hSpecificationFresh
        (hSubstitute := hReplacementCheck)
        (hSource := hBodyTermCheck)
        (hBoundVariable := hVariableAtCheck 0)
        (hReplacement := hVariableAtCheck 1)
        (hCandidate := hResultTermCheck)
    rw [logical_certificate_conjunction_substituteFree]
    simp only [template, List.map, logical_certificate_conjunction]
    rw [hSequenceCondition, hBodyCondition, hSubstitutionCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hQuantifierCondition,
      hPayloadTerm, hSequenceTerm, hBodyTerm, hResultTerm,
      hFormulaCodeSubstitute, hCertificateTermSubstitute,
      hNumeralSubstitute]
  have hAssignmentCanonicalFresh
      (id : FreeVarId)
      (hMember : id ∈ [payloadId, sequenceId, bodyId, resultId]) :
      id ∉ [320, 321, 322] := by
    intro hCanonical
    have hTermMember :
        x#id ∈ [x#payloadId, x#sequenceId, x#bodyId, x#resultId] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hMember ⊢
      rcases hMember with rfl | rfl | rfl | rfl <;> simp
    have hFresh :=
      hReservedFresh (x#id) hTermMember id (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hCanonical ⊢
        rcases hCanonical with rfl | rfl | rfl <;> simp)
    have hSelf :
        (SetSort.set, id) ∈ Term.freeSupport (x#id) := by
      change (SetSort.set, id) ∈ [(SetSort.set, id)]
      exact List.mem_singleton_self _
    exact hFresh hSelf
  have hAssignmentNeTrace
      (id : FreeVarId)
      (hMember : id ∈ [payloadId, sequenceId, bodyId, resultId]) :
      id ≠ traceId := by
    intro hEqual
    subst id
    exact hTraceFresh hMember
  have hAssignmentNeIndex
      (id : FreeVarId)
      (hMember : id ∈ [payloadId, sequenceId, bodyId, resultId]) :
      id ≠ indexId := by
    intro hEqual
    subst id
    exact hIndexFresh hMember
  have hPayloadNeSequence : payloadId ≠ sequenceId := by
    intro hEqual
    subst sequenceId
    simp at hAssignmentIds
  have hPayloadNeBody : payloadId ≠ bodyId := by
    intro hEqual
    subst bodyId
    simp at hAssignmentIds
  have hPayloadNeResult : payloadId ≠ resultId := by
    intro hEqual
    subst resultId
    simp at hAssignmentIds
  have hSequenceNeBody : sequenceId ≠ bodyId := by
    intro hEqual
    subst bodyId
    simp at hAssignmentIds
  have hSequenceNeResult : sequenceId ≠ resultId := by
    intro hEqual
    subst resultId
    simp at hAssignmentIds
  have hBodyNeResult : bodyId ≠ resultId := by
    intro hEqual
    subst resultId
    simp at hAssignmentIds
  have hPayloadVariableCheck :
      Term.CheckCertificate (x#payloadId) SetSort.set :=
    Term.check_certificate_of_admissible
      (set_variable_admissible payloadId)
  have hSequenceVariableCheck :
      Term.CheckCertificate (x#sequenceId) SetSort.set :=
    Term.check_certificate_of_admissible
      (set_variable_admissible sequenceId)
  have hBodyVariableCheck :
      Term.CheckCertificate (x#bodyId) SetSort.set :=
    Term.check_certificate_of_admissible
      (set_variable_admissible bodyId)
  have hResultVariableCheck :
      Term.CheckCertificate (x#resultId) SetSort.set :=
    Term.check_certificate_of_admissible
      (set_variable_admissible resultId)
  have hClosedReservedFresh
      (term : SetTerm)
      (hTermFree : Term.freeSupport term = [])
      (reserved : FreeVarId) :
      (SetSort.set, reserved) ∉ Term.freeSupport term := by
    rw [hTermFree]
    exact List.not_mem_nil
  have hPayloadStep :
      Formula.substituteFree SetSort.set payloadId (numₘ(payload))
          (template
            (x#payloadId) (x#sequenceId) (x#bodyId) (x#resultId)) =
        template
          (numₘ(payload)) (x#sequenceId) (x#bodyId) (x#resultId) := by
    refine hTemplateSubstitute
      (sourceId := payloadId)
      (replacement := numₘ(payload))
      (payloadTerm := x#payloadId)
      (sequenceTerm := x#sequenceId)
      (bodyTerm := x#bodyId)
      (resultTerm := x#resultId)
      (payloadResult := numₘ(payload))
      (sequenceResult := x#sequenceId)
      (bodyResult := x#bodyId)
      (resultResult := x#resultId)
      (hSourceNeTrace := hAssignmentNeTrace payloadId (by simp))
      (hSourceNeIndex := hAssignmentNeIndex payloadId (by simp))
      (hSourceCanonicalFresh :=
        hAssignmentCanonicalFresh payloadId (by simp))
      (hReplacementCheck := hPayloadCheck)
      (hReplacementFree := hPayloadFree)
      (hSequenceTermCheck := hSequenceVariableCheck)
      (hBodyTermCheck := hBodyVariableCheck)
      (hResultTermCheck := hResultVariableCheck)
      (hTermsFresh := ?_) ?_ ?_ ?_ ?_
    · intro term hTerm reserved hReserved
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
      rcases hTerm with rfl | rfl | rfl | rfl | rfl
      · exact hClosedReservedFresh _ hPayloadFree reserved
      · exact hReservedFreshBase (x#payloadId) (by simp) reserved hReserved
      · exact hReservedFreshBase (x#sequenceId) (by simp) reserved hReserved
      · exact hReservedFreshBase (x#bodyId) (by simp) reserved hReserved
      · exact hReservedFreshBase (x#resultId) (by simp) reserved hReserved
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeSequence]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeBody]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeResult]
  have hSequenceStep :
      Formula.substituteFree SetSort.set sequenceId
          (standard_token_sequence [leftId, rightId, bodyCode])
          (template
            (numₘ(payload)) (x#sequenceId) (x#bodyId) (x#resultId)) =
        template
          (numₘ(payload))
          (standard_token_sequence [leftId, rightId, bodyCode])
          (x#bodyId) (x#resultId) := by
    refine hTemplateSubstitute
      (sourceId := sequenceId)
      (replacement :=
        standard_token_sequence [leftId, rightId, bodyCode])
      (payloadTerm := numₘ(payload))
      (sequenceTerm := x#sequenceId)
      (bodyTerm := x#bodyId)
      (resultTerm := x#resultId)
      (payloadResult := numₘ(payload))
      (sequenceResult :=
        standard_token_sequence [leftId, rightId, bodyCode])
      (bodyResult := x#bodyId)
      (resultResult := x#resultId)
      (hSourceNeTrace := hAssignmentNeTrace sequenceId (by simp))
      (hSourceNeIndex := hAssignmentNeIndex sequenceId (by simp))
      (hSourceCanonicalFresh :=
        hAssignmentCanonicalFresh sequenceId (by simp))
      (hReplacementCheck := hSequenceCheck)
      (hReplacementFree := hSequenceFree)
      (hSequenceTermCheck := hSequenceVariableCheck)
      (hBodyTermCheck := hBodyVariableCheck)
      (hResultTermCheck := hResultVariableCheck)
      (hTermsFresh := ?_) ?_ ?_ ?_ ?_
    · intro term hTerm reserved hReserved
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
      rcases hTerm with rfl | rfl | rfl | rfl | rfl
      · exact hClosedReservedFresh _ hSequenceFree reserved
      · exact hClosedReservedFresh _ hPayloadFree reserved
      · exact hReservedFreshBase (x#sequenceId) (by simp) reserved hReserved
      · exact hReservedFreshBase (x#bodyId) (by simp) reserved hReserved
      · exact hReservedFreshBase (x#resultId) (by simp) reserved hReserved
    · exact hPayloadSubstitute sequenceId
        (standard_token_sequence [leftId, rightId, bodyCode])
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSequenceNeBody]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSequenceNeResult]
  have hBodyStep :
      Formula.substituteFree SetSort.set bodyId
          (fs_zfc_formula_code_term body)
          (template
            (numₘ(payload))
            (standard_token_sequence [leftId, rightId, bodyCode])
            (x#bodyId) (x#resultId)) =
        template
          (numₘ(payload))
          (standard_token_sequence [leftId, rightId, bodyCode])
          (fs_zfc_formula_code_term body) (x#resultId) := by
    refine hTemplateSubstitute
      (sourceId := bodyId)
      (replacement := fs_zfc_formula_code_term body)
      (payloadTerm := numₘ(payload))
      (sequenceTerm :=
        standard_token_sequence [leftId, rightId, bodyCode])
      (bodyTerm := x#bodyId)
      (resultTerm := x#resultId)
      (payloadResult := numₘ(payload))
      (sequenceResult :=
        standard_token_sequence [leftId, rightId, bodyCode])
      (bodyResult := fs_zfc_formula_code_term body)
      (resultResult := x#resultId)
      (hSourceNeTrace := hAssignmentNeTrace bodyId (by simp))
      (hSourceNeIndex := hAssignmentNeIndex bodyId (by simp))
      (hSourceCanonicalFresh :=
        hAssignmentCanonicalFresh bodyId (by simp))
      (hReplacementCheck := hBodyCheck)
      (hReplacementFree := hBodyFree)
      (hSequenceTermCheck := hSequenceCheck)
      (hBodyTermCheck := hBodyVariableCheck)
      (hResultTermCheck := hResultVariableCheck)
      (hTermsFresh := ?_) ?_ ?_ ?_ ?_
    · intro term hTerm reserved hReserved
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
      rcases hTerm with rfl | rfl | rfl | rfl | rfl
      · exact hClosedReservedFresh _ hBodyFree reserved
      · exact hClosedReservedFresh _ hPayloadFree reserved
      · exact hClosedReservedFresh _ hSequenceFree reserved
      · exact hReservedFreshBase (x#bodyId) (by simp) reserved hReserved
      · exact hReservedFreshBase (x#resultId) (by simp) reserved hReserved
    · exact hPayloadSubstitute bodyId
        (fs_zfc_formula_code_term body)
    · exact hSequenceSubstitute bodyId
        (fs_zfc_formula_code_term body)
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hBodyNeResult]
  have hResultStep :
      Formula.substituteFree SetSort.set resultId resultCode
          (template
            (numₘ(payload))
            (standard_token_sequence [leftId, rightId, bodyCode])
            (fs_zfc_formula_code_term body) (x#resultId)) =
        actualBody := by
    dsimp only [actualBody]
    refine hTemplateSubstitute
      (sourceId := resultId)
      (replacement := resultCode)
      (payloadTerm := numₘ(payload))
      (sequenceTerm :=
        standard_token_sequence [leftId, rightId, bodyCode])
      (bodyTerm := fs_zfc_formula_code_term body)
      (resultTerm := x#resultId)
      (payloadResult := numₘ(payload))
      (sequenceResult :=
        standard_token_sequence [leftId, rightId, bodyCode])
      (bodyResult := fs_zfc_formula_code_term body)
      (resultResult := resultCode)
      (hSourceNeTrace := hAssignmentNeTrace resultId (by simp))
      (hSourceNeIndex := hAssignmentNeIndex resultId (by simp))
      (hSourceCanonicalFresh :=
        hAssignmentCanonicalFresh resultId (by simp))
      (hReplacementCheck := hResultCheck)
      (hReplacementFree := hResultFree)
      (hSequenceTermCheck := hSequenceCheck)
      (hBodyTermCheck := hBodyCheck)
      (hResultTermCheck := hResultVariableCheck)
      (hTermsFresh := ?_) ?_ ?_ ?_ ?_
    · intro term hTerm reserved hReserved
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
      rcases hTerm with rfl | rfl | rfl | rfl | rfl
      · exact hClosedReservedFresh _ hResultFree reserved
      · exact hClosedReservedFresh _ hPayloadFree reserved
      · exact hClosedReservedFresh _ hSequenceFree reserved
      · exact hClosedReservedFresh _ hBodyFree reserved
      · exact hReservedFreshBase (x#resultId) (by simp) reserved hReserved
    · exact hPayloadSubstitute resultId resultCode
    · exact hSequenceSubstitute resultId resultCode
    · exact hBodySubstitute resultId resultCode
    · simp [Term.substituteFree, set_variable]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, numₘ(payload)),
    (sequenceId,
      standard_token_sequence [leftId, rightId, bodyCode]),
    (bodyId, fs_zfc_formula_code_term body),
    (resultId, resultCode)]
  have hAssignmentsIds :
      (assignments.map (fun assignment => assignment.1)).Nodup := by
    simpa [assignments] using hAssignmentIds
  have hAssignmentsCheck :
      ∀ assignment, assignment ∈ assignments →
        Term.CheckCertificate assignment.2 SetSort.set := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl | rfl
    · exact hPayloadCheck
    · exact hSequenceCheck
    · exact hBodyCheck
    · exact hResultCheck
  have hAssignmentsFree :
      ∀ assignment, assignment ∈ assignments →
        Term.freeSupport assignment.2 = [] := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl | rfl
    · exact hPayloadFree
    · exact hSequenceFree
    · exact hBodyFree
    · exact hResultFree
  have hPayloadSubstitution :
      Formula.substituteFreeAssignments SetSort.set
          assignments bodyCondition =
        actualBody := by
    change
      Formula.substituteFreeAssignments SetSort.set [
          (payloadId, numₘ(payload)),
          (sequenceId,
            standard_token_sequence [leftId, rightId, bodyCode]),
          (bodyId, fs_zfc_formula_code_term body),
          (resultId, resultCode)]
          (template
            (x#payloadId) (x#sequenceId) (x#bodyId) (x#resultId)) =
        actualBody
    simp only [Formula.substituteFreeAssignments]
    rw [hPayloadStep, hSequenceStep, hBodyStep, hResultStep]
  have hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFreeAssignments SetSort.set
          assignments bodyCondition) := by
    rw [hPayloadSubstitution]
    exact hActualBody
  have hNested :=
    FirstOrder.Derives.exists_intro_substituted_assignments
      (T := fs_zfc_support_raw_theory) (Γ := [])
      assignments bodyCondition hAssignmentsIds
      hAssignmentsCheck hAssignmentsFree hInstance
  simpa [logical_equality_substitution_certificate_condition_with_ids,
    assignments, bodyCondition, template,
    Formula.existsFreeAssignments] using hNested

theorem fs_zfc_support_raw_logical_equality_substitution_certificate_with_base_of_check
    {formula : SetFormula} {certificate : Nat}
    (formulaCode certificateTerm : SetTerm)
    (base : FreeVarId)
    (hBaseLower : 700 ≤ base)
    (hFormulaBoundary :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hCertificateBoundary :
      GodelQuotation.Numbered.CodeBoundary certificateTerm)
    (hFormulaCode :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ fs_zfc_formula_code_term formula))
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate)))
    (hCheck :
      fs_logical_base_axiom_canonical_check formula certificate = true)
    (hTag :
      (godel_unpair_value certificate).1 = 10) :
    Derives fs_zfc_support_raw_theory [] (
      logical_base_certificate_condition_with_base
        formulaCode certificateTerm base) := by
  have hWitness :=
    fs_logical_base_axiom_canonical_check_first_order_witness
      hCheck (by omega) (by omega)
  rw [hTag] at hWitness
  cases hWitness with
  | equality_substitution leftId rightId bodyCode body
      hPayload hBody hFormula =>
      have hBodyAdmissible :
          Formula.Admissible body :=
        fs_formula_token_code_decode_admissible hBody
      let target :=
        Formula.substituteFree SetSort.set leftId
          (Term.var (.fvar SetSort.set rightId)) body
      have hRightTerm :
          Term.Admissible
            (Term.var (.fvar SetSort.set rightId) : SetTerm)
            SetSort.set := by
        exact ⟨
          TermWellSorted.fvar
            (σ := Nonlogical.BasicSetTheory.signature)
            SetSort.set rightId,
          TermScoped.fvar
            (σ := Nonlogical.BasicSetTheory.signature)
            (ctx := (Scope.empty : Scope
              Nonlogical.BasicSetTheory.signature))
            SetSort.set rightId⟩
      have hLeftTerm :
          Term.Admissible
            (Term.var (.fvar SetSort.set leftId) : SetTerm)
            SetSort.set := by
        exact ⟨
          TermWellSorted.fvar
            (σ := Nonlogical.BasicSetTheory.signature)
            SetSort.set leftId,
          TermScoped.fvar
            (σ := Nonlogical.BasicSetTheory.signature)
            (ctx := (Scope.empty : Scope
              Nonlogical.BasicSetTheory.signature))
            SetSort.set leftId⟩
      have hTargetAdmissible :
          Formula.Admissible target := by
        simpa [target] using
          Formula.Admissible.substituteFree
            SetSort.set leftId hBodyAdmissible hRightTerm
      have hSourceQuote :
          GodelQuotation.Numbered.quote? body =
            some (fs_zfc_formula_code_term body) := by
        rcases GodelQuotation.Numbered.quote?_exists
            hBodyAdmissible with ⟨code, hCode⟩
        simp [fs_zfc_formula_code_term, hCode]
      have hNoQuantifier :
          Derives fs_zfc_support_raw_theory [] (
            ¬ₘ quantifier_occurs_condition
              (var_codeₘ(numₘ(2 * leftId)))
              (fs_zfc_formula_code_term body)) := by
        simpa [GodelQuotation.free_name] using
          FirstOrder.Derives.theory_weaken
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_quotation_occurrence hFormula)
            (GodelQuotation.quote?_not_quantifier_occurs_free_name
              leftId hBodyAdmissible hSourceQuote)
      rcases fs_zfc_support_raw_equality_substitution_axiom_code_exists
          leftId rightId hBodyAdmissible with
        ⟨_, _, _, hSubstitutable⟩
      have hSourceTokens :
          GodelQuotation.Numbered.quote_tokens? body =
            some (nat_sequence_decode bodyCode) :=
        fs_formula_token_code_decode_quote_tokens hBody
      rcases GodelQuotation.quote_term_tokens?_exists
          (term := (Term.var
            (.fvar SetSort.set rightId) : SetTerm))
          hRightTerm with
        ⟨replacementTokens, hReplacementTokens⟩
      let replacementCode : SetTerm :=
        var_codeₘ(numₘ(2 * rightId))
      have hReplacementQuote :
          GodelQuotation.Numbered.quote_term_with?
              GodelQuotation.free_name []
              (Term.var (.fvar SetSort.set rightId) : SetTerm) =
            some replacementCode := by
        simp [replacementCode,
          GodelQuotation.Numbered.quote_term_with?,
          GodelQuotation.Numbered.named_variable_code,
          GodelQuotation.free_name]
      have hTargetQuote :
          GodelQuotation.Numbered.quote? target =
            some (fs_zfc_formula_code_term target) := by
        rcases GodelQuotation.Numbered.quote?_exists
            hTargetAdmissible with ⟨code, hCode⟩
        simp [fs_zfc_formula_code_term, hCode]
      have hSubstitutionGodel :=
        GodelQuotation.quote?_substitution_result_spec_derives
          leftId hSourceTokens hSourceQuote
          hReplacementTokens hReplacementQuote hTargetQuote
      have hSubstitution :
          Derives fs_zfc_support_raw_theory [] (
            code_substitution_spec
              (fs_zfc_formula_code_term body)
              (var_codeₘ(numₘ(2 * leftId)))
              (var_codeₘ(numₘ(2 * rightId)))
              (fs_zfc_formula_code_term target)) := by
        simpa [replacementCode,
          GodelQuotation.Numbered.named_variable_code,
          GodelQuotation.free_name] using
          fs_zfc_support_raw_derives_of_godel_quotation
            hSubstitutionGodel
      have hFormulaCanonical :
          fs_zfc_formula_code_term formula =
            imp_codeₘ(
              eq_codeₘ(
                var_codeₘ(numₘ(2 * leftId)),
                var_codeₘ(numₘ(2 * rightId))),
              imp_codeₘ(
                fs_zfc_formula_code_term body,
                fs_zfc_formula_code_term target)) := by
        have hLeftQuote :
            GodelQuotation.Numbered.quote_term_with?
                GodelQuotation.free_name []
                (Term.var (.fvar SetSort.set leftId) : SetTerm) =
              some (var_codeₘ(numₘ(2 * leftId))) := by
          simp [GodelQuotation.Numbered.quote_term_with?,
            GodelQuotation.Numbered.named_variable_code,
            GodelQuotation.free_name]
        have hRightQuote :
            GodelQuotation.Numbered.quote_term_with?
                GodelQuotation.free_name []
                (Term.var (.fvar SetSort.set rightId) : SetTerm) =
              some (var_codeₘ(numₘ(2 * rightId))) := by
          exact hReplacementQuote
        have hEqualityCode :=
          fs_zfc_formula_code_term_equal_of_quote
            (Term.var (.fvar SetSort.set leftId) : SetTerm)
            (Term.var (.fvar SetSort.set rightId) : SetTerm)
            (var_codeₘ(numₘ(2 * leftId)))
            (var_codeₘ(numₘ(2 * rightId)))
            hLeftQuote hRightQuote
        have hInnerCode :=
          fs_zfc_formula_code_term_imp body target
            hBodyAdmissible hTargetAdmissible
        have hOuterAdmissible :
            Formula.Admissible
              (Formula.equal
                (Term.var
                  (.fvar SetSort.set leftId) : SetTerm)
                (Term.var
                  (.fvar SetSort.set rightId) : SetTerm)) :=
          Formula.Admissible.equal
            hLeftTerm hRightTerm
        have hRightFormulaAdmissible :
            Formula.Admissible
              (Formula.imp body target) :=
          Formula.Admissible.imp hBodyAdmissible hTargetAdmissible
        rw [hFormula]
        rw [fs_zfc_formula_code_term_imp
          _ _ hOuterAdmissible hRightFormulaAdmissible]
        rw [hEqualityCode, hInnerCode]
      have hCertificate :
          certificate =
            godel_pair_value 10
              (godel_unpair_value certificate).2 := by
        simpa [hTag] using
          (godel_unpair_value_spec certificate).symm
      have hPayload' :
          (godel_unpair_value certificate).2 =
            nat_sequence_code_value [leftId, rightId, bodyCode] := by
        simpa using hPayload
      have hBaseReserved
          (offset : Nat) :
          ∀ id, id ∈ [310, 311, 320, 321, 322] →
            base + offset ≠ id := by
        have hOffsetLower : 700 ≤ base + offset :=
          Nat.le_trans hBaseLower (Nat.le_add_right base offset)
        intro id hId
        simp at hId
        rcases hId with rfl | rfl | rfl | rfl | rfl
        · exact Nat.ne_of_gt <|
            Nat.lt_of_lt_of_le (by decide : 310 < 700) hOffsetLower
        · exact Nat.ne_of_gt <|
            Nat.lt_of_lt_of_le (by decide : 311 < 700) hOffsetLower
        · exact Nat.ne_of_gt <|
            Nat.lt_of_lt_of_le (by decide : 320 < 700) hOffsetLower
        · exact Nat.ne_of_gt <|
            Nat.lt_of_lt_of_le (by decide : 321 < 700) hOffsetLower
        · exact Nat.ne_of_gt <|
            Nat.lt_of_lt_of_le (by decide : 322 < 700) hOffsetLower
      have hReserved :
          ReservedIdsFresh [310, 311, 320, 321, 322] [
            x#(base + 58), x#(base + 59),
            x#(base + 60), x#(base + 61)] :=
        reserved_ids_fresh_cons_variable
          (base + 58) (hBaseReserved 58) <|
        reserved_ids_fresh_cons_variable
          (base + 59) (hBaseReserved 59) <|
        reserved_ids_fresh_cons_variable
          (base + 60) (hBaseReserved 60) <|
        reserved_ids_fresh_cons_variable
          (base + 61) (hBaseReserved 61) <|
        reserved_ids_fresh_nil [310, 311, 320, 321, 322]
      have hBranch :=
        fs_zfc_support_raw_logical_equality_substitution_certificate_of_decode
          (godel_unpair_value certificate).2 certificate
          leftId rightId bodyCode body
          formulaCode (fs_zfc_formula_code_term target) certificateTerm
          (base + 58) (base + 59) (base + 60) (base + 61)
          (base + 40) (base + 41)
          (by simp) (by simp) (by simp)
          (by
            exact Nat.ne_of_lt
              (Nat.add_lt_add_left (by decide : 40 < 41) base))
          hReserved
          hCertificate
          hPayload' hBody hNoQuantifier hSubstitutable hSubstitution
          (by
            apply Metatheory.Derives.equality_trans hFormulaCode
            rw [← hFormulaCanonical]
            exact FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (fs_zfc_formula_code_term formula)
              (hTermCheck := Term.check_certificate_of_admissible
                (fs_zfc_formula_code_term_code_boundary formula).1))
          (fs_zfc_formula_code_term_code_boundary target)
          hFormulaBoundary hCertificateBoundary hCertificateCode
      have hCondition :
          Formula.Admissible
            (logical_base_certificate_condition_with_base
              formulaCode certificateTerm base) :=
        logical_base_certificate_condition_with_base_admissible
          formulaCode certificateTerm base
          hFormulaBoundary.1
          hCertificateBoundary.1
      have hTail₁ := Formula.Admissible.disj_right hCondition
      have hTail₂ := Formula.Admissible.disj_right hTail₁
      have hTail₃ := Formula.Admissible.disj_right hTail₂
      have hTail₄ := Formula.Admissible.disj_right hTail₃
      have hTail₅ := Formula.Admissible.disj_right hTail₄
      have hTail₆ := Formula.Admissible.disj_right hTail₅
      have hTail₇ := Formula.Admissible.disj_right hTail₆
      have hTail₈ := Formula.Admissible.disj_right hTail₇
      have hTail₉ := Formula.Admissible.disj_right hTail₈
      have hTail₁₀ := Formula.Admissible.disj_right hTail₉
      have hReflexivityCondition :
          Formula.Admissible
            (logical_equality_reflexivity_certificate_condition_with_id
              formulaCode certificateTerm (base + 62)) := by
        simpa using
          logical_equality_reflexivity_certificate_condition_with_id_admissible
            formulaCode certificateTerm (base + 62)
            hFormulaBoundary.1
            hCertificateBoundary.1
      have hHead₀ := Formula.Admissible.disj_left hCondition
      have hHead₁ := Formula.Admissible.disj_left hTail₁
      have hHead₂ := Formula.Admissible.disj_left hTail₂
      have hHead₃ := Formula.Admissible.disj_left hTail₃
      have hHead₄ := Formula.Admissible.disj_left hTail₄
      have hHead₅ := Formula.Admissible.disj_left hTail₅
      have hHead₆ := Formula.Admissible.disj_left hTail₆
      have hHead₇ := Formula.Admissible.disj_left hTail₇
      have hHead₈ := Formula.Admissible.disj_left hTail₈
      have hHead₉ := Formula.Admissible.disj_left hTail₉
      unfold logical_base_certificate_condition_with_base
      dsimp only
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₀)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₁)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₂)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₃)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₄)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₅)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₆)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₇)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₈)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₉)
      simpa using
        FirstOrder.Derives.disjIntroLeft hBranch
          (hRightCheck :=
            Formula.check_certificate_of_admissible hReflexivityCondition)

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
