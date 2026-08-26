import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCBaseLogicalReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.CheckedSyntax
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateLineRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateSingletonInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalBaseTagMismatchRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalFirstOrderTagMismatchRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalFirstOrderFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalSpecializationFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalEqualitySubstitutionFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalPropositionalFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalVacuousForallFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateContentRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution.Base

/-!
# 逻辑基础证书失败适配器的析取聚合

本模块只负责把各个基础逻辑证书分支的对象层否定聚合成总条件否定。
它不反演 payload，不读取 replay 失败视图，也不把 trace 暴露到终局接口。
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

/-!
## 基础条件的地面运输

终端适配器先把 transcript 中恢复出的两个开放项沿对象等式运输到规范行与
地面证书码。内部 payload binder 保持不变；这里仅使用等词替换，不重新反演
任何证书字段。
-/

/--
把终端基础条件沿末公式与末证书等式运输到对应的地面基础条件。
-/
theorem
    fs_zfc_support_raw_logical_base_certificate_condition_ground_of_equalities
    {Γ : Context signature}
    (formulaCode certificate : SetTerm)
    (row : List Nat)
    (raw : Nat)
    (base formulaParameter certificateParameter : FreeVarId)
    (hFormulaParameterFresh :
      LogicalBaseCertificateSubstitutionFresh formulaParameter base)
    (hCertificateParameterFresh :
      LogicalBaseCertificateSubstitutionFresh certificateParameter base)
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set)
    (hCertificate :
      Term.Admissible certificate SetSort.set)
    (hFormulaReplacementFresh :
      LogicalBaseCertificateReplacementFresh formulaCode base)
    (hCertificateReplacementFresh :
      LogicalBaseCertificateReplacementFresh certificate base)
    (hFormulaParameterFreshCertificate :
      (SetSort.set, formulaParameter) ∉
        Term.freeSupport certificate)
    (hFormulaEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        formulaCode ≐ₘ standard_token_sequence row)
    (hCertificateEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        certificate ≐ₘ numₘ(raw))
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_base_certificate_condition_with_base
          formulaCode certificate base) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      logical_base_certificate_condition_with_base
        (standard_token_sequence row) (numₘ(raw)) base := by
  let formulaBody : SetFormula :=
    logical_base_certificate_condition_with_base
      (x#formulaParameter) certificate base
  have hFormulaBody :
      Formula.Admissible formulaBody := by
    simpa [formulaBody] using
      logical_base_certificate_condition_with_base_admissible
        (x#formulaParameter) certificate base
        (set_variable_admissible formulaParameter)
        hCertificate
  have hFormulaTransportRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (sort := SetSort.set)
      (eigen := formulaParameter)
      (left := formulaCode)
      (right := standard_token_sequence row)
      (body := formulaBody)
      hFormulaEquality
      (hBodyCheck :=
        Formula.check_admissible_complete hFormulaBody)
  have hRowReplacementFresh :
      LogicalBaseCertificateReplacementFresh
        (standard_token_sequence row) base := by
    intro id hId
    rw [standard_token_sequence_freeSupport_nil] at hId
    exact False.elim (List.not_mem_nil hId)
  have hCertificateFixed :
      Term.substituteFree SetSort.set formulaParameter
          formulaCode certificate =
        certificate :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set formulaParameter formulaCode certificate
      hFormulaParameterFreshCertificate
  have hCertificateFixedRow :
      Term.substituteFree SetSort.set formulaParameter
          (standard_token_sequence row) certificate =
        certificate :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set formulaParameter
        (standard_token_sequence row) certificate
        hFormulaParameterFreshCertificate
  have hFormulaTransport :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_base_certificate_condition_with_base
            formulaCode certificate base ↔ₘ
          logical_base_certificate_condition_with_base
            (standard_token_sequence row) certificate base := by
    simpa [formulaBody,
      logical_base_certificate_condition_with_base_substitute_fresh
        (x#formulaParameter) certificate formulaCode
        formulaCode certificate base formulaParameter
        hFormulaParameterFresh hFormulaCode
        hFormulaReplacementFresh
        (by simp [Term.substituteFree, set_variable])
        hCertificateFixed,
      logical_base_certificate_condition_with_base_substitute_fresh
        (x#formulaParameter) certificate
        (standard_token_sequence row)
        (standard_token_sequence row) certificate
        base formulaParameter
        hFormulaParameterFresh
        (standard_token_sequence_admissible row)
        hRowReplacementFresh
        (by simp [Term.substituteFree, set_variable])
        hCertificateFixedRow] using hFormulaTransportRaw
  have hFormulaGround :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_base_certificate_condition_with_base
          (standard_token_sequence row) certificate base :=
    FirstOrder.Derives.iffElimRight
      hFormulaTransport hCondition
  let certificateBody : SetFormula :=
    logical_base_certificate_condition_with_base
      (standard_token_sequence row)
      (x#certificateParameter) base
  have hCertificateBody :
      Formula.Admissible certificateBody := by
    simpa [certificateBody] using
      logical_base_certificate_condition_with_base_admissible
        (standard_token_sequence row)
        (x#certificateParameter) base
        (standard_token_sequence_admissible row)
        (set_variable_admissible certificateParameter)
  have hCertificateTransportRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (sort := SetSort.set)
      (eigen := certificateParameter)
      (left := certificate)
      (right := numₘ(raw))
      (body := certificateBody)
      hCertificateEquality
      (hBodyCheck :=
        Formula.check_admissible_complete hCertificateBody)
  have hNumeralReplacementFresh :
      LogicalBaseCertificateReplacementFresh (numₘ(raw)) base := by
    intro id hId
    rw [finite_numeral_term_freeSupport] at hId
    exact False.elim (List.not_mem_nil hId)
  have hRowFixed :
      Term.substituteFree SetSort.set certificateParameter
          certificate (standard_token_sequence row) =
        standard_token_sequence row :=
    fs_zfc_support_raw_closed_term_substitute
      (standard_token_sequence_freeSupport_nil row)
      certificateParameter certificate
  have hRowFixedNumeral :
      Term.substituteFree SetSort.set certificateParameter
          (numₘ(raw)) (standard_token_sequence row) =
        standard_token_sequence row :=
    fs_zfc_support_raw_closed_term_substitute
      (standard_token_sequence_freeSupport_nil row)
      certificateParameter (numₘ(raw))
  have hCertificateTransport :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_base_certificate_condition_with_base
            (standard_token_sequence row) certificate base ↔ₘ
          logical_base_certificate_condition_with_base
            (standard_token_sequence row) (numₘ(raw)) base := by
    simpa [certificateBody,
      logical_base_certificate_condition_with_base_substitute_fresh
        (standard_token_sequence row) (x#certificateParameter)
        certificate
        (standard_token_sequence row) certificate
        base certificateParameter
        hCertificateParameterFresh hCertificate
        hCertificateReplacementFresh
        hRowFixed
        (by simp [Term.substituteFree, set_variable]),
      logical_base_certificate_condition_with_base_substitute_fresh
        (standard_token_sequence row) (x#certificateParameter)
        (numₘ(raw))
        (standard_token_sequence row) (numₘ(raw))
        base certificateParameter
        hCertificateParameterFresh
        (finite_numeral_term_admissible raw)
        hNumeralReplacementFresh
        hRowFixedNumeral
        (by simp [Term.substituteFree, set_variable])] using
      hCertificateTransportRaw
  exact FirstOrder.Derives.iffElimRight
    hCertificateTransport hFormulaGround

/-!
## 命题分支的标签错配

实际证书标签与某个命题分支标签不同时，只打开该分支的有限 witness，并读取
证书配对字段与 payload 序列条件。payload 内容和公式构造器均不参与反演。
-/

/-- 一元命题分支的标签错配直接否定该对象分支。 -/
theorem
    fs_zfc_support_raw_logical_unary_base_certificate_neg_of_tag_mismatch
    (raw tag : Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId componentId traceId indexId : FreeVarId)
    (hConstructorAdmissible :
      ∀ component,
        Term.Admissible component SetSort.set →
          Term.Admissible (constructor component) SetSort.set)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ tag) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_unary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId componentId traceId indexId) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(1),
      logical_formula_payload_component_condition_with_ids
        (x#componentId) (x#sequenceId ·ₘ numₘ(0))
        traceId indexId,
      formulaCode ≐ₘ constructor (x#componentId)]
  let assignments : List (FreeVarId × SetTerm) :=
    [(payloadId, x#payloadId), (sequenceId, x#sequenceId),
      (componentId, x#componentId)]
  have hCondition :=
    logical_unary_base_certificate_condition_with_ids_admissible
      tag constructor formulaCode certificate
      payloadId sequenceId componentId traceId indexId
      hConstructorAdmissible hFormulaCode hCertificate
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments
      assignments body <| by
        simpa [assignments, body,
          logical_unary_base_certificate_condition_with_ids,
          Formula.existsFreeAssignments] using hCondition
  simpa [assignments, body,
    logical_unary_base_certificate_condition_with_ids,
    Formula.existsFreeAssignments] using
    fs_zfc_support_raw_logical_tagged_exists_neg
      assignments raw tag certificate (x#payloadId) body
      (set_variable_admissible payloadId) hBody hCertificateCode
      (by
        intro Γ h
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft h)
      (by
        intro Γ h
        exact
          (fs_zfc_support_raw_nat_sequence_code_condition_parts
            (x#sequenceId) (x#payloadId) traceId indexId <| by
              simpa [body, logical_certificate_conjunction] using
                FirstOrder.Derives.conjElimLeft <|
                  FirstOrder.Derives.conjElimRight h).2.1)
      hTagMismatch

/-- 二元命题分支的标签错配直接否定该对象分支。 -/
theorem
    fs_zfc_support_raw_logical_binary_base_certificate_neg_of_tag_mismatch
    (raw tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId)
    (hConstructorAdmissible :
      ∀ left right,
        Term.Admissible left SetSort.set →
        Term.Admissible right SetSort.set →
          Term.Admissible (constructor left right) SetSort.set)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ tag) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_binary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId leftId rightId traceId indexId) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(2),
      logical_formula_payload_component_condition_with_ids
        (x#leftId) (x#sequenceId ·ₘ numₘ(0)) traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#rightId) (x#sequenceId ·ₘ numₘ(1)) traceId indexId,
      formulaCode ≐ₘ constructor (x#leftId) (x#rightId)]
  let assignments : List (FreeVarId × SetTerm) :=
    [(payloadId, x#payloadId), (sequenceId, x#sequenceId),
      (leftId, x#leftId), (rightId, x#rightId)]
  have hCondition :=
    logical_binary_base_certificate_condition_with_ids_admissible
      tag constructor formulaCode certificate payloadId sequenceId
      leftId rightId traceId indexId hConstructorAdmissible
      hFormulaCode hCertificate
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments
      assignments body <| by
        simpa [assignments, body,
          logical_binary_base_certificate_condition_with_ids,
          Formula.existsFreeAssignments] using hCondition
  simpa [assignments, body,
    logical_binary_base_certificate_condition_with_ids,
    Formula.existsFreeAssignments] using
    fs_zfc_support_raw_logical_tagged_exists_neg
      assignments raw tag certificate (x#payloadId) body
      (set_variable_admissible payloadId) hBody hCertificateCode
      (by
        intro Γ h
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft h)
      (by
        intro Γ h
        exact
          (fs_zfc_support_raw_nat_sequence_code_condition_parts
            (x#sequenceId) (x#payloadId) traceId indexId <| by
              simpa [body, logical_certificate_conjunction] using
                FirstOrder.Derives.conjElimLeft <|
                  FirstOrder.Derives.conjElimRight h).2.1)
      hTagMismatch

/-- 三元命题分支的标签错配直接否定该对象分支。 -/
theorem
    fs_zfc_support_raw_logical_ternary_base_certificate_neg_of_tag_mismatch
    (raw tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId firstId secondId thirdId traceId indexId :
      FreeVarId)
    (hConstructorAdmissible :
      ∀ first second third,
        Term.Admissible first SetSort.set →
        Term.Admissible second SetSort.set →
        Term.Admissible third SetSort.set →
          Term.Admissible (constructor first second third) SetSort.set)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ tag) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_ternary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId firstId secondId thirdId traceId indexId) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(3),
      logical_formula_payload_component_condition_with_ids
        (x#firstId) (x#sequenceId ·ₘ numₘ(0)) traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#secondId) (x#sequenceId ·ₘ numₘ(1)) traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#thirdId) (x#sequenceId ·ₘ numₘ(2)) traceId indexId,
      formulaCode ≐ₘ constructor (x#firstId) (x#secondId) (x#thirdId)]
  let assignments : List (FreeVarId × SetTerm) :=
    [(payloadId, x#payloadId), (sequenceId, x#sequenceId),
      (firstId, x#firstId), (secondId, x#secondId),
      (thirdId, x#thirdId)]
  have hCondition :=
    logical_ternary_base_certificate_condition_with_ids_admissible
      tag constructor formulaCode certificate payloadId sequenceId
      firstId secondId thirdId traceId indexId hConstructorAdmissible
      hFormulaCode hCertificate
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments
      assignments body <| by
        simpa [assignments, body,
          logical_ternary_base_certificate_condition_with_ids,
          Formula.existsFreeAssignments] using hCondition
  simpa [assignments, body,
    logical_ternary_base_certificate_condition_with_ids,
    Formula.existsFreeAssignments] using
    fs_zfc_support_raw_logical_tagged_exists_neg
      assignments raw tag certificate (x#payloadId) body
      (set_variable_admissible payloadId) hBody hCertificateCode
      (by
        intro Γ h
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft h)
      (by
        intro Γ h
        exact
          (fs_zfc_support_raw_nat_sequence_code_condition_parts
            (x#sequenceId) (x#payloadId) traceId indexId <| by
              simpa [body, logical_certificate_conjunction] using
                FirstOrder.Derives.conjElimLeft <|
                  FirstOrder.Derives.conjElimRight h).2.1)
      hTagMismatch

/--
命题分支的统一失败出口：实际标签相同时消费 checker 失败视图，否则只比较标签。
-/
theorem
    fs_zfc_support_raw_logical_propositional_branch_neg_of_check_false
    (raw tag freeBase : Nat)
    (row : List Nat)
    (formula : SetFormula)
    (formulaCode certificate : SetTerm)
    (base : FreeVarId)
    (hTagBound : tag ≤ 6)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        (fs_zfc_logical_propositional_reserved_ids_with_base base tag)
        [formulaCode, certificate])
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence row))
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hRowDecode :
      fs_named_hilbert_tokens_decode_with_env freeBase [] row =
        some formula)
    (hCheck :
      fs_logical_base_axiom_check freeBase formula raw = false) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_logical_propositional_certificate_branch_with_base
        formulaCode certificate base tag) := by
  by_cases hTag : (godel_unpair_value raw).1 = tag
  · have hActualBound : (godel_unpair_value raw).1 ≤ 6 := by
      omega
    simpa [hTag] using
      fs_zfc_support_raw_logical_propositional_branch_neg_of_failure
        raw freeBase row formula formulaCode certificate base
        hFormulaCode hCertificate
        (by simpa [hTag] using hReservedFresh)
        hFormulaToRow hCertificateCode
        hRowDecode hActualBound
        (fs_logical_base_axiom_check_propositional_failure
          hCheck hActualBound)
  · have hCases :
        tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨
          tag = 4 ∨ tag = 5 ∨ tag = 6 := by
      omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [fs_zfc_logical_propositional_certificate_branch_with_base] using
        fs_zfc_support_raw_logical_ternary_base_certificate_neg_of_tag_mismatch
          raw 0 implication_distribution_axiom_code_term
          formulaCode certificate
          base (base + 1) (base + 2) (base + 3) (base + 4)
          (base + 40) (base + 41)
          implication_distribution_axiom_code_term_admissible
          hFormulaCode hCertificate hCertificateCode hTag
    · simpa only [fs_zfc_logical_propositional_certificate_branch_with_base] using
        fs_zfc_support_raw_logical_unary_base_certificate_neg_of_tag_mismatch
          raw 1 self_implication_axiom_code_term
          formulaCode certificate
          (base + 5) (base + 6) (base + 7)
          (base + 40) (base + 41)
          self_implication_axiom_code_term_admissible
          hFormulaCode hCertificate hCertificateCode hTag
    · simpa only [fs_zfc_logical_propositional_certificate_branch_with_base] using
        fs_zfc_support_raw_logical_binary_base_certificate_neg_of_tag_mismatch
          raw 2 weakening_axiom_code_term formulaCode certificate
          (base + 8) (base + 9) (base + 10) (base + 11)
          (base + 40) (base + 41)
          weakening_axiom_code_term_admissible
          hFormulaCode hCertificate hCertificateCode hTag
    · simpa only [fs_zfc_logical_propositional_certificate_branch_with_base] using
        fs_zfc_support_raw_logical_binary_base_certificate_neg_of_tag_mismatch
          raw 3 contradiction_axiom_code_term formulaCode certificate
          (base + 12) (base + 13) (base + 14) (base + 15)
          (base + 40) (base + 41)
          contradiction_axiom_code_term_admissible
          hFormulaCode hCertificate hCertificateCode hTag
    · simpa only [fs_zfc_logical_propositional_certificate_branch_with_base] using
        fs_zfc_support_raw_logical_unary_base_certificate_neg_of_tag_mismatch
          raw 4 classical_axiom_code_term formulaCode certificate
          (base + 16) (base + 17) (base + 18)
          (base + 40) (base + 41)
          classical_axiom_code_term_admissible
          hFormulaCode hCertificate hCertificateCode hTag
    · simpa only [fs_zfc_logical_propositional_certificate_branch_with_base] using
        fs_zfc_support_raw_logical_binary_base_certificate_neg_of_tag_mismatch
          raw 5 explosion_axiom_code_term formulaCode certificate
          (base + 19) (base + 20) (base + 21) (base + 22)
          (base + 40) (base + 41)
          explosion_axiom_code_term_admissible
          hFormulaCode hCertificate hCertificateCode hTag
    · simpa only [fs_zfc_logical_propositional_certificate_branch_with_base] using
        fs_zfc_support_raw_logical_binary_base_certificate_neg_of_tag_mismatch
          raw 6 case_analysis_axiom_code_term formulaCode certificate
          (base + 23) (base + 24) (base + 25) (base + 26)
          (base + 40) (base + 41)
          case_analysis_axiom_code_term_admissible
          hFormulaCode hCertificate hCertificateCode hTag

/-! ## 一阶分支的标签错配 -/

/-- 无关全称分支的嵌套字段保证 payload 为自然数，故异标签时可否定该分支。 -/
theorem
    fs_zfc_support_raw_logical_vacuous_forall_certificate_neg_of_tag_mismatch
    (raw : Nat)
    (formulaCode certificate : SetTerm)
    (payloadId eigenId bodyNumericId sourceId variableId universalId
      traceId indexId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ 9) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_vacuous_forall_certificate_condition_with_ids
        formulaCode certificate payloadId eigenId bodyNumericId sourceId
        variableId universalId traceId indexId) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ godel_pairₘ(⟨numₘ(9), x#payloadId⟩ₘ),
      x#payloadId ≐ₘ
        godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ),
      x#eigenId ∈ₘ ωₘ,
      logical_formula_payload_component_condition_with_ids
        (x#sourceId) (x#bodyNumericId) traceId indexId,
      x#variableId ≐ₘ var_codeₘ(numₘ(2) *ₘ x#eigenId),
      ¬ₘ ((x#variableId) ∈ₘ varsₘ(x#sourceId)),
      canonical_forall_closure_code_condition
        (x#sourceId) (x#variableId) (x#universalId),
      formulaCode ≐ₘ imp_codeₘ(x#sourceId, x#universalId)]
  let assignments : List (FreeVarId × SetTerm) :=
    [(payloadId, x#payloadId), (eigenId, x#eigenId),
      (bodyNumericId, x#bodyNumericId), (sourceId, x#sourceId),
      (variableId, x#variableId), (universalId, x#universalId)]
  have hCondition :=
    logical_vacuous_forall_certificate_condition_with_ids_admissible
      formulaCode certificate payloadId eigenId bodyNumericId sourceId
      variableId universalId traceId indexId hFormulaCode hCertificate
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments assignments body <| by
      simpa [assignments, body,
        logical_vacuous_forall_certificate_condition_with_ids,
        Formula.existsFreeAssignments] using hCondition
  simpa [assignments, body,
    logical_vacuous_forall_certificate_condition_with_ids,
    Formula.existsFreeAssignments] using
    fs_zfc_support_raw_logical_tagged_exists_neg
      assignments raw 9 certificate (x#payloadId) body
      (set_variable_admissible payloadId) hBody hCertificateCode
      (by
        intro Γ h
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft h)
      (by
        intro Γ h
        have hPayload :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              x#payloadId ≐ₘ
                godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ) := by
          simpa [body, logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft <|
              FirstOrder.Derives.conjElimRight h
        have hEigen :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              x#eigenId ∈ₘ ωₘ := by
          simpa [body, logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft <|
              FirstOrder.Derives.conjElimRight <|
                FirstOrder.Derives.conjElimRight h
        have hComponent :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              logical_formula_payload_component_condition_with_ids
                (x#sourceId) (x#bodyNumericId) traceId indexId := by
          simpa [body, logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft <|
              FirstOrder.Derives.conjElimRight <|
                FirstOrder.Derives.conjElimRight <|
                  FirstOrder.Derives.conjElimRight h
        exact fs_zfc_support_raw_godel_pairing_mem_omega_of_equality
          (x#payloadId) (x#eigenId) (x#bodyNumericId)
          (set_variable_admissible payloadId)
          (set_variable_admissible eigenId)
          (set_variable_admissible bodyNumericId)
          hEigen
          (fs_zfc_support_raw_logical_formula_payload_numeric_mem_omega
            (x#sourceId) (x#bodyNumericId) traceId indexId hComponent)
          hPayload)
      hTagMismatch

/-- 等式替换分支的 payload 是自然数序列码，故异标签时可直接否定该分支。 -/
theorem
    fs_zfc_support_raw_logical_equality_substitution_certificate_neg_of_tag_mismatch
    (raw : Nat)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId bodyId resultId traceId indexId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ 10) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_equality_substitution_certificate_condition_with_ids
        formulaCode certificate payloadId sequenceId bodyId resultId
        traceId indexId) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ godel_pairₘ(⟨numₘ(10), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(3),
      logical_formula_payload_component_condition_with_ids
        (x#bodyId) (x#sequenceId ·ₘ numₘ(2)) traceId indexId,
      ¬ₘ quantifier_occurs_condition (var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0)))) (x#bodyId),
      substitutableₘ(var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0))), var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(1))), x#bodyId),
      code_substitution_spec
        (x#bodyId)
        (var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0))))
        (var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(1))))
        (x#resultId),
      formulaCode ≐ₘ
        imp_codeₘ(
          eq_codeₘ(
            var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0))),
            var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(1)))),
          imp_codeₘ(x#bodyId, x#resultId))]
  let assignments : List (FreeVarId × SetTerm) :=
    [(payloadId, x#payloadId), (sequenceId, x#sequenceId),
      (bodyId, x#bodyId), (resultId, x#resultId)]
  have hCondition :=
    logical_equality_substitution_certificate_condition_with_ids_admissible
      formulaCode certificate payloadId sequenceId bodyId resultId
      traceId indexId hFormulaCode hCertificate
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments assignments body <| by
      simpa [assignments, body,
        logical_equality_substitution_certificate_condition_with_ids,
        Formula.existsFreeAssignments] using hCondition
  simpa [assignments, body,
    logical_equality_substitution_certificate_condition_with_ids,
    Formula.existsFreeAssignments] using
    fs_zfc_support_raw_logical_tagged_exists_neg
      assignments raw 10 certificate (x#payloadId) body
      (set_variable_admissible payloadId) hBody hCertificateCode
      (by
        intro Γ h
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft h)
      (by
        intro Γ h
        exact
          (fs_zfc_support_raw_nat_sequence_code_condition_parts
            (x#sequenceId) (x#payloadId) traceId indexId <| by
              simpa [body, logical_certificate_conjunction] using
                FirstOrder.Derives.conjElimLeft <|
                  FirstOrder.Derives.conjElimRight h).2.1)
      hTagMismatch

/-!
## 等式自反分支的公式错配

tag 11 没有 payload decoder；checker 失败只能来自当前行公式与自反候选不同。
对象 witness 由地面配对等式唯一固定，再沿乘法与公式码构造器运输到该候选。
-/

/--
tag 11 的对象分支唯一决定一个可由具名 decoder 恢复的规范候选行。

该接口只做地面配对与公式码构造器的函数性；当前宿主行是否等于候选由上层
失败适配器判断。
-/
theorem
    fs_zfc_support_raw_logical_reflexivity_certificate_candidate
    (freeBase raw : Nat)
    (formulaCode certificate : SetTerm)
    (identifierId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hIdentifierFresh :
      (SetSort.set, identifierId) ∉
        Term.freeSupport formulaCode)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw))) :
    ∃ expectedTokens candidate,
      candidate =
          Formula.equal
            (Term.var (.fvar SetSort.set
              (godel_unpair_value raw).2))
            (Term.var (.fvar SetSort.set
              (godel_unpair_value raw).2)) ∧
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] expectedTokens =
        some candidate ∧
      Derives fs_zfc_support_raw_theory [] (
        logical_equality_reflexivity_certificate_condition_with_id
            formulaCode certificate identifierId ⟶ₘ
          formulaCode ≐ₘ
            standard_token_sequence expectedTokens) := by
  let identifier := (godel_unpair_value raw).2
  let variableTokens : List Nat :=
    [Numbered.variable_token (free_name identifier)]
  let expectedTokens :=
    Numbered.equality_tokens variableTokens variableTokens
  let candidate : SetFormula :=
    Formula.equal
      (Term.var (.fvar SetSort.set identifier))
      (Term.var (.fvar SetSort.set identifier))
  have hVariableDecode :
      fs_named_term_tokens_decode_with_env
          freeBase [] variableTokens =
        some (Term.var (.fvar SetSort.set identifier)) := by
    simpa [variableTokens, fs_named_variable_of_name,
      fs_bound_name_index, free_name] using
      fs_named_term_tokens_decode_with_env_variable
        freeBase [] (free_name identifier)
  have hExpectedDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] expectedTokens =
        some candidate := by
    simpa [expectedTokens, candidate] using
      fs_named_hilbert_tokens_decode_with_env_equality_of_term_tokens
        freeBase [] hVariableDecode hVariableDecode
  refine ⟨expectedTokens, candidate,
    (by simp [candidate, identifier]), hExpectedDecode, ?_⟩
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(11), x#identifierId⟩ₘ),
      x#identifierId ∈ₘ ωₘ,
      formulaCode ≐ₘ
        eq_codeₘ(
          var_codeₘ(numₘ(2) *ₘ x#identifierId),
          var_codeₘ(numₘ(2) *ₘ x#identifierId))]
  have hBody :
      Formula.Admissible body := by
    have hIdentifier :
        Term.Admissible (x#identifierId) SetSort.set :=
      set_variable_admissible identifierId
    have hProduct :
        Term.Admissible
          (numₘ(2) *ₘ x#identifierId) SetSort.set :=
      natural_multiplication_term_admissible
        (numₘ(2)) (x#identifierId)
        (finite_numeral_term_admissible 2) hIdentifier
    have hVariable :
        Term.Admissible
          (var_codeₘ(numₘ(2) *ₘ x#identifierId))
          SetSort.set :=
      variable_code_term_admissible
        (numₘ(2) *ₘ x#identifierId) hProduct
    dsimp [body]
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl
    · exact Formula.Admissible.equal hCertificate <|
        godel_pairing_term_admissible _ <|
          ordered_pair_term_admissible _ _
            (finite_numeral_term_admissible 11)
            hIdentifier
    · exact membership_formula_admissible
        hIdentifier omega_term_admissible
    · exact Formula.Admissible.equal hFormulaCode <|
        equality_formula_code_term_admissible _ _
          hVariable hVariable
  have hBodyImp :
      Derives fs_zfc_support_raw_theory [] (
        body ⟶ₘ
          formulaCode ≐ₘ
            standard_token_sequence expectedTokens) := by
    apply FirstOrder.Derives.impIntro
      (hAntecedentCheck :=
        Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete hBody)
    have hPair :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(11), x#identifierId⟩ₘ) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hNatural :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#identifierId ∈ₘ ωₘ := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hBodyAt
    have hFormula :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          formulaCode ≐ₘ
            eq_codeₘ(
              var_codeₘ(numₘ(2) *ₘ x#identifierId),
              var_codeₘ(numₘ(2) *ₘ x#identifierId)) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight hBodyAt
    have hRawPair :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            godel_pairₘ(⟨numₘ(11), x#identifierId⟩ₘ) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm <|
          FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp) hCertificateCode)
        hPair
    have hIdentifier :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#identifierId ≐ₘ numₘ(identifier) := by
      simpa [identifier] using
        ProofT.pair_right_unique
          ProofT.ZFC.pairing_core
          raw 11 (x#identifierId)
          (set_variable_admissible identifierId)
          hNatural hRawPair
    have hProduct :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (numₘ(2) *ₘ x#identifierId) ≐ₘ
            numₘ(2 * identifier) := by
      have hCongruence :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            (numₘ(2) *ₘ x#identifierId) ≐ₘ
              (numₘ(2) *ₘ numₘ(identifier)) :=
        Metatheory.Derives.unary_term_constructor_congr_of_equality
          (fun term => numₘ(2) *ₘ term)
          (fun term hTerm =>
            natural_multiplication_term_admissible
              (numₘ(2)) term
              (finite_numeral_term_admissible 2) hTerm)
          (by
            intros
            simp [Term.substituteFree,
              Term.substituteFree_eq_self_of_not_mem,
              finite_numeral_term_freeSupport])
          (x#identifierId) (numₘ(identifier))
          (set_variable_admissible identifierId)
          (finite_numeral_term_admissible identifier)
          hIdentifier
      exact Metatheory.Derives.equality_trans hCongruence <|
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            Metatheory.Derives.equality_symm <|
              fs_zfc_support_raw_derives_of_standard_sequence
                (standard_token_sequence_finite_numeral_multiplication
                  2 identifier)
    have hVariable :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          var_codeₘ(numₘ(2) *ₘ x#identifierId) ≐ₘ
            var_codeₘ(numₘ(2 * identifier)) :=
      Metatheory.Derives.unary_term_constructor_congr_of_equality
        (fun term => var_codeₘ(term))
        (fun term hTerm =>
          variable_code_term_admissible term hTerm)
        (by intros; simp [Term.substituteFree])
        (numₘ(2) *ₘ x#identifierId)
        (numₘ(2 * identifier))
        (natural_multiplication_term_admissible
          (numₘ(2)) (x#identifierId)
          (finite_numeral_term_admissible 2)
          (set_variable_admissible identifierId))
        (finite_numeral_term_admissible (2 * identifier))
        hProduct
    have hEqualityCode :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          eq_codeₘ(
              var_codeₘ(numₘ(2) *ₘ x#identifierId),
              var_codeₘ(numₘ(2) *ₘ x#identifierId)) ≐ₘ
            eq_codeₘ(
              var_codeₘ(numₘ(2 * identifier)),
              var_codeₘ(numₘ(2 * identifier))) :=
      Metatheory.Derives.binary_term_constructor_congr_of_equalities
        (fun left right => eq_codeₘ(left, right))
        (fun left right hLeft hRight =>
          equality_formula_code_term_admissible
            left right hLeft hRight)
        (by intros; simp [Term.substituteFree])
        _ _ _ _
        (variable_code_term_admissible _ <|
          natural_multiplication_term_admissible
            (numₘ(2)) (x#identifierId)
            (finite_numeral_term_admissible 2)
            (set_variable_admissible identifierId))
        (variable_code_term_admissible _
          (finite_numeral_term_admissible (2 * identifier)))
        (variable_code_term_admissible _ <|
          natural_multiplication_term_admissible
            (numₘ(2)) (x#identifierId)
            (finite_numeral_term_admissible 2)
            (set_variable_admissible identifierId))
        (variable_code_term_admissible _
          (finite_numeral_term_admissible (2 * identifier)))
        hVariable hVariable
    have hGroundStandard :
        Derives fs_zfc_support_raw_theory [] (
          eq_codeₘ(
              var_codeₘ(numₘ(2 * identifier)),
              var_codeₘ(numₘ(2 * identifier))) ≐ₘ
            standard_token_sequence expectedTokens) := by
      apply FirstOrder.Derives.theory_weaken
        (fun _ h =>
          fs_zfc_support_raw_contains_godel_quotation h)
      simpa [expectedTokens, variableTokens,
        Numbered.named_variable_code, free_name] using
        equality_formula_code_eq_standard_token_sequence
          variableTokens variableTokens
          (Numbered.named_variable_code (free_name identifier))
          (Numbered.named_variable_code (free_name identifier))
          (named_variable_code_is_term_code
            (free_name identifier))
          (named_variable_code_is_term_code
            (free_name identifier))
          (named_variable_code_eq_standard_token_sequence
            (free_name identifier))
          (named_variable_code_eq_standard_token_sequence
            (free_name identifier))
    exact Metatheory.Derives.equality_trans hFormula <|
      Metatheory.Derives.equality_trans hEqualityCode <|
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) hGroundStandard
  have hExistsImp :
      Derives fs_zfc_support_raw_theory [] (
        (∃ₘ[SetSort.set, identifierId], body) ⟶ₘ
          formulaCode ≐ₘ
            standard_token_sequence expectedTokens) := by
    apply FirstOrder.Derives.exists_imp_of_imp
      (T := fs_zfc_support_raw_theory)
      (Γ := ([] : Context signature))
      (sort := SetSort.set)
      (eigen := identifierId)
      (body := body)
      (conclusion :=
        formulaCode ≐ₘ
          standard_token_sequence expectedTokens)
    · intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      exact False.elim (List.not_mem_nil hFormula)
    · simpa [Formula.freeSupport, Term.freeSupportList,
        standard_token_sequence_freeSupport_nil] using
        hIdentifierFresh
    · exact hBodyImp
  simpa [logical_equality_reflexivity_certificate_condition_with_id,
    body] using hExistsImp

theorem
    fs_zfc_support_raw_logical_reflexivity_certificate_neg_of_mismatch
    (freeBase raw : Nat)
    (row : List Nat)
    (decoded : FSDecodedFormula)
    (identifierId : FreeVarId)
    (hDecode :
      fs_formula_row_decode freeBase row = some decoded)
    (hTag :
      (godel_unpair_value raw).1 = 11)
    (hCheck :
      fs_logical_base_axiom_check
        freeBase decoded.formula raw = false) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_equality_reflexivity_certificate_condition_with_id
        (standard_token_sequence row) (numₘ(raw)) identifierId) := by
  obtain ⟨expectedTokens, candidate, hCandidate,
      hExpectedDecode, hExpected⟩ :=
    fs_zfc_support_raw_logical_reflexivity_certificate_candidate
      freeBase raw
      (standard_token_sequence row) (numₘ(raw))
      identifierId
      (standard_token_sequence_admissible row)
      (finite_numeral_term_admissible raw)
      (by
        rw [standard_token_sequence_freeSupport_nil]
        exact List.not_mem_nil)
      (FirstOrder.Derives.eq_refl_m (numₘ(raw)))
  have hFormulaCheck :
      fs_formula_code_eq decoded.formula candidate = false := by
    simpa [fs_logical_base_axiom_check,
      fs_logical_base_axiom_check_with, hTag, hCandidate] using hCheck
  have hCandidateDifferent :
      candidate ≠ decoded.formula :=
    Ne.symm (fs_formula_code_eq_ne_of_false hFormulaCheck)
  have hRowNe : row ≠ expectedTokens := by
    have hNamedDecode :
        fs_named_hilbert_tokens_decode_with_env freeBase [] row =
          some decoded.formula :=
      fs_formula_row_decode_named_of_some hDecode
    intro hRows
    rw [hRows] at hNamedDecode
    exact hCandidateDifferent <|
      Option.some.inj (hExpectedDecode.symm.trans hNamedDecode)
  exact
    fs_zfc_support_raw_logical_branch_neg_of_candidate_ne
      (logical_equality_reflexivity_certificate_condition_with_id
        (standard_token_sequence row) (numₘ(raw)) identifierId)
      (standard_token_sequence row)
      row expectedTokens hExpected
      (FirstOrder.Derives.eq_refl_m
        (standard_token_sequence row))
      hRowNe

/--
等式自反分支的统一失败出口：同标签消费公式错配，异标签只读取证书首字段。
-/
theorem
    fs_zfc_support_raw_logical_reflexivity_branch_neg_of_check_false
    (freeBase raw : Nat)
    (row : List Nat)
    (decoded : FSDecodedFormula)
    (identifierId : FreeVarId)
    (hDecode :
      fs_formula_row_decode freeBase row = some decoded)
    (hCheck :
      fs_logical_base_axiom_check
        freeBase decoded.formula raw = false) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_equality_reflexivity_certificate_condition_with_id
        (standard_token_sequence row) (numₘ(raw)) identifierId) := by
  by_cases hTag : (godel_unpair_value raw).1 = 11
  · exact
      fs_zfc_support_raw_logical_reflexivity_certificate_neg_of_mismatch
        freeBase raw row decoded identifierId hDecode hTag hCheck
  · let body : SetFormula :=
      logical_certificate_conjunction [
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(11), x#identifierId⟩ₘ),
        x#identifierId ∈ₘ ωₘ,
        standard_token_sequence row ≐ₘ
          eq_codeₘ(
            var_codeₘ(numₘ(2) *ₘ x#identifierId),
            var_codeₘ(numₘ(2) *ₘ x#identifierId))]
    let assignments : List (FreeVarId × SetTerm) :=
      [(identifierId, x#identifierId)]
    have hCondition :=
      logical_equality_reflexivity_certificate_condition_with_id_admissible
        (standard_token_sequence row) (numₘ(raw)) identifierId
        (standard_token_sequence_admissible row)
        (finite_numeral_term_admissible raw)
    have hBody : Formula.Admissible body :=
      fs_zfc_admissible_body_of_exists_assignments assignments body <| by
        simpa [assignments, body,
          logical_equality_reflexivity_certificate_condition_with_id,
          Formula.existsFreeAssignments] using hCondition
    simpa [assignments, body,
      logical_equality_reflexivity_certificate_condition_with_id,
      Formula.existsFreeAssignments] using
      fs_zfc_support_raw_logical_tagged_exists_neg
        assignments raw 11 (numₘ(raw)) (x#identifierId) body
        (set_variable_admissible identifierId) hBody
        (FirstOrder.Derives.eq_refl_m (numₘ(raw)))
        (by
          intro Γ h
          simpa [body, logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft h)
        (by
          intro Γ h
          simpa [body, logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft <|
              FirstOrder.Derives.conjElimRight h)
        hTag

/-!
## 单例终端适配

该层只打开完整逻辑证书的三个 witness，并调用既有单例反演恢复末索引、
末证书值与末公式行。基础公理的具体拒绝理由由局部回调提供。
-/

/--
单例逻辑 payload 的完整条件可归约为末端基础公理条件的局部拒绝。

`hReject` 只消费对象上下文中的末公式、末证书等式和基础条件；因此 checker
失败的有限分类不会进入 transcript 反演层。
-/
theorem
    fs_zfc_support_raw_logical_certificate_condition_neg_of_singleton_terminal_reject
    (formulaCode : SetTerm)
    (certificateCode baseCode : Nat)
    (row : List Nat)
    (hFormulaCode :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence row))
    (hPayload :
      nat_sequence_decode certificateCode = [baseCode])
    (hReject :
      Derives fs_zfc_support_raw_theory [] (
        logical_base_certificate_condition_with_base
            (x#ProofT.lc_formula_trace_id ·ₘ
              x#ProofT.lc_last_index_id)
            (x#ProofT.lc_sequence_id ·ₘ
              x#ProofT.lc_last_index_id)
            ProofT.lc_base_id ⟶ₘ
          ((x#ProofT.lc_formula_trace_id ·ₘ
                x#ProofT.lc_last_index_id) ≐ₘ
              standard_token_sequence row) ⟶ₘ
          ((x#ProofT.lc_sequence_id ·ₘ
                x#ProofT.lc_last_index_id) ≐ₘ
              numₘ(baseCode)) ⟶ₘ
            Formula.falsum)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_certificate_condition_with_ids
        formulaCode
        (numₘ(certificateCode))
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id) := by
  have hCertificateCode :
      certificateCode =
        nat_sequence_code_value [baseCode] := by
    calc
      certificateCode =
          nat_sequence_code_value
            (nat_sequence_decode certificateCode) :=
        (nat_sequence_code_value_decode certificateCode).symm
      _ = nat_sequence_code_value [baseCode] := by
        rw [hPayload]
  subst certificateCode
  let body : SetFormula :=
    logical_certificate_body_with_ids
      formulaCode
      (numₘ(nat_sequence_code_value [baseCode]))
      (x#ProofT.lc_sequence_id)
      (x#ProofT.lc_formula_trace_id)
      (x#ProofT.lc_last_index_id)
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      fs_zfc_logical_certificate_body_admissible
        formulaCode
        (numₘ(nat_sequence_code_value [baseCode]))
        hFormulaCode.1
        (finite_numeral_term_admissible
          (nat_sequence_code_value [baseCode]))
  simpa [logical_certificate_condition_with_ids, body] using
    fs_zfc_support_raw_logical_exists_three_neg
      body hBodyAdmissible (by
        let thirdMatrix : SetFormula :=
          (x#ProofT.lc_last_index_id ∈ₘ
              domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body
        let thirdExists : SetFormula :=
          ∃ₘ[SetSort.set, ProofT.lc_last_index_id], thirdMatrix
        let secondMatrix : SetFormula :=
          (x#ProofT.lc_formula_trace_id ∈ₘ
              seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ thirdExists
        let secondExists : SetFormula :=
          ∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
            secondMatrix
        let firstMatrix : SetFormula :=
          (x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
            secondExists
        let condition : SetFormula :=
          ∃ₘ[SetSort.set, ProofT.lc_sequence_id],
            firstMatrix
        let Δ : Context signature :=
          thirdMatrix :: secondMatrix :: firstMatrix :: [condition]
        change Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
        have hThirdMatrixAt :
            Δ ⊢ₘ[fs_zfc_support_raw_theory] thirdMatrix :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hBodyAt :
            Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
          FirstOrder.Derives.conjElimRight hThirdMatrixAt
        have hCertificateCondition :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              nat_sequence_code_condition_with_ids
                (x#ProofT.lc_sequence_id)
                (numₘ(nat_sequence_code_value [baseCode]))
                ProofT.lc_code_trace_id
                ProofT.lc_code_index_id := by
          simpa [body, logical_certificate_body_with_ids,
            logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft hBodyAt
        have hDomainSuccessor :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              domₘ(x#ProofT.lc_sequence_id) ≐ₘ
                Sₘ(x#ProofT.lc_last_index_id) := by
          simpa [body, logical_certificate_body_with_ids,
            logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight hBodyAt)))
        have hInitialFormula :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              formulaCode ≐ₘ
                (x#ProofT.lc_formula_trace_id ·ₘ
                  numₘ(0)) := by
          simpa [body, logical_certificate_body_with_ids,
            logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight
                    (FirstOrder.Derives.conjElimRight hBodyAt))))
        have hBaseCondition :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              logical_base_certificate_condition_with_base
                (x#ProofT.lc_formula_trace_id ·ₘ
                  x#ProofT.lc_last_index_id)
                (x#ProofT.lc_sequence_id ·ₘ
                  x#ProofT.lc_last_index_id)
                ProofT.lc_base_id := by
          simpa [body, logical_certificate_body_with_ids,
            logical_certificate_conjunction,
            ProofT.lc_base_id] using
            FirstOrder.Derives.conjElimLeft
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight
                    (FirstOrder.Derives.conjElimRight
                      (FirstOrder.Derives.conjElimRight hBodyAt)))))
        have hTerminal :=
          fs_zfc_support_raw_logical_singleton_terminal_inversion
            (Γ := Δ)
            (x#ProofT.lc_sequence_id)
            (x#ProofT.lc_last_index_id)
            baseCode
            ProofT.lc_code_trace_id
            ProofT.lc_code_index_id
            (set_variable_admissible
              ProofT.lc_sequence_id)
            (set_variable_admissible
              ProofT.lc_last_index_id)
            (by native_decide)
            (by
              simp [Term.freeSupport]
              native_decide)
            (by
              simp [Term.freeSupport]
              native_decide)
            hCertificateCondition hDomainSuccessor
        have hLastIndexZero :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              x#ProofT.lc_last_index_id ≐ₘ numₘ(0) :=
          FirstOrder.Derives.conjElimLeft hTerminal
        have hCertificateTerminal :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              (x#ProofT.lc_sequence_id ·ₘ
                  x#ProofT.lc_last_index_id) ≐ₘ
                numₘ(baseCode) :=
          FirstOrder.Derives.conjElimRight hTerminal
        have hTraceTerminalZero :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              (x#ProofT.lc_formula_trace_id ·ₘ
                  x#ProofT.lc_last_index_id) ≐ₘ
                (x#ProofT.lc_formula_trace_id ·ₘ
                  numₘ(0)) :=
          function_application_term_congr_argument_of_equality
            (x#ProofT.lc_formula_trace_id)
            (x#ProofT.lc_last_index_id)
            (numₘ(0))
            (set_variable_admissible
              ProofT.lc_formula_trace_id)
            (set_variable_admissible
              ProofT.lc_last_index_id)
            (finite_numeral_term_admissible 0)
            hLastIndexZero
        have hFormulaTerminal :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              (x#ProofT.lc_formula_trace_id ·ₘ
                  x#ProofT.lc_last_index_id) ≐ₘ
                standard_token_sequence row :=
          Metatheory.Derives.equality_trans
            hTraceTerminalZero <|
            Metatheory.Derives.equality_trans
              (Metatheory.Derives.equality_symm hInitialFormula)
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Δ) (by simp)
                hFormulaToRow)
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.impElim
            (FirstOrder.Derives.impElim
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Δ) (by simp)
                hReject)
              hBaseCondition)
            hFormulaTerminal)
          hCertificateTerminal)

/-- 两个分支均被否定时，右结合析取也被否定。 -/
theorem fs_zfc_support_raw_neg_of_disj
    {left right : SetFormula}
    (hLeft :
      Derives fs_zfc_support_raw_theory [] (¬ₘ left))
    (hRight :
      Derives fs_zfc_support_raw_theory [] (¬ₘ right)) :
    Derives fs_zfc_support_raw_theory [] (¬ₘ (left ∨ₘ right)) := by
  have hLeftAdmissible : Formula.Admissible left :=
    Formula.Admissible.neg_body hLeft.admissible
  have hRightAdmissible : Formula.Admissible right :=
    Formula.Admissible.neg_body hRight.admissible
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete <|
        Formula.Admissible.disj hLeftAdmissible hRightAdmissible)
  let Γ : Context signature := [left ∨ₘ right]
  change Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
  exact FirstOrder.Derives.disjElim
    (FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete <|
        Formula.Admissible.disj hLeftAdmissible hRightAdmissible))
    (FirstOrder.Derives.negElim
      (FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete hLeftAdmissible))
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := left :: Γ) (by simp) hLeft))
    (FirstOrder.Derives.negElim
      (FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete hRightAdmissible))
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := right :: Γ) (by simp) hRight))

/-- 右结合析取链的逐分支负证书聚合。 -/
theorem fs_zfc_support_raw_neg_of_disj_chain
    (parts : List SetFormula)
    (hNeg :
      ∀ part, part ∈ parts →
        Derives fs_zfc_support_raw_theory [] (¬ₘ part)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_support_raw_disj_chain parts) := by
  induction parts with
  | nil =>
      apply FirstOrder.Derives.negIntro
        (hBodyCheck :=
          Formula.check_admissible_complete Formula.Admissible.falsum)
      exact FirstOrder.Derives.assumption
        (by simp)
        (Formula.check_admissible_complete Formula.Admissible.falsum)
  | cons head tail ih =>
      cases tail with
      | nil =>
          simpa [fs_zfc_support_raw_disj_chain] using
            hNeg head (by simp)
      | cons second rest =>
          have hHead :
              Derives fs_zfc_support_raw_theory [] (¬ₘ head) :=
            hNeg head (by simp)
          have hTail :
              ∀ part, part ∈ second :: rest →
                Derives fs_zfc_support_raw_theory [] (¬ₘ part) := by
            intro part hPart
            exact hNeg part (by simp [hPart])
          have hTailNeg :
              Derives fs_zfc_support_raw_theory [] (
                ¬ₘ fs_zfc_support_raw_disj_chain (second :: rest)) :=
            ih hTail
          simpa [fs_zfc_support_raw_disj_chain] using
            fs_zfc_support_raw_neg_of_disj hHead hTailNeg

/-- 十二类对象基础逻辑证书分支，顺序与编码定义严格一致。 -/
private def fs_zfc_logical_base_certificate_branches
    (formulaCode certificate : SetTerm)
    (base : FreeVarId) : List SetFormula :=
  [ fs_zfc_logical_propositional_certificate_branch_with_base
      formulaCode certificate base 0,
    fs_zfc_logical_propositional_certificate_branch_with_base
      formulaCode certificate base 1,
    fs_zfc_logical_propositional_certificate_branch_with_base
      formulaCode certificate base 2,
    fs_zfc_logical_propositional_certificate_branch_with_base
      formulaCode certificate base 3,
    fs_zfc_logical_propositional_certificate_branch_with_base
      formulaCode certificate base 4,
    fs_zfc_logical_propositional_certificate_branch_with_base
      formulaCode certificate base 5,
    fs_zfc_logical_propositional_certificate_branch_with_base
      formulaCode certificate base 6,
    logical_specialization_certificate_condition_with_ids
      formulaCode certificate
      (base + 27) (base + 28) (base + 29) (base + 30)
      (base + 31) (base + 32) (base + 33) (base + 34)
      (base + 35) (base + 36) (base + 40) (base + 41),
    logical_forall_distribution_certificate_condition_with_ids
      formulaCode certificate
      (base + 42) (base + 43) (base + 44) (base + 45)
      (base + 46) (base + 47) (base + 48) (base + 49)
      (base + 50) (base + 51) (base + 40) (base + 41),
    logical_vacuous_forall_certificate_condition_with_ids
      formulaCode certificate
      (base + 52) (base + 53) (base + 54) (base + 55)
      (base + 56) (base + 57) (base + 40) (base + 41),
    logical_equality_substitution_certificate_condition_with_ids
      formulaCode certificate
      (base + 58) (base + 59) (base + 60) (base + 61)
      (base + 40) (base + 41),
    logical_equality_reflexivity_certificate_condition_with_id
      formulaCode certificate (base + 62) ]

/-- 十二类基础逻辑证书分支否定的终局适配接口。 -/
theorem fs_zfc_support_raw_logical_base_certificate_condition_neg_of_branch_negs
    (formulaCode certificate : SetTerm)
    (base : FreeVarId)
    (hNeg :
      ∀ branch,
        branch ∈
          fs_zfc_logical_base_certificate_branches
            formulaCode certificate base →
        Derives fs_zfc_support_raw_theory [] (¬ₘ branch)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_base_certificate_condition_with_base
        formulaCode certificate base) := by
  simpa [logical_base_certificate_condition_with_base,
    fs_zfc_logical_base_certificate_branches,
    fs_zfc_support_raw_disj_chain] using
    fs_zfc_support_raw_neg_of_disj_chain
      (fs_zfc_logical_base_certificate_branches
        formulaCode certificate base)
      (by
        intro branch hBranch
        exact hNeg branch hBranch)

/-!
## `.base` 失败适配器接口

该接口固定终局所需的唯一失败出口。它只消费当前规范行、当前逻辑证书码、
成功的宿主行解码和 `fs_logical_base_axiom_check = false`；内部如何把
payload 失败或公式错配转成对象层否定，留在本适配器中完成。

各基础分支只在本层消费宿主检查结果；接口本身不引入新的反演数据，也不把
replay trace 提升到终局。
-/

/--
标准公式行上的基础逻辑 checker 失败，直接否定相应地面对象条件。

该接口只保留 tail 递归末端实际需要的最弱数据，不包含完整 logical transcript。
-/
theorem fs_zfc_support_raw_logical_base_ground_neg_of_check_false
    (baseCode freeBase : Nat)
    (row : List Nat)
    (decoded : FSDecodedFormula)
    (hBaseBound : baseCode < freeBase)
    (hDecode :
      fs_formula_row_decode freeBase row = some decoded)
    (hCheck :
      fs_logical_base_axiom_check
        freeBase decoded.formula baseCode = false) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_base_certificate_condition_with_base
        (standard_token_sequence row) (numₘ(baseCode))
        ProofT.lc_base_id) := by
  have hNamedDecode :
      fs_named_hilbert_tokens_decode_with_env freeBase [] row =
        some decoded.formula :=
    fs_formula_row_decode_named_of_some hDecode
  have hGroundFresh (tag : Nat) :
      ReservedIdsFresh
        (fs_zfc_logical_propositional_reserved_ids_with_base
          ProofT.lc_base_id tag)
        [standard_token_sequence row, numₘ(baseCode)] := by
    intro term hTerm id _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl
    · rw [standard_token_sequence_freeSupport_nil]
      exact List.not_mem_nil
    · rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil
  have hPropositional (tag : Nat) (hTagBound : tag ≤ 6) :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ fs_zfc_logical_propositional_certificate_branch_with_base
          (standard_token_sequence row) (numₘ(baseCode))
          ProofT.lc_base_id tag) :=
    fs_zfc_support_raw_logical_propositional_branch_neg_of_check_false
      baseCode tag freeBase row decoded.formula
      (standard_token_sequence row) (numₘ(baseCode))
      ProofT.lc_base_id hTagBound
      (standard_token_sequence_admissible row)
      (finite_numeral_term_admissible baseCode)
      (hGroundFresh tag)
      (FirstOrder.Derives.eq_refl_m (standard_token_sequence row))
      (FirstOrder.Derives.eq_refl_m (numₘ(baseCode)))
      hNamedDecode hCheck
  apply
    fs_zfc_support_raw_logical_base_certificate_condition_neg_of_branch_negs
  intro branch hBranch
  simp only [fs_zfc_logical_base_certificate_branches,
    List.mem_cons, List.not_mem_nil, or_false] at hBranch
  rcases hBranch with
    rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact hPropositional 0 (by decide)
  · exact hPropositional 1 (by decide)
  · exact hPropositional 2 (by decide)
  · exact hPropositional 3 (by decide)
  · exact hPropositional 4 (by decide)
  · exact hPropositional 5 (by decide)
  · exact hPropositional 6 (by decide)
  · by_cases hTag : (godel_unpair_value baseCode).1 = 7
    · exact
        fs_zfc_support_raw_logical_specialization_neg_of_check_false
          baseCode freeBase row decoded ProofT.lc_base_id
          (by native_decide) hBaseBound hTag hDecode hCheck
    · exact
        fs_zfc_support_raw_logical_specialization_certificate_neg_of_tag_mismatch
          baseCode (standard_token_sequence row) (numₘ(baseCode))
          (ProofT.lc_base_id + 27)
          (ProofT.lc_base_id + 28)
          (ProofT.lc_base_id + 29)
          (ProofT.lc_base_id + 30)
          (ProofT.lc_base_id + 31)
          (ProofT.lc_base_id + 32)
          (ProofT.lc_base_id + 33)
          (ProofT.lc_base_id + 34)
          (ProofT.lc_base_id + 35)
          (ProofT.lc_base_id + 36)
          (ProofT.lc_base_id + 40)
          (ProofT.lc_base_id + 41)
          (standard_token_sequence_admissible row)
          (finite_numeral_term_admissible baseCode)
          (FirstOrder.Derives.eq_refl_m (numₘ(baseCode))) hTag
  · by_cases hTag : (godel_unpair_value baseCode).1 = 8
    · exact
        fs_zfc_support_raw_logical_forall_distribution_neg_of_check_false
          baseCode freeBase row decoded ProofT.lc_base_id
          (by native_decide) hBaseBound hTag hDecode hCheck
    · exact
        fs_zfc_support_raw_logical_forall_distribution_certificate_neg_of_tag_mismatch
          baseCode (standard_token_sequence row) (numₘ(baseCode))
          (ProofT.lc_base_id + 42)
          (ProofT.lc_base_id + 43)
          (ProofT.lc_base_id + 44)
          (ProofT.lc_base_id + 45)
          (ProofT.lc_base_id + 46)
          (ProofT.lc_base_id + 47)
          (ProofT.lc_base_id + 48)
          (ProofT.lc_base_id + 49)
          (ProofT.lc_base_id + 50)
          (ProofT.lc_base_id + 51)
          (ProofT.lc_base_id + 40)
          (ProofT.lc_base_id + 41)
          (standard_token_sequence_admissible row)
          (finite_numeral_term_admissible baseCode)
          (FirstOrder.Derives.eq_refl_m (numₘ(baseCode))) hTag
  · by_cases hTag : (godel_unpair_value baseCode).1 = 9
    · exact
        fs_zfc_support_raw_logical_vacuous_forall_neg_of_check_false
          baseCode freeBase row decoded
          ProofT.lc_base_id
          (by native_decide) hBaseBound hTag hDecode hCheck
    · exact
        fs_zfc_support_raw_logical_vacuous_forall_certificate_neg_of_tag_mismatch
          baseCode (standard_token_sequence row) (numₘ(baseCode))
          (ProofT.lc_base_id + 52)
          (ProofT.lc_base_id + 53)
          (ProofT.lc_base_id + 54)
          (ProofT.lc_base_id + 55)
          (ProofT.lc_base_id + 56)
          (ProofT.lc_base_id + 57)
          (ProofT.lc_base_id + 40)
          (ProofT.lc_base_id + 41)
          (standard_token_sequence_admissible row)
          (finite_numeral_term_admissible baseCode)
          (FirstOrder.Derives.eq_refl_m (numₘ(baseCode))) hTag
  · by_cases hTag : (godel_unpair_value baseCode).1 = 10
    · exact
        fs_zfc_support_raw_logical_equality_substitution_neg_of_check_false
          baseCode freeBase row decoded ProofT.lc_base_id
          (by native_decide) hBaseBound hTag hDecode hCheck
    · exact
        fs_zfc_support_raw_logical_equality_substitution_certificate_neg_of_tag_mismatch
          baseCode (standard_token_sequence row) (numₘ(baseCode))
          (ProofT.lc_base_id + 58)
          (ProofT.lc_base_id + 59)
          (ProofT.lc_base_id + 60)
          (ProofT.lc_base_id + 61)
          (ProofT.lc_base_id + 40)
          (ProofT.lc_base_id + 41)
          (standard_token_sequence_admissible row)
          (finite_numeral_term_admissible baseCode)
          (FirstOrder.Derives.eq_refl_m (numₘ(baseCode))) hTag
  · exact
      fs_zfc_support_raw_logical_reflexivity_branch_neg_of_check_false
        freeBase baseCode row decoded (ProofT.lc_base_id + 62)
        hDecode hCheck

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
