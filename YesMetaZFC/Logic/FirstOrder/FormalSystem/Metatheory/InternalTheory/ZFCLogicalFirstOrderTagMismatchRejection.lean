import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalBaseTagMismatchRejection

/-!
# 一阶逻辑证书的标签错配拒绝

本模块只处理 tags 7、8 的嵌套 Gödel 配对 payload。公式字段仅用于证明两个
数值坐标属于对象自然数，不进入 decoder 或公式构造反演。
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

private theorem fs_zfc_support_raw_logical_nested_tagged_exists_neg
    (assignments : List (FreeVarId × SetTerm))
    (raw tag : Nat)
    (certificate payload eigen left right : SetTerm)
    (body : SetFormula)
    (hPayload : Term.Admissible payload SetSort.set)
    (hEigen : Term.Admissible eigen SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hBody : Formula.Admissible body)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hCertificateField :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body →
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            certificate ≐ₘ
              godel_pairₘ(⟨numₘ(tag), payload⟩ₘ))
    (hPayloadField :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body →
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            payload ≐ₘ
              godel_pairₘ(⟨eigen,
                godel_pairₘ(⟨left, right⟩ₘ)⟩ₘ))
    (hEigenNatural :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body →
          Γ ⊢ₘ[fs_zfc_support_raw_theory] eigen ∈ₘ ωₘ)
    (hLeftNatural :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body →
          Γ ⊢ₘ[fs_zfc_support_raw_theory] left ∈ₘ ωₘ)
    (hRightNatural :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body →
          Γ ⊢ₘ[fs_zfc_support_raw_theory] right ∈ₘ ωₘ)
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ tag) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ Formula.existsFreeAssignments
        SetSort.set assignments body) := by
  exact fs_zfc_support_raw_logical_tagged_exists_neg
    assignments raw tag certificate payload body
    hPayload hBody hCertificateCode hCertificateField
    (fun h =>
      fs_zfc_support_raw_logical_nested_pair_payload_mem_omega
        payload eigen left right hPayload hEigen hLeft hRight
        (hEigenNatural h) (hLeftNatural h) (hRightNatural h)
        (hPayloadField h))
    hTagMismatch

/-- tag 7 以外的实际标签否定全称特化证书分支。 -/
theorem fs_zfc_support_raw_logical_specialization_certificate_neg_of_tag_mismatch
    (raw : Nat)
    (formulaCode certificate : SetTerm)
    (payloadId eigenId bodyNumericId carrierNumericId sourceId carrierId
      termId variableId universalId resultId traceId indexId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ 7) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_specialization_certificate_condition_with_ids
        formulaCode certificate payloadId eigenId bodyNumericId
        carrierNumericId sourceId carrierId termId variableId
        universalId resultId traceId indexId) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ godel_pairₘ(⟨numₘ(7), x#payloadId⟩ₘ),
      x#payloadId ≐ₘ
        godel_pairₘ(⟨x#eigenId,
          godel_pairₘ(⟨x#bodyNumericId, x#carrierNumericId⟩ₘ)⟩ₘ),
      x#eigenId ∈ₘ ωₘ,
      logical_formula_payload_component_condition_with_ids
        (x#sourceId) (x#bodyNumericId) traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#carrierId) (x#carrierNumericId) traceId indexId,
      term_codeₘ(x#termId),
      x#carrierId ≐ₘ eq_codeₘ(x#termId, x#termId),
      x#variableId ≐ₘ var_codeₘ(numₘ(2) *ₘ x#eigenId),
      ¬ₘ quantifier_occurs_condition (x#variableId) (x#sourceId),
      substitutableₘ(x#variableId, x#termId, x#sourceId),
      canonical_forall_closure_code_condition
        (x#sourceId) (x#variableId) (x#universalId),
      code_substitution_spec
        (x#sourceId) (x#variableId) (x#termId) (x#resultId),
      formulaCode ≐ₘ
        specialization_axiom_code_term (x#universalId) (x#resultId)]
  let assignments : List (FreeVarId × SetTerm) :=
    [(payloadId, x#payloadId), (eigenId, x#eigenId),
      (bodyNumericId, x#bodyNumericId),
      (carrierNumericId, x#carrierNumericId),
      (sourceId, x#sourceId), (carrierId, x#carrierId),
      (termId, x#termId), (variableId, x#variableId),
      (universalId, x#universalId), (resultId, x#resultId)]
  have hCondition :=
    logical_specialization_certificate_condition_with_ids_admissible
      formulaCode certificate payloadId eigenId bodyNumericId
      carrierNumericId sourceId carrierId termId variableId
      universalId resultId traceId indexId hFormulaCode hCertificate
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments assignments body <| by
      simpa [assignments, body,
        logical_specialization_certificate_condition_with_ids,
        Formula.existsFreeAssignments] using hCondition
  simpa [assignments, body,
    logical_specialization_certificate_condition_with_ids,
    Formula.existsFreeAssignments] using
    fs_zfc_support_raw_logical_nested_tagged_exists_neg
      assignments raw 7 certificate
      (x#payloadId) (x#eigenId)
      (x#bodyNumericId) (x#carrierNumericId) body
      (set_variable_admissible payloadId)
      (set_variable_admissible eigenId)
      (set_variable_admissible bodyNumericId)
      (set_variable_admissible carrierNumericId)
      hBody hCertificateCode
      (fun h => by
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft h)
      (fun h => by
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight h)
      (fun h => by
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight <|
              FirstOrder.Derives.conjElimRight h)
      (fun h =>
        fs_zfc_support_raw_logical_formula_payload_numeric_mem_omega
          (x#sourceId) (x#bodyNumericId) traceId indexId <| by
            simpa [body, logical_certificate_conjunction] using
              FirstOrder.Derives.conjElimLeft <|
                FirstOrder.Derives.conjElimRight <|
                  FirstOrder.Derives.conjElimRight <|
                    FirstOrder.Derives.conjElimRight h)
      (fun h =>
        fs_zfc_support_raw_logical_formula_payload_numeric_mem_omega
          (x#carrierId) (x#carrierNumericId) traceId indexId <| by
            simpa [body, logical_certificate_conjunction] using
              FirstOrder.Derives.conjElimLeft <|
                FirstOrder.Derives.conjElimRight <|
                  FirstOrder.Derives.conjElimRight <|
                    FirstOrder.Derives.conjElimRight <|
                      FirstOrder.Derives.conjElimRight h)
      hTagMismatch

/-- tag 8 以外的实际标签否定全称分配证书分支。 -/
theorem fs_zfc_support_raw_logical_forall_distribution_certificate_neg_of_tag_mismatch
    (raw : Nat)
    (formulaCode certificate : SetTerm)
    (payloadId eigenId leftNumericId rightNumericId leftId rightId
      variableId closedImplicationId closedLeftId closedRightId
      traceId indexId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ 8) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_forall_distribution_certificate_condition_with_ids
        formulaCode certificate payloadId eigenId leftNumericId
        rightNumericId leftId rightId variableId closedImplicationId
        closedLeftId closedRightId traceId indexId) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ godel_pairₘ(⟨numₘ(8), x#payloadId⟩ₘ),
      x#payloadId ≐ₘ
        godel_pairₘ(⟨x#eigenId,
          godel_pairₘ(⟨x#leftNumericId, x#rightNumericId⟩ₘ)⟩ₘ),
      x#eigenId ∈ₘ ωₘ,
      logical_formula_payload_component_condition_with_ids
        (x#leftId) (x#leftNumericId) traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#rightId) (x#rightNumericId) traceId indexId,
      x#variableId ≐ₘ var_codeₘ(numₘ(2) *ₘ x#eigenId),
      ¬ₘ quantifier_occurs_condition (x#variableId) (x#leftId),
      ¬ₘ quantifier_occurs_condition (x#variableId) (x#rightId),
      canonical_forall_closure_code_condition
        (imp_codeₘ(x#leftId, x#rightId))
        (x#variableId) (x#closedImplicationId),
      canonical_forall_closure_code_condition
        (x#leftId) (x#variableId) (x#closedLeftId),
      canonical_forall_closure_code_condition
        (x#rightId) (x#variableId) (x#closedRightId),
      formulaCode ≐ₘ
        imp_codeₘ(x#closedImplicationId,
          imp_codeₘ(x#closedLeftId, x#closedRightId))]
  let assignments : List (FreeVarId × SetTerm) :=
    [(payloadId, x#payloadId), (eigenId, x#eigenId),
      (leftNumericId, x#leftNumericId),
      (rightNumericId, x#rightNumericId),
      (leftId, x#leftId), (rightId, x#rightId),
      (variableId, x#variableId),
      (closedImplicationId, x#closedImplicationId),
      (closedLeftId, x#closedLeftId),
      (closedRightId, x#closedRightId)]
  have hCondition :=
    logical_forall_distribution_certificate_condition_with_ids_admissible
      formulaCode certificate payloadId eigenId leftNumericId
      rightNumericId leftId rightId variableId closedImplicationId
      closedLeftId closedRightId traceId indexId
      hFormulaCode hCertificate
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments assignments body <| by
      simpa [assignments, body,
        logical_forall_distribution_certificate_condition_with_ids,
        Formula.existsFreeAssignments] using hCondition
  simpa [assignments, body,
    logical_forall_distribution_certificate_condition_with_ids,
    Formula.existsFreeAssignments] using
    fs_zfc_support_raw_logical_nested_tagged_exists_neg
      assignments raw 8 certificate
      (x#payloadId) (x#eigenId)
      (x#leftNumericId) (x#rightNumericId) body
      (set_variable_admissible payloadId)
      (set_variable_admissible eigenId)
      (set_variable_admissible leftNumericId)
      (set_variable_admissible rightNumericId)
      hBody hCertificateCode
      (fun h => by
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft h)
      (fun h => by
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight h)
      (fun h => by
        simpa [body, logical_certificate_conjunction] using
          FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight <|
              FirstOrder.Derives.conjElimRight h)
      (fun h =>
        fs_zfc_support_raw_logical_formula_payload_numeric_mem_omega
          (x#leftId) (x#leftNumericId) traceId indexId <| by
            simpa [body, logical_certificate_conjunction] using
              FirstOrder.Derives.conjElimLeft <|
                FirstOrder.Derives.conjElimRight <|
                  FirstOrder.Derives.conjElimRight <|
                    FirstOrder.Derives.conjElimRight h)
      (fun h =>
        fs_zfc_support_raw_logical_formula_payload_numeric_mem_omega
          (x#rightId) (x#rightNumericId) traceId indexId <| by
            simpa [body, logical_certificate_conjunction] using
              FirstOrder.Derives.conjElimLeft <|
                FirstOrder.Derives.conjElimRight <|
                  FirstOrder.Derives.conjElimRight <|
                    FirstOrder.Derives.conjElimRight <|
                      FirstOrder.Derives.conjElimRight h)
      hTagMismatch

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
