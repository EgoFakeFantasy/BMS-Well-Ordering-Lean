import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Base

/-!
# 完整逻辑证书 transcript

本模块在基础公理证书之上编码有限次全称闭包与完整逻辑证书条件。
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

namespace CertifiedProof

/-! ## 完整逻辑证书 transcript -/

/-- transcript 中一个非末位置精确执行一次全称闭包。 -/
def logical_closure_certificate_step_condition
    (certificateSequence formulaTrace index : SetTerm) : SetFormula :=
  let variableCode :=
    var_codeₘ(numₘ(2) *ₘ
      (certificateSequence ·ₘ index))
  ((¬ₘ variable_symbol_occurs_condition
        variableCode (formulaTrace ·ₘ index)) ∧ₘ
      canonical_forall_closure_code_condition
        (formulaTrace ·ₘ Sₘ(index))
        variableCode
        (formulaTrace ·ₘ index)) ∧ₘ
    canonical_forall_open_code_condition
      (formulaTrace ·ₘ index)
      variableCode
      (formulaTrace ·ₘ Sₘ(index))

theorem logical_closure_certificate_step_condition_admissible
    (certificateSequence formulaTrace index : SetTerm)
    (hCertificateSequence :
      Term.Admissible certificateSequence SetSort.set)
    (hFormulaTrace : Term.Admissible formulaTrace SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (logical_closure_certificate_step_condition
        certificateSequence formulaTrace index) := by
  have hNextIndex :
      Term.Admissible (Sₘ(index)) SetSort.set :=
    successor_term_admissible index hIndex
  have hSource :
      Term.Admissible
        (formulaTrace ·ₘ Sₘ(index)) SetSort.set :=
    function_application_term_admissible
      formulaTrace (Sₘ(index)) hFormulaTrace hNextIndex
  have hCertificate :
      Term.Admissible
        (certificateSequence ·ₘ index) SetSort.set :=
    function_application_term_admissible
      certificateSequence index hCertificateSequence hIndex
  have hProduct :
      Term.Admissible
        (numₘ(2) *ₘ (certificateSequence ·ₘ index)) SetSort.set :=
    natural_multiplication_term_admissible
      (numₘ(2)) (certificateSequence ·ₘ index)
      (finite_numeral_term_admissible 2) hCertificate
  have hVariable :
      Term.Admissible
        (var_codeₘ(numₘ(2) *ₘ
          (certificateSequence ·ₘ index))) SetSort.set :=
    variable_code_term_admissible
      (numₘ(2) *ₘ (certificateSequence ·ₘ index)) hProduct
  have hTarget :
      Term.Admissible (formulaTrace ·ₘ index) SetSort.set :=
    function_application_term_admissible
      formulaTrace index hFormulaTrace hIndex
  exact Formula.Admissible.conj
    (Formula.Admissible.conj
      (Formula.Admissible.neg <|
        variable_symbol_occurs_condition_admissible
          (var_codeₘ(numₘ(2) *ₘ
            (certificateSequence ·ₘ index)))
          (formulaTrace ·ₘ index) hVariable hTarget)
      (canonical_forall_closure_code_condition_admissible
        (formulaTrace ·ₘ Sₘ(index))
        (var_codeₘ(numₘ(2) *ₘ
          (certificateSequence ·ₘ index)))
        (formulaTrace ·ₘ index)
        hSource hVariable hTarget))
    (canonical_forall_open_code_condition_admissible
      (formulaTrace ·ₘ index)
      (var_codeₘ(numₘ(2) *ₘ
        (certificateSequence ·ₘ index)))
      (formulaTrace ·ₘ Sₘ(index))
      hTarget hVariable hSource)

/--
完整逻辑证书主体中基础证书分支使用的稳定 binder 基址。

该值按三个外层 witness 变量计算，而不是按 witness 替换后的项重新计算，因此
存在量词实例化不会改变基础证书关系内部的 binder 编号。
-/
def logical_certificate_body_base_with_ids
    (certificateSequenceId formulaTraceId lastIndexId : FreeVarId) :
    FreeVarId :=
  logical_certificate_fresh_base [
    x#formulaTraceId ·ₘ x#lastIndexId,
    x#certificateSequenceId ·ₘ x#lastIndexId]

/-- 给定三个 witness 项时的完整逻辑证书七字段主体。 -/
def logical_certificate_body_with_ids
    (formulaCode certificatePayload : SetTerm)
    (certificateSequence formulaTrace lastIndex : SetTerm)
    (certificateSequenceId formulaTraceId lastIndexId lineIndexId
      codeTraceId codeIndexId : FreeVarId) : SetFormula :=
  logical_certificate_conjunction [
    nat_sequence_code_condition_with_ids
      certificateSequence certificatePayload
      codeTraceId codeIndexId,
    formulaTrace ∈ₘ seq₊_spaceₘ(FormulaCodeₘ),
    domₘ(formulaTrace) ≐ₘ domₘ(certificateSequence),
    domₘ(certificateSequence) ≐ₘ Sₘ(lastIndex),
    formulaCode ≐ₘ (formulaTrace ·ₘ numₘ(0)),
    logical_base_certificate_condition_with_base
      (formulaTrace ·ₘ lastIndex)
      (certificateSequence ·ₘ lastIndex)
      (logical_certificate_body_base_with_ids
        certificateSequenceId formulaTraceId lastIndexId),
    ∀ₘ[SetSort.set, lineIndexId],
      (x#lineIndexId ∈ₘ lastIndex) ⟶ₘ
        logical_closure_certificate_step_condition
          certificateSequence formulaTrace (x#lineIndexId)]

/--
显式 binder 编号下的完整逻辑证书条件。

`certificatePayload` 编码闭包变量序列与末端 base 证书；`formulaTrace`
从当前公式逐层打开，直到基础公理公式。
-/
def logical_certificate_condition_with_ids
    (formulaCode certificatePayload : SetTerm)
    (certificateSequenceId formulaTraceId lastIndexId lineIndexId
      codeTraceId codeIndexId : FreeVarId) : SetFormula :=
  (∃ₘ[SetSort.set, certificateSequenceId],
    (x#certificateSequenceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
      (∃ₘ[SetSort.set, formulaTraceId],
        (x#formulaTraceId ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
          (∃ₘ[SetSort.set, lastIndexId],
            (x#lastIndexId ∈ₘ domₘ(x#certificateSequenceId)) ∧ₘ
              logical_certificate_body_with_ids
                formulaCode certificatePayload
                (x#certificateSequenceId) (x#formulaTraceId) (x#lastIndexId)
                certificateSequenceId formulaTraceId lastIndexId lineIndexId
                codeTraceId codeIndexId)))

/-- 自动选择内部 binder 的完整逻辑证书条件。 -/
def logical_certificate_condition
    (formulaCode certificatePayload : SetTerm) : SetFormula :=
  let base :=
    logical_certificate_fresh_base [formulaCode, certificatePayload]
  logical_certificate_condition_with_ids
    formulaCode certificatePayload
    base (base + 1) (base + 2) (base + 3)
    (base + 4) (base + 5)

theorem logical_certificate_condition_with_ids_admissible
    (formulaCode certificatePayload : SetTerm)
    (certificateSequenceId formulaTraceId lastIndexId lineIndexId
      codeTraceId codeIndexId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificatePayload :
      Term.Admissible certificatePayload SetSort.set) :
    Formula.Admissible
      (logical_certificate_condition_with_ids
        formulaCode certificatePayload
        certificateSequenceId formulaTraceId lastIndexId lineIndexId
        codeTraceId codeIndexId) := by
  have hCertificateSequence :
      Term.Admissible (x#certificateSequenceId) SetSort.set :=
    set_variable_admissible certificateSequenceId
  have hFormulaTrace :
      Term.Admissible (x#formulaTraceId) SetSort.set :=
    set_variable_admissible formulaTraceId
  have hLastIndex :
      Term.Admissible (x#lastIndexId) SetSort.set :=
    set_variable_admissible lastIndexId
  have hLineIndex :
      Term.Admissible (x#lineIndexId) SetSort.set :=
    set_variable_admissible lineIndexId
  have hCertificateDomain :
      Term.Admissible
        (domₘ(x#certificateSequenceId)) SetSort.set :=
    domain_term_admissible
      (x#certificateSequenceId) hCertificateSequence
  have hFormulaTraceDomain :
      Term.Admissible
        (domₘ(x#formulaTraceId)) SetSort.set :=
    domain_term_admissible
      (x#formulaTraceId) hFormulaTrace
  have hLastSuccessor :
      Term.Admissible (Sₘ(x#lastIndexId)) SetSort.set :=
    successor_term_admissible (x#lastIndexId) hLastIndex
  have hFormulaTraceZero :
      Term.Admissible
        (x#formulaTraceId ·ₘ numₘ(0)) SetSort.set :=
    function_application_term_admissible
      (x#formulaTraceId) (numₘ(0)) hFormulaTrace
      (finite_numeral_term_admissible 0)
  have hFormulaTraceLast :
      Term.Admissible
        (x#formulaTraceId ·ₘ x#lastIndexId) SetSort.set :=
    function_application_term_admissible
      (x#formulaTraceId) (x#lastIndexId)
      hFormulaTrace hLastIndex
  have hCertificateLast :
      Term.Admissible
        (x#certificateSequenceId ·ₘ x#lastIndexId) SetSort.set :=
    function_application_term_admissible
      (x#certificateSequenceId) (x#lastIndexId)
      hCertificateSequence hLastIndex
  have hPayloadCode :
      Formula.Admissible
        (nat_sequence_code_condition_with_ids
          (x#certificateSequenceId) certificatePayload
          codeTraceId codeIndexId) :=
    nat_sequence_code_condition_with_ids_admissible
      (x#certificateSequenceId) certificatePayload
      codeTraceId codeIndexId
      hCertificateSequence hCertificatePayload
  have hFormulaTraceSpace :
      Formula.Admissible
        (x#formulaTraceId ∈ₘ
          seq₊_spaceₘ(FormulaCodeₘ)) :=
    membership_formula_admissible hFormulaTrace <|
      nonempty_finite_sequence_space_term_admissible
        FormulaCodeₘ formula_code_set_term_admissible
  have hEqualDomains :
      Formula.Admissible
        (domₘ(x#formulaTraceId) ≐ₘ
          domₘ(x#certificateSequenceId)) :=
    Formula.Admissible.equal
      hFormulaTraceDomain hCertificateDomain
  have hNonemptyDomain :
      Formula.Admissible
        (domₘ(x#certificateSequenceId) ≐ₘ
          Sₘ(x#lastIndexId)) :=
    Formula.Admissible.equal
      hCertificateDomain hLastSuccessor
  have hInitialFormula :
      Formula.Admissible
        (formulaCode ≐ₘ
          (x#formulaTraceId ·ₘ numₘ(0))) :=
    Formula.Admissible.equal hFormulaCode hFormulaTraceZero
  have hBaseCertificate :
      Formula.Admissible
        (logical_base_certificate_condition_with_base
          (x#formulaTraceId ·ₘ x#lastIndexId)
          (x#certificateSequenceId ·ₘ x#lastIndexId)
          (logical_certificate_body_base_with_ids
            certificateSequenceId formulaTraceId lastIndexId)) :=
    logical_base_certificate_condition_with_base_admissible
      (x#formulaTraceId ·ₘ x#lastIndexId)
      (x#certificateSequenceId ·ₘ x#lastIndexId)
      (logical_certificate_body_base_with_ids
        certificateSequenceId formulaTraceId lastIndexId)
      hFormulaTraceLast hCertificateLast
  have hLineBound :
      Formula.Admissible
        (x#lineIndexId ∈ₘ x#lastIndexId) :=
    membership_formula_admissible hLineIndex hLastIndex
  have hClosureStep :
      Formula.Admissible
        (logical_closure_certificate_step_condition
          (x#certificateSequenceId) (x#formulaTraceId)
          (x#lineIndexId)) :=
    logical_closure_certificate_step_condition_admissible
      (x#certificateSequenceId) (x#formulaTraceId)
      (x#lineIndexId)
      hCertificateSequence hFormulaTrace hLineIndex
  have hAllClosureSteps :
      Formula.Admissible
        (∀ₘ[SetSort.set, lineIndexId],
          (x#lineIndexId ∈ₘ x#lastIndexId) ⟶ₘ
            logical_closure_certificate_step_condition
              (x#certificateSequenceId) (x#formulaTraceId)
              (x#lineIndexId)) :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set lineIndexId <|
        Formula.Admissible.imp hLineBound hClosureStep
  have hCondition :
      Formula.Admissible
      (logical_certificate_body_with_ids
          formulaCode certificatePayload
          (x#certificateSequenceId) (x#formulaTraceId) (x#lastIndexId)
          certificateSequenceId formulaTraceId lastIndexId lineIndexId
          codeTraceId codeIndexId) := by
    unfold logical_certificate_body_with_ids
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hPayloadCode
    · exact hFormulaTraceSpace
    · exact hEqualDomains
    · exact hNonemptyDomain
    · exact hInitialFormula
    · exact hBaseCertificate
    · exact hAllClosureSteps
  have hCertificateSequenceSpace :
      Formula.Admissible
        (x#certificateSequenceId ∈ₘ seq_spaceₘ(ωₘ)) :=
    membership_formula_admissible hCertificateSequence <|
      finite_sequence_space_term_admissible
        ωₘ omega_term_admissible
  have hLastIndexBound :
      Formula.Admissible
        (x#lastIndexId ∈ₘ domₘ(x#certificateSequenceId)) :=
    membership_formula_admissible hLastIndex hCertificateDomain
  simpa [logical_certificate_condition_with_ids] using
    Formula.Admissible.exists_closeFreeAt
        SetSort.set certificateSequenceId <|
      Formula.Admissible.conj hCertificateSequenceSpace <|
        Formula.Admissible.exists_closeFreeAt
            SetSort.set formulaTraceId <|
          Formula.Admissible.conj hFormulaTraceSpace <|
            Formula.Admissible.exists_closeFreeAt
              SetSort.set lastIndexId <|
                Formula.Admissible.conj hLastIndexBound hCondition

theorem logical_certificate_condition_admissible
    (formulaCode certificatePayload : SetTerm)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificatePayload :
      Term.Admissible certificatePayload SetSort.set) :
    Formula.Admissible
      (logical_certificate_condition formulaCode certificatePayload) := by
  exact logical_certificate_condition_with_ids_admissible
    formulaCode certificatePayload _ _ _ _ _ _
    hFormulaCode hCertificatePayload


end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
