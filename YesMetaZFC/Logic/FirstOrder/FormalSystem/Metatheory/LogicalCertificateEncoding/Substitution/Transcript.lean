import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution.Base

/-!
# 逻辑证书 transcript 主体的闭项替换

本模块把七字段主体视为一个稳定关系：三个存在见证对应的项可以逐个替换，
而行索引、序列编码和基础证书内部的 binder 编号保持不变。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

namespace CertifiedProof

/-- 七字段主体替换恰好需要避开的内部 binder。 -/
def LogicalCertificateBodySubstitutionFresh
    (sourceId certificateSequenceId formulaTraceId lastIndexId
      lineIndexId codeTraceId codeIndexId : FreeVarId) : Prop :=
  sourceId ≠ lineIndexId ∧
    sourceId ≠ codeTraceId ∧
      sourceId ≠ codeIndexId ∧
        sourceId ∉
          [310, 311, 312, 460, 461, 462, 463, 464,
            465, 466, 467, 468, 469, 470] ∧
          LogicalBaseCertificateSubstitutionFresh sourceId
            (logical_certificate_body_base_with_ids
              certificateSequenceId formulaTraceId lastIndexId)

/--
闭项替换逐公开项穿过完整逻辑证书的七字段主体。

该接口允许 `sourceId` 正是三个外层 witness 编号之一；限制只来自主体内实际关闭的
行索引、自然数序列编码 binder、canonical 闭包 binder 与基础证书 binder。
-/
theorem logical_certificate_body_with_ids_substitute_closed
    (formulaCode certificatePayload certificateSequence formulaTrace
      lastIndex replacement formulaCodeResult certificatePayloadResult
      certificateSequenceResult formulaTraceResult lastIndexResult : SetTerm)
    (sourceId certificateSequenceId formulaTraceId lastIndexId
      lineIndexId codeTraceId codeIndexId : FreeVarId)
    (hSourceFresh :
      LogicalCertificateBodySubstitutionFresh sourceId
        certificateSequenceId formulaTraceId lastIndexId
        lineIndexId codeTraceId codeIndexId)
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFree :
      Term.freeSupport replacement = [])
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaCode =
        formulaCodeResult)
    (hCertificatePayloadSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          certificatePayload =
        certificatePayloadResult)
    (hCertificateSequenceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          certificateSequence =
        certificateSequenceResult)
    (hFormulaTraceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaTrace =
        formulaTraceResult)
    (hLastIndexSubstitution :
      Term.substituteFree SetSort.set sourceId replacement lastIndex =
        lastIndexResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_certificate_body_with_ids
          formulaCode certificatePayload
          certificateSequence formulaTrace lastIndex
          certificateSequenceId formulaTraceId lastIndexId lineIndexId
          codeTraceId codeIndexId) =
      logical_certificate_body_with_ids
        formulaCodeResult certificatePayloadResult
        certificateSequenceResult formulaTraceResult lastIndexResult
        certificateSequenceId formulaTraceId lastIndexId lineIndexId
        codeTraceId codeIndexId := by
  rcases hSourceFresh with
    ⟨hSourceNeLineIndex, hSourceNeCodeTrace, hSourceNeCodeIndex,
      hSourceClosureFresh, hSourceBaseFresh⟩
  have hReplacementFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport replacement := by
    rw [hReplacementFree]
    exact List.not_mem_nil
  have hZeroFixed :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hLineIndexFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (x#lineIndexId) =
        x#lineIndexId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeLineIndex]
  have hCertificateCode :=
    nat_sequence_code_condition_with_ids_substitute_closed
      certificateSequence certificatePayload replacement
      certificateSequenceResult certificatePayloadResult
      sourceId codeTraceId codeIndexId
      hSourceNeCodeTrace hSourceNeCodeIndex
      hReplacementAdmissible.2
      (hReplacementFresh codeTraceId)
      (hReplacementFresh codeIndexId)
      hCertificateSequenceSubstitution
      hCertificatePayloadSubstitution
  have hFormulaLastSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          (formulaTrace ·ₘ lastIndex) =
        formulaTraceResult ·ₘ lastIndexResult := by
    simp [Term.substituteFree,
      hFormulaTraceSubstitution, hLastIndexSubstitution]
  have hCertificateLastSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          (certificateSequence ·ₘ lastIndex) =
        certificateSequenceResult ·ₘ lastIndexResult := by
    simp [Term.substituteFree,
      hCertificateSequenceSubstitution, hLastIndexSubstitution]
  have hBaseCertificate :=
    logical_base_certificate_condition_with_base_substitute_fresh
      (formulaTrace ·ₘ lastIndex)
      (certificateSequence ·ₘ lastIndex)
      replacement
      (formulaTraceResult ·ₘ lastIndexResult)
      (certificateSequenceResult ·ₘ lastIndexResult)
      (logical_certificate_body_base_with_ids
        certificateSequenceId formulaTraceId lastIndexId)
      sourceId hSourceBaseFresh
      hReplacementAdmissible
      (by
        intro id hMember
        rw [hReplacementFree] at hMember
        exact False.elim (List.not_mem_nil hMember))
      hFormulaLastSubstitution hCertificateLastSubstitution
  have hLineCommute (body : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement
          (Formula.closeFreeAt SetSort.set lineIndexId 0 body) =
        Formula.closeFreeAt SetSort.set lineIndexId 0
          (Formula.substituteFree SetSort.set sourceId replacement
            body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId lineIndexId 0 replacement body
      hSourceNeLineIndex hReplacementAdmissible.2
      (hReplacementFresh lineIndexId)).symm
  have hClosureStep :=
    logical_closure_certificate_step_condition_substitute_closed
      certificateSequence formulaTrace (x#lineIndexId) replacement
      certificateSequenceResult formulaTraceResult (x#lineIndexId)
      sourceId hSourceClosureFresh
      hReplacementAdmissible hReplacementFree
      hCertificateSequenceSubstitution
      hFormulaTraceSubstitution hLineIndexFixed
  have hClosureSteps :
      Formula.substituteFree SetSort.set sourceId replacement
          (∀ₘ[SetSort.set, lineIndexId],
            (x#lineIndexId ∈ₘ lastIndex) ⟶ₘ
              logical_closure_certificate_step_condition
                certificateSequence formulaTrace (x#lineIndexId)) =
        (∀ₘ[SetSort.set, lineIndexId],
          (x#lineIndexId ∈ₘ lastIndexResult) ⟶ₘ
            logical_closure_certificate_step_condition
              certificateSequenceResult formulaTraceResult
              (x#lineIndexId)) := by
    simp only [Formula.substituteFree]
    rw [hLineCommute]
    simp only [Formula.substituteFree]
    rw [hClosureStep]
    simp [
      hLineIndexFixed, hLastIndexSubstitution]
  unfold logical_certificate_body_with_ids
  rw [logical_certificate_conjunction_substituteFree]
  simp only [List.map]
  rw [hCertificateCode, hBaseCertificate, hClosureSteps]
  simp [Formula.substituteFree, Term.substituteFree,
    hFormulaCodeSubstitution,
    hCertificateSequenceSubstitution, hFormulaTraceSubstitution,
    hLastIndexSubstitution, hZeroFixed]

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
