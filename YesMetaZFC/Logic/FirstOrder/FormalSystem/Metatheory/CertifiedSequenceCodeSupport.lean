import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedSequenceCodeEncoding

/-!
# 已认证序列编码的自由变量支持

本模块只处理编码公式的语法支持，不引入对象理论假设。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode

set_option autoImplicit false

/--
显式 binder 编号的自然数序列编码只依赖序列项与编码项。

trace 与逐点 index 都在对象公式内部关闭，不会扩张公开自由支持。
-/
theorem nat_sequence_code_condition_with_ids_freeSupport_subset
    (sequence code : SetTerm)
    (traceId indexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (nat_sequence_code_condition_with_ids
              sequence code traceId indexId) →
      freeVariable ∈ Term.freeSupport sequence ∨
        freeVariable ∈ Term.freeSupport code := by
  intro freeVariable hMember
  by_cases hSequence :
      freeVariable ∈ Term.freeSupport sequence
  · exact Or.inl hSequence
  by_cases hCode :
      freeVariable ∈ Term.freeSupport code
  · exact Or.inr hCode
  · exfalso
    simp_all [
      nat_sequence_code_condition_with_ids,
      sequence_domain_code_bound,
      nat_sequence_value_code_bound_with_id,
      sequence_trace_code_bound_with_id,
      nat_sequence_code_step_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    grind

/--
自然数序列编码的公开自由支持精确来自序列与编码两项。

两个输入都已在最外层类型字段出现，因此 subset 的反向不依赖内部 binder 编号。
-/
@[simp]
theorem mem_freeSupport_nat_sequence_code_condition_with_ids_iff
    (freeVariable : FreeVariable signature)
    (sequence code : SetTerm)
    (traceId indexId : FreeVarId) :
    freeVariable ∈
        Formula.freeSupport
          (nat_sequence_code_condition_with_ids
            sequence code traceId indexId) ↔
      freeVariable ∈ Term.freeSupport sequence ∨
        freeVariable ∈ Term.freeSupport code := by
  constructor
  · exact nat_sequence_code_condition_with_ids_freeSupport_subset
      sequence code traceId indexId freeVariable
  · intro hMember
    rcases hMember with hSequence | hCode
    · simp [nat_sequence_code_condition_with_ids,
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList, hSequence]
    · simp [nat_sequence_code_condition_with_ids,
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList, hCode]

/-- proof-sequence 单步关系中，`rowTraceId` 不泄漏到自由支持。 -/
theorem proof_sequence_code_step_condition_with_ids_row_trace_fresh
    (sequence trace index rowCode : SetTerm)
    (rowTraceId rowIndexId : FreeVarId)
    (hSequenceFresh :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport sequence)
    (hTraceFresh :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport trace)
    (hIndexFresh :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport index)
    (hRowCodeFresh :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport rowCode) :
    (SetSort.set, rowTraceId) ∉
      Formula.freeSupport
        (proof_sequence_code_step_condition_with_ids
          sequence trace index rowCode rowTraceId rowIndexId) := by
  have hSequenceAtFresh :
      (SetSort.set, rowTraceId) ∉
        Term.freeSupport (sequence ·ₘ index) := by
    simp only [Term.freeSupport, Term.freeSupportList,
      List.append_nil]
    exact List.not_mem_append hSequenceFresh hIndexFresh
  have hInnerFresh :=
    nat_sequence_code_condition_with_ids_trace_fresh
      (sequence ·ₘ index) rowCode rowTraceId rowIndexId
      hSequenceAtFresh hRowCodeFresh
  have hStepValueFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          ((trace ·ₘ Sₘ(index)) ≐ₘ
            Sₘ(godel_pairₘ(
              ⟨trace ·ₘ index, rowCode⟩ₘ))) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    have hTraceIndexFresh :=
      List.not_mem_append hTraceFresh hIndexFresh
    have hTraceIndexRowCodeFresh :=
      List.not_mem_append
        hTraceIndexFresh hRowCodeFresh
    exact List.not_mem_append hTraceIndexFresh
      hTraceIndexRowCodeFresh
  unfold proof_sequence_code_step_condition_with_ids
  simp only [Formula.freeSupport]
  exact List.not_mem_append hInnerFresh hStepValueFresh

/-- proof-sequence 条件中由 trace 绑定量词关闭的公式体。 -/
def proof_sequence_code_trace_body_with_ids
    (sequence code : SetTerm)
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId) :
    SetFormula :=
  (((x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
      (domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence)))) ∧ₘ
    sequence_trace_code_bound_with_id
      (x#traceId) code indexId) ∧ₘ
  (((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
    ((∀ₘ[SetSort.set, indexId],
        (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
          (∃ₘ[SetSort.set, rowCodeId],
            ((x#rowCodeId ∈ₘ code) ∧ₘ
              proof_sequence_code_step_condition_with_ids
                sequence (x#traceId) (x#indexId) (x#rowCodeId)
                rowTraceId rowIndexId))) ∧ₘ
      (code ≐ₘ (x#traceId ·ₘ domₘ(sequence)))))

/-- 行码绑定号不出现在 proof-sequence trace body 的自由支持中。 -/
theorem proof_sequence_code_trace_body_with_ids_row_code_fresh
    (sequence code : SetTerm)
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hSequenceFresh :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport sequence)
    (hCodeFresh :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport code)
    (hTraceFresh :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport (x#traceId))
    (hIndexNeRowCode : indexId ≠ rowCodeId) :
    (SetSort.set, rowCodeId) ∉
      Formula.freeSupport
        (proof_sequence_code_trace_body_with_ids
          sequence code traceId indexId
          rowCodeId rowTraceId rowIndexId) := by
  have hBoundFresh :=
    sequence_trace_code_bound_with_id_fresh_of_not_mem
      (x#traceId) code rowCodeId indexId
      hTraceFresh hCodeFresh hIndexNeRowCode.symm
  have hStepExistsFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport
          (∃ₘ[SetSort.set, rowCodeId],
            ((x#rowCodeId ∈ₘ code) ∧ₘ
              proof_sequence_code_step_condition_with_ids
                sequence (x#traceId) (x#indexId) (x#rowCodeId)
                rowTraceId rowIndexId)) := by
    exact Formula.not_mem_freeSupport_closeFreeAt
      (σ := signature) SetSort.set rowCodeId 0
      ((x#rowCodeId ∈ₘ code) ∧ₘ
        proof_sequence_code_step_condition_with_ids
          sequence (x#traceId) (x#indexId) (x#rowCodeId)
          rowTraceId rowIndexId)
  have hIndexFresh :
      (SetSort.set, rowCodeId) ∉
        [(SetSort.set, indexId)] := by
    intro hMember
    exact hIndexNeRowCode.symm
      (congrArg Prod.snd (List.mem_singleton.mp hMember))
  have hStepAntecedentFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport
          ((x#indexId ∈ₘ domₘ(sequence)) ) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append hIndexFresh hSequenceFresh
  have hStepFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport
          ((x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
            (∃ₘ[SetSort.set, rowCodeId],
              ((x#rowCodeId ∈ₘ code) ∧ₘ
                proof_sequence_code_step_condition_with_ids
                  sequence (x#traceId) (x#indexId) (x#rowCodeId)
                  rowTraceId rowIndexId))) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append
      hStepAntecedentFresh hStepExistsFresh
  have hStepsFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport
          (∀ₘ[SetSort.set, indexId],
            (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
              (∃ₘ[SetSort.set, rowCodeId],
                ((x#rowCodeId ∈ₘ code) ∧ₘ
                  proof_sequence_code_step_condition_with_ids
                    sequence (x#traceId) (x#indexId) (x#rowCodeId)
                    rowTraceId rowIndexId))) := by
    exact Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (σ := signature) (SetSort.set, rowCodeId)
      SetSort.set indexId 0
      ((x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
        (∃ₘ[SetSort.set, rowCodeId],
          ((x#rowCodeId ∈ₘ code) ∧ₘ
            proof_sequence_code_step_condition_with_ids
              sequence (x#traceId) (x#indexId) (x#rowCodeId)
              rowTraceId rowIndexId)))
      hStepFresh
  have hSpaceFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport (x#traceId ∈ₘ seq_spaceₘ(ωₘ)) := by
    simpa [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList] using hTraceFresh
  have hDomainFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport
          (domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence))) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append hTraceFresh hSequenceFresh
  have hSpaceDomainFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport
          ((x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
            (domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence)))) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append hSpaceFresh hDomainFresh
  have hZeroFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport
          ((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) := by
    simpa [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList] using hTraceFresh
  have hFinalFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport
          (code ≐ₘ (x#traceId ·ₘ domₘ(sequence))) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append hCodeFresh
      (List.not_mem_append hTraceFresh hSequenceFresh)
  have hLeftFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport
          (((x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
              (domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence)))) ∧ₘ
            sequence_trace_code_bound_with_id
              (x#traceId) code indexId) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append hSpaceDomainFresh hBoundFresh
  have hRightFresh :
      (SetSort.set, rowCodeId) ∉
        Formula.freeSupport
          (((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
            ((∀ₘ[SetSort.set, indexId],
                (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
                  (∃ₘ[SetSort.set, rowCodeId],
                    ((x#rowCodeId ∈ₘ code) ∧ₘ
                      proof_sequence_code_step_condition_with_ids
                        sequence (x#traceId) (x#indexId) (x#rowCodeId)
                        rowTraceId rowIndexId))) ∧ₘ
              (code ≐ₘ (x#traceId ·ₘ domₘ(sequence))))) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append hZeroFresh
      (List.not_mem_append hStepsFresh hFinalFresh)
  unfold proof_sequence_code_trace_body_with_ids
  simp only [Formula.freeSupport]
  exact List.not_mem_append hLeftFresh hRightFresh

/-- 内层行轨迹绑定号不出现在 proof-sequence trace body 的自由支持中。 -/
theorem proof_sequence_code_trace_body_with_ids_row_trace_fresh
    (sequence code : SetTerm)
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hSequenceFresh :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport sequence)
    (hCodeFresh :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport code)
    (hTraceFresh :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport (x#traceId))
    (hIndexNeRowTrace : indexId ≠ rowTraceId)
    (hRowCodeNeRowTrace : rowCodeId ≠ rowTraceId) :
    (SetSort.set, rowTraceId) ∉
      Formula.freeSupport
        (proof_sequence_code_trace_body_with_ids
          sequence code traceId indexId
          rowCodeId rowTraceId rowIndexId) := by
  have hBoundFresh :=
    sequence_trace_code_bound_with_id_fresh_of_not_mem
      (x#traceId) code rowTraceId indexId
      hTraceFresh hCodeFresh hIndexNeRowTrace.symm
  have hIndexFresh :
      (SetSort.set, rowTraceId) ∉
        [(SetSort.set, indexId)] := by
    intro hMember
    exact hIndexNeRowTrace.symm
      (congrArg Prod.snd (List.mem_singleton.mp hMember))
  have hIndexTermFresh :
      (SetSort.set, rowTraceId) ∉
        Term.freeSupport (x#indexId) := by
    change (SetSort.set, rowTraceId) ∉
      [(SetSort.set, indexId)]
    exact hIndexFresh
  have hRowCodeFresh :
      (SetSort.set, rowTraceId) ∉
        [(SetSort.set, rowCodeId)] := by
    intro hMember
    exact hRowCodeNeRowTrace.symm
      (congrArg Prod.snd (List.mem_singleton.mp hMember))
  have hRowCodeTermFresh :
      (SetSort.set, rowTraceId) ∉
        Term.freeSupport (x#rowCodeId) := by
    change (SetSort.set, rowTraceId) ∉
      [(SetSort.set, rowCodeId)]
    exact hRowCodeFresh
  have hStepConditionFresh :=
    proof_sequence_code_step_condition_with_ids_row_trace_fresh
      sequence (x#traceId) (x#indexId) (x#rowCodeId)
      rowTraceId rowIndexId
      hSequenceFresh hTraceFresh
      hIndexTermFresh hRowCodeTermFresh
  have hRowCodeBoundFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport (x#rowCodeId ∈ₘ code) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append hRowCodeFresh hCodeFresh
  have hStepWitnessFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          ((x#rowCodeId ∈ₘ code) ∧ₘ
            proof_sequence_code_step_condition_with_ids
              sequence (x#traceId) (x#indexId) (x#rowCodeId)
              rowTraceId rowIndexId) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append
      hRowCodeBoundFresh hStepConditionFresh
  have hStepExistsFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          (∃ₘ[SetSort.set, rowCodeId],
            ((x#rowCodeId ∈ₘ code) ∧ₘ
              proof_sequence_code_step_condition_with_ids
                sequence (x#traceId) (x#indexId) (x#rowCodeId)
                rowTraceId rowIndexId)) := by
    exact Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (σ := signature) (SetSort.set, rowTraceId)
      SetSort.set rowCodeId 0
      ((x#rowCodeId ∈ₘ code) ∧ₘ
        proof_sequence_code_step_condition_with_ids
          sequence (x#traceId) (x#indexId) (x#rowCodeId)
          rowTraceId rowIndexId)
      hStepWitnessFresh
  have hStepAntecedentFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          (x#indexId ∈ₘ domₘ(sequence)) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append hIndexFresh hSequenceFresh
  have hStepFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          ((x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
            (∃ₘ[SetSort.set, rowCodeId],
              ((x#rowCodeId ∈ₘ code) ∧ₘ
                proof_sequence_code_step_condition_with_ids
                  sequence (x#traceId) (x#indexId) (x#rowCodeId)
                  rowTraceId rowIndexId))) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append
      hStepAntecedentFresh hStepExistsFresh
  have hStepsFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          (∀ₘ[SetSort.set, indexId],
            (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
              (∃ₘ[SetSort.set, rowCodeId],
                ((x#rowCodeId ∈ₘ code) ∧ₘ
                  proof_sequence_code_step_condition_with_ids
                    sequence (x#traceId) (x#indexId) (x#rowCodeId)
                    rowTraceId rowIndexId))) := by
    exact Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (σ := signature) (SetSort.set, rowTraceId)
      SetSort.set indexId 0
      ((x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
        (∃ₘ[SetSort.set, rowCodeId],
          ((x#rowCodeId ∈ₘ code) ∧ₘ
            proof_sequence_code_step_condition_with_ids
              sequence (x#traceId) (x#indexId) (x#rowCodeId)
              rowTraceId rowIndexId)))
      hStepFresh
  have hSpaceFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport (x#traceId ∈ₘ seq_spaceₘ(ωₘ)) := by
    simpa [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList] using hTraceFresh
  have hDomainFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          (domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence))) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append hTraceFresh hSequenceFresh
  have hSpaceDomainFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          ((x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
            (domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence)))) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append hSpaceFresh hDomainFresh
  have hZeroFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          ((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) := by
    simpa [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList] using hTraceFresh
  have hFinalFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          (code ≐ₘ (x#traceId ·ₘ domₘ(sequence))) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append hCodeFresh
      (List.not_mem_append hTraceFresh hSequenceFresh)
  have hLeftFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          (((x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
              (domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence)))) ∧ₘ
            sequence_trace_code_bound_with_id
              (x#traceId) code indexId) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append hSpaceDomainFresh hBoundFresh
  have hRightFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          (((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
            ((∀ₘ[SetSort.set, indexId],
                (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
                  (∃ₘ[SetSort.set, rowCodeId],
                    ((x#rowCodeId ∈ₘ code) ∧ₘ
                      proof_sequence_code_step_condition_with_ids
                        sequence (x#traceId) (x#indexId) (x#rowCodeId)
                        rowTraceId rowIndexId))) ∧ₘ
              (code ≐ₘ (x#traceId ·ₘ domₘ(sequence))))) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append hZeroFresh
      (List.not_mem_append hStepsFresh hFinalFresh)
  unfold proof_sequence_code_trace_body_with_ids
  simp only [Formula.freeSupport]
  exact List.not_mem_append hLeftFresh hRightFresh

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
