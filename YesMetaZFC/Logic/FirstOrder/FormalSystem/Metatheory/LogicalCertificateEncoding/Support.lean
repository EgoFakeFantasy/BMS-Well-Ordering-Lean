import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Support.Base

/-!
# 逻辑证书 transcript 的自由变量支持

本模块只组合基础证书、自然数序列与 canonical 全称闭包的公开支持接口，不展开这些
编码关系的内部实现。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace CertifiedProof

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 对象存在量词精确删除其关闭的自由变量。 -/
private theorem mem_freeSupport_exists_closeFreeAt_iff
    (freeVariable : FreeVariable signature)
    (sort : signature.SortSymbol) (id : FreeVarId)
    (formula : Formula signature) :
    freeVariable ∈
        Formula.freeSupport
          (∃ₘ[sort, id], formula) ↔
      freeVariable ∈ Formula.freeSupport formula ∧
        freeVariable ≠ (sort, id) := by
  simpa only [Formula.freeSupport] using
    Formula.mem_freeSupport_closeFreeAt_iff
      freeVariable sort id 0 formula

/-- 对象全称量词精确删除其关闭的自由变量。 -/
private theorem mem_freeSupport_forall_closeFreeAt_iff
    (freeVariable : FreeVariable signature)
    (sort : signature.SortSymbol) (id : FreeVarId)
    (formula : Formula signature) :
    freeVariable ∈
        Formula.freeSupport
          (∀ₘ[sort, id], formula) ↔
      freeVariable ∈ Formula.freeSupport formula ∧
        freeVariable ≠ (sort, id) := by
  simpa only [Formula.freeSupport] using
    Formula.mem_freeSupport_closeFreeAt_iff
      freeVariable sort id 0 formula

/-- 合取的自由变量支持精确分解到两个分支。 -/
private theorem mem_freeSupport_conj_iff
    (freeVariable : FreeVariable signature)
    (left right : Formula signature) :
    freeVariable ∈ Formula.freeSupport (left ∧ₘ right) ↔
      freeVariable ∈ Formula.freeSupport left ∨
        freeVariable ∈ Formula.freeSupport right := by
  simp only [Formula.freeSupport, List.mem_append]

/-- transcript 的一次全称闭包只依赖证书序列、公式轨迹与当前位置。 -/
theorem logical_closure_certificate_step_condition_freeSupport_subset
    (certificateSequence formulaTrace index : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_closure_certificate_step_condition
              certificateSequence formulaTrace index) →
      freeVariable ∈ Term.freeSupport certificateSequence ∨
        freeVariable ∈ Term.freeSupport formulaTrace ∨
          freeVariable ∈ Term.freeSupport index := by
  intro freeVariable hMember
  have hSplit :
      freeVariable ∈ Formula.freeSupport
          (¬ₘ variable_symbol_occurs_condition
            (var_codeₘ(numₘ(2) *ₘ
              (certificateSequence ·ₘ index)))
            (formulaTrace ·ₘ index)) ∨
        freeVariable ∈ Formula.freeSupport
          (canonical_forall_closure_code_condition
            (formulaTrace ·ₘ Sₘ(index))
            (var_codeₘ(numₘ(2) *ₘ
              (certificateSequence ·ₘ index)))
            (formulaTrace ·ₘ index)) ∨
        freeVariable ∈ Formula.freeSupport
          (canonical_forall_open_code_condition
            (formulaTrace ·ₘ index)
            (var_codeₘ(numₘ(2) *ₘ
              (certificateSequence ·ₘ index)))
            (formulaTrace ·ₘ Sₘ(index))) := by
    simpa [logical_closure_certificate_step_condition,
      Formula.freeSupport, List.mem_append] using hMember
  rcases hSplit with hOccurrence | hClosure | hOpen
  · simp_all [variable_symbol_occurs_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append] <;> grind
  · rcases canonical_forall_closure_code_condition_freeSupport_subset
        (formulaTrace ·ₘ Sₘ(index))
        (var_codeₘ(numₘ(2) *ₘ
          (certificateSequence ·ₘ index)))
        (formulaTrace ·ₘ index)
        freeVariable hClosure with
      hSource | hVariable | hTarget
    all_goals
      simp_all [
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
      <;> grind
  · rcases canonical_forall_open_code_condition_freeSupport_subset
        (formulaTrace ·ₘ index)
        (var_codeₘ(numₘ(2) *ₘ
          (certificateSequence ·ₘ index)))
        (formulaTrace ·ₘ Sₘ(index))
        freeVariable hOpen with
      hSource | hVariable | hTarget
    all_goals
      simp_all [
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
      <;> grind

/-- 所有非末 transcript 步骤只依赖两条轨迹与末位置。 -/
theorem logical_closure_certificate_steps_freeSupport_subset
    (certificateSequence formulaTrace lastIndex : SetTerm)
    (lineIndexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (∀ₘ[SetSort.set, lineIndexId],
              (x#lineIndexId ∈ₘ lastIndex) ⟶ₘ
                logical_closure_certificate_step_condition
                  certificateSequence formulaTrace (x#lineIndexId)) →
      freeVariable ∈ Term.freeSupport certificateSequence ∨
        freeVariable ∈ Term.freeSupport formulaTrace ∨
          freeVariable ∈ Term.freeSupport lastIndex := by
  intro freeVariable hMember
  by_cases hCertificate :
      freeVariable ∈ Term.freeSupport certificateSequence
  · exact Or.inl hCertificate
  by_cases hTrace :
      freeVariable ∈ Term.freeSupport formulaTrace
  · exact Or.inr (Or.inl hTrace)
  by_cases hLast :
      freeVariable ∈ Term.freeSupport lastIndex
  · exact Or.inr (Or.inr hLast)
  · exfalso
    rw [mem_freeSupport_forall_closeFreeAt_iff] at hMember
    rcases hMember with ⟨hBody, hLineFresh⟩
    have hSplit :
        freeVariable ∈ Term.freeSupport (x#lineIndexId) ∨
          freeVariable ∈ Term.freeSupport lastIndex ∨
          freeVariable ∈
            Formula.freeSupport
              (logical_closure_certificate_step_condition
                certificateSequence formulaTrace (x#lineIndexId)) := by
      simpa [
        Formula.freeSupport, Term.freeSupportList,
        List.mem_append] using hBody
    rcases hSplit with hLine | hLastIndex | hStep
    · simp_all [Term.freeSupport]
    · exact hLast hLastIndex
    · rcases
        logical_closure_certificate_step_condition_freeSupport_subset
          certificateSequence formulaTrace (x#lineIndexId)
          freeVariable hStep with
        hMember | hMember | hMember
      · exact hCertificate hMember
      · exact hTrace hMember
      · simp_all [Term.freeSupport]

/-- 显式 binder 编号下的完整逻辑证书只依赖两个公开入口。 -/
theorem logical_certificate_condition_with_ids_freeSupport_subset
    (formulaCode certificatePayload : SetTerm)
    (certificateSequenceId formulaTraceId lastIndexId lineIndexId
      codeTraceId codeIndexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_certificate_condition_with_ids
              formulaCode certificatePayload
              certificateSequenceId formulaTraceId lastIndexId lineIndexId
              codeTraceId codeIndexId) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificatePayload := by
  intro freeVariable hMember
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formulaCode
  · exact Or.inl hFormula
  by_cases hCertificate :
      freeVariable ∈ Term.freeSupport certificatePayload
  · exact Or.inr hCertificate
  · exfalso
    unfold logical_certificate_condition_with_ids at hMember
    rw [mem_freeSupport_exists_closeFreeAt_iff] at hMember
    rcases hMember with ⟨hMember, hSequenceFresh⟩
    rw [mem_freeSupport_conj_iff] at hMember
    rcases hMember with hSequenceGuard | hMember
    · have hEqual :
          freeVariable = (SetSort.set, certificateSequenceId) := by
        simpa [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList] using hSequenceGuard
      exact hSequenceFresh hEqual
    rw [mem_freeSupport_exists_closeFreeAt_iff] at hMember
    rcases hMember with ⟨hMember, hTraceFresh⟩
    rw [mem_freeSupport_conj_iff] at hMember
    rcases hMember with hTraceGuard | hMember
    · have hEqual :
          freeVariable = (SetSort.set, formulaTraceId) := by
        simpa [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList] using hTraceGuard
      exact hTraceFresh hEqual
    rw [mem_freeSupport_exists_closeFreeAt_iff] at hMember
    rcases hMember with ⟨hMember, hLastFresh⟩
    rw [mem_freeSupport_conj_iff] at hMember
    rcases hMember with hLastGuard | hBody
    · have hEqual :
          freeVariable = (SetSort.set, lastIndexId) ∨
            freeVariable = (SetSort.set, certificateSequenceId) := by
        simpa [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList] using hLastGuard
      exact hEqual.elim hLastFresh hSequenceFresh
    rcases logical_certificate_conjunction_freeSupport
        _ freeVariable hBody with
      ⟨field, hField, hFieldSupport⟩
    simp only [
      List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases nat_sequence_code_condition_with_ids_freeSupport_subset
          (x#certificateSequenceId) certificatePayload
          codeTraceId codeIndexId
          freeVariable hFieldSupport with
        hMember | hMember
      · simp_all [Term.freeSupport]
      · exact hCertificate hMember
    · simp_all [
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList]
    · simp_all [
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList]
    · simp_all [
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList]
    · simp_all [
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList,
        finite_numeral_term_freeSupport]
    · have hBase :=
        logical_base_certificate_condition_freeSupport_subset
          (x#formulaTraceId ·ₘ x#lastIndexId)
          (x#certificateSequenceId ·ₘ x#lastIndexId)
          freeVariable hFieldSupport
      simp_all [Term.freeSupport, Term.freeSupportList]
    · have hSteps :=
        logical_closure_certificate_steps_freeSupport_subset
          (x#certificateSequenceId) (x#formulaTraceId)
          (x#lastIndexId) lineIndexId
          freeVariable hFieldSupport
      simp_all [Term.freeSupport]

/-- 自动 binder 版本的完整逻辑证书只依赖两个公开入口。 -/
theorem logical_certificate_condition_freeSupport_subset
    (formulaCode certificatePayload : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_certificate_condition
              formulaCode certificatePayload) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificatePayload := by
  intro freeVariable hMember
  exact logical_certificate_condition_with_ids_freeSupport_subset
    formulaCode certificatePayload _ _ _ _ _ _
    freeVariable
    (by simpa [logical_certificate_condition] using hMember)

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
