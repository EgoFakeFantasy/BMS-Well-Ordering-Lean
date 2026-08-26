import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaCertificateReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalProjectTokenShift.Replay

/-!
# ZFC schema 的具体 checked replay

本模块把外部 schema 的有限 token 证书逐项接回对象 verifier。先提供代码边界与
公式码等式运输接口，后续 separation/collection 实例只消费这些最弱的语法合同。
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

set_option autoImplicit false

/-! ## 总化公式码的边界 -/

/-- 任何 admissible 公式的总化 quotation 项仍满足闭代码边界。 -/
theorem fs_zfc_support_raw_formula_code_term_boundary
    {formula : SetFormula}
    (hFormula : Formula.Admissible formula) :
    GodelQuotation.Numbered.CodeBoundary
      (fs_zfc_formula_code_term formula) := by
  unfold fs_zfc_formula_code_term
  cases hQuote : GodelQuotation.Numbered.quote? formula with
  | none =>
      rcases GodelQuotation.Numbered.quote?_exists hFormula with
        ⟨code, hCode⟩
      simp [hQuote] at hCode
  | some code =>
      exact GodelQuotation.Numbered.quote?_code_boundary hQuote

/-! ## 公式码分类条件的代码等式运输 -/

/-- 公式码分类条件可沿闭代码的对象等式运输。 -/
theorem fs_zfc_support_raw_canonical_formula_code_condition_iff_of_code_equality
    (entryDepth leftCode rightCode : SetTerm)
    (base : FreeVarId)
    (hEntryDepth :
      GodelQuotation.Numbered.CodeBoundary entryDepth)
    (hLeftCode :
      GodelQuotation.Numbered.CodeBoundary leftCode)
    (hRightCode :
      GodelQuotation.Numbered.CodeBoundary rightCode)
    (hEquality :
      Derives fs_zfc_support_raw_theory [] (leftCode ≐ₘ rightCode)) :
    Derives fs_zfc_support_raw_theory [] (
      canonical_project_formula_code_condition_with_ids
        entryDepth leftCode
        base (base + 1) (base + 2) (base + 3)
        (base + 4) (base + 5)
        (base + 6) (base + 7)
        (base + 8) (base + 9) ↔ₘ
      canonical_project_formula_code_condition_with_ids
        entryDepth rightCode
        base (base + 1) (base + 2) (base + 3)
        (base + 4) (base + 5)
        (base + 6) (base + 7)
        (base + 8) (base + 9)) := by
  let sourceId := base + 10
  let body :=
    canonical_project_formula_code_condition_with_ids
      entryDepth (x#sourceId)
      base (base + 1) (base + 2) (base + 3)
      (base + 4) (base + 5)
      (base + 6) (base + 7)
      (base + 8) (base + 9)
  have hBody : Formula.Admissible body := by
    simpa [body] using
      canonical_project_formula_code_condition_with_ids_admissible
        entryDepth (x#sourceId)
        base (base + 1) (base + 2) (base + 3)
        (base + 4) (base + 5)
        (base + 6) (base + 7)
        (base + 8) (base + 9)
        hEntryDepth.1
        (set_variable_admissible sourceId)
  have hTransport :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (sort := SetSort.set) (eigen := sourceId)
      (left := leftCode) (right := rightCode) (body := body)
      hEquality
  have hSourceNe (offset : Nat) (hOffset : offset < 10) :
      sourceId ≠ base + offset := by
    dsimp [sourceId]
    intro hEquality'
    have hTenEq : 10 = offset :=
      Nat.add_left_cancel hEquality'
    exact (Nat.ne_of_lt hOffset) hTenEq.symm
  change
    Derives fs_zfc_support_raw_theory [] (
      Formula.substituteFree SetSort.set sourceId leftCode body ↔ₘ
        Formula.substituteFree SetSort.set sourceId rightCode body)
    at hTransport
  have hLeftSubstitution :
      Formula.substituteFree SetSort.set sourceId leftCode body =
        canonical_project_formula_code_condition_with_ids
          entryDepth leftCode
          base (base + 1) (base + 2) (base + 3)
          (base + 4) (base + 5)
          (base + 6) (base + 7)
          (base + 8) (base + 9) := by
    have hEntryDepthSubstitution :
        Term.substituteFree SetSort.set sourceId leftCode entryDepth =
          entryDepth := by
      apply Term.substituteFree_eq_self_of_not_mem
      rw [hEntryDepth.2]
      exact List.not_mem_nil
    simpa [body, sourceId] using
      canonical_project_formula_code_condition_with_ids_substitute_closed
        entryDepth (x#sourceId) leftCode
        entryDepth leftCode
        sourceId
        base (base + 1) (base + 2) (base + 3)
        (base + 4) (base + 5)
        (base + 6) (base + 7)
        (base + 8) (base + 9)
        (hSourceNe 0 (by omega)) (hSourceNe 1 (by omega))
        (hSourceNe 2 (by omega)) (hSourceNe 3 (by omega))
        (hSourceNe 4 (by omega)) (hSourceNe 5 (by omega))
        (hSourceNe 6 (by omega)) (hSourceNe 7 (by omega))
        (hSourceNe 8 (by omega)) (hSourceNe 9 (by omega))
        hLeftCode
        hEntryDepthSubstitution
        (by simp [Term.substituteFree, set_variable])
  have hRightSubstitution :
      Formula.substituteFree SetSort.set sourceId rightCode body =
        canonical_project_formula_code_condition_with_ids
          entryDepth rightCode
          base (base + 1) (base + 2) (base + 3)
          (base + 4) (base + 5)
          (base + 6) (base + 7)
          (base + 8) (base + 9) := by
    have hEntryDepthSubstitution :
        Term.substituteFree SetSort.set sourceId rightCode entryDepth =
          entryDepth := by
      apply Term.substituteFree_eq_self_of_not_mem
      rw [hEntryDepth.2]
      exact List.not_mem_nil
    simpa [body, sourceId] using
      canonical_project_formula_code_condition_with_ids_substitute_closed
        entryDepth (x#sourceId) rightCode
        entryDepth rightCode
        sourceId
        base (base + 1) (base + 2) (base + 3)
        (base + 4) (base + 5)
        (base + 6) (base + 7)
        (base + 8) (base + 9)
        (hSourceNe 0 (by omega)) (hSourceNe 1 (by omega))
        (hSourceNe 2 (by omega)) (hSourceNe 3 (by omega))
        (hSourceNe 4 (by omega)) (hSourceNe 5 (by omega))
        (hSourceNe 6 (by omega)) (hSourceNe 7 (by omega))
        (hSourceNe 8 (by omega)) (hSourceNe 9 (by omega))
        hRightCode
        hEntryDepthSubstitution
        (by simp [Term.substituteFree, set_variable])
  simpa [hLeftSubstitution, hRightSubstitution] using hTransport

/-! ## 有限序列与 shift 条件的代码等式运输 -/

/-- 有限自然数序列条件可沿最终代码的闭等式运输。 -/
theorem fs_zfc_support_raw_nat_sequence_code_condition_with_ids_iff_of_code_equality
    (sequence leftCode rightCode : SetTerm)
    (traceId indexId : FreeVarId)
    (hSequence :
      GodelQuotation.Numbered.CodeBoundary sequence)
    (hLeftCode :
      GodelQuotation.Numbered.CodeBoundary leftCode)
    (hRightCode :
      GodelQuotation.Numbered.CodeBoundary rightCode)
    (hEquality :
      Derives fs_zfc_support_raw_theory [] (leftCode ≐ₘ rightCode)) :
    Derives fs_zfc_support_raw_theory [] (
      nat_sequence_code_condition_with_ids
        sequence leftCode traceId indexId ↔ₘ
      nat_sequence_code_condition_with_ids
        sequence rightCode traceId indexId) := by
  let sourceId := traceId + indexId + 1
  let body :=
    nat_sequence_code_condition_with_ids
      sequence (x#sourceId) traceId indexId
  have hBody : Formula.Admissible body := by
    simpa [body] using
      nat_sequence_code_condition_with_ids_admissible
        sequence (x#sourceId) traceId indexId
        hSequence.1 (set_variable_admissible sourceId)
  have hTransport :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (sort := SetSort.set) (eigen := sourceId)
      (left := leftCode) (right := rightCode) (body := body)
      hEquality
  have hSourceNeTrace : sourceId ≠ traceId := by
    dsimp [sourceId]
    intro hEquality'
    have hEquality'' :
        traceId + (indexId + 1) = traceId + 0 := by
      calc
        traceId + (indexId + 1) =
            (traceId + indexId) + 1 :=
          (Nat.add_assoc traceId indexId 1).symm
        _ = traceId := hEquality'
        _ = traceId + 0 := (Nat.add_zero traceId).symm
    have hZero : indexId + 1 = 0 :=
      Nat.add_left_cancel hEquality''
    exact Nat.succ_ne_zero indexId (by simp at hZero)
  have hSourceNeIndex : sourceId ≠ indexId := by
    dsimp [sourceId]
    intro hEquality'
    have hEquality'' :
        indexId + (traceId + 1) = indexId + 0 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hEquality'
    have hZero : traceId + 1 = 0 :=
      Nat.add_left_cancel hEquality''
    exact Nat.succ_ne_zero traceId (by simp at hZero)
  have hSequenceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement sequence =
        sequence := by
    exact GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hSequence sourceId replacement
  have hLeftSubstitution :
      Formula.substituteFree SetSort.set sourceId leftCode body =
        nat_sequence_code_condition_with_ids
          sequence leftCode traceId indexId := by
    have hLeftFresh (id : FreeVarId) :
        (SetSort.set, id) ∉ Term.freeSupport leftCode := by
      rw [hLeftCode.2]
      exact List.not_mem_nil
    have hTraceComm (subformula : SetFormula) :
        Formula.closeFreeAt SetSort.set traceId 0
            (Formula.substituteFree SetSort.set sourceId leftCode subformula) =
          Formula.substituteFree SetSort.set sourceId leftCode
            (Formula.closeFreeAt SetSort.set traceId 0 subformula) :=
      Formula.closeFreeAt_substituteFree_comm
        SetSort.set sourceId traceId 0 leftCode subformula
        hSourceNeTrace hLeftCode.1.2 (hLeftFresh traceId)
    have hInnerComm (subformula : SetFormula) :
        Formula.closeFreeAt SetSort.set indexId 0
            (Formula.substituteFree SetSort.set sourceId leftCode subformula) =
          Formula.substituteFree SetSort.set sourceId leftCode
            (Formula.closeFreeAt SetSort.set indexId 0 subformula) :=
      Formula.closeFreeAt_substituteFree_comm
        SetSort.set sourceId indexId 0 leftCode subformula
        hSourceNeIndex hLeftCode.1.2 (hLeftFresh indexId)
    have hZeroFixed :
        Term.substituteFree SetSort.set sourceId leftCode (numₘ(0)) =
          numₘ(0) := by
      apply Term.substituteFree_eq_self_of_not_mem
      rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil
    have hStepFixed :
        Formula.substituteFree SetSort.set sourceId leftCode
            (nat_sequence_code_step_condition
              sequence (x#traceId) (x#indexId)) =
          nat_sequence_code_step_condition
            sequence (x#traceId) (x#indexId) := by
      apply Formula.substituteFree_eq_self_of_not_mem
      simp [nat_sequence_code_step_condition,
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList, sourceId,
        hSourceNeTrace,
        hSourceNeIndex]
      rw [hSequence.2]
      simp
    simp [body, nat_sequence_code_condition_with_ids,
      sequence_domain_code_bound,
      nat_sequence_value_code_bound_with_id,
      sequence_trace_code_bound_with_id,
      Formula.substituteFree, sourceId,
      Term.substituteFree, set_variable,
      hSequenceFixed leftCode, hZeroFixed,
      Ne.symm hSourceNeTrace, Ne.symm hSourceNeIndex,
      hStepFixed, ← hTraceComm, ← hInnerComm]
  have hRightSubstitution :
      Formula.substituteFree SetSort.set sourceId rightCode body =
        nat_sequence_code_condition_with_ids
          sequence rightCode traceId indexId := by
    have hRightFresh (id : FreeVarId) :
        (SetSort.set, id) ∉ Term.freeSupport rightCode := by
      rw [hRightCode.2]
      exact List.not_mem_nil
    have hTraceComm (subformula : SetFormula) :
        Formula.closeFreeAt SetSort.set traceId 0
            (Formula.substituteFree SetSort.set sourceId rightCode subformula) =
          Formula.substituteFree SetSort.set sourceId rightCode
            (Formula.closeFreeAt SetSort.set traceId 0 subformula) :=
      Formula.closeFreeAt_substituteFree_comm
        SetSort.set sourceId traceId 0 rightCode subformula
        hSourceNeTrace hRightCode.1.2 (hRightFresh traceId)
    have hInnerComm (subformula : SetFormula) :
        Formula.closeFreeAt SetSort.set indexId 0
            (Formula.substituteFree SetSort.set sourceId rightCode subformula) =
          Formula.substituteFree SetSort.set sourceId rightCode
            (Formula.closeFreeAt SetSort.set indexId 0 subformula) :=
      Formula.closeFreeAt_substituteFree_comm
        SetSort.set sourceId indexId 0 rightCode subformula
        hSourceNeIndex hRightCode.1.2 (hRightFresh indexId)
    have hZeroFixed :
        Term.substituteFree SetSort.set sourceId rightCode (numₘ(0)) =
          numₘ(0) := by
      apply Term.substituteFree_eq_self_of_not_mem
      rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil
    have hStepFixed :
        Formula.substituteFree SetSort.set sourceId rightCode
            (nat_sequence_code_step_condition
              sequence (x#traceId) (x#indexId)) =
          nat_sequence_code_step_condition
            sequence (x#traceId) (x#indexId) := by
      apply Formula.substituteFree_eq_self_of_not_mem
      simp [nat_sequence_code_step_condition,
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList, sourceId,
        hSourceNeTrace,
        hSourceNeIndex]
      rw [hSequence.2]
      simp
    simp [body, nat_sequence_code_condition_with_ids,
      sequence_domain_code_bound,
      nat_sequence_value_code_bound_with_id,
      sequence_trace_code_bound_with_id,
      Formula.substituteFree, sourceId,
      Term.substituteFree, set_variable,
      hSequenceFixed rightCode, hZeroFixed,
      Ne.symm hSourceNeTrace, Ne.symm hSourceNeIndex,
      hStepFixed, ← hTraceComm, ← hInnerComm]
  simpa [hLeftSubstitution, hRightSubstitution] using hTransport

/-- 有限自然数序列条件可沿序列对象的闭等式运输。 -/
theorem fs_zfc_support_raw_nat_sequence_code_condition_with_ids_iff_of_sequence_equality
    (leftSequence rightSequence code : SetTerm)
    (traceId indexId : FreeVarId)
    (hLeftSequence :
      GodelQuotation.Numbered.CodeBoundary leftSequence)
    (hRightSequence :
      GodelQuotation.Numbered.CodeBoundary rightSequence)
    (hCode :
      GodelQuotation.Numbered.CodeBoundary code)
    (hEquality :
      Derives fs_zfc_support_raw_theory [] (leftSequence ≐ₘ rightSequence)) :
    Derives fs_zfc_support_raw_theory [] (
      nat_sequence_code_condition_with_ids
        leftSequence code traceId indexId ↔ₘ
      nat_sequence_code_condition_with_ids
        rightSequence code traceId indexId) := by
  let sourceId := traceId + indexId + 1
  let body :=
    nat_sequence_code_condition_with_ids
      (x#sourceId) code traceId indexId
  have hBody : Formula.Admissible body := by
    simpa [body] using
      nat_sequence_code_condition_with_ids_admissible
        (x#sourceId) code traceId indexId
        (set_variable_admissible sourceId) hCode.1
  have hTransport :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (sort := SetSort.set) (eigen := sourceId)
      (left := leftSequence) (right := rightSequence) (body := body)
      hEquality
  have hSourceNeTrace : sourceId ≠ traceId := by
    dsimp [sourceId]
    intro hEquality'
    have hEquality'' :
        traceId + (indexId + 1) = traceId + 0 := by
      calc
        traceId + (indexId + 1) =
            (traceId + indexId) + 1 :=
          (Nat.add_assoc traceId indexId 1).symm
        _ = traceId := hEquality'
        _ = traceId + 0 := (Nat.add_zero traceId).symm
    have hZero : indexId + 1 = 0 :=
      Nat.add_left_cancel hEquality''
    exact Nat.succ_ne_zero indexId (by simp at hZero)
  have hSourceNeIndex : sourceId ≠ indexId := by
    dsimp [sourceId]
    intro hEquality'
    have hEquality'' :
        indexId + (traceId + 1) = indexId + 0 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hEquality'
    have hZero : traceId + 1 = 0 :=
      Nat.add_left_cancel hEquality''
    exact Nat.succ_ne_zero traceId (by simp at hZero)
  have hSubstitution (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set sourceId replacement body =
        nat_sequence_code_condition_with_ids
          replacement code traceId indexId := by
    have hReplacementFresh (id : FreeVarId) :
        (SetSort.set, id) ∉ Term.freeSupport replacement := by
      rw [hReplacement.2]
      exact List.not_mem_nil
    have hSequenceSubstitution :
        Term.substituteFree SetSort.set sourceId replacement
            (x#sourceId) =
          replacement := by
      simp [Term.substituteFree, set_variable]
    have hCodeFixed :
        Term.substituteFree SetSort.set sourceId replacement code =
          code :=
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hCode sourceId replacement
    have hZeroFixed :
        Term.substituteFree SetSort.set sourceId replacement (numₘ(0)) =
          numₘ(0) := by
      apply Term.substituteFree_eq_self_of_not_mem
      rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil
    have hTraceComm (subformula : SetFormula) :
        Formula.closeFreeAt SetSort.set traceId 0
            (Formula.substituteFree SetSort.set sourceId replacement subformula) =
          Formula.substituteFree SetSort.set sourceId replacement
            (Formula.closeFreeAt SetSort.set traceId 0 subformula) :=
      Formula.closeFreeAt_substituteFree_comm
        SetSort.set sourceId traceId 0 replacement subformula
        hSourceNeTrace hReplacement.1.2
        (hReplacementFresh traceId)
    have hInnerComm (subformula : SetFormula) :
        Formula.closeFreeAt SetSort.set indexId 0
            (Formula.substituteFree SetSort.set sourceId replacement subformula) =
          Formula.substituteFree SetSort.set sourceId replacement
            (Formula.closeFreeAt SetSort.set indexId 0 subformula) :=
      Formula.closeFreeAt_substituteFree_comm
        SetSort.set sourceId indexId 0 replacement subformula
        hSourceNeIndex hReplacement.1.2
        (hReplacementFresh indexId)
    have hStepSubstitution :
        Formula.substituteFree SetSort.set sourceId replacement
            (nat_sequence_code_step_condition
              (x#sourceId) (x#traceId) (x#indexId)) =
          nat_sequence_code_step_condition
            replacement (x#traceId) (x#indexId) := by
      simp [nat_sequence_code_step_condition,
        Formula.substituteFree, Term.substituteFree,
        set_variable, sourceId,
        Ne.symm hSourceNeTrace,
        Ne.symm hSourceNeIndex, hSequenceSubstitution]
    simp [body, nat_sequence_code_condition_with_ids,
      sequence_domain_code_bound,
      nat_sequence_value_code_bound_with_id,
      sequence_trace_code_bound_with_id,
      Formula.substituteFree, sourceId,
      Term.substituteFree, set_variable,
      hSequenceSubstitution, hCodeFixed, hZeroFixed,
      Ne.symm hSourceNeTrace, Ne.symm hSourceNeIndex,
      hStepSubstitution, ← hTraceComm, ← hInnerComm]
  have hLeftSubstitution :=
    hSubstitution leftSequence hLeftSequence
  have hRightSubstitution :=
    hSubstitution rightSequence hRightSequence
  simpa [hLeftSubstitution, hRightSubstitution] using hTransport

/-- 全称前缀条件可沿最终公式码的闭等式运输。 -/
theorem fs_zfc_support_raw_canonical_forall_prefix_code_condition_iff_of_code_equality
    (binderCount core leftCode rightCode : SetTerm)
    (base : FreeVarId)
    (hBinderCount :
      GodelQuotation.Numbered.CodeBoundary binderCount)
    (hCore :
      GodelQuotation.Numbered.CodeBoundary core)
    (hLeftCode :
      GodelQuotation.Numbered.CodeBoundary leftCode)
    (hRightCode :
      GodelQuotation.Numbered.CodeBoundary rightCode)
    (hEquality :
      Derives fs_zfc_support_raw_theory [] (leftCode ≐ₘ rightCode)) :
    Derives fs_zfc_support_raw_theory [] (
      canonical_forall_prefix_code_condition_with_ids
        binderCount core leftCode base (base + 1) ↔ₘ
      canonical_forall_prefix_code_condition_with_ids
        binderCount core rightCode base (base + 1)) := by
  let sourceId := base + 2
  let body :=
    canonical_forall_prefix_code_condition_with_ids
      binderCount core (x#sourceId) base (base + 1)
  have hBody : Formula.Admissible body := by
    simpa [body] using
      canonical_forall_prefix_code_condition_with_ids_admissible
        binderCount core (x#sourceId) base (base + 1)
        hBinderCount.1 hCore.1
        (set_variable_admissible sourceId)
  have hTransport :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (sort := SetSort.set) (eigen := sourceId)
      (left := leftCode) (right := rightCode) (body := body)
      hEquality
  have hSourceNeTrace : sourceId ≠ base := by
    dsimp [sourceId]
    intro hEquality'
    have hEquality'' : base + 2 = base + 0 := by
      exact hEquality'.trans (Nat.add_zero base).symm
    have hTwoEq : 2 = 0 :=
      Nat.add_left_cancel hEquality''
    omega
  have hSourceNeIndex : sourceId ≠ base + 1 := by
    dsimp [sourceId]
    intro hEquality'
    have hEquality'' : base + 2 = base + 1 := by
      exact hEquality'
    have hTwoEq : 2 = 1 :=
      Nat.add_left_cancel hEquality''
    omega
  have hBinderCountFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement binderCount =
        binderCount :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hBinderCount sourceId replacement
  have hCoreFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement core =
        core :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hCore sourceId replacement
  have hLeftSubstitution :
      Formula.substituteFree SetSort.set sourceId leftCode body =
        canonical_forall_prefix_code_condition_with_ids
          binderCount core leftCode base (base + 1) := by
    simpa [body, sourceId] using
      canonical_forall_prefix_code_condition_with_ids_substitute_closed
        binderCount core (x#sourceId) leftCode
        binderCount core leftCode
        sourceId base (base + 1)
        hSourceNeTrace hSourceNeIndex
        hLeftCode
        (hBinderCountFixed leftCode)
        (hCoreFixed leftCode)
        (by simp [Term.substituteFree, set_variable])
  have hRightSubstitution :
      Formula.substituteFree SetSort.set sourceId rightCode body =
        canonical_forall_prefix_code_condition_with_ids
          binderCount core rightCode base (base + 1) := by
    simpa [body, sourceId] using
      canonical_forall_prefix_code_condition_with_ids_substitute_closed
        binderCount core (x#sourceId) rightCode
        binderCount core rightCode
        sourceId base (base + 1)
        hSourceNeTrace hSourceNeIndex
        hRightCode
        (hBinderCountFixed rightCode)
        (hCoreFixed rightCode)
        (by simp [Term.substituteFree, set_variable])
  change
    Derives fs_zfc_support_raw_theory [] (
      Formula.substituteFree SetSort.set sourceId leftCode body ↔ₘ
        Formula.substituteFree SetSort.set sourceId rightCode body)
    at hTransport
  simpa [hLeftSubstitution, hRightSubstitution] using hTransport

/-! ## separation 的两次局部重命名 -/

/-- 一元参数在第一个局部 binder 下的 cutoff-shift 索引合同。 -/
theorem fs_zfc_separation_unary_index_shift_first
    (parameterCount : Nat) :
    CanonicalProjectIndexShift
      (originalDepth := parameterCount + 1)
      (sourceDepth := parameterCount + 1)
      parameterCount
      (fun entry : Fin (parameterCount + 1) => entry)
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne parameterCount) := by
  intro entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · simp [
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
      ]
  · have hDepthLt :
        parameterCount - previous.val - 1 < parameterCount := by
      omega
    simp [
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne,
      canonical_project_shift_depth_of_lt hDepthLt]

/-- 一元参数在第二个局部 binder 下的 cutoff-shift 索引合同。 -/
theorem fs_zfc_separation_unary_index_shift_second
    (parameterCount : Nat) :
    CanonicalProjectIndexShift
      (originalDepth := parameterCount + 1)
      (sourceDepth := parameterCount + 2)
      parameterCount
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne parameterCount)
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo parameterCount) := by
  intro entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · simp [
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne,
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
      ]
  · have hDepthLt :
        parameterCount - previous.val - 1 < parameterCount := by
      omega
    simp [
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne,
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo,
      canonical_project_shift_depth_of_lt hDepthLt]

/-! ## separation 的三条规范公式轨迹 -/

/-- 项目项沿恒等替换保持原状。 -/
theorem fs_zfc_project_term_bind_id
    {depth : Nat}
    (term :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.Term
        depth) :
    term.bind
        (fun entry : Fin depth =>
          (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
            entry : _root_.YesMetaZFC.SetTheory.Definitional.Term depth)) =
      term := by
  cases term <;> rfl

/-- 项目项沿恒等索引图重命名后保持原状。 -/
theorem fs_zfc_project_term_rename_id
    {depth : Nat}
    (term :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.Term
        depth) :
    term.rename (fun entry : Fin depth => entry) = term := by
  simpa [
    _root_.YesMetaZFC.SetTheory.Definitional.Term.rename] using
    fs_zfc_project_term_bind_id term

/-- 项目参数向量沿恒等索引图重命名后保持原状。 -/
theorem fs_zfc_project_term_vector_bind_id
    {count depth : Nat}
    (terms :
      _root_.YesMetaZFC.SetTheory.Definitional.TermVector
        count depth) :
    terms.bind
        (fun entry : Fin depth =>
          (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
            entry : _root_.YesMetaZFC.SetTheory.Definitional.Term depth)) =
      terms := by
  cases terms with
  | mk values hSize =>
      cases hSize
      have hValues :
          Array.map
              (fun term =>
                term.bind
                  (fun entry : Fin depth =>
                    (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                      entry : _root_.YesMetaZFC.SetTheory.Definitional.Term depth)))
              values =
            values := by
        have hMapped :
            Array.map
                (fun term =>
                  term.bind
                    (fun entry : Fin depth =>
                      (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                        entry : _root_.YesMetaZFC.SetTheory.Definitional.Term depth)))
                values =
              Array.map id values := by
          apply (Array.map_eq_map_iff).2
          intro term hTerm
          exact fs_zfc_project_term_bind_id term
        simpa using hMapped
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.TermVector.bind]
      congr

/-- 项目参数向量沿恒等索引图重命名后保持原状。 -/
theorem fs_zfc_project_term_vector_rename_id
    {count depth : Nat}
    (terms :
      _root_.YesMetaZFC.SetTheory.Definitional.TermVector
        count depth) :
    terms.rename (fun entry : Fin depth => entry) = terms := by
  simpa [
    _root_.YesMetaZFC.SetTheory.Definitional.TermVector.rename] using
    fs_zfc_project_term_vector_bind_id terms

/-- 恒等替换穿过一个项目量词后仍是恒等替换。 -/
theorem fs_zfc_project_term_lift_bind_id
    (depth : Nat) :
    _root_.YesMetaZFC.SetTheory.Definitional.Term.liftSubstitution
        (sourceDepth := depth) (targetDepth := depth)
        (fun entry : Fin depth =>
          (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
            entry : _root_.YesMetaZFC.SetTheory.Definitional.Term depth)) =
      (fun entry : Fin (depth + 1) =>
        (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
          entry : _root_.YesMetaZFC.SetTheory.Definitional.Term
            (depth + 1))) := by
  funext entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · rfl
  · simp [
      _root_.YesMetaZFC.SetTheory.Definitional.Term.liftSubstitution,
      _root_.YesMetaZFC.SetTheory.Definitional.Term.weaken,
      _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
      _root_.YesMetaZFC.SetTheory.Definitional.Term.bind]

/-- 项目公式沿恒等替换保持原状。 -/
theorem fs_zfc_project_formula_bind_id
    {depth : Nat}
    (formula :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula
        1 depth) :
    formula.bind
        (fun entry : Fin depth =>
          (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
            entry : _root_.YesMetaZFC.SetTheory.Definitional.Term depth)) =
      formula := by
  induction formula with
  | falsum =>
      rfl
  | truth =>
      rfl
  | mem left right =>
      change
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.mem
            (left.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _)))
            (right.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _))) =
          _root_.YesMetaZFC.SetTheory.Definitional.Formula.mem left right
      cases left <;> cases right <;> rfl
  | atom symbol hStage arguments =>
      change
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.atom
            symbol hStage
            (arguments.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _))) =
          _root_.YesMetaZFC.SetTheory.Definitional.Formula.atom
            symbol hStage arguments
      rw [fs_zfc_project_term_vector_bind_id]
  | neg body ih =>
      change
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.neg
            (body.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _))) =
          _root_.YesMetaZFC.SetTheory.Definitional.Formula.neg body
      rw [ih]
  | conj left right ihLeft ihRight =>
      change
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.conj
            (left.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _)))
            (right.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _))) =
          _root_.YesMetaZFC.SetTheory.Definitional.Formula.conj left right
      rw [ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      change
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.disj
            (left.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _)))
            (right.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _))) =
          _root_.YesMetaZFC.SetTheory.Definitional.Formula.disj left right
      rw [ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      change
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.imp
            (left.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _)))
            (right.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _))) =
          _root_.YesMetaZFC.SetTheory.Definitional.Formula.imp left right
      rw [ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      change
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.iff
            (left.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _)))
            (right.bind (fun entry : Fin _ =>
              (_root_.YesMetaZFC.SetTheory.Definitional.Term.bound
                entry : _root_.YesMetaZFC.SetTheory.Definitional.Term _))) =
          _root_.YesMetaZFC.SetTheory.Definitional.Formula.iff left right
      rw [ihLeft, ihRight]
  | forallE body ih =>
      simp [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_zfc_project_term_lift_bind_id,
        ih]
  | existsE body ih =>
      simp [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        fs_zfc_project_term_lift_bind_id,
        ih]

/-- 项目公式沿恒等索引图重命名后保持原状。 -/
theorem fs_zfc_project_formula_rename_id
    {depth : Nat}
    (formula :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula
        1 depth) :
    formula.rename (fun entry : Fin depth => entry) = formula := by
  simpa [
    _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename] using
    fs_zfc_project_formula_bind_id formula

/-- 分离模式 body 及其两次局部重命名具有规范 trace 与 shift 证书。 -/
theorem fs_zfc_separation_unary_trace_bundle
    {parameterCount : Nat}
    (schema : _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
      parameterCount) :
    ∃ bodyTrace firstTrace secondTrace,
      canonical_project_hilbert_trace?
          (parameterCount + 1)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula schema.body)) =
        some bodyTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 2)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
                  parameterCount)))) =
        some firstTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
                  parameterCount)))) =
        some secondTrace ∧
      CanonicalProjectTraceShift parameterCount bodyTrace firstTrace ∧
      CanonicalProjectTraceShift parameterCount firstTrace secondTrace := by
  have hFirstShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 1)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (fun entry : Fin (parameterCount + 1) => entry))))
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
                (schema.body.rename
                  (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
                  parameterCount)))) :=
    fs_embed_project_formula_rename_hilbert_shift
      schema.body
      (fun entry : Fin (parameterCount + 1) => entry)
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
        parameterCount)
      schema.freeClosed
      (by omega)
      (fs_zfc_separation_unary_index_shift_first parameterCount)
  have hSecondShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 2)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
                  parameterCount))))
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
            (schema.body.rename
              (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
                parameterCount)))) :=
    fs_embed_project_formula_rename_hilbert_shift
      schema.body
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
        parameterCount)
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
        parameterCount)
      schema.freeClosed
      (by omega)
      (fs_zfc_separation_unary_index_shift_second parameterCount)
  rcases CanonicalProjectFormulaShift.trace_from? hFirstShift 0 with
    ⟨rawBodyTrace, firstTrace, hBodyTrace, hFirstTrace, hFirstShiftTrace⟩
  rcases CanonicalProjectFormulaShift.trace_from? hSecondShift 0 with
    ⟨rawFirstTrace, secondTrace, hRawFirstTrace, hSecondTrace,
      hSecondShiftTrace⟩
  have hBodyTrace' :
      canonical_project_hilbert_trace?
          (parameterCount + 1)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula schema.body)) =
        some rawBodyTrace := by
    rw [← fs_zfc_project_formula_rename_id schema.body]
    exact hBodyTrace
  have hFirstTraceEq : rawFirstTrace = firstTrace :=
    Option.some.inj (hRawFirstTrace.symm.trans hFirstTrace)
  subst rawFirstTrace
  exact ⟨rawBodyTrace, firstTrace, secondTrace,
    hBodyTrace', hFirstTrace, hSecondTrace, hFirstShiftTrace,
    hSecondShiftTrace⟩

/-! ## 分离 body 的根码与有限序列回放 -/

/-- 分离 body 的根码等于其规范 token 序列，并满足对象层有限序列条件。 -/
theorem fs_zfc_separation_unary_body_sequence_component
    {parameterCount : Nat}
    (schema : _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
      parameterCount)
    (base : FreeVarId) :
    ∃ bodyTrace,
      canonical_project_hilbert_trace?
          (parameterCount + 1)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula schema.body)) =
        some bodyTrace ∧
      Derives fs_zfc_support_raw_theory [] (
        bodyTrace.rootCode ≐ₘ
          standard_token_sequence
            (fs_project_hilbert_token_tree schema.body).tokens) ∧
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          bodyTrace.rootCode
          (numₘ(nat_sequence_code_value
            (fs_project_hilbert_token_tree schema.body).tokens))
          (base + 5) (base + 6)) := by
  rcases fs_zfc_separation_unary_trace_bundle schema with
    ⟨bodyTrace, firstTrace, secondTrace, hBodyTrace, hFirstTrace,
      hSecondTrace, hFirstShiftTrace, hSecondShiftTrace⟩
  let tokens : List Nat :=
    (fs_project_hilbert_token_tree schema.body).tokens
  have hTokens :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names (parameterCount + 1))
          (parameterCount + 1)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula schema.body)) =
        some tokens := by
    simpa [tokens] using
      fs_project_hilbert_token_tree_tokens
        schema.body schema.freeClosed
  have hRootQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names (parameterCount + 1))
          (parameterCount + 1)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula schema.body)) =
        some bodyTrace.rootCode :=
    canonical_project_hilbert_trace_from?_root_quote hBodyTrace
  have hRootEqualityGodel :
      Derives GodelQuotation.godel_quotation_theory [] (
        bodyTrace.rootCode ≐ₘ
          standard_token_sequence tokens) :=
    GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
      GodelQuotation.free_name
      GodelQuotation.bound_name
      hTokens hRootQuote
  have hRootEquality :
      Derives fs_zfc_support_raw_theory [] (
        bodyTrace.rootCode ≐ₘ
          standard_token_sequence tokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation hRootEqualityGodel
  have hRootBoundary :
      GodelQuotation.Numbered.CodeBoundary bodyTrace.rootCode :=
    canonical_project_hilbert_trace_from?_root_code_boundary hBodyTrace
  have hStandardBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (standard_token_sequence tokens) :=
    ⟨standard_token_sequence_admissible tokens,
      standard_token_sequence_freeSupport_nil tokens⟩
  have hRootEqualitySymm :
      Derives fs_zfc_support_raw_theory [] (
        standard_token_sequence tokens ≐ₘ bodyTrace.rootCode) :=
    Metatheory.Derives.equality_symm
      hRootEquality
  have hStandardSequence :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (standard_token_sequence tokens)
          (numₘ(nat_sequence_code_value tokens))
          (base + 5) (base + 6)) :=
    fs_zfc_support_raw_nat_sequence_code_condition_with_ids
      tokens (base + 5) (base + 6) (by
        intro hEquality
        have hNumeralEquality : 5 = 6 :=
          Nat.add_left_cancel hEquality
        omega)
  have hCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (numₘ(nat_sequence_code_value tokens)) :=
    ⟨finite_numeral_term_admissible
        (nat_sequence_code_value tokens),
      finite_numeral_term_freeSupport
        (nat_sequence_code_value tokens)⟩
  have hSequenceTransport :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (standard_token_sequence tokens)
          (numₘ(nat_sequence_code_value tokens))
          (base + 5) (base + 6) ↔ₘ
        nat_sequence_code_condition_with_ids
          bodyTrace.rootCode
          (numₘ(nat_sequence_code_value tokens))
          (base + 5) (base + 6)) :=
    fs_zfc_support_raw_nat_sequence_code_condition_with_ids_iff_of_sequence_equality
      (standard_token_sequence tokens)
      bodyTrace.rootCode
      (numₘ(nat_sequence_code_value tokens))
      (base + 5) (base + 6)
      hStandardBoundary hRootBoundary hCodeBoundary
      hRootEqualitySymm
  have hSequence :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          bodyTrace.rootCode
          (numₘ(nat_sequence_code_value tokens))
          (base + 5) (base + 6)) :=
    FirstOrder.Derives.iffElimRight
      hSequenceTransport hStandardSequence
  exact ⟨bodyTrace, hBodyTrace, by simpa [tokens] using hRootEquality,
    by simpa [tokens] using hSequence⟩

/-- 分离 body 的规范公式码分类条件已运输到 verifier 的入口深度。 -/
theorem fs_zfc_separation_unary_classifier_component
    {parameterCount : Nat}
    (schema : _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
      parameterCount)
    (base : FreeVarId) :
    ∃ bodyTrace,
      canonical_project_hilbert_trace?
          (parameterCount + 1)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula schema.body)) =
        some bodyTrace ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_formula_code_condition_with_ids
          (Sₘ(numₘ(parameterCount))) bodyTrace.rootCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)) := by
  rcases fs_zfc_separation_unary_trace_bundle schema with
    ⟨bodyTrace, firstTrace, secondTrace, hBodyTrace, hFirstTrace,
      hSecondTrace, hFirstShiftTrace, hSecondShiftTrace⟩
  have hClassifierGodel :=
    canonical_project_hilbert_trace?_code_condition_from_base_derives
      hBodyTrace (base + 7)
  have hClassifierRaw :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_formula_code_condition_with_ids
          (numₘ(parameterCount + 1)) bodyTrace.rootCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)) :=
    fs_zfc_support_raw_derives_of_godel_quotation hClassifierGodel
  have hParameterNumeralBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (numₘ(parameterCount + 1)) :=
    ⟨finite_numeral_term_admissible (parameterCount + 1),
      finite_numeral_term_freeSupport (parameterCount + 1)⟩
  have hParameterSuccessorBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (Sₘ(numₘ(parameterCount))) := by
    simpa [finite_numeral_term] using
      hParameterNumeralBoundary
  have hParameterSuccessorEquality :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(parameterCount + 1) ≐ₘ
          Sₘ(numₘ(parameterCount))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (Sₘ(numₘ(parameterCount))))
  have hBodyBoundary :
      GodelQuotation.Numbered.CodeBoundary bodyTrace.rootCode :=
    canonical_project_hilbert_trace_from?_root_code_boundary hBodyTrace
  have hClassifierTransport :=
    canonical_project_formula_code_condition_from_base_iff_of_entry_depth_equality
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (numₘ(parameterCount + 1))
      (Sₘ(numₘ(parameterCount)))
      bodyTrace.rootCode (base + 7)
      hParameterNumeralBoundary
      hParameterSuccessorBoundary
      hBodyBoundary
      hParameterSuccessorEquality
  have hClassifier :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_formula_code_condition_with_ids
          (Sₘ(numₘ(parameterCount))) bodyTrace.rootCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)) :=
    FirstOrder.Derives.iffElimRight
      hClassifierTransport hClassifierRaw
  exact ⟨bodyTrace, hBodyTrace, hClassifier⟩

/-! ## 分离 shift 的二元代码回放 -/

/-- 分离两次局部重命名直接回放为二元 token 代码关系。 -/
theorem fs_zfc_separation_unary_shift_components
    {parameterCount : Nat}
    (schema : _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
      parameterCount)
    (base : FreeVarId) :
    ∃ bodyTrace firstTrace secondTrace,
      canonical_project_hilbert_trace?
          (parameterCount + 1)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula schema.body)) =
        some bodyTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 2)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
                  parameterCount)))) =
        some firstTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
                  parameterCount)))) =
        some secondTrace ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (numₘ(parameterCount))
          bodyTrace.rootCode firstTrace.rootCode
          (base + 17) (base + 18) (base + 19)) ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode
          (base + 25) (base + 26) (base + 27)) := by
  rcases fs_zfc_separation_unary_trace_bundle schema with
    ⟨bodyTrace, firstTrace, secondTrace, hBodyTrace, hFirstTrace,
      hSecondTrace, _, _⟩
  let sourceFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula schema.body)
  let firstFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
            parameterCount)))
  let secondFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
            parameterCount)))
  have hFirstFormulaShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 1) sourceFormula firstFormula := by
    simpa [sourceFormula, firstFormula,
      fs_zfc_project_formula_rename_id] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (fun entry : Fin (parameterCount + 1) => entry)
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
          parameterCount)
        schema.freeClosed
        (by omega)
        (fs_zfc_separation_unary_index_shift_first
          parameterCount))
  have hSecondFormulaShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 2) firstFormula secondFormula := by
    simpa [firstFormula, secondFormula] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
          parameterCount)
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
          parameterCount)
        schema.freeClosed
        (by omega)
        (fs_zfc_separation_unary_index_shift_second
          parameterCount))
  have hBodyQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 1))
          (parameterCount + 1) sourceFormula =
        some bodyTrace.rootCode := by
    simpa [sourceFormula,
      fs_zfc_project_formula_rename_id] using
      canonical_project_hilbert_trace_from?_root_quote hBodyTrace
  have hFirstQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 2))
          (parameterCount + 2) firstFormula =
        some firstTrace.rootCode := by
    simpa [firstFormula] using
      canonical_project_hilbert_trace_from?_root_quote hFirstTrace
  have hSecondQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 3))
          (parameterCount + 3) secondFormula =
        some secondTrace.rootCode := by
    simpa [secondFormula] using
      canonical_project_hilbert_trace_from?_root_quote hSecondTrace
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hFirstFormulaShift with
    ⟨bodyTokens, firstTokens, hBodyTokens, hFirstTokens⟩
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hSecondFormulaShift with
    ⟨firstTokens', secondTokens, hFirstTokens', hSecondTokens⟩
  have hFirstShift :=
    CanonicalProjectFormulaShift.quote_hilbert_with?_code_condition_with_ids
      hFirstFormulaShift (by omega)
      hBodyTokens hFirstTokens hBodyQuote hFirstQuote (base + 17)
  have hSecondShift :=
    CanonicalProjectFormulaShift.quote_hilbert_with?_code_condition_with_ids
      hSecondFormulaShift (by omega)
      hFirstTokens' hSecondTokens hFirstQuote hSecondQuote (base + 25)
  exact ⟨bodyTrace, firstTrace, secondTrace,
    hBodyTrace, hFirstTrace, hSecondTrace,
    fs_zfc_support_raw_derives_of_godel_quotation hFirstShift,
    fs_zfc_support_raw_derives_of_godel_quotation hSecondShift⟩

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
