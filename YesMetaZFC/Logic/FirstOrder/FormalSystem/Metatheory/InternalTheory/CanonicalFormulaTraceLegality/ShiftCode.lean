import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.ShiftTrace
/-!
# 规范公式同步平移的码条件证书
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/--
闭项替换逐参数穿过同步平移 trace 条件。
该定理统一处理末行存在量词、逐行全称量词以及行内全部 binder，供外层三序列存在
见证依次代入时复用。
-/
theorem canonical_project_formula_shift_trace_condition_substitute (cutoff entryDepth leftCode rightCode
      leftCodes rightCodes depths replacement : SetTerm) (sourceId lastIndexId indexId firstPremiseId secondPremiseId
      atomicBaseId : FreeVarId) (hSourceNeLastIndex : sourceId ≠ lastIndexId) (hSourceNeIndex : sourceId ≠ indexId)
    (hSourceNeFirstPremise : sourceId ≠ firstPremiseId) (hSourceNeSecondPremise : sourceId ≠ secondPremiseId) (hSourceFreshAtomicBlock :
      ∀ offset, offset < 8 → sourceId ≠ atomicBaseId + offset) (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement) :
    Formula.substituteFree SetSort.set sourceId replacement (canonical_project_formula_shift_trace_condition
          cutoff entryDepth leftCode rightCode
          leftCodes rightCodes depths
          lastIndexId indexId firstPremiseId secondPremiseId
          atomicBaseId) =
      canonical_project_formula_shift_trace_condition (Term.substituteFree SetSort.set sourceId replacement cutoff)
        (Term.substituteFree SetSort.set sourceId replacement entryDepth) (Term.substituteFree SetSort.set sourceId replacement leftCode)
        (Term.substituteFree SetSort.set sourceId replacement rightCode) (Term.substituteFree SetSort.set sourceId replacement leftCodes)
        (Term.substituteFree SetSort.set sourceId replacement rightCodes) (Term.substituteFree SetSort.set sourceId replacement depths)
        lastIndexId indexId firstPremiseId secondPremiseId
        atomicBaseId := by
  have hReplacementFresh (binderId : FreeVarId) : (SetSort.set, binderId) ∉ Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hLastIndexComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set lastIndexId
            0 subformula) =
        Formula.closeFreeAt SetSort.set lastIndexId
          0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId lastIndexId 0 replacement subformula
      hSourceNeLastIndex hReplacement.1.2 (hReplacementFresh lastIndexId)).symm
  have hIndexComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set indexId
            0 subformula) =
        Formula.closeFreeAt SetSort.set indexId
          0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId indexId 0 replacement subformula
      hSourceNeIndex hReplacement.1.2 (hReplacementFresh indexId)).symm
  have hLineSubstitution :=
    canonical_project_formula_shift_line_condition_with_ids_substitute
      cutoff leftCodes rightCodes depths (x#indexId)
      replacement sourceId firstPremiseId secondPremiseId
      atomicBaseId
      hSourceNeFirstPremise hSourceNeSecondPremise
      hSourceFreshAtomicBlock hReplacement
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  unfold canonical_project_formula_shift_trace_condition
  simp [Formula.substituteFree, Term.substituteFree, set_variable,
    hLastIndexComm, hIndexComm, hLineSubstitution,
    hNumeralFixed, Ne.symm hSourceNeLastIndex,
    Ne.symm hSourceNeIndex]
/--
闭代码项替换逐参数穿过显式八 binder 的完整公式码平移分类器。
该接口把三层序列存在量词与 trace 内部 binder 的捕获规避统一收束为编号新鲜性合同；
四个外部代码参数可以同时更新，供 schema 模板实例化与对象等式运输共同复用。
-/
theorem canonical_project_formula_shift_code_condition_with_ids_substitute_closed (cutoff entryDepth leftCode rightCode replacement
      cutoffResult entryDepthResult leftCodeResult
      rightCodeResult : SetTerm) (sourceId leftCodesId rightCodesId depthsId lastIndexId
      indexId firstPremiseId secondPremiseId
      atomicBaseId : FreeVarId) (hSourceNeLeftCodes : sourceId ≠ leftCodesId) (hSourceNeRightCodes : sourceId ≠ rightCodesId)
    (hSourceNeDepths : sourceId ≠ depthsId) (hSourceNeLastIndex : sourceId ≠ lastIndexId) (hSourceNeIndex : sourceId ≠ indexId)
    (hSourceNeFirstPremise : sourceId ≠ firstPremiseId) (hSourceNeSecondPremise : sourceId ≠ secondPremiseId) (hSourceFreshAtomicBlock :
      ∀ offset, offset < 8 → sourceId ≠ atomicBaseId + offset) (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement) (hCutoffSubstitution :
      Term.substituteFree SetSort.set sourceId replacement cutoff =
        cutoffResult) (hEntryDepthSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          entryDepth =
        entryDepthResult) (hLeftCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement leftCode =
        leftCodeResult) (hRightCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement rightCode =
        rightCodeResult) :
    Formula.substituteFree SetSort.set sourceId replacement (canonical_project_formula_shift_code_condition_with_ids
          cutoff entryDepth leftCode rightCode
          leftCodesId rightCodesId depthsId lastIndexId
          indexId firstPremiseId secondPremiseId atomicBaseId) =
      canonical_project_formula_shift_code_condition_with_ids
        cutoffResult entryDepthResult leftCodeResult rightCodeResult
        leftCodesId rightCodesId depthsId lastIndexId
        indexId firstPremiseId secondPremiseId atomicBaseId := by
  have hReplacementFresh (binderId : FreeVarId) : (SetSort.set, binderId) ∉
        Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hComm (binderId : FreeVarId) (hSourceNeBinder : sourceId ≠ binderId) (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set binderId 0 subformula) =
        Formula.closeFreeAt SetSort.set binderId 0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId binderId 0 replacement subformula
      hSourceNeBinder hReplacement.1.2 (hReplacementFresh binderId)).symm
  have hLeftCodesFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#leftCodesId) =
        x#leftCodesId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeLeftCodes]
  have hRightCodesFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#rightCodesId) =
        x#rightCodesId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeRightCodes]
  have hDepthsFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#depthsId) =
        x#depthsId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeDepths]
  have hTraceSubstitution :
      Formula.substituteFree SetSort.set sourceId replacement (canonical_project_formula_shift_trace_condition
            cutoff entryDepth leftCode rightCode (x#leftCodesId) (x#rightCodesId) (x#depthsId)
            lastIndexId indexId firstPremiseId secondPremiseId
            atomicBaseId) =
        canonical_project_formula_shift_trace_condition
          cutoffResult entryDepthResult leftCodeResult rightCodeResult (x#leftCodesId) (x#rightCodesId) (x#depthsId)
          lastIndexId indexId firstPremiseId secondPremiseId
          atomicBaseId := by
    have hSubstitution :=
      canonical_project_formula_shift_trace_condition_substitute
        cutoff entryDepth leftCode rightCode (x#leftCodesId) (x#rightCodesId) (x#depthsId)
        replacement sourceId lastIndexId indexId
        firstPremiseId secondPremiseId atomicBaseId
        hSourceNeLastIndex hSourceNeIndex
        hSourceNeFirstPremise hSourceNeSecondPremise
        hSourceFreshAtomicBlock hReplacement
    simpa [hCutoffSubstitution, hEntryDepthSubstitution,
      hLeftCodeSubstitution, hRightCodeSubstitution,
      hLeftCodesFixed, hRightCodesFixed, hDepthsFixed] using
      hSubstitution
  unfold canonical_project_formula_shift_code_condition_with_ids
  simp [Formula.substituteFree, Term.substituteFree,
    hCutoffSubstitution, hEntryDepthSubstitution,
    hLeftCodeSubstitution, hRightCodeSubstitution,
    hComm leftCodesId hSourceNeLeftCodes,
    hComm rightCodesId hSourceNeRightCodes,
    hComm depthsId hSourceNeDepths,
    hTraceSubstitution]
/--
连续编号版公式码平移条件允许把额外保留编号作为 cutoff 孔进行闭项代入。
-/
theorem canonical_project_formula_shift_code_condition_from_base_substitute_cutoff (replacement entryDepth leftCode rightCode : SetTerm) (baseId : FreeVarId)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement) (hEntryDepth :
      GodelQuotation.Numbered.CodeBoundary entryDepth) (hLeftCode :
      GodelQuotation.Numbered.CodeBoundary leftCode) (hRightCode :
      GodelQuotation.Numbered.CodeBoundary rightCode) :
    Formula.substituteFree SetSort.set (baseId + 15) replacement (canonical_project_formula_shift_code_condition_with_ids
          (x#(baseId + 15)) entryDepth leftCode rightCode
          baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7)) =
      canonical_project_formula_shift_code_condition_with_ids
        replacement entryDepth leftCode rightCode
        baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7) := by
  have hSourceNe (offset : Nat) (hOffset : offset < 15) :
      baseId + 15 ≠ baseId + offset := by
    intro hEquality
    have hFifteenEq : 15 = offset :=
      Nat.add_left_cancel hEquality
    exact (Nat.ne_of_lt hOffset) hFifteenEq.symm
  have hFixed (term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set (baseId + 15)
          replacement term =
        term :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hTerm (baseId + 15) replacement
  exact
    canonical_project_formula_shift_code_condition_with_ids_substitute_closed (x#(baseId + 15)) entryDepth leftCode rightCode replacement
      replacement entryDepth leftCode rightCode (baseId + 15)
      baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7) (hSourceNe 0 (by omega)) (hSourceNe 1 (by omega))
      (hSourceNe 2 (by omega)) (hSourceNe 3 (by omega)) (hSourceNe 4 (by omega)) (hSourceNe 5 (by omega)) (hSourceNe 6 (by omega)) (by
        intro offset hOffset
        simpa [Nat.add_assoc] using
          hSourceNe (7 + offset) (by
              simpa using Nat.add_lt_add_left hOffset 7))
      hReplacement (by simp [Term.substituteFree, set_variable]) (hFixed entryDepth hEntryDepth) (hFixed leftCode hLeftCode) (hFixed rightCode hRightCode)
/--
连续编号版公式码平移条件允许把额外保留编号作为入口深度孔进行闭项代入。
-/
theorem canonical_project_formula_shift_code_condition_from_base_substitute_entry_depth (cutoff replacement leftCode rightCode : SetTerm) (baseId : FreeVarId)
    (hCutoff :
      GodelQuotation.Numbered.CodeBoundary cutoff) (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement) (hLeftCode :
      GodelQuotation.Numbered.CodeBoundary leftCode) (hRightCode :
      GodelQuotation.Numbered.CodeBoundary rightCode) :
    Formula.substituteFree SetSort.set (baseId + 15) replacement (canonical_project_formula_shift_code_condition_with_ids
          cutoff (x#(baseId + 15)) leftCode rightCode
          baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7)) =
      canonical_project_formula_shift_code_condition_with_ids
        cutoff replacement leftCode rightCode
        baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7) := by
  have hSourceNe (offset : Nat) (hOffset : offset < 15) :
      baseId + 15 ≠ baseId + offset := by
    intro hEquality
    have hFifteenEq : 15 = offset :=
      Nat.add_left_cancel hEquality
    exact (Nat.ne_of_lt hOffset) hFifteenEq.symm
  have hFixed (term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set (baseId + 15)
          replacement term =
        term :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hTerm (baseId + 15) replacement
  exact
    canonical_project_formula_shift_code_condition_with_ids_substitute_closed
      cutoff (x#(baseId + 15)) leftCode rightCode replacement
      cutoff replacement leftCode rightCode (baseId + 15)
      baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7) (hSourceNe 0 (by omega)) (hSourceNe 1 (by omega))
      (hSourceNe 2 (by omega)) (hSourceNe 3 (by omega)) (hSourceNe 4 (by omega)) (hSourceNe 5 (by omega)) (hSourceNe 6 (by omega)) (by
        intro offset hOffset
        simpa [Nat.add_assoc] using
          hSourceNe (7 + offset) (by
              simpa using Nat.add_lt_add_left hOffset 7))
      hReplacement (hFixed cutoff hCutoff) (by simp [Term.substituteFree, set_variable]) (hFixed leftCode hLeftCode) (hFixed rightCode hRightCode)
/--
cutoff 的对象等式可运输连续编号版的完整公式码平移条件。
-/
theorem canonical_project_formula_shift_code_condition_from_base_iff_of_cutoff_equality
    {T : SetTheory} {Γ : Context signature} (left right entryDepth leftCode rightCode : SetTerm) (baseId : FreeVarId)
    (hLeft : GodelQuotation.Numbered.CodeBoundary left) (hRight : GodelQuotation.Numbered.CodeBoundary right) (hEntryDepth :
      GodelQuotation.Numbered.CodeBoundary entryDepth) (hLeftCode :
      GodelQuotation.Numbered.CodeBoundary leftCode) (hRightCode :
      GodelQuotation.Numbered.CodeBoundary rightCode) (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      canonical_project_formula_shift_code_condition_with_ids
          left entryDepth leftCode rightCode
          baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7) ↔ₘ
        canonical_project_formula_shift_code_condition_with_ids
          right entryDepth leftCode rightCode
          baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7) := by
  let sourceId := baseId + 15
  let body :=
    canonical_project_formula_shift_code_condition_with_ids (x#sourceId) entryDepth leftCode rightCode
      baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7)
  have hBody : Formula.Admissible body := by
    simpa [body] using
      canonical_project_formula_shift_code_condition_with_ids_admissible (x#sourceId) entryDepth leftCode rightCode
        baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7) (set_variable_admissible sourceId)
        hEntryDepth.1 hLeftCode.1 hRightCode.1
  have hTransport :=
    Metatheory.Derives.equality_iff_of_equality (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := sourceId) (left := left) (right := right) (body := body)
      hEquality
  change
    Γ ⊢ₘ[T] (Formula.substituteFree SetSort.set sourceId left body ↔ₘ
        Formula.substituteFree SetSort.set sourceId right body)
    at hTransport
  simpa [body, sourceId,
    canonical_project_formula_shift_code_condition_from_base_substitute_cutoff
      left entryDepth leftCode rightCode baseId
      hLeft hEntryDepth hLeftCode hRightCode,
    canonical_project_formula_shift_code_condition_from_base_substitute_cutoff
      right entryDepth leftCode rightCode baseId
      hRight hEntryDepth hLeftCode hRightCode] using
    hTransport
/--
入口深度的对象等式可运输连续编号版的完整公式码平移条件。
-/
theorem canonical_project_formula_shift_code_condition_from_base_iff_of_entry_depth_equality
    {T : SetTheory} {Γ : Context signature} (left right cutoff leftCode rightCode : SetTerm) (baseId : FreeVarId)
    (hLeft : GodelQuotation.Numbered.CodeBoundary left) (hRight : GodelQuotation.Numbered.CodeBoundary right)
    (hCutoff : GodelQuotation.Numbered.CodeBoundary cutoff) (hLeftCode :
      GodelQuotation.Numbered.CodeBoundary leftCode) (hRightCode :
      GodelQuotation.Numbered.CodeBoundary rightCode) (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      canonical_project_formula_shift_code_condition_with_ids
          cutoff left leftCode rightCode
          baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7) ↔ₘ
        canonical_project_formula_shift_code_condition_with_ids
          cutoff right leftCode rightCode
          baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7) := by
  let sourceId := baseId + 15
  let body :=
    canonical_project_formula_shift_code_condition_with_ids
      cutoff (x#sourceId) leftCode rightCode
      baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7)
  have hBody : Formula.Admissible body := by
    simpa [body] using
      canonical_project_formula_shift_code_condition_with_ids_admissible
        cutoff (x#sourceId) leftCode rightCode
        baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7)
        hCutoff.1 (set_variable_admissible sourceId)
        hLeftCode.1 hRightCode.1
  have hTransport :=
    Metatheory.Derives.equality_iff_of_equality (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := sourceId) (left := left) (right := right) (body := body)
      hEquality
  change
    Γ ⊢ₘ[T] (Formula.substituteFree SetSort.set sourceId left body ↔ₘ
        Formula.substituteFree SetSort.set sourceId right body)
    at hTransport
  simpa [body, sourceId,
    canonical_project_formula_shift_code_condition_from_base_substitute_entry_depth
      cutoff left leftCode rightCode baseId
      hCutoff hLeft hLeftCode hRightCode,
    canonical_project_formula_shift_code_condition_from_base_substitute_entry_depth
      cutoff right leftCode rightCode baseId
      hCutoff hRight hLeftCode hRightCode] using
    hTransport
/--
从任意基础编号连续分配同步平移分类器的全部内部 binder，并装配完整公式码关系证书。
-/
theorem canonical_project_formula_shift_code_condition_from_base_derives
    {sourceEntryDepth targetEntryDepth cutoff : Nat}
    {sourceFormula targetFormula : SetFormula}
    {sourceTrace targetTrace : CanonicalProjectTrace} (hSourceTrace :
      canonical_project_hilbert_trace?
        sourceEntryDepth sourceFormula = some sourceTrace) (hTargetTrace :
      canonical_project_hilbert_trace?
        targetEntryDepth targetFormula = some targetTrace) (hShift :
      CanonicalProjectTraceShift cutoff sourceTrace targetTrace) (hCutoffLe : cutoff ≤ sourceEntryDepth) (baseId : FreeVarId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_formula_shift_code_condition_with_ids (numₘ(cutoff)) (numₘ(sourceEntryDepth))
        sourceTrace.rootCode targetTrace.rootCode
        baseId (baseId + 1) (baseId + 2) (baseId + 3) (baseId + 4) (baseId + 5) (baseId + 6) (baseId + 7) := by
  let leftCodesId := baseId
  let rightCodesId := baseId + 1
  let depthsId := baseId + 2
  let lastIndexId := baseId + 3
  let indexId := baseId + 4
  let firstPremiseId := baseId + 5
  let secondPremiseId := baseId + 6
  let atomicBaseId := baseId + 7
  have hOffsetNe (left right : Nat) (hOffsets : left ≠ right) :
      baseId + left ≠ baseId + right := by
    intro hEquality
    exact hOffsets (Nat.add_left_cancel hEquality)
  have hCutoffBoundary :
      GodelQuotation.Numbered.CodeBoundary numₘ(cutoff) :=
    ⟨finite_numeral_term_admissible cutoff,
      finite_numeral_term_freeSupport cutoff⟩
  have hEntryDepthBoundary :
      GodelQuotation.Numbered.CodeBoundary numₘ(sourceEntryDepth) :=
    ⟨finite_numeral_term_admissible sourceEntryDepth,
      finite_numeral_term_freeSupport sourceEntryDepth⟩
  have hSourceRootBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hSourceTrace
  have hTargetRootBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hTargetTrace
  have hSourceBoundary :=
    canonical_project_hilbert_trace_from?_code_sequence_boundary
      hSourceTrace
  have hTargetBoundary :=
    canonical_project_hilbert_trace_from?_code_sequence_boundary
      hTargetTrace
  have hDepthsBoundary :=
    canonical_project_trace_depth_sequence_boundary sourceTrace
  have hFixed (sourceId : FreeVarId) (replacement term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set sourceId replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hCutoffFixed (sourceId : FreeVarId) (replacement : SetTerm) :=
    hFixed sourceId replacement (numₘ(cutoff)) hCutoffBoundary
  have hEntryDepthFixed (sourceId : FreeVarId) (replacement : SetTerm) :=
    hFixed sourceId replacement (numₘ(sourceEntryDepth))
      hEntryDepthBoundary
  have hSourceRootFixed (sourceId : FreeVarId) (replacement : SetTerm) :=
    hFixed sourceId replacement sourceTrace.rootCode
      hSourceRootBoundary
  have hTargetRootFixed (sourceId : FreeVarId) (replacement : SetTerm) :=
    hFixed sourceId replacement targetTrace.rootCode
      hTargetRootBoundary
  have hSourceFixed (sourceId : FreeVarId) (replacement : SetTerm) :=
    hFixed sourceId replacement sourceTrace.code_sequence
      hSourceBoundary
  have hTargetFixed (sourceId : FreeVarId) (replacement : SetTerm) :=
    hFixed sourceId replacement targetTrace.code_sequence
      hTargetBoundary
  have hDepthsFixed (sourceId : FreeVarId) (replacement : SetTerm) :=
    hFixed sourceId replacement sourceTrace.depth_sequence
      hDepthsBoundary
  have hLeftCoreSubstitution :
      Formula.substituteFree SetSort.set leftCodesId
          sourceTrace.code_sequence (canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
            sourceTrace.rootCode targetTrace.rootCode (x#leftCodesId) (x#rightCodesId) (x#depthsId)
            lastIndexId indexId firstPremiseId secondPremiseId
            atomicBaseId) =
        canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
          sourceTrace.rootCode targetTrace.rootCode
          sourceTrace.code_sequence (x#rightCodesId) (x#depthsId)
          lastIndexId indexId firstPremiseId secondPremiseId
          atomicBaseId := by
    have hSubstitution :=
      canonical_project_formula_shift_trace_condition_substitute (numₘ(cutoff)) (numₘ(sourceEntryDepth))
        sourceTrace.rootCode targetTrace.rootCode (x#leftCodesId) (x#rightCodesId) (x#depthsId)
        sourceTrace.code_sequence (sourceId := leftCodesId) (lastIndexId := lastIndexId) (indexId := indexId) (firstPremiseId := firstPremiseId)
        (secondPremiseId := secondPremiseId) (atomicBaseId := atomicBaseId) (hSourceNeLastIndex := by
          simp [leftCodesId, lastIndexId]) (hSourceNeIndex := by
          simp [leftCodesId, indexId]) (hSourceNeFirstPremise := by
          simp [leftCodesId, firstPremiseId]) (hSourceNeSecondPremise := by
          simp [leftCodesId, secondPremiseId]) (hSourceFreshAtomicBlock := by
          intro offset hOffset
          simp [leftCodesId, atomicBaseId, Nat.add_assoc]) (hReplacement := hSourceBoundary)
    simpa [Term.substituteFree, set_variable,
      leftCodesId, rightCodesId, depthsId,
      hCutoffFixed, hEntryDepthFixed,
      hSourceRootFixed, hTargetRootFixed] using hSubstitution
  have hRightCoreSubstitution :
      Formula.substituteFree SetSort.set rightCodesId
          targetTrace.code_sequence (canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
            sourceTrace.rootCode targetTrace.rootCode
            sourceTrace.code_sequence (x#rightCodesId) (x#depthsId)
            lastIndexId indexId firstPremiseId secondPremiseId
            atomicBaseId) =
        canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
          sourceTrace.rootCode targetTrace.rootCode
          sourceTrace.code_sequence targetTrace.code_sequence (x#depthsId)
          lastIndexId indexId firstPremiseId secondPremiseId
          atomicBaseId := by
    have hSubstitution :=
      canonical_project_formula_shift_trace_condition_substitute (numₘ(cutoff)) (numₘ(sourceEntryDepth))
        sourceTrace.rootCode targetTrace.rootCode
        sourceTrace.code_sequence (x#rightCodesId) (x#depthsId)
        targetTrace.code_sequence (sourceId := rightCodesId) (lastIndexId := lastIndexId) (indexId := indexId) (firstPremiseId := firstPremiseId)
        (secondPremiseId := secondPremiseId) (atomicBaseId := atomicBaseId) (hSourceNeLastIndex := by
          simp [rightCodesId, lastIndexId]) (hSourceNeIndex := by
          simp [rightCodesId, indexId]) (hSourceNeFirstPremise := by
          simp [rightCodesId, firstPremiseId]) (hSourceNeSecondPremise := by
          simp [rightCodesId, secondPremiseId]) (hSourceFreshAtomicBlock := by
          intro offset hOffset
          simpa [rightCodesId, atomicBaseId, Nat.add_assoc] using
            hOffsetNe 1 (7 + offset) (by omega)) (hReplacement := hTargetBoundary)
    simpa [Term.substituteFree, set_variable,
      rightCodesId, depthsId,
      hCutoffFixed, hEntryDepthFixed,
      hSourceRootFixed, hTargetRootFixed,
      hSourceFixed] using hSubstitution
  have hDepthsCoreSubstitution :
      Formula.substituteFree SetSort.set depthsId
          sourceTrace.depth_sequence (canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
            sourceTrace.rootCode targetTrace.rootCode
            sourceTrace.code_sequence targetTrace.code_sequence (x#depthsId)
            lastIndexId indexId firstPremiseId secondPremiseId
            atomicBaseId) =
        canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
          sourceTrace.rootCode targetTrace.rootCode
          sourceTrace.code_sequence targetTrace.code_sequence
          sourceTrace.depth_sequence
          lastIndexId indexId firstPremiseId secondPremiseId
          atomicBaseId := by
    have hSubstitution :=
      canonical_project_formula_shift_trace_condition_substitute (numₘ(cutoff)) (numₘ(sourceEntryDepth))
        sourceTrace.rootCode targetTrace.rootCode
        sourceTrace.code_sequence targetTrace.code_sequence (x#depthsId) sourceTrace.depth_sequence (sourceId := depthsId) (lastIndexId := lastIndexId)
        (indexId := indexId) (firstPremiseId := firstPremiseId) (secondPremiseId := secondPremiseId) (atomicBaseId := atomicBaseId) (hSourceNeLastIndex := by
          simp [depthsId, lastIndexId]) (hSourceNeIndex := by
          simp [depthsId, indexId]) (hSourceNeFirstPremise := by
          simp [depthsId, firstPremiseId]) (hSourceNeSecondPremise := by
          simp [depthsId, secondPremiseId]) (hSourceFreshAtomicBlock := by
          intro offset hOffset
          simpa [depthsId, atomicBaseId, Nat.add_assoc] using
            hOffsetNe 2 (7 + offset) (by omega)) (hReplacement := hDepthsBoundary)
    simpa [Term.substituteFree, set_variable, depthsId,
      hCutoffFixed, hEntryDepthFixed,
      hSourceRootFixed, hTargetRootFixed,
      hSourceFixed, hTargetFixed] using hSubstitution
  have hSourceFresh (binderId : FreeVarId) : (SetSort.set, binderId) ∉
        Term.freeSupport sourceTrace.code_sequence := by
    rw [hSourceBoundary.2]
    exact List.not_mem_nil
  have hTargetFresh (binderId : FreeVarId) : (SetSort.set, binderId) ∉
        Term.freeSupport targetTrace.code_sequence := by
    rw [hTargetBoundary.2]
    exact List.not_mem_nil
  have hLeftPastDepths :
      Formula.substituteFree SetSort.set leftCodesId
          sourceTrace.code_sequence (∃ₘ[SetSort.set, depthsId],
            canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
              sourceTrace.rootCode targetTrace.rootCode (x#leftCodesId) (x#rightCodesId) (x#depthsId)
              lastIndexId indexId firstPremiseId secondPremiseId
              atomicBaseId) = (∃ₘ[SetSort.set, depthsId],
          canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
            sourceTrace.rootCode targetTrace.rootCode
            sourceTrace.code_sequence (x#rightCodesId) (x#depthsId)
            lastIndexId indexId firstPremiseId secondPremiseId
            atomicBaseId) := by
    change
      Formula.substituteFree SetSort.set leftCodesId
          sourceTrace.code_sequence (Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set depthsId 0 (canonical_project_formula_shift_trace_condition
                (numₘ(cutoff)) (numₘ(sourceEntryDepth))
                sourceTrace.rootCode targetTrace.rootCode (x#leftCodesId) (x#rightCodesId) (x#depthsId)
                lastIndexId indexId firstPremiseId secondPremiseId
                atomicBaseId))) =
        Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set depthsId 0 (canonical_project_formula_shift_trace_condition
              (numₘ(cutoff)) (numₘ(sourceEntryDepth))
              sourceTrace.rootCode targetTrace.rootCode
              sourceTrace.code_sequence (x#rightCodesId) (x#depthsId)
              lastIndexId indexId firstPremiseId secondPremiseId
              atomicBaseId))
    simp only [Formula.substituteFree]
    apply congrArg (fun formula : SetFormula =>
      Formula.existsE SetSort.set formula)
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set leftCodesId depthsId 0
      sourceTrace.code_sequence _ (by
        simp [leftCodesId, depthsId])
      hSourceBoundary.1.2 (hSourceFresh depthsId)]
    exact congrArg (Formula.closeFreeAt SetSort.set depthsId 0)
      hLeftCoreSubstitution
  have hLeftPastRightDepths :
      Formula.substituteFree SetSort.set leftCodesId
          sourceTrace.code_sequence (∃ₘ[SetSort.set, rightCodesId],
            ∃ₘ[SetSort.set, depthsId],
              canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
                sourceTrace.rootCode targetTrace.rootCode (x#leftCodesId) (x#rightCodesId) (x#depthsId)
                lastIndexId indexId firstPremiseId secondPremiseId
                atomicBaseId) = (∃ₘ[SetSort.set, rightCodesId],
          ∃ₘ[SetSort.set, depthsId],
            canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
              sourceTrace.rootCode targetTrace.rootCode
              sourceTrace.code_sequence (x#rightCodesId) (x#depthsId)
              lastIndexId indexId firstPremiseId secondPremiseId
              atomicBaseId) := by
    change
      Formula.substituteFree SetSort.set leftCodesId
          sourceTrace.code_sequence (Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set rightCodesId 0 (Formula.existsE SetSort.set
                (Formula.closeFreeAt SetSort.set depthsId 0 (canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
                    sourceTrace.rootCode targetTrace.rootCode (x#leftCodesId) (x#rightCodesId) (x#depthsId)
                    lastIndexId indexId firstPremiseId secondPremiseId
                    atomicBaseId))))) =
        Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set rightCodesId 0 (Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set depthsId 0
                (canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
                  sourceTrace.rootCode targetTrace.rootCode
                  sourceTrace.code_sequence (x#rightCodesId) (x#depthsId)
                  lastIndexId indexId firstPremiseId secondPremiseId
                  atomicBaseId))))
    simp only [Formula.substituteFree]
    apply congrArg (fun formula : SetFormula =>
        Formula.existsE SetSort.set formula)
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set leftCodesId rightCodesId 0
      sourceTrace.code_sequence _ (by
        simp [leftCodesId, rightCodesId])
      hSourceBoundary.1.2 (hSourceFresh rightCodesId)]
    exact congrArg (Formula.closeFreeAt SetSort.set rightCodesId 0)
      hLeftPastDepths
  have hRightPastDepths :
      Formula.substituteFree SetSort.set rightCodesId
          targetTrace.code_sequence (∃ₘ[SetSort.set, depthsId],
            canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
              sourceTrace.rootCode targetTrace.rootCode
              sourceTrace.code_sequence (x#rightCodesId) (x#depthsId)
              lastIndexId indexId firstPremiseId secondPremiseId
              atomicBaseId) = (∃ₘ[SetSort.set, depthsId],
          canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
            sourceTrace.rootCode targetTrace.rootCode
            sourceTrace.code_sequence targetTrace.code_sequence (x#depthsId)
            lastIndexId indexId firstPremiseId secondPremiseId
            atomicBaseId) := by
    change
      Formula.substituteFree SetSort.set rightCodesId
          targetTrace.code_sequence (Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set depthsId 0 (canonical_project_formula_shift_trace_condition
                (numₘ(cutoff)) (numₘ(sourceEntryDepth))
                sourceTrace.rootCode targetTrace.rootCode
                sourceTrace.code_sequence (x#rightCodesId) (x#depthsId)
                lastIndexId indexId firstPremiseId secondPremiseId
                atomicBaseId))) =
        Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set depthsId 0 (canonical_project_formula_shift_trace_condition
              (numₘ(cutoff)) (numₘ(sourceEntryDepth))
              sourceTrace.rootCode targetTrace.rootCode
              sourceTrace.code_sequence targetTrace.code_sequence (x#depthsId)
              lastIndexId indexId firstPremiseId secondPremiseId
              atomicBaseId))
    simp only [Formula.substituteFree]
    apply congrArg (fun formula : SetFormula =>
        Formula.existsE SetSort.set formula)
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set rightCodesId depthsId 0
      targetTrace.code_sequence _ (by
        simp [rightCodesId, depthsId])
      hTargetBoundary.1.2 (hTargetFresh depthsId)]
    exact congrArg (Formula.closeFreeAt SetSort.set depthsId 0)
      hRightCoreSubstitution
  have hCutoffOmega :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(cutoff) ∈ₘ ωₘ :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_omega cutoff)
  have hEntryDepthOmega :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(sourceEntryDepth) ∈ₘ ωₘ :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_omega
        sourceEntryDepth)
  have hCutoffOrder :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (numₘ(cutoff) ≐ₘ numₘ(sourceEntryDepth)) ∨ₘ (numₘ(cutoff) ∈ₘ numₘ(sourceEntryDepth)) := by
    by_cases hEqual : cutoff = sourceEntryDepth
    · nd_apply FirstOrder.Derives.disjIntroLeft
      subst sourceEntryDepth
      exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(cutoff))
    · have hLess : cutoff < sourceEntryDepth := by
        omega
      nd_apply FirstOrder.Derives.disjIntroRight
      exact GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
          cutoff sourceEntryDepth hLess)
  have hSourceFormulaCode :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        formula_codeₘ(sourceTrace.rootCode) :=
    GodelQuotation.gq_is_formula_code_of_mem
      sourceTrace.rootCode hSourceRootBoundary.1 (canonical_project_hilbert_trace_from?_root_formula_code_mem
        hSourceTrace)
  have hTargetFormulaCode :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        formula_codeₘ(targetTrace.rootCode) :=
    GodelQuotation.gq_is_formula_code_of_mem
      targetTrace.rootCode hTargetRootBoundary.1 (canonical_project_hilbert_trace_from?_root_formula_code_mem
        hTargetTrace)
  have hCore :=
    canonical_project_formula_shift_trace_condition_derives
      hSourceTrace hTargetTrace hShift
      lastIndexId indexId firstPremiseId secondPremiseId
      atomicBaseId (by
        simp [indexId, firstPremiseId]) (by
        simp [indexId, secondPremiseId]) (by
        intro offset hOffset
        simpa [indexId, atomicBaseId, Nat.add_assoc] using
          hOffsetNe 4 (7 + offset) (by omega)) (by
        simp [firstPremiseId, secondPremiseId])
  unfold canonical_project_formula_shift_code_condition_with_ids
  apply FirstOrder.Derives.conjIntro
  · apply FirstOrder.Derives.conjIntro
    · apply FirstOrder.Derives.conjIntro
      · exact FirstOrder.Derives.conjIntro
          hCutoffOmega hEntryDepthOmega
      · exact hCutoffOrder
    · exact FirstOrder.Derives.conjIntro
        hSourceFormulaCode hTargetFormulaCode
  · nd_apply FirstOrder.Derives.exists_intro
      (term := sourceTrace.code_sequence)
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    rw [hLeftPastRightDepths]
    nd_apply FirstOrder.Derives.exists_intro
      (term := targetTrace.code_sequence)
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    rw [hRightPastDepths]
    nd_apply FirstOrder.Derives.exists_intro
      (term := sourceTrace.depth_sequence)
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    rw [hDepthsCoreSubstitution]
    exact hCore
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
