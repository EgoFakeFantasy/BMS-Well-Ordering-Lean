import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.FormulaLines
/-!
# 规范公式同步平移的逐行与轨迹证书
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/-! ## 同步平移复合行的闭见证装配 -/
/-- 左右码序列共享一个否定前提时，得到同步平移行的否定分支。 -/
private theorem canonical_shift_negation_line_branch_derives_of_witness
    {T : SetTheory} {Γ : Context signature}
    (leftCodes rightCodes depths index premise : SetTerm)
    (firstPremiseId : FreeVarId) (hLeftCodes :
      GodelQuotation.Numbered.CodeBoundary leftCodes) (hRightCodes :
      GodelQuotation.Numbered.CodeBoundary rightCodes) (hDepths :
      GodelQuotation.Numbered.CodeBoundary depths) (hIndex :
      GodelQuotation.Numbered.CodeBoundary index) (hPremise :
      GodelQuotation.Numbered.CodeBoundary premise) (hEarlier : Γ ⊢ₘ[T] premise ∈ₘ index) (hPremiseDomain :
      Γ ⊢ₘ[T] premise ∈ₘ domₘ(leftCodes)) (hDepth :
      Γ ⊢ₘ[T] (depths ·ₘ premise) ≐ₘ (depths ·ₘ index)) (hLeftCode :
      Γ ⊢ₘ[T] (leftCodes ·ₘ index) ≐ₘ
          neg_codeₘ(leftCodes ·ₘ premise)) (hRightCode :
      Γ ⊢ₘ[T] (rightCodes ·ₘ index) ≐ₘ
          neg_codeₘ(rightCodes ·ₘ premise)) :
    Γ ⊢ₘ[T]
      ∃ₘ[SetSort.set, firstPremiseId], ((((x#firstPremiseId ∈ₘ index) ∧ₘ (x#firstPremiseId ∈ₘ domₘ(leftCodes))) ∧ₘ ((depths ·ₘ x#firstPremiseId) ≐ₘ
              (depths ·ₘ index))) ∧ₘ (((leftCodes ·ₘ index) ≐ₘ
              neg_codeₘ(leftCodes ·ₘ x#firstPremiseId)) ∧ₘ ((rightCodes ·ₘ index) ≐ₘ
              neg_codeₘ(rightCodes ·ₘ x#firstPremiseId)))) := by
  have hFixed (variableId : FreeVarId) (replacement term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set variableId replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hLeftCodesFixed :=
    hFixed firstPremiseId premise leftCodes hLeftCodes
  have hRightCodesFixed :=
    hFixed firstPremiseId premise rightCodes hRightCodes
  have hDepthsFixed :=
    hFixed firstPremiseId premise depths hDepths
  have hIndexFixed :=
    hFixed firstPremiseId premise index hIndex
  nd_apply FirstOrder.Derives.exists_intro
    (term := premise)
  rw [Formula.openAt_closeFreeAt_eq_substituteFree]
  simpa [Formula.substituteFree, Term.substituteFree,
    set_variable,
    hLeftCodesFixed, hRightCodesFixed,
    hDepthsFixed, hIndexFixed] using (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro
          hEarlier hPremiseDomain)
        hDepth) (FirstOrder.Derives.conjIntro hLeftCode hRightCode))
/--
左右码序列共享两个互异的蕴含前提时，得到同步平移行的蕴含分支。
-/
private theorem canonical_shift_implication_line_branch_derives_of_witnesses
    {T : SetTheory} {Γ : Context signature}
    (leftCodes rightCodes depths index leftPremise rightPremise : SetTerm)
    (firstPremiseId secondPremiseId : FreeVarId)
    (hPremiseIds : firstPremiseId ≠ secondPremiseId) (hLeftCodes :
      GodelQuotation.Numbered.CodeBoundary leftCodes) (hRightCodes :
      GodelQuotation.Numbered.CodeBoundary rightCodes) (hDepths :
      GodelQuotation.Numbered.CodeBoundary depths) (hIndex :
      GodelQuotation.Numbered.CodeBoundary index) (hLeftPremise :
      GodelQuotation.Numbered.CodeBoundary leftPremise) (hRightPremise :
      GodelQuotation.Numbered.CodeBoundary rightPremise) (hLeftEarlier : Γ ⊢ₘ[T] leftPremise ∈ₘ index) (hLeftPremiseDomain :
      Γ ⊢ₘ[T] leftPremise ∈ₘ domₘ(leftCodes)) (hRightEarlier : Γ ⊢ₘ[T] rightPremise ∈ₘ index) (hRightPremiseDomain :
      Γ ⊢ₘ[T] rightPremise ∈ₘ domₘ(leftCodes)) (hLeftDepth :
      Γ ⊢ₘ[T] (depths ·ₘ leftPremise) ≐ₘ (depths ·ₘ index)) (hRightDepth :
      Γ ⊢ₘ[T] (depths ·ₘ rightPremise) ≐ₘ (depths ·ₘ index)) (hLeftCode :
      Γ ⊢ₘ[T] (leftCodes ·ₘ index) ≐ₘ
          imp_codeₘ(
            leftCodes ·ₘ leftPremise,
            leftCodes ·ₘ rightPremise)) (hRightCode :
      Γ ⊢ₘ[T] (rightCodes ·ₘ index) ≐ₘ
          imp_codeₘ(
            rightCodes ·ₘ leftPremise,
            rightCodes ·ₘ rightPremise)) :
    Γ ⊢ₘ[T]
      ∃ₘ[SetSort.set, firstPremiseId],
        ∃ₘ[SetSort.set, secondPremiseId], (((((x#firstPremiseId ∈ₘ index) ∧ₘ (x#firstPremiseId ∈ₘ domₘ(leftCodes))) ∧ₘ ((x#secondPremiseId ∈ₘ index) ∧ₘ
                (x#secondPremiseId ∈ₘ domₘ(leftCodes)))) ∧ₘ (((depths ·ₘ x#firstPremiseId) ≐ₘ (depths ·ₘ index)) ∧ₘ ((depths ·ₘ x#secondPremiseId) ≐ₘ
                (depths ·ₘ index)))) ∧ₘ (((leftCodes ·ₘ index) ≐ₘ
                imp_codeₘ(
                  leftCodes ·ₘ x#firstPremiseId,
                  leftCodes ·ₘ x#secondPremiseId)) ∧ₘ ((rightCodes ·ₘ index) ≐ₘ
                imp_codeₘ(
                  rightCodes ·ₘ x#firstPremiseId,
                  rightCodes ·ₘ x#secondPremiseId)))) := by
  have hFixed (variableId : FreeVarId) (replacement term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set variableId replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hLeftCodesFirstFixed :=
    hFixed firstPremiseId leftPremise leftCodes hLeftCodes
  have hRightCodesFirstFixed :=
    hFixed firstPremiseId leftPremise rightCodes hRightCodes
  have hDepthsFirstFixed :=
    hFixed firstPremiseId leftPremise depths hDepths
  have hIndexFirstFixed :=
    hFixed firstPremiseId leftPremise index hIndex
  have hLeftCodesSecondFixed :=
    hFixed secondPremiseId rightPremise leftCodes hLeftCodes
  have hRightCodesSecondFixed :=
    hFixed secondPremiseId rightPremise rightCodes hRightCodes
  have hDepthsSecondFixed :=
    hFixed secondPremiseId rightPremise depths hDepths
  have hIndexSecondFixed :=
    hFixed secondPremiseId rightPremise index hIndex
  have hLeftPremiseSecondFixed :=
    hFixed secondPremiseId rightPremise
      leftPremise hLeftPremise
  have hSecondPremiseNeFirst :
      secondPremiseId ≠ firstPremiseId :=
    Ne.symm hPremiseIds
  nd_apply FirstOrder.Derives.exists_intro
    (term := leftPremise)
  rw [Formula.openAt_closeFreeAt_eq_substituteFree]
  nd_apply FirstOrder.Derives.exists_intro
    (term := rightPremise)
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set firstPremiseId secondPremiseId 0
    leftPremise _ hPremiseIds hLeftPremise.1.2 (by
      rw [hLeftPremise.2]
      exact List.not_mem_nil)]
  rw [Formula.openAt_closeFreeAt_eq_substituteFree]
  simpa [Formula.substituteFree, Term.substituteFree,
    set_variable,
    hLeftCodesFirstFixed, hRightCodesFirstFixed,
    hDepthsFirstFixed, hIndexFirstFixed,
    hLeftCodesSecondFixed, hRightCodesSecondFixed,
    hDepthsSecondFixed, hIndexSecondFixed,
    hLeftPremiseSecondFixed,
    hPremiseIds, hSecondPremiseNeFirst] using (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro
          (FirstOrder.Derives.conjIntro
            hLeftEarlier hLeftPremiseDomain) (FirstOrder.Derives.conjIntro
            hRightEarlier hRightPremiseDomain)) (FirstOrder.Derives.conjIntro
          hLeftDepth hRightDepth)) (FirstOrder.Derives.conjIntro hLeftCode hRightCode))
/-- 左右码序列共享一个全称前提时，得到同步平移行的全称分支。 -/
private theorem canonical_shift_universal_line_branch_derives_of_witness
    {T : SetTheory} {Γ : Context signature}
    (leftCodes rightCodes depths index premise : SetTerm)
    (firstPremiseId : FreeVarId) (hLeftCodes :
      GodelQuotation.Numbered.CodeBoundary leftCodes) (hRightCodes :
      GodelQuotation.Numbered.CodeBoundary rightCodes) (hDepths :
      GodelQuotation.Numbered.CodeBoundary depths) (hIndex :
      GodelQuotation.Numbered.CodeBoundary index) (hPremise :
      GodelQuotation.Numbered.CodeBoundary premise) (hEarlier : Γ ⊢ₘ[T] premise ∈ₘ index) (hPremiseDomain :
      Γ ⊢ₘ[T] premise ∈ₘ domₘ(leftCodes)) (hDepth :
      Γ ⊢ₘ[T] (depths ·ₘ premise) ≐ₘ
          Sₘ(depths ·ₘ index)) (hLeftCode :
      Γ ⊢ₘ[T] (leftCodes ·ₘ index) ≐ₘ
          forall_codeₘ(
            canonical_binder_variable_code_term (depths ·ₘ index),
            leftCodes ·ₘ premise)) (hRightCode :
      Γ ⊢ₘ[T] (rightCodes ·ₘ index) ≐ₘ
          forall_codeₘ(
            canonical_binder_variable_code_term (Sₘ(depths ·ₘ index)),
            rightCodes ·ₘ premise)) :
    Γ ⊢ₘ[T]
      ∃ₘ[SetSort.set, firstPremiseId], ((((x#firstPremiseId ∈ₘ index) ∧ₘ (x#firstPremiseId ∈ₘ domₘ(leftCodes))) ∧ₘ ((depths ·ₘ x#firstPremiseId) ≐ₘ
              Sₘ(depths ·ₘ index))) ∧ₘ (((leftCodes ·ₘ index) ≐ₘ
              forall_codeₘ(
                canonical_binder_variable_code_term (depths ·ₘ index),
                leftCodes ·ₘ x#firstPremiseId)) ∧ₘ ((rightCodes ·ₘ index) ≐ₘ
              forall_codeₘ(
                canonical_binder_variable_code_term (Sₘ(depths ·ₘ index)),
                rightCodes ·ₘ x#firstPremiseId)))) := by
  have hFixed (variableId : FreeVarId) (replacement term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set variableId replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hLeftCodesFixed :=
    hFixed firstPremiseId premise leftCodes hLeftCodes
  have hRightCodesFixed :=
    hFixed firstPremiseId premise rightCodes hRightCodes
  have hDepthsFixed :=
    hFixed firstPremiseId premise depths hDepths
  have hIndexFixed :=
    hFixed firstPremiseId premise index hIndex
  have hTwoFixed :
      Term.substituteFree SetSort.set firstPremiseId
          premise (numₘ(2)) =
        numₘ(2) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  nd_apply FirstOrder.Derives.exists_intro
    (term := premise)
  rw [Formula.openAt_closeFreeAt_eq_substituteFree]
  simpa [Formula.substituteFree, Term.substituteFree,
    set_variable,
    hLeftCodesFixed, hRightCodesFixed,
    hDepthsFixed, hIndexFixed, hTwoFixed] using (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro
          hEarlier hPremiseDomain)
        hDepth) (FirstOrder.Derives.conjIntro hLeftCode hRightCode))
/-! ## cutoff-shift 双轨迹的具体逐行合法性 -/
/--
一对同步 cutoff-shift 轨迹在同一 numeral 位置满足对象语言逐行条件。
源轨迹提供共享的深度序列；目标轨迹只提供右侧公式码序列。逐行关系保证两侧采用
同一构造标签和同一前提位置，两个外部行合同则分别恢复左右码形状。
-/
private theorem canonical_project_formula_shift_line_condition_at_numeral
    {sourceEntryDepth targetEntryDepth cutoff index : Nat}
    {sourceFormula targetFormula : SetFormula}
    {sourceTrace targetTrace : CanonicalProjectTrace}
    {sourceRow : CanonicalProjectTraceRow} (hSourceTrace :
      canonical_project_hilbert_trace?
        sourceEntryDepth sourceFormula = some sourceTrace) (hTargetTrace :
      canonical_project_hilbert_trace?
        targetEntryDepth targetFormula = some targetTrace) (hShift :
      CanonicalProjectTraceShift cutoff sourceTrace targetTrace) (hSourceRow :
      sourceTrace.rows[index]? = some sourceRow) (firstPremiseId secondPremiseId atomicBaseId : FreeVarId) (hPremiseIds : firstPremiseId ≠ secondPremiseId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_formula_shift_line_condition_with_ids (numₘ(cutoff))
        sourceTrace.code_sequence targetTrace.code_sequence
        sourceTrace.depth_sequence (numₘ(index))
        firstPremiseId secondPremiseId atomicBaseId := by
  rcases CanonicalProjectTraceShift.row_at hShift hSourceRow with
    ⟨targetRow, hTargetRow, hRowShift⟩
  have hCutoff :
      GodelQuotation.Numbered.CodeBoundary numₘ(cutoff) :=
    ⟨finite_numeral_term_admissible cutoff,
      finite_numeral_term_freeSupport cutoff⟩
  have hLeftCodes :
      GodelQuotation.Numbered.CodeBoundary
        sourceTrace.code_sequence :=
    canonical_project_hilbert_trace_from?_code_sequence_boundary
      hSourceTrace
  have hRightCodes :
      GodelQuotation.Numbered.CodeBoundary
        targetTrace.code_sequence :=
    canonical_project_hilbert_trace_from?_code_sequence_boundary
      hTargetTrace
  have hDepths :
      GodelQuotation.Numbered.CodeBoundary
        sourceTrace.depth_sequence :=
    canonical_project_trace_depth_sequence_boundary sourceTrace
  have hIndex :
      GodelQuotation.Numbered.CodeBoundary numₘ(index) :=
    ⟨finite_numeral_term_admissible index,
      finite_numeral_term_freeSupport index⟩
  have hCurrentLeftBoundary :
      GodelQuotation.Numbered.CodeBoundary (sourceTrace.code_sequence ·ₘ numₘ(index)) :=
    canonical_project_hilbert_trace?_code_application_boundary
      hSourceTrace
  have hCurrentRightBoundary :
      GodelQuotation.Numbered.CodeBoundary (targetTrace.code_sequence ·ₘ numₘ(index)) :=
    canonical_project_hilbert_trace?_code_application_boundary
      hTargetTrace
  have hCurrentDepthBoundary :
      GodelQuotation.Numbered.CodeBoundary (sourceTrace.depth_sequence ·ₘ numₘ(index)) :=
    canonical_project_trace_depth_application_boundary
      sourceTrace index
  have hSourceRowCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary sourceRow.code :=
    canonical_project_hilbert_trace_from?_row_code_boundary
      hSourceTrace (List.mem_of_getElem? hSourceRow)
  have hTargetRowCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary targetRow.code :=
    canonical_project_hilbert_trace_from?_row_code_boundary
      hTargetTrace (List.mem_of_getElem? hTargetRow)
  have hCurrentLeft :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.code_sequence ·ₘ numₘ(index)) ≐ₘ
          sourceRow.code :=
    canonical_project_hilbert_trace?_code_value_of_getElem?
      hSourceTrace hSourceRow
  have hCurrentRight :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (targetTrace.code_sequence ·ₘ numₘ(index)) ≐ₘ
          targetRow.code :=
    canonical_project_hilbert_trace?_code_value_of_getElem?
      hTargetTrace hTargetRow
  have hCurrentDepth :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.depth_sequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(sourceRow.depth) :=
    canonical_project_trace_depth_value_of_getElem? hSourceRow
  have hEarlierObject (premise : Nat) (hEarlier : premise < index) :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(premise) ∈ₘ numₘ(index) :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
        premise index hEarlier)
  have hIndexBound : index < sourceTrace.rows.length := (List.getElem?_eq_some_iff.mp hSourceRow).1
  have hPremiseDomainObject (premise : Nat) (hEarlier : premise < index) :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(premise) ∈ₘ
          domₘ(sourceTrace.code_sequence) := by
    have hNumeral :
        ⊢ₘ[GodelQuotation.godel_quotation_theory]
          numₘ(premise) ∈ₘ
            numₘ(sourceTrace.rows.length) :=
      GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
          premise sourceTrace.rows.length (by omega))
    exact FirstOrder.Derives.iffElimLeft (membership_right_iff_of_equality (numₘ(premise)) (domₘ(sourceTrace.code_sequence)) (numₘ(sourceTrace.rows.length))
        (finite_numeral_term_admissible premise) (domain_term_admissible
          sourceTrace.code_sequence hLeftCodes.1) (finite_numeral_term_admissible
          sourceTrace.rows.length) (canonical_project_hilbert_trace?_code_sequence_domain
          hSourceTrace))
      hNumeral
  have hSourceEvidence :=
    canonical_project_hilbert_trace?_rows_evidence
      hSourceTrace hSourceRow
  have hTargetEvidence :=
    canonical_project_hilbert_trace?_rows_evidence
      hTargetTrace hTargetRow
  have hLineAdmissible :=
    canonical_project_formula_shift_line_condition_with_ids_admissible (numₘ(cutoff))
      sourceTrace.code_sequence targetTrace.code_sequence
      sourceTrace.depth_sequence (numₘ(index))
      firstPremiseId secondPremiseId atomicBaseId
      hCutoff.1 hLeftCodes.1 hRightCodes.1 hDepths.1 hIndex.1
  rw [canonical_project_formula_shift_line_condition_with_ids] at hLineAdmissible
  have hAtomicAdmissible :=
    Formula.Admissible.disj_left hLineAdmissible
  have hNegationBranchAdmissible :=
    Formula.Admissible.disj_left <|
      Formula.Admissible.disj_right hLineAdmissible
  have hImplicationBranchAdmissible :=
    Formula.Admissible.disj_left <|
      Formula.Admissible.disj_right <|
        Formula.Admissible.disj_right hLineAdmissible
  have hUniversalBranchAdmissible :=
    Formula.Admissible.disj_right <|
      Formula.Admissible.disj_right <|
        Formula.Admissible.disj_right hLineAdmissible
  cases hRowShift with
  | atomic depth sourceRowFormula targetRowFormula
      kind leftDepth rightDepth =>
      rcases hSourceEvidence.atomic_view rfl with
        ⟨hLeftDepth, hRightDepth, _⟩
      have hAtomicExplicit :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            canonical_project_atomic_shift_condition_with_ids (numₘ(cutoff)) (sourceTrace.depth_sequence ·ₘ numₘ(index))
               (sourceTrace.code_sequence ·ₘ numₘ(index)) (targetTrace.code_sequence ·ₘ numₘ(index))
               atomicBaseId (atomicBaseId + 1) (atomicBaseId + 2) (atomicBaseId + 3) (atomicBaseId + 4) (atomicBaseId + 6) :=
        canonical_project_atomic_shift_condition_with_base_of_equalities_derives
          cutoff depth (CanonicalProjectTrace.canonical_project_atom_code
            kind leftDepth rightDepth) (CanonicalProjectTrace.canonical_project_atom_code
            kind (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth)) (sourceTrace.depth_sequence ·ₘ numₘ(index))
           (sourceTrace.code_sequence ·ₘ numₘ(index)) (targetTrace.code_sequence ·ₘ numₘ(index))
           atomicBaseId
          hSourceRowCodeBoundary hTargetRowCodeBoundary
          hCurrentDepthBoundary hCurrentLeftBoundary
          hCurrentRightBoundary
           hCurrentDepth hCurrentLeft hCurrentRight (canonical_project_atomic_shift_condition_with_base_numeral_derives
             cutoff depth leftDepth rightDepth kind atomicBaseId
             hLeftDepth hRightDepth)
      unfold canonical_project_formula_shift_line_condition_with_ids
      exact FirstOrder.Derives.disjIntroLeft hAtomicExplicit
  | negation depth sourcePremise targetPremise
      sourceBodyFormula targetBodyFormula
      sourceBodyCode targetBodyCode hPremise =>
      subst targetPremise
      rcases hSourceEvidence.negation_view rfl with
        ⟨sourcePremiseRow, _, hEarlierRaw,
          hSourcePremiseGet, hSourcePremiseDepthCode,
          hSourceShape⟩
      rcases hTargetEvidence.negation_view rfl with
        ⟨targetPremiseRow, _, _,
          hTargetPremiseGet, _, hTargetShape⟩
      have hSourcePremiseRow :
          sourceTrace.rows[sourcePremise]? =
            some sourcePremiseRow := by
        simpa using hSourcePremiseGet
      have hTargetPremiseRow :
          targetTrace.rows[sourcePremise]? =
            some targetPremiseRow := by
        simpa using hTargetPremiseGet
      have hEarlier : sourcePremise < index := by
        simpa using hEarlierRaw
      have hEarlierPoint :=
        hEarlierObject sourcePremise hEarlier
      have hPremiseDomainPoint :=
        hPremiseDomainObject sourcePremise hEarlier
      have hSourcePremiseCode :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.code_sequence ·ₘ
                numₘ(sourcePremise)) ≐ₘ
              sourcePremiseRow.code :=
        canonical_project_hilbert_trace?_code_value_of_getElem?
          hSourceTrace hSourcePremiseRow
      have hTargetPremiseCode :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (targetTrace.code_sequence ·ₘ
                numₘ(sourcePremise)) ≐ₘ
              targetPremiseRow.code :=
        canonical_project_hilbert_trace?_code_value_of_getElem?
          hTargetTrace hTargetPremiseRow
      have hSourcePremiseCodeBoundary :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hSourceTrace (List.mem_of_getElem? hSourcePremiseRow)
      have hTargetPremiseCodeBoundary :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hTargetTrace (List.mem_of_getElem? hTargetPremiseRow)
      have hSourcePremiseApplication :=
        canonical_project_hilbert_trace?_code_application_boundary (index := sourcePremise) hSourceTrace
      have hTargetPremiseApplication :=
        canonical_project_hilbert_trace?_code_application_boundary (index := sourcePremise) hTargetTrace
      have hPremiseDepth :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.depth_sequence ·ₘ
                numₘ(sourcePremise)) ≐ₘ
              numₘ(depth) := by
        have hValue :=
          canonical_project_trace_depth_value_of_getElem?
            hSourcePremiseRow
        simpa [hSourcePremiseDepthCode] using hValue
      have hDepthAgreement :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.depth_sequence ·ₘ
                numₘ(sourcePremise)) ≐ₘ (sourceTrace.depth_sequence ·ₘ numₘ(index)) :=
        Metatheory.Derives.equality_join
          hPremiseDepth hCurrentDepth
      rw [hSourceShape] at hCurrentLeft
      rw [hTargetShape] at hCurrentRight
      have hSourceNegationCongruence :=
        canonical_negation_code_term_congr_of_equality (sourceTrace.code_sequence ·ₘ numₘ(sourcePremise))
          sourcePremiseRow.code
          hSourcePremiseApplication.1
          hSourcePremiseCodeBoundary.1 hSourcePremiseCode
      have hTargetNegationCongruence :=
        canonical_negation_code_term_congr_of_equality (targetTrace.code_sequence ·ₘ numₘ(sourcePremise))
          targetPremiseRow.code
          hTargetPremiseApplication.1
          hTargetPremiseCodeBoundary.1 hTargetPremiseCode
      have hSourceCodeAgreement :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.code_sequence ·ₘ numₘ(index)) ≐ₘ
              neg_codeₘ(
                sourceTrace.code_sequence ·ₘ
                  numₘ(sourcePremise)) := by
        exact Metatheory.Derives.equality_join
          hCurrentLeft hSourceNegationCongruence
      have hTargetCodeAgreement :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (targetTrace.code_sequence ·ₘ numₘ(index)) ≐ₘ
              neg_codeₘ(
                targetTrace.code_sequence ·ₘ
                  numₘ(sourcePremise)) := by
        exact Metatheory.Derives.equality_join
          hCurrentRight hTargetNegationCongruence
      have hNegation :=
        canonical_shift_negation_line_branch_derives_of_witness
          sourceTrace.code_sequence targetTrace.code_sequence
          sourceTrace.depth_sequence (numₘ(index)) (numₘ(sourcePremise))
          firstPremiseId
          hLeftCodes hRightCodes hDepths hIndex
          ⟨finite_numeral_term_admissible sourcePremise,
            finite_numeral_term_freeSupport sourcePremise⟩
          hEarlierPoint hPremiseDomainPoint hDepthAgreement
          hSourceCodeAgreement hTargetCodeAgreement
      unfold canonical_project_formula_shift_line_condition_with_ids
      exact FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroLeft hNegation)
  | implication depth
      sourceLeftPremise sourceRightPremise
      targetLeftPremise targetRightPremise
      sourceLeftFormula sourceRightFormula
      targetLeftFormula targetRightFormula
      sourceLeftCode sourceRightCode
      targetLeftCode targetRightCode
      hLeftPremise hRightPremise =>
      subst targetLeftPremise
      subst targetRightPremise
      rcases hSourceEvidence.implication_view rfl with
        ⟨sourceLeftRow, sourceRightRow,
          _, hLeftEarlierRaw, _, hRightEarlierRaw,
          hSourceLeftGet, hSourceRightGet,
          hSourceLeftDepthCode, hSourceRightDepthCode,
          hSourceShape⟩
      rcases hTargetEvidence.implication_view rfl with
        ⟨targetLeftRow, targetRightRow,
          _, _, _, _,
          hTargetLeftGet, hTargetRightGet,
          _, _, hTargetShape⟩
      have hLeftEarlier : sourceLeftPremise < index := by
        simpa using hLeftEarlierRaw
      have hRightEarlier : sourceRightPremise < index := by
        simpa using hRightEarlierRaw
      have hSourceLeftRow :
          sourceTrace.rows[sourceLeftPremise]? =
            some sourceLeftRow := by
        simpa using hSourceLeftGet
      have hSourceRightRow :
          sourceTrace.rows[sourceRightPremise]? =
            some sourceRightRow := by
        simpa using hSourceRightGet
      have hTargetLeftRow :
          targetTrace.rows[sourceLeftPremise]? =
            some targetLeftRow := by
        simpa using hTargetLeftGet
      have hTargetRightRow :
          targetTrace.rows[sourceRightPremise]? =
            some targetRightRow := by
        simpa using hTargetRightGet
      have hLeftEarlierPoint :=
        hEarlierObject sourceLeftPremise hLeftEarlier
      have hLeftPremiseDomainPoint :=
        hPremiseDomainObject sourceLeftPremise hLeftEarlier
      have hRightEarlierPoint :=
        hEarlierObject sourceRightPremise hRightEarlier
      have hRightPremiseDomainPoint :=
        hPremiseDomainObject sourceRightPremise hRightEarlier
      have hSourceLeftCode :=
        canonical_project_hilbert_trace?_code_value_of_getElem?
          hSourceTrace hSourceLeftRow
      have hSourceRightCode :=
        canonical_project_hilbert_trace?_code_value_of_getElem?
          hSourceTrace hSourceRightRow
      have hTargetLeftCode :=
        canonical_project_hilbert_trace?_code_value_of_getElem?
          hTargetTrace hTargetLeftRow
      have hTargetRightCode :=
        canonical_project_hilbert_trace?_code_value_of_getElem?
          hTargetTrace hTargetRightRow
      have hSourceLeftCodeBoundary :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hSourceTrace (List.mem_of_getElem? hSourceLeftRow)
      have hSourceRightCodeBoundary :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hSourceTrace (List.mem_of_getElem? hSourceRightRow)
      have hTargetLeftCodeBoundary :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hTargetTrace (List.mem_of_getElem? hTargetLeftRow)
      have hTargetRightCodeBoundary :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hTargetTrace (List.mem_of_getElem? hTargetRightRow)
      have hSourceLeftApplication :=
        canonical_project_hilbert_trace?_code_application_boundary (index := sourceLeftPremise) hSourceTrace
      have hSourceRightApplication :=
        canonical_project_hilbert_trace?_code_application_boundary (index := sourceRightPremise) hSourceTrace
      have hTargetLeftApplication :=
        canonical_project_hilbert_trace?_code_application_boundary (index := sourceLeftPremise) hTargetTrace
      have hTargetRightApplication :=
        canonical_project_hilbert_trace?_code_application_boundary (index := sourceRightPremise) hTargetTrace
      have hSourceLeftDepth :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            (sourceTrace.depth_sequence ·ₘ
              numₘ(sourceLeftPremise)) ≐ₘ numₘ(depth) := by
        have hValue :=
          canonical_project_trace_depth_value_of_getElem?
            hSourceLeftRow
        simpa [hSourceLeftDepthCode] using hValue
      have hSourceRightDepth :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            (sourceTrace.depth_sequence ·ₘ
              numₘ(sourceRightPremise)) ≐ₘ numₘ(depth) := by
        have hValue :=
          canonical_project_trace_depth_value_of_getElem?
            hSourceRightRow
        simpa [hSourceRightDepthCode] using hValue
      have hLeftDepthAgreement :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.depth_sequence ·ₘ
                numₘ(sourceLeftPremise)) ≐ₘ (sourceTrace.depth_sequence ·ₘ numₘ(index)) :=
        Metatheory.Derives.equality_join
          hSourceLeftDepth hCurrentDepth
      have hRightDepthAgreement :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.depth_sequence ·ₘ
                numₘ(sourceRightPremise)) ≐ₘ (sourceTrace.depth_sequence ·ₘ numₘ(index)) :=
        Metatheory.Derives.equality_join
          hSourceRightDepth hCurrentDepth
      rw [hSourceShape] at hCurrentLeft
      rw [hTargetShape] at hCurrentRight
      have hSourceImplicationCongruence :=
        canonical_implication_code_term_congr_of_equalities (sourceTrace.code_sequence ·ₘ
            numₘ(sourceLeftPremise))
          sourceLeftRow.code (sourceTrace.code_sequence ·ₘ
            numₘ(sourceRightPremise))
          sourceRightRow.code
          hSourceLeftApplication.1 hSourceLeftCodeBoundary.1
          hSourceRightApplication.1 hSourceRightCodeBoundary.1
          hSourceLeftCode hSourceRightCode
      have hTargetImplicationCongruence :=
        canonical_implication_code_term_congr_of_equalities (targetTrace.code_sequence ·ₘ
            numₘ(sourceLeftPremise))
          targetLeftRow.code (targetTrace.code_sequence ·ₘ
            numₘ(sourceRightPremise))
          targetRightRow.code
          hTargetLeftApplication.1 hTargetLeftCodeBoundary.1
          hTargetRightApplication.1 hTargetRightCodeBoundary.1
          hTargetLeftCode hTargetRightCode
      have hSourceCodeAgreement :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.code_sequence ·ₘ numₘ(index)) ≐ₘ
              imp_codeₘ(
                sourceTrace.code_sequence ·ₘ
                  numₘ(sourceLeftPremise),
                sourceTrace.code_sequence ·ₘ
                  numₘ(sourceRightPremise)) :=
        Metatheory.Derives.equality_join
          hCurrentLeft hSourceImplicationCongruence
      have hTargetCodeAgreement :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (targetTrace.code_sequence ·ₘ numₘ(index)) ≐ₘ
              imp_codeₘ(
                targetTrace.code_sequence ·ₘ
                  numₘ(sourceLeftPremise),
                targetTrace.code_sequence ·ₘ
                  numₘ(sourceRightPremise)) :=
        Metatheory.Derives.equality_join
          hCurrentRight hTargetImplicationCongruence
      have hImplication :=
        canonical_shift_implication_line_branch_derives_of_witnesses
          sourceTrace.code_sequence targetTrace.code_sequence
          sourceTrace.depth_sequence (numₘ(index)) (numₘ(sourceLeftPremise)) (numₘ(sourceRightPremise))
          firstPremiseId secondPremiseId hPremiseIds
          hLeftCodes hRightCodes hDepths hIndex
          ⟨finite_numeral_term_admissible sourceLeftPremise,
            finite_numeral_term_freeSupport sourceLeftPremise⟩
          ⟨finite_numeral_term_admissible sourceRightPremise,
            finite_numeral_term_freeSupport sourceRightPremise⟩
          hLeftEarlierPoint hLeftPremiseDomainPoint
          hRightEarlierPoint hRightPremiseDomainPoint
          hLeftDepthAgreement hRightDepthAgreement
          hSourceCodeAgreement hTargetCodeAgreement
      unfold canonical_project_formula_shift_line_condition_with_ids
      exact FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.disjIntroLeft hImplication))
  | universal depth sourcePremise targetPremise
      sourceBodyFormula targetBodyFormula
      sourceBodyCode targetBodyCode hPremise =>
      subst targetPremise
      rcases hSourceEvidence.universal_view rfl with
        ⟨sourcePremiseRow, _, hEarlierRaw,
          hSourcePremiseGet, hSourcePremiseDepthCode,
          hSourceShape⟩
      rcases hTargetEvidence.universal_view rfl with
        ⟨targetPremiseRow, _, _,
          hTargetPremiseGet, _, hTargetShape⟩
      have hEarlier : sourcePremise < index := by
        simpa using hEarlierRaw
      have hSourcePremiseRow :
          sourceTrace.rows[sourcePremise]? =
            some sourcePremiseRow := by
        simpa using hSourcePremiseGet
      have hTargetPremiseRow :
          targetTrace.rows[sourcePremise]? =
            some targetPremiseRow := by
        simpa using hTargetPremiseGet
      have hEarlierPoint :=
        hEarlierObject sourcePremise hEarlier
      have hPremiseDomainPoint :=
        hPremiseDomainObject sourcePremise hEarlier
      have hSourcePremiseCode :=
        canonical_project_hilbert_trace?_code_value_of_getElem?
          hSourceTrace hSourcePremiseRow
      have hTargetPremiseCode :=
        canonical_project_hilbert_trace?_code_value_of_getElem?
          hTargetTrace hTargetPremiseRow
      have hSourcePremiseCodeBoundary :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hSourceTrace (List.mem_of_getElem? hSourcePremiseRow)
      have hTargetPremiseCodeBoundary :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hTargetTrace (List.mem_of_getElem? hTargetPremiseRow)
      have hSourcePremiseApplication :=
        canonical_project_hilbert_trace?_code_application_boundary (index := sourcePremise) hSourceTrace
      have hTargetPremiseApplication :=
        canonical_project_hilbert_trace?_code_application_boundary (index := sourcePremise) hTargetTrace
      have hPremiseDepth :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            (sourceTrace.depth_sequence ·ₘ
              numₘ(sourcePremise)) ≐ₘ numₘ(depth + 1) := by
        have hValue :=
          canonical_project_trace_depth_value_of_getElem?
            hSourcePremiseRow
        simpa [hSourcePremiseDepthCode] using hValue
      have hPremiseDepthSuccessor :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.depth_sequence ·ₘ
                numₘ(sourcePremise)) ≐ₘ
              Sₘ(numₘ(depth)) := by
        simpa [finite_numeral_term] using hPremiseDepth
      have hCurrentSuccessor :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            Sₘ(sourceTrace.depth_sequence ·ₘ numₘ(index)) ≐ₘ
              Sₘ(numₘ(depth)) :=
        successor_term_congr_of_equality (sourceTrace.depth_sequence ·ₘ numₘ(index)) (numₘ(depth))
          hCurrentDepthBoundary.1 (finite_numeral_term_admissible depth)
          hCurrentDepth
      have hCurrentSuccessorApplication :=
        successor_term_admissible _
          hCurrentDepthBoundary.1
      have hCurrentSuccessorSymm :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            Sₘ(numₘ(depth)) ≐ₘ
              Sₘ(sourceTrace.depth_sequence ·ₘ numₘ(index)) :=
        Metatheory.Derives.equality_symm
          hCurrentSuccessor
      have hDepthAgreement :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.depth_sequence ·ₘ
                numₘ(sourcePremise)) ≐ₘ
              Sₘ(sourceTrace.depth_sequence ·ₘ numₘ(index)) :=
        Metatheory.Derives.equality_trans
          hPremiseDepthSuccessor hCurrentSuccessorSymm
      rw [hSourceShape] at hCurrentLeft
      rw [hTargetShape] at hCurrentRight
      have hDepthCurrentSymm :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(depth) ≐ₘ (sourceTrace.depth_sequence ·ₘ numₘ(index)) :=
        Metatheory.Derives.equality_symm
          hCurrentDepth
      have hLeftBinderNumeral :=
        canonical_binder_variable_code_numeral_derives depth
      have hLeftBinderNumeralToCurrent :=
        canonical_binder_variable_code_term_congr_of_equality (numₘ(depth)) (sourceTrace.depth_sequence ·ₘ numₘ(index)) (finite_numeral_term_admissible depth)
          hCurrentDepthBoundary.1 hDepthCurrentSymm
      have hLeftNamedCode :=
        variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name depth))
      have hLeftCanonicalCurrentCode :=
        canonical_binder_variable_code_term_admissible _
          hCurrentDepthBoundary.1
      have hLeftBinderCode :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth) ≐ₘ
              canonical_binder_variable_code_term (sourceTrace.depth_sequence ·ₘ numₘ(index)) :=
        Metatheory.Derives.equality_trans
          hLeftBinderNumeral hLeftBinderNumeralToCurrent
      have hSourcePremiseCodeSymm :=
        Metatheory.Derives.equality_symm
          hSourcePremiseCode
      have hLeftUniversalCongruence :=
        canonical_universal_code_term_congr_of_equalities (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth))
          (canonical_binder_variable_code_term (sourceTrace.depth_sequence ·ₘ numₘ(index)))
          sourcePremiseRow.code (sourceTrace.code_sequence ·ₘ numₘ(sourcePremise))
          hLeftNamedCode hLeftCanonicalCurrentCode
          hSourcePremiseCodeBoundary.1
          hSourcePremiseApplication.1
          hLeftBinderCode hSourcePremiseCodeSymm
      have hSourceCodeAgreement :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (sourceTrace.code_sequence ·ₘ numₘ(index)) ≐ₘ
              forall_codeₘ(
                canonical_binder_variable_code_term (sourceTrace.depth_sequence ·ₘ numₘ(index)),
                sourceTrace.code_sequence ·ₘ
                  numₘ(sourcePremise)) :=
        Metatheory.Derives.equality_trans
          hCurrentLeft hLeftUniversalCongruence
      have hTargetBinderNumeral :=
        canonical_binder_variable_code_numeral_derives (depth + 1)
      have hNumeralSuccessorToCurrent :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(depth + 1) ≐ₘ
              Sₘ(sourceTrace.depth_sequence ·ₘ numₘ(index)) := by
        simpa [finite_numeral_term] using hCurrentSuccessorSymm
      have hTargetBinderNumeralToCurrent :=
        canonical_binder_variable_code_term_congr_of_equality (numₘ(depth + 1)) (Sₘ(sourceTrace.depth_sequence ·ₘ numₘ(index)))
          (finite_numeral_term_admissible (depth + 1))
          hCurrentSuccessorApplication
          hNumeralSuccessorToCurrent
      have hTargetNamedCode :=
        variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name (depth + 1)))
      have hTargetCanonicalCurrentCode :=
        canonical_binder_variable_code_term_admissible _
          hCurrentSuccessorApplication
      have hTargetBinderCode :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name (depth + 1)) ≐ₘ
              canonical_binder_variable_code_term (Sₘ(sourceTrace.depth_sequence ·ₘ numₘ(index))) :=
        Metatheory.Derives.equality_trans
          hTargetBinderNumeral hTargetBinderNumeralToCurrent
      have hTargetPremiseCodeSymm :=
        Metatheory.Derives.equality_symm
          hTargetPremiseCode
      have hTargetUniversalCongruence :=
        canonical_universal_code_term_congr_of_equalities (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name (depth + 1)))
          (canonical_binder_variable_code_term (Sₘ(sourceTrace.depth_sequence ·ₘ numₘ(index))))
          targetPremiseRow.code (targetTrace.code_sequence ·ₘ numₘ(sourcePremise))
          hTargetNamedCode hTargetCanonicalCurrentCode
          hTargetPremiseCodeBoundary.1
          hTargetPremiseApplication.1
          hTargetBinderCode hTargetPremiseCodeSymm
      have hTargetCodeAgreement :
          ⊢ₘ[GodelQuotation.godel_quotation_theory] (targetTrace.code_sequence ·ₘ numₘ(index)) ≐ₘ
              forall_codeₘ(
                canonical_binder_variable_code_term (Sₘ(sourceTrace.depth_sequence ·ₘ numₘ(index))),
                targetTrace.code_sequence ·ₘ
                  numₘ(sourcePremise)) :=
        Metatheory.Derives.equality_trans
          hCurrentRight hTargetUniversalCongruence
      have hUniversal :=
        canonical_shift_universal_line_branch_derives_of_witness
          sourceTrace.code_sequence targetTrace.code_sequence
          sourceTrace.depth_sequence (numₘ(index)) (numₘ(sourcePremise))
          firstPremiseId
          hLeftCodes hRightCodes hDepths hIndex
          ⟨finite_numeral_term_admissible sourcePremise,
            finite_numeral_term_freeSupport sourcePremise⟩
          hEarlierPoint hPremiseDomainPoint hDepthAgreement
          hSourceCodeAgreement hTargetCodeAgreement
      unfold canonical_project_formula_shift_line_condition_with_ids
      exact FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.disjIntroRight hUniversal))
/-! ## cutoff-shift 行条件的索引替换与全称装配 -/
/--
对全部内部 binder 新鲜的 admissible 替换逐参数穿过同步平移行条件。
源变量可以出现在 cutoff、三条序列或索引项的任意位置；唯一限制是它不能与行条件
内部的前提 binder 和八元原子 binder 块冲突。
-/
theorem
    canonical_project_formula_shift_line_condition_with_ids_substitute_of_fresh (cutoff leftCodes rightCodes depths index replacement : SetTerm)
    (sourceId firstPremiseId secondPremiseId atomicBaseId : FreeVarId) (hSourceNeFirstPremise : sourceId ≠ firstPremiseId)
    (hSourceNeSecondPremise : sourceId ≠ secondPremiseId) (hSourceFreshAtomicBlock :
      ∀ offset, offset < 8 → sourceId ≠ atomicBaseId + offset) (hReplacement : Term.Admissible replacement SetSort.set) (hReplacementFreshFirstPremise :
      (SetSort.set, firstPremiseId) ∉
        Term.freeSupport replacement) (hReplacementFreshSecondPremise : (SetSort.set, secondPremiseId) ∉
        Term.freeSupport replacement) (hReplacementFreshAtomicBlock :
      ∀ offset, offset < 8 → (SetSort.set, atomicBaseId + offset) ∉
          Term.freeSupport replacement) :
    Formula.substituteFree SetSort.set sourceId replacement (canonical_project_formula_shift_line_condition_with_ids
          cutoff leftCodes rightCodes depths index
          firstPremiseId secondPremiseId atomicBaseId) =
      canonical_project_formula_shift_line_condition_with_ids (Term.substituteFree SetSort.set sourceId replacement cutoff)
        (Term.substituteFree SetSort.set sourceId replacement leftCodes) (Term.substituteFree SetSort.set sourceId replacement rightCodes)
        (Term.substituteFree SetSort.set sourceId replacement depths) (Term.substituteFree SetSort.set sourceId replacement index)
        firstPremiseId secondPremiseId atomicBaseId := by
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hFirstPremiseNeSource :
      firstPremiseId ≠ sourceId :=
    Ne.symm hSourceNeFirstPremise
  have hSecondPremiseNeSource :
      secondPremiseId ≠ sourceId :=
    Ne.symm hSourceNeSecondPremise
  have hFirstPremiseComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set firstPremiseId
            0 subformula) =
        Formula.closeFreeAt SetSort.set firstPremiseId
          0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId firstPremiseId 0 replacement subformula
      hSourceNeFirstPremise hReplacement.2
      hReplacementFreshFirstPremise).symm
  have hSecondPremiseComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set secondPremiseId
            0 subformula) =
        Formula.closeFreeAt SetSort.set secondPremiseId
          0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId secondPremiseId 0 replacement subformula
      hSourceNeSecondPremise hReplacement.2
      hReplacementFreshSecondPremise).symm
  have hAtomicSubstitution :=
    canonical_project_atomic_shift_condition_with_ids_substitute_of_fresh
      cutoff (depths ·ₘ index) (leftCodes ·ₘ index) (rightCodes ·ₘ index)
      replacement sourceId
      atomicBaseId (atomicBaseId + 1) (atomicBaseId + 2) (atomicBaseId + 3) (atomicBaseId + 4) (atomicBaseId + 6) (by
        simpa using hSourceFreshAtomicBlock 0 (by decide)) (hSourceFreshAtomicBlock 1 (by decide)) (hSourceFreshAtomicBlock 2 (by decide))
      (hSourceFreshAtomicBlock 3 (by decide)) (hSourceFreshAtomicBlock 4 (by decide)) (hSourceFreshAtomicBlock 5 (by decide))
      (hSourceFreshAtomicBlock 6 (by decide)) (hSourceFreshAtomicBlock 7 (by decide))
      hReplacement (by
        simpa using hReplacementFreshAtomicBlock 0 (by decide)) (hReplacementFreshAtomicBlock 1 (by decide)) (hReplacementFreshAtomicBlock 2 (by decide))
      (hReplacementFreshAtomicBlock 3 (by decide)) (hReplacementFreshAtomicBlock 4 (by decide)) (hReplacementFreshAtomicBlock 5 (by decide))
      (hReplacementFreshAtomicBlock 6 (by decide)) (hReplacementFreshAtomicBlock 7 (by decide))
  unfold canonical_project_formula_shift_line_condition_with_ids
  simp only [Formula.substituteFree]
  rw [hAtomicSubstitution]
  simp [Formula.substituteFree, Term.substituteFree, set_variable,
    hFirstPremiseComm, hSecondPremiseComm,
    hNumeralFixed, hFirstPremiseNeSource,
    hSecondPremiseNeSource]
/--
闭项替换逐参数穿过显式编号的同步平移行条件。
-/
theorem canonical_project_formula_shift_line_condition_with_ids_substitute (cutoff leftCodes rightCodes depths index replacement : SetTerm)
    (sourceId firstPremiseId secondPremiseId atomicBaseId : FreeVarId) (hSourceNeFirstPremise : sourceId ≠ firstPremiseId)
    (hSourceNeSecondPremise : sourceId ≠ secondPremiseId) (hSourceFreshAtomicBlock :
      ∀ offset, offset < 8 → sourceId ≠ atomicBaseId + offset) (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement) :
    Formula.substituteFree SetSort.set sourceId replacement (canonical_project_formula_shift_line_condition_with_ids
          cutoff leftCodes rightCodes depths index
          firstPremiseId secondPremiseId atomicBaseId) =
      canonical_project_formula_shift_line_condition_with_ids (Term.substituteFree SetSort.set sourceId replacement cutoff)
        (Term.substituteFree SetSort.set sourceId replacement leftCodes) (Term.substituteFree SetSort.set sourceId replacement rightCodes)
        (Term.substituteFree SetSort.set sourceId replacement depths) (Term.substituteFree SetSort.set sourceId replacement index)
        firstPremiseId secondPremiseId atomicBaseId := by
  apply
    canonical_project_formula_shift_line_condition_with_ids_substitute_of_fresh
      cutoff leftCodes rightCodes depths index replacement
      sourceId firstPremiseId secondPremiseId atomicBaseId
      hSourceNeFirstPremise hSourceNeSecondPremise
      hSourceFreshAtomicBlock hReplacement.1
  · rw [hReplacement.2]
    exact List.not_mem_nil
  · rw [hReplacement.2]
    exact List.not_mem_nil
  · intro offset hOffset
    rw [hReplacement.2]
    exact List.not_mem_nil
/--
闭项替换逐参数穿过显式编号的同步平移行条件。
原子分支使用一个长度为八的连续 binder 块；复合分支只使用两个前提 binder。
把这两组捕获规避条件集中在此，可使具体 numeral 行沿对象索引等式稳定运输。
-/
theorem canonical_project_formula_shift_line_condition_with_ids_substitute_closed (cutoff leftCodes rightCodes depths replacement : SetTerm)
    (indexId firstPremiseId secondPremiseId atomicBaseId : FreeVarId) (hIndexNeFirstPremise : indexId ≠ firstPremiseId)
    (hIndexNeSecondPremise : indexId ≠ secondPremiseId) (hIndexFreshAtomicBlock :
      ∀ offset, offset < 8 → indexId ≠ atomicBaseId + offset) (hCutoff : GodelQuotation.Numbered.CodeBoundary cutoff)
    (hLeftCodes : GodelQuotation.Numbered.CodeBoundary leftCodes) (hRightCodes : GodelQuotation.Numbered.CodeBoundary rightCodes)
    (hDepths : GodelQuotation.Numbered.CodeBoundary depths) (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement) :
    Formula.substituteFree SetSort.set indexId replacement (canonical_project_formula_shift_line_condition_with_ids
          cutoff leftCodes rightCodes depths (x#indexId)
          firstPremiseId secondPremiseId atomicBaseId) =
      canonical_project_formula_shift_line_condition_with_ids
        cutoff leftCodes rightCodes depths replacement
        firstPremiseId secondPremiseId atomicBaseId := by
  have hReplacementFresh (binderId : FreeVarId) : (SetSort.set, binderId) ∉ Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hFixed (term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set indexId replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hCutoffFixed := hFixed cutoff hCutoff
  have hLeftCodesFixed := hFixed leftCodes hLeftCodes
  have hRightCodesFixed := hFixed rightCodes hRightCodes
  have hDepthsFixed := hFixed depths hDepths
  have hPointSubstitution :
      Term.substituteFree SetSort.set indexId replacement (x#indexId) =
        replacement := by
    simp [Term.substituteFree, set_variable]
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set indexId replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hFirstPremiseNeIndex :
      firstPremiseId ≠ indexId :=
    Ne.symm hIndexNeFirstPremise
  have hSecondPremiseNeIndex :
      secondPremiseId ≠ indexId :=
    Ne.symm hIndexNeSecondPremise
  have hFirstPremiseComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set indexId replacement (Formula.closeFreeAt SetSort.set firstPremiseId
            0 subformula) =
        Formula.closeFreeAt SetSort.set firstPremiseId
          0 (Formula.substituteFree SetSort.set indexId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set indexId firstPremiseId 0 replacement subformula
      hIndexNeFirstPremise hReplacement.1.2 (hReplacementFresh firstPremiseId)).symm
  have hSecondPremiseComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set indexId replacement (Formula.closeFreeAt SetSort.set secondPremiseId
            0 subformula) =
        Formula.closeFreeAt SetSort.set secondPremiseId
          0 (Formula.substituteFree SetSort.set indexId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set indexId secondPremiseId 0 replacement subformula
      hIndexNeSecondPremise hReplacement.1.2 (hReplacementFresh secondPremiseId)).symm
  have hAtomicSubstitution :=
    canonical_project_atomic_shift_condition_with_ids_substitute_closed
      cutoff (depths ·ₘ x#indexId) (leftCodes ·ₘ x#indexId) (rightCodes ·ₘ x#indexId)
      replacement indexId
      atomicBaseId (atomicBaseId + 1) (atomicBaseId + 2) (atomicBaseId + 3) (atomicBaseId + 4) (atomicBaseId + 6) (by
        simpa using hIndexFreshAtomicBlock 0 (by decide)) (hIndexFreshAtomicBlock 1 (by decide)) (hIndexFreshAtomicBlock 2 (by decide))
      (hIndexFreshAtomicBlock 3 (by decide)) (hIndexFreshAtomicBlock 4 (by decide)) (hIndexFreshAtomicBlock 5 (by decide))
      (hIndexFreshAtomicBlock 6 (by decide)) (hIndexFreshAtomicBlock 7 (by decide))
      hReplacement
  unfold canonical_project_formula_shift_line_condition_with_ids
  simp only [Formula.substituteFree]
  rw [hAtomicSubstitution]
  simp [Formula.substituteFree, Term.substituteFree, set_variable,
    hFirstPremiseComm, hSecondPremiseComm,
    hCutoffFixed, hLeftCodesFixed, hRightCodesFixed,
    hDepthsFixed, hPointSubstitution, hNumeralFixed,
    hFirstPremiseNeIndex, hSecondPremiseNeIndex]
/--
把具体 numeral 处的同步平移行证书沿对象索引等式运输到自由索引变量。
左端以同一变量替换自身，右端由闭项替换定理规范化；因此运输过程不再依赖自动
fresh 编号的重新计算。
-/
private theorem canonical_project_formula_shift_line_condition_with_ids_of_index_equality (cutoff leftCodes rightCodes depths : SetTerm)
    (indexId firstPremiseId secondPremiseId atomicBaseId : FreeVarId) (hIndexNeFirstPremise : indexId ≠ firstPremiseId)
    (hIndexNeSecondPremise : indexId ≠ secondPremiseId) (hIndexFreshAtomicBlock :
      ∀ offset, offset < 8 → indexId ≠ atomicBaseId + offset) (hCutoff : GodelQuotation.Numbered.CodeBoundary cutoff)
    (hLeftCodes : GodelQuotation.Numbered.CodeBoundary leftCodes) (hRightCodes : GodelQuotation.Numbered.CodeBoundary rightCodes)
    (hDepths : GodelQuotation.Numbered.CodeBoundary depths) (index : Nat) (hConcrete :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_formula_shift_line_condition_with_ids
          cutoff leftCodes rightCodes depths (numₘ(index))
          firstPremiseId secondPremiseId atomicBaseId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory] ((x#indexId) ≐ₘ numₘ(index)) ⟶ₘ
        canonical_project_formula_shift_line_condition_with_ids
          cutoff leftCodes rightCodes depths (x#indexId)
          firstPremiseId secondPremiseId atomicBaseId := by
  let point : SetTerm := x#indexId
  let body : SetFormula :=
    canonical_project_formula_shift_line_condition_with_ids
      cutoff leftCodes rightCodes depths point
      firstPremiseId secondPremiseId atomicBaseId
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  have hPoint : Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hNumeral :
      GodelQuotation.Numbered.CodeBoundary numₘ(index) :=
    ⟨finite_numeral_term_admissible index,
      finite_numeral_term_freeSupport index⟩
  have hBodyAdmissible : Formula.Admissible body := by
    dsimp [body]
    exact canonical_project_formula_shift_line_condition_with_ids_admissible
      cutoff leftCodes rightCodes depths point
      firstPremiseId secondPremiseId atomicBaseId
      hCutoff.1 hLeftCodes.1 hRightCodes.1 hDepths.1 hPoint
  have hEquality :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := GodelQuotation.godel_quotation_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := GodelQuotation.godel_quotation_theory) (Γ := Γ) (sort := SetSort.set) (eigen := indexId)
      (left := point) (right := numₘ(index)) (body := body)
      hEquality
  have hNumeralSubstitution :=
    canonical_project_formula_shift_line_condition_with_ids_substitute_closed
      cutoff leftCodes rightCodes depths (numₘ(index))
      indexId firstPremiseId secondPremiseId atomicBaseId
      hIndexNeFirstPremise hIndexNeSecondPremise
      hIndexFreshAtomicBlock
      hCutoff hLeftCodes hRightCodes hDepths hNumeral
  have hTransport :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_formula_shift_line_condition_with_ids
            cutoff leftCodes rightCodes depths point
            firstPremiseId secondPremiseId atomicBaseId ↔ₘ
          canonical_project_formula_shift_line_condition_with_ids
            cutoff leftCodes rightCodes depths (numₘ(index))
            firstPremiseId secondPremiseId atomicBaseId := by
    simpa only [body, point, Formula.substituteFree_self,
      hNumeralSubstitution] using hIff
  have hConcreteInContext :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_formula_shift_line_condition_with_ids
          cutoff leftCodes rightCodes depths (numₘ(index))
          firstPremiseId secondPremiseId atomicBaseId :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hConcrete
  have hResult :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_formula_shift_line_condition_with_ids
          cutoff leftCodes rightCodes depths point
          firstPremiseId secondPremiseId atomicBaseId :=
    FirstOrder.Derives.iffElimLeft hTransport hConcreteInContext
  have hImplication :=
    FirstOrder.Derives.impIntro hResult
  simpa [Γ, equality, body, point] using hImplication
/--
一对成功的同步 cutoff-shift 轨迹在源标准序列定义域上逐行满足对象分类条件。
有限 numeral 消去读取源轨迹的每一行；`CanonicalProjectTraceShift.row_at` 同步恢复
目标行，最后由显式编号的索引等式运输定理回到受量化索引。
-/
theorem canonical_project_formula_shift_line_conditions_derives
    {sourceEntryDepth targetEntryDepth cutoff : Nat}
    {sourceFormula targetFormula : SetFormula}
    {sourceTrace targetTrace : CanonicalProjectTrace} (hSourceTrace :
      canonical_project_hilbert_trace?
        sourceEntryDepth sourceFormula = some sourceTrace) (hTargetTrace :
      canonical_project_hilbert_trace?
        targetEntryDepth targetFormula = some targetTrace) (hShift :
      CanonicalProjectTraceShift cutoff sourceTrace targetTrace) (indexId firstPremiseId secondPremiseId atomicBaseId : FreeVarId)
    (hIndexNeFirstPremise : indexId ≠ firstPremiseId) (hIndexNeSecondPremise : indexId ≠ secondPremiseId) (hIndexFreshAtomicBlock :
      ∀ offset, offset < 8 → indexId ≠ atomicBaseId + offset) (hPremiseIds : firstPremiseId ≠ secondPremiseId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      ∀ₘ[SetSort.set, indexId], ((x#indexId ∈ₘ domₘ(sourceTrace.code_sequence)) ⟶ₘ
          canonical_project_formula_shift_line_condition_with_ids (numₘ(cutoff))
            sourceTrace.code_sequence targetTrace.code_sequence
            sourceTrace.depth_sequence (x#indexId)
            firstPremiseId secondPremiseId atomicBaseId) := by
  let cutoffTerm : SetTerm := numₘ(cutoff)
  let source := sourceTrace.code_sequence
  let target := targetTrace.code_sequence
  let depths := sourceTrace.depth_sequence
  let point : SetTerm := x#indexId
  let conclusion : SetFormula :=
    canonical_project_formula_shift_line_condition_with_ids
      cutoffTerm source target depths point
      firstPremiseId secondPremiseId atomicBaseId
  let stepBody : SetFormula := (point ∈ₘ domₘ(source)) ⟶ₘ conclusion
  have hCutoff :
      GodelQuotation.Numbered.CodeBoundary cutoffTerm := by
    simpa [cutoffTerm] using (show GodelQuotation.Numbered.CodeBoundary numₘ(cutoff) from
        ⟨finite_numeral_term_admissible cutoff,
          finite_numeral_term_freeSupport cutoff⟩)
  have hSource :
      GodelQuotation.Numbered.CodeBoundary source := by
    simpa [source] using
      canonical_project_hilbert_trace_from?_code_sequence_boundary
        hSourceTrace
  have hTarget :
      GodelQuotation.Numbered.CodeBoundary target := by
    simpa [target] using
      canonical_project_hilbert_trace_from?_code_sequence_boundary
        hTargetTrace
  have hDepths :
      GodelQuotation.Numbered.CodeBoundary depths := by
    simpa [depths] using
      canonical_project_trace_depth_sequence_boundary sourceTrace
  have hPoint : Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hConclusionCheck :
      Formula.CheckCertificate conclusion :=
    Formula.check_admissible_complete <| by
      dsimp [conclusion]
      exact canonical_project_formula_shift_line_condition_with_ids_admissible
        cutoffTerm source target depths point
        firstPremiseId secondPremiseId atomicBaseId
        hCutoff.1 hSource.1 hTarget.1 hDepths.1 hPoint
  have hCases :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        GodelQuotation.stdseq_numeral_member_condition
            sourceTrace.rows.length point ⟶ₘ
          conclusion := by
    refine GodelQuotation.stdseq_numeral_member_condition_elim_of_theory
      sourceTrace.rows.length point conclusion
      (hConclusionCheck := hConclusionCheck) ?_
    intro rowIndex hRowIndex
    let row : CanonicalProjectTraceRow :=
      sourceTrace.rows[rowIndex]
    have hRow :
        sourceTrace.rows[rowIndex]? = some row :=
      List.getElem?_eq_some_iff.mpr
        ⟨hRowIndex, rfl⟩
    have hConcrete :
        ⊢ₘ[GodelQuotation.godel_quotation_theory]
          canonical_project_formula_shift_line_condition_with_ids
            cutoffTerm source target depths (numₘ(rowIndex))
            firstPremiseId secondPremiseId atomicBaseId := by
      simpa [cutoffTerm, source, target, depths] using
        canonical_project_formula_shift_line_condition_at_numeral
          hSourceTrace hTargetTrace hShift hRow
          firstPremiseId secondPremiseId atomicBaseId
          hPremiseIds
    simpa [conclusion, point, cutoffTerm, source, target, depths] using
      canonical_project_formula_shift_line_condition_with_ids_of_index_equality
        cutoffTerm source target depths
        indexId firstPremiseId secondPremiseId atomicBaseId
        hIndexNeFirstPremise hIndexNeSecondPremise
        hIndexFreshAtomicBlock
        hCutoff hSource hTarget hDepths rowIndex hConcrete
  have hNumeralIff :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (point ∈ₘ numₘ(sourceTrace.rows.length)) ↔ₘ
          GodelQuotation.stdseq_numeral_member_condition
            sourceTrace.rows.length point :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.stdseq_numeral_member_iff
        sourceTrace.rows.length point hPoint)
  have hDomain :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        domₘ(source) ≐ₘ numₘ(sourceTrace.rows.length) := by
    simpa [source] using
      canonical_project_hilbert_trace?_code_sequence_domain
        hSourceTrace
  have hDomainIff :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (point ∈ₘ domₘ(source)) ↔ₘ (point ∈ₘ numₘ(sourceTrace.rows.length)) :=
    membership_right_iff_of_equality
      point (domₘ(source)) (numₘ(sourceTrace.rows.length))
      hPoint (domain_term_admissible source hSource.1) (finite_numeral_term_admissible sourceTrace.rows.length)
      hDomain
  have hMembershipAdmissible :
      Formula.Admissible (point ∈ₘ domₘ(source)) :=
    membership_formula_admissible hPoint (domain_term_admissible source hSource.1)
  have hStepOpen :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] stepBody := by
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ domₘ(source)] ⊢ₘ[
          GodelQuotation.godel_quotation_theory]
          point ∈ₘ domₘ(source) :=
      FirstOrder.Derives.assumption (by simp)
    have hNumeralMembership :
        [point ∈ₘ domₘ(source)] ⊢ₘ[
          GodelQuotation.godel_quotation_theory]
          point ∈ₘ numₘ(sourceTrace.rows.length) :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hDomainIff)
        hMembership
    have hCondition :
        [point ∈ₘ domₘ(source)] ⊢ₘ[
          GodelQuotation.godel_quotation_theory]
          GodelQuotation.stdseq_numeral_member_condition
            sourceTrace.rows.length point :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hNumeralIff)
        hNumeralMembership
    simpa [stepBody] using
      FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
        hCondition
  have hTheoryFresh :
      ∀ formula,
        GodelQuotation.godel_quotation_theory formula → (SetSort.set, indexId) ∉ Formula.freeSupport formula := by
    intro theoryFormula hTheoryFormula
    rw [(GodelQuotation.godel_quotation_theory_sentence
      hTheoryFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := GodelQuotation.godel_quotation_theory) (Γ := []) (sort := SetSort.set) (eigen := indexId)
      hTheoryFresh (by simp) hStepOpen
  simpa [stepBody, conclusion, point, cutoffTerm,
    source, target, depths] using hGeneralized
/--
公式级 cutoff-shift 的两次成功 quotation 在对象理论中给出等长的根代码定义域。
Lean 只计算两条 token 列表的长度相同；左右根代码到标准序列的等式以及最终定义域
等式都在 Gödel quotation 理论内部证明。
-/
theorem canonical_project_formula_shift_root_code_domains_eq
    {cutoff entryDepth : Nat}
    {sourceFormula targetFormula : SetFormula}
    {sourceTrace targetTrace : CanonicalProjectTrace} (hShift :
      CanonicalProjectFormulaShift cutoff entryDepth
        sourceFormula targetFormula) (hSourceTrace :
      canonical_project_hilbert_trace?
        entryDepth sourceFormula = some sourceTrace) (hTargetTrace :
      canonical_project_hilbert_trace? (entryDepth + 1) targetFormula = some targetTrace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      domₘ(sourceTrace.rootCode) ≐ₘ
        domₘ(targetTrace.rootCode) := by
  have hSourceCode :=
    canonical_project_hilbert_trace?_root_quote hSourceTrace
  have hTargetCode :=
    canonical_project_hilbert_trace?_root_quote hTargetTrace
  rcases hShift.quote_hilbert_tokens_exists with
    ⟨sourceTokens, targetTokens, hSourceTokens, hTargetTokens⟩
  have hLengths :
      sourceTokens.length = targetTokens.length :=
    hShift.quote_hilbert_tokens_length_eq
      hSourceTokens hTargetTokens
  have hSourceEquality :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        sourceTrace.rootCode ≐ₘ
          GodelQuotation.standard_token_sequence sourceTokens :=
    GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
      GodelQuotation.free_name
      GodelQuotation.bound_name
      hSourceTokens hSourceCode
  have hTargetEquality :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        targetTrace.rootCode ≐ₘ
          GodelQuotation.standard_token_sequence targetTokens :=
    GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
      GodelQuotation.free_name
      GodelQuotation.bound_name
      hTargetTokens hTargetCode
  have hSourceBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hSourceTrace
  have hTargetBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hTargetTrace
  have hSourceDomain :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        domₘ(sourceTrace.rootCode) ≐ₘ
          numₘ(sourceTokens.length) :=
    GodelQuotation.gq_domain_eq_length_of_eq_standard_token_sequence_of_theory (fun _ hAxiom => hAxiom)
      sourceTrace.rootCode sourceTokens
      hSourceEquality
      (hCode := Term.check_admissible_complete hSourceBoundary.1)
  have hTargetDomain :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        domₘ(targetTrace.rootCode) ≐ₘ
          numₘ(sourceTokens.length) := by
    simpa [hLengths] using
      GodelQuotation.gq_domain_eq_length_of_eq_standard_token_sequence_of_theory (fun _ hAxiom => hAxiom)
        targetTrace.rootCode targetTokens
        hTargetEquality
        (hCode := Term.check_admissible_complete hTargetBoundary.1)
  have hTargetDomainSymm :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(sourceTokens.length) ≐ₘ
          domₘ(targetTrace.rootCode) :=
    Metatheory.Derives.equality_symm hTargetDomain
  exact Metatheory.Derives.equality_trans (middle := numₘ(sourceTokens.length)) hSourceDomain hTargetDomainSymm
/-- 同步 cutoff-shift 的左右公式码标准序列具有相同的对象定义域。 -/
theorem canonical_project_formula_shift_code_sequence_domains_eq
    {sourceEntryDepth targetEntryDepth cutoff : Nat}
    {sourceFormula targetFormula : SetFormula}
    {sourceTrace targetTrace : CanonicalProjectTrace} (hSourceTrace :
      canonical_project_hilbert_trace?
        sourceEntryDepth sourceFormula = some sourceTrace) (hTargetTrace :
      canonical_project_hilbert_trace?
        targetEntryDepth targetFormula = some targetTrace) (hShift :
      CanonicalProjectTraceShift cutoff sourceTrace targetTrace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      domₘ(sourceTrace.code_sequence) ≐ₘ
        domₘ(targetTrace.code_sequence) := by
  have hSourceDomain :=
    canonical_project_hilbert_trace?_code_sequence_domain
      hSourceTrace
  have hTargetDomain :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        domₘ(targetTrace.code_sequence) ≐ₘ
          numₘ(sourceTrace.rows.length) := by
    simpa [CanonicalProjectTraceShift.rows_length_eq hShift] using
      canonical_project_hilbert_trace?_code_sequence_domain
        hTargetTrace
  have hTargetSymm :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(sourceTrace.rows.length) ≐ₘ
          domₘ(targetTrace.code_sequence) :=
    Metatheory.Derives.equality_symm
      hTargetDomain
  exact Metatheory.Derives.equality_trans (middle := numₘ(sourceTrace.rows.length))
    hSourceDomain hTargetSymm
/--
同步 cutoff-shift 轨迹共享同一个末行编号；该行同时恢复左右根码和源入口深度。
-/
theorem canonical_project_formula_shift_terminal_contract
    {sourceEntryDepth targetEntryDepth cutoff : Nat}
    {sourceFormula targetFormula : SetFormula}
    {sourceTrace targetTrace : CanonicalProjectTrace} (hSourceTrace :
      canonical_project_hilbert_trace?
        sourceEntryDepth sourceFormula = some sourceTrace) (hTargetTrace :
      canonical_project_hilbert_trace?
        targetEntryDepth targetFormula = some targetTrace) (hShift :
      CanonicalProjectTraceShift cutoff sourceTrace targetTrace) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory] (((numₘ(sourceTrace.rootIndex) ∈ₘ
            domₘ(sourceTrace.code_sequence)) ∧ₘ (domₘ(sourceTrace.code_sequence) ≐ₘ
            Sₘ(numₘ(sourceTrace.rootIndex)))) ∧ₘ (((sourceTrace.rootCode ≐ₘ (sourceTrace.code_sequence ·ₘ
                numₘ(sourceTrace.rootIndex))) ∧ₘ (targetTrace.rootCode ≐ₘ (targetTrace.code_sequence ·ₘ
                numₘ(sourceTrace.rootIndex)))) ∧ₘ (numₘ(sourceEntryDepth) ≐ₘ (sourceTrace.depth_sequence ·ₘ
              numₘ(sourceTrace.rootIndex))))) := by
  have hSourceCodeSymm :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        sourceTrace.rootCode ≐ₘ (sourceTrace.code_sequence ·ₘ
            numₘ(sourceTrace.rootIndex)) :=
    Metatheory.Derives.equality_symm
      (canonical_project_hilbert_trace?_root_code_value
        hSourceTrace)
  have hTargetValue :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (targetTrace.code_sequence ·ₘ
            numₘ(sourceTrace.rootIndex)) ≐ₘ
          targetTrace.rootCode := by
    rw [CanonicalProjectTraceShift.root_index_eq hShift]
    exact canonical_project_hilbert_trace?_root_code_value
      hTargetTrace
  have hTargetCodeSymm :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        targetTrace.rootCode ≐ₘ (targetTrace.code_sequence ·ₘ
            numₘ(sourceTrace.rootIndex)) :=
    Metatheory.Derives.equality_symm
      hTargetValue
  have hDepthSymm :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(sourceEntryDepth) ≐ₘ (sourceTrace.depth_sequence ·ₘ
            numₘ(sourceTrace.rootIndex)) :=
    Metatheory.Derives.equality_symm
      (canonical_project_hilbert_trace?_root_depth_value
        hSourceTrace)
  exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (canonical_project_hilbert_trace?_root_index_mem_domain
        hSourceTrace) (canonical_project_hilbert_trace?_domain_eq_root_successor
        hSourceTrace)) (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro
        hSourceCodeSymm hTargetCodeSymm)
      hDepthSymm)
/--
一对成功的同步 cutoff-shift 轨迹满足完整的三序列对象 trace 条件。
该接口汇总左右公式码序列、源深度序列、共同定义域、全称逐行证书和共享末行合同。
-/
theorem canonical_project_formula_shift_trace_condition_derives
    {sourceEntryDepth targetEntryDepth cutoff : Nat}
    {sourceFormula targetFormula : SetFormula}
    {sourceTrace targetTrace : CanonicalProjectTrace} (hSourceTrace :
      canonical_project_hilbert_trace?
        sourceEntryDepth sourceFormula = some sourceTrace) (hTargetTrace :
      canonical_project_hilbert_trace?
        targetEntryDepth targetFormula = some targetTrace) (hShift :
      CanonicalProjectTraceShift cutoff sourceTrace targetTrace) (lastIndexId indexId firstPremiseId secondPremiseId
      atomicBaseId : FreeVarId) (hIndexNeFirstPremise : indexId ≠ firstPremiseId) (hIndexNeSecondPremise : indexId ≠ secondPremiseId) (hIndexFreshAtomicBlock :
      ∀ offset, offset < 8 → indexId ≠ atomicBaseId + offset) (hPremiseIds : firstPremiseId ≠ secondPremiseId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_formula_shift_trace_condition (numₘ(cutoff)) (numₘ(sourceEntryDepth))
        sourceTrace.rootCode targetTrace.rootCode
        sourceTrace.code_sequence targetTrace.code_sequence
        sourceTrace.depth_sequence
        lastIndexId indexId firstPremiseId secondPremiseId
        atomicBaseId := by
  have hEntryDepth :=
    finite_numeral_term_admissible sourceEntryDepth
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
  have hLastIndex :=
    finite_numeral_term_admissible sourceTrace.rootIndex
  have hFixed (term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set lastIndexId (numₘ(sourceTrace.rootIndex)) term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hSourceRootFixed :=
    hFixed sourceTrace.rootCode hSourceRootBoundary
  have hTargetRootFixed :=
    hFixed targetTrace.rootCode hTargetRootBoundary
  have hSourceFixed :=
    hFixed sourceTrace.code_sequence hSourceBoundary
  have hTargetFixed :=
    hFixed targetTrace.code_sequence hTargetBoundary
  have hDepthsFixed :=
    hFixed sourceTrace.depth_sequence hDepthsBoundary
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set lastIndexId (numₘ(sourceTrace.rootIndex)) (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  unfold canonical_project_formula_shift_trace_condition
  apply FirstOrder.Derives.conjIntro
  · apply FirstOrder.Derives.conjIntro
    · exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (canonical_project_hilbert_trace?_code_sequence_mem
            hSourceTrace) (canonical_project_hilbert_trace?_code_sequence_mem
            hTargetTrace)) (canonical_project_hilbert_trace?_depth_sequence_mem
          hSourceTrace)
    · exact FirstOrder.Derives.conjIntro (canonical_project_formula_shift_code_sequence_domains_eq
          hSourceTrace hTargetTrace hShift) (canonical_project_hilbert_trace?_sequence_domains_eq
          hSourceTrace)
  · apply FirstOrder.Derives.conjIntro
    · exact canonical_project_hilbert_trace?_zero_mem_domain
        hSourceTrace
    · apply FirstOrder.Derives.conjIntro
      · exact canonical_project_formula_shift_line_conditions_derives
          hSourceTrace hTargetTrace hShift
          indexId firstPremiseId secondPremiseId atomicBaseId
          hIndexNeFirstPremise hIndexNeSecondPremise
          hIndexFreshAtomicBlock hPremiseIds
      · nd_apply FirstOrder.Derives.exists_intro
          (term := numₘ(sourceTrace.rootIndex))
        rw [Formula.openAt_closeFreeAt_eq_substituteFree]
        simpa [Formula.substituteFree, Term.substituteFree,
          set_variable, hSourceRootFixed, hTargetRootFixed,
          hSourceFixed, hTargetFixed, hDepthsFixed,
          hNumeralFixed] using
          canonical_project_formula_shift_terminal_contract
            hSourceTrace hTargetTrace hShift
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
