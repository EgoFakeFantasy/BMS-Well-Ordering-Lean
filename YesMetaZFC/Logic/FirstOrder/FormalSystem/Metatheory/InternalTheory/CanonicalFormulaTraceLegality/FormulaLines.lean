import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.CodeTransport
/-!
# 规范公式轨迹的逐行对象证书
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/-! ## 复合行的闭见证装配 -/
/-- 一个闭的严格前序位置、深度同步式和码形状式给出否定行分支。 -/
private theorem canonical_negation_line_branch_derives_of_witness
    {T : SetTheory} {Γ : Context signature} (codes depths index premise : SetTerm) (firstPremiseId : FreeVarId) (hCodes :
      GodelQuotation.Numbered.CodeBoundary codes) (hDepths :
      GodelQuotation.Numbered.CodeBoundary depths) (hIndex :
      GodelQuotation.Numbered.CodeBoundary index) (hPremise :
      GodelQuotation.Numbered.CodeBoundary premise) (hEarlier : Γ ⊢ₘ[T] premise ∈ₘ index) (hPremiseDomain :
      Γ ⊢ₘ[T] premise ∈ₘ domₘ(codes)) (hDepth :
      Γ ⊢ₘ[T] (depths ·ₘ premise) ≐ₘ (depths ·ₘ index)) (hCode :
      Γ ⊢ₘ[T] (codes ·ₘ index) ≐ₘ
          neg_codeₘ(codes ·ₘ premise)) :
    Γ ⊢ₘ[T]
      ∃ₘ[SetSort.set, firstPremiseId],
        (x#firstPremiseId ∈ₘ index) ∧ₘ
          (((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
              ((depths ·ₘ x#firstPremiseId) ≐ₘ
                (depths ·ₘ index))) ∧ₘ
            ((codes ·ₘ index) ≐ₘ
              neg_codeₘ(codes ·ₘ x#firstPremiseId))) := by
  have hFixed (variableId : FreeVarId) (replacement term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set variableId replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hCodesFixed :=
    hFixed firstPremiseId premise codes hCodes
  have hDepthsFixed :=
    hFixed firstPremiseId premise depths hDepths
  have hIndexFixed :=
    hFixed firstPremiseId premise index hIndex
  nd_apply FirstOrder.Derives.exists_intro
    (term := premise)
  rw [Formula.openAt_closeFreeAt_eq_substituteFree]
  apply FirstOrder.Derives.conjIntro
  · simpa [Formula.substituteFree, Term.substituteFree,
      set_variable, hIndexFixed] using hEarlier
  · simpa [Formula.substituteFree, Term.substituteFree,
      set_variable, hCodesFixed, hDepthsFixed, hIndexFixed] using
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro hPremiseDomain hDepth)
        hCode)
/--
两个互异 binder 下的闭前序位置、同步深度和码形状式给出蕴含行分支。
互异条件只负责存在量词换名；调用处使用分类器统一分配的相邻编号。
-/
private theorem canonical_implication_line_branch_derives_of_witnesses
    {T : SetTheory} {Γ : Context signature} (codes depths index leftPremise rightPremise : SetTerm) (firstPremiseId secondPremiseId : FreeVarId)
    (hPremiseIds : firstPremiseId ≠ secondPremiseId) (hCodes :
      GodelQuotation.Numbered.CodeBoundary codes) (hDepths :
      GodelQuotation.Numbered.CodeBoundary depths) (hIndex :
      GodelQuotation.Numbered.CodeBoundary index) (hLeftPremise :
      GodelQuotation.Numbered.CodeBoundary leftPremise) (hRightPremise :
      GodelQuotation.Numbered.CodeBoundary rightPremise) (hLeftEarlier : Γ ⊢ₘ[T] leftPremise ∈ₘ index) (hLeftPremiseDomain :
      Γ ⊢ₘ[T] leftPremise ∈ₘ domₘ(codes)) (hRightEarlier : Γ ⊢ₘ[T] rightPremise ∈ₘ index) (hRightPremiseDomain :
      Γ ⊢ₘ[T] rightPremise ∈ₘ domₘ(codes)) (hLeftDepth :
      Γ ⊢ₘ[T] (depths ·ₘ leftPremise) ≐ₘ (depths ·ₘ index)) (hRightDepth :
      Γ ⊢ₘ[T] (depths ·ₘ rightPremise) ≐ₘ (depths ·ₘ index)) (hCode :
      Γ ⊢ₘ[T] (codes ·ₘ index) ≐ₘ
          imp_codeₘ(
            codes ·ₘ leftPremise,
            codes ·ₘ rightPremise)) :
    Γ ⊢ₘ[T]
      ∃ₘ[SetSort.set, firstPremiseId],
        (x#firstPremiseId ∈ₘ index) ∧ₘ
          (∃ₘ[SetSort.set, secondPremiseId],
            (x#secondPremiseId ∈ₘ index) ∧ₘ
              ((((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
                  (x#secondPremiseId ∈ₘ domₘ(codes))) ∧ₘ
                  (((depths ·ₘ x#firstPremiseId) ≐ₘ
                      (depths ·ₘ index)) ∧ₘ
                    ((depths ·ₘ x#secondPremiseId) ≐ₘ
                      (depths ·ₘ index)))) ∧ₘ
                ((codes ·ₘ index) ≐ₘ
                  imp_codeₘ(
                    codes ·ₘ x#firstPremiseId,
                    codes ·ₘ x#secondPremiseId)))) := by
  have hFixed (variableId : FreeVarId) (replacement term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set variableId replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hCodesFirstFixed :=
    hFixed firstPremiseId leftPremise codes hCodes
  have hDepthsFirstFixed :=
    hFixed firstPremiseId leftPremise depths hDepths
  have hIndexFirstFixed :=
    hFixed firstPremiseId leftPremise index hIndex
  have hCodesSecondFixed :=
    hFixed secondPremiseId rightPremise codes hCodes
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
  apply FirstOrder.Derives.conjIntro
  · simpa [Formula.substituteFree, Term.substituteFree,
      set_variable, hIndexFirstFixed] using hLeftEarlier
  ·
    nd_apply FirstOrder.Derives.exists_intro
      (term := rightPremise)
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set firstPremiseId secondPremiseId 0
      leftPremise _ hPremiseIds hLeftPremise.1.2 (by
        rw [hLeftPremise.2]
        exact List.not_mem_nil)]
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    apply FirstOrder.Derives.conjIntro
    · simpa [Formula.substituteFree, Term.substituteFree,
        set_variable, hIndexFirstFixed, hIndexSecondFixed,
        hPremiseIds, hSecondPremiseNeFirst] using
        hRightEarlier
    · simpa [Formula.substituteFree, Term.substituteFree,
        set_variable,
        hCodesFirstFixed, hDepthsFirstFixed, hIndexFirstFixed,
        hCodesSecondFixed, hDepthsSecondFixed, hIndexSecondFixed,
        hLeftPremiseSecondFixed,
        hPremiseIds, hSecondPremiseNeFirst] using
        (FirstOrder.Derives.conjIntro
          (FirstOrder.Derives.conjIntro
            (FirstOrder.Derives.conjIntro
              hLeftPremiseDomain hRightPremiseDomain)
            (FirstOrder.Derives.conjIntro
              hLeftDepth hRightDepth))
          hCode)
/-- 一个闭的严格前序位置、后继深度式和码形状式给出全称量词行分支。 -/
private theorem canonical_universal_line_branch_derives_of_witness
    {T : SetTheory} {Γ : Context signature} (codes depths index premise : SetTerm) (firstPremiseId : FreeVarId) (hCodes :
      GodelQuotation.Numbered.CodeBoundary codes) (hDepths :
      GodelQuotation.Numbered.CodeBoundary depths) (hIndex :
      GodelQuotation.Numbered.CodeBoundary index) (hPremise :
      GodelQuotation.Numbered.CodeBoundary premise) (hEarlier : Γ ⊢ₘ[T] premise ∈ₘ index) (hPremiseDomain :
      Γ ⊢ₘ[T] premise ∈ₘ domₘ(codes)) (hDepth :
      Γ ⊢ₘ[T] (depths ·ₘ premise) ≐ₘ
          Sₘ(depths ·ₘ index)) (hCode :
      Γ ⊢ₘ[T] (codes ·ₘ index) ≐ₘ
          forall_codeₘ(
            canonical_binder_variable_code_term (depths ·ₘ index),
            codes ·ₘ premise)) :
    Γ ⊢ₘ[T]
      ∃ₘ[SetSort.set, firstPremiseId],
        (x#firstPremiseId ∈ₘ index) ∧ₘ
          (((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
              ((depths ·ₘ x#firstPremiseId) ≐ₘ
                Sₘ(depths ·ₘ index))) ∧ₘ
            ((codes ·ₘ index) ≐ₘ
              forall_codeₘ(
                canonical_binder_variable_code_term
                  (depths ·ₘ index),
                codes ·ₘ x#firstPremiseId))) := by
  have hFixed (variableId : FreeVarId) (replacement term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set variableId replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hCodesFixed :=
    hFixed firstPremiseId premise codes hCodes
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
  apply FirstOrder.Derives.conjIntro
  · simpa [Formula.substituteFree, Term.substituteFree,
      set_variable, hIndexFixed] using hEarlier
  · simpa [Formula.substituteFree, Term.substituteFree,
      set_variable, hCodesFixed, hDepthsFixed, hIndexFixed,
      hTwoFixed] using
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro hPremiseDomain hDepth)
        hCode)
/-! ## 轨迹标准序列的逐点读取 -/
/-- 成功轨迹的公式码序列在任意外部行编号处精确读回该行公式码。 -/
theorem canonical_project_hilbert_trace?_code_value_of_getElem?
    {entryDepth index : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace}
    {row : CanonicalProjectTraceRow} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) (hRow : trace.rows[index]? = some row) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ numₘ(index)) ≐ₘ row.code := by
  have hCodeGet :
      trace.code_terms[index]? = some row.code := by
    simpa [CanonicalProjectTrace.code_terms] using
      congrArg (Option.map CanonicalProjectTraceRow.code)
        hRow
  have hBoundary :=
    canonical_project_hilbert_trace_from?_row_code_boundary
      hTrace (List.mem_of_getElem? hRow)
  apply GodelQuotation.gq_weaken_standard_sequence
  simpa [CanonicalProjectTrace.code_sequence] using
    (GodelQuotation.standard_sequence_from_apply_getElem?
      0 hCodeGet
      (canonical_project_hilbert_trace_from?_code_terms_admissible
        hTrace)
      (canonical_project_hilbert_trace_from?_code_terms_closed
        hTrace)
      hBoundary.1)
/-- 任意轨迹的深度序列在外部行编号处精确读回该行 quotation 深度 numeral。 -/
theorem canonical_project_trace_depth_value_of_getElem?
    {index : Nat}
    {trace : CanonicalProjectTrace}
    {row : CanonicalProjectTraceRow} (hRow : trace.rows[index]? = some row) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(index)) ≐ₘ
        numₘ(row.depth) := by
  have hDepthGet :
      trace.depth_terms[index]? =
        some (numₘ(row.depth)) := by
    simpa [CanonicalProjectTrace.depth_terms] using
      congrArg (Option.map fun row : CanonicalProjectTraceRow =>
          numₘ(row.depth))
        hRow
  apply GodelQuotation.gq_weaken_standard_sequence
  simpa [CanonicalProjectTrace.depth_sequence] using
    (GodelQuotation.standard_sequence_from_apply_getElem?
      0 hDepthGet
      (canonical_project_trace_depth_terms_admissible trace)
      (canonical_project_trace_depth_terms_closed trace)
      (finite_numeral_term_admissible row.depth))
/-- 成功轨迹的公式码序列逐点应用具有统一闭项边界。 -/
theorem canonical_project_hilbert_trace?_code_application_boundary
    {entryDepth index : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) :
    GodelQuotation.Numbered.CodeBoundary (trace.code_sequence ·ₘ numₘ(index)) := by
  have hSequence :=
    canonical_project_hilbert_trace_from?_code_sequence_boundary
      hTrace
  constructor
  · exact function_application_term_admissible
      trace.code_sequence (numₘ(index))
      hSequence.1 (finite_numeral_term_admissible index)
  · simp [Term.freeSupport, Term.freeSupportList,
      hSequence.2, finite_numeral_term_freeSupport]
/-- 任意轨迹的深度序列逐点应用具有统一闭项边界。 -/
theorem canonical_project_trace_depth_application_boundary (trace : CanonicalProjectTrace) (index : Nat) :
    GodelQuotation.Numbered.CodeBoundary (trace.depth_sequence ·ₘ numₘ(index)) := by
  have hSequence :=
    canonical_project_trace_depth_sequence_boundary trace
  constructor
  · exact function_application_term_admissible
      trace.depth_sequence (numₘ(index))
      hSequence.1 (finite_numeral_term_admissible index)
  · simp [Term.freeSupport, Term.freeSupportList,
      hSequence.2, finite_numeral_term_freeSupport]
/-! ## 具体 numeral 行的对象合法性 -/
/--
把一条已知外部行沿对象索引等式提升为任意对象索引处的逐行条件。
原子条件内部的存在 binder 由实际深度项决定，不能仅靠公式语法替换来搬运。这里直接
把 `point = numeral(index)` 提升为两个标准序列应用的等式，再按外部构造合同重建四个
分支；因此所得全称证明不依赖 α-编号偶然相同。
-/
private theorem canonical_project_hilbert_trace?_line_condition_of_index_equality
    {Γ : Context signature}
    {entryDepth index : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace}
    {row : CanonicalProjectTraceRow} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) (hRow : trace.rows[index]? = some row) (point : SetTerm) (hPoint :
      GodelQuotation.Numbered.CodeBoundary point) (hPointValue :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        point ≐ₘ numₘ(index)) (firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hPremiseIds : firstPremiseId ≠ secondPremiseId) (hLeftCodeNeRightCode :
      leftVariableCodeId ≠ rightVariableCodeId) (hLeftCodeNeLeftDepth :
      leftVariableCodeId ≠ leftVariableDepthId) (hRightCodeNeRightDepth :
      rightVariableCodeId ≠ rightVariableDepthId) :
    Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_formula_line_condition_with_ids
        trace.code_sequence trace.depth_sequence
        point
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId := by
  have hCodes :
      GodelQuotation.Numbered.CodeBoundary trace.code_sequence :=
    canonical_project_hilbert_trace_from?_code_sequence_boundary
      hTrace
  have hDepths :
      GodelQuotation.Numbered.CodeBoundary trace.depth_sequence :=
    canonical_project_trace_depth_sequence_boundary trace
  have hNumeralIndex :
      GodelQuotation.Numbered.CodeBoundary numₘ(index) :=
    ⟨finite_numeral_term_admissible index,
      finite_numeral_term_freeSupport index⟩
  have hNumeralCurrentCode :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ numₘ(index)) ≐ₘ row.code :=
    canonical_project_hilbert_trace?_code_value_of_getElem?
      hTrace hRow
  have hNumeralCurrentDepth :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(row.depth) :=
    canonical_project_trace_depth_value_of_getElem? hRow
  have hCurrentCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary (trace.code_sequence ·ₘ point) := by
    constructor
    · exact function_application_term_admissible
        trace.code_sequence point hCodes.1 hPoint.1
    · simp [Term.freeSupport, Term.freeSupportList,
        hCodes.2, hPoint.2]
  have hCurrentDepthBoundary :
      GodelQuotation.Numbered.CodeBoundary (trace.depth_sequence ·ₘ point) := by
    constructor
    · exact function_application_term_admissible
        trace.depth_sequence point hDepths.1 hPoint.1
    · simp [Term.freeSupport, Term.freeSupportList,
        hDepths.2, hPoint.2]
  have hCurrentCodeAtNumeral :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ point) ≐ₘ (trace.code_sequence ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      trace.code_sequence point (numₘ(index))
      hCodes.1 hPoint.1 hNumeralIndex.1 hPointValue
  have hCurrentDepthAtNumeral :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ point) ≐ₘ (trace.depth_sequence ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      trace.depth_sequence point (numₘ(index))
      hDepths.1 hPoint.1 hNumeralIndex.1 hPointValue
  have hCurrentCode :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ point) ≐ₘ row.code :=
    Metatheory.Derives.equality_trans
      hCurrentCodeAtNumeral (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp)
        hNumeralCurrentCode)
  have hCurrentDepth :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ point) ≐ₘ
          numₘ(row.depth) :=
    Metatheory.Derives.equality_trans
      hCurrentDepthAtNumeral (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp)
        hNumeralCurrentDepth)
  have hEarlierObject (premise : Nat) (hEarlier : premise < index) :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(premise) ∈ₘ point := by
    have hNumeralEarlier :
        Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
          numₘ(premise) ∈ₘ numₘ(index) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) (GodelQuotation.gq_weaken_standard_sequence
          (GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
            premise index hEarlier))
    have hTransport :=
      membership_right_iff_of_equality (numₘ(premise)) point (numₘ(index)) (finite_numeral_term_admissible premise)
        hPoint.1 hNumeralIndex.1 hPointValue
    exact FirstOrder.Derives.iffElimLeft
      hTransport hNumeralEarlier
  have hPremiseDomainObject (premise : Nat) (hPremise : premise < index) :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(premise) ∈ₘ domₘ(trace.code_sequence) := by
    have hIndexBound : index < trace.rows.length := (List.getElem?_eq_some_iff.mp hRow).1
    have hPremiseBound : premise < trace.rows.length :=
      Nat.lt_trans hPremise hIndexBound
    have hNumeralMember :
        Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
          numₘ(premise) ∈ₘ numₘ(trace.rows.length) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
          GodelQuotation.gq_weaken_standard_sequence <|
            GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
              premise trace.rows.length hPremiseBound
    exact FirstOrder.Derives.iffElimLeft (membership_right_iff_of_equality (numₘ(premise)) (domₘ(trace.code_sequence)) (numₘ(trace.rows.length))
        (finite_numeral_term_admissible premise) (domain_term_admissible trace.code_sequence hCodes.1) (finite_numeral_term_admissible trace.rows.length)
        (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) (canonical_project_hilbert_trace?_code_sequence_domain
            hTrace)))
      hNumeralMember
  have hLineCheck :
      Formula.CheckCertificate
        (canonical_project_formula_line_condition_with_ids
          trace.code_sequence trace.depth_sequence point
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId) :=
    canonical_project_formula_line_condition_with_ids_check
      trace.code_sequence trace.depth_sequence point
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      (Term.check_admissible_complete hCodes.1)
      (Term.check_admissible_complete hDepths.1)
      (Term.check_admissible_complete hPoint.1)
  rw [canonical_project_formula_line_condition_with_ids] at hLineCheck
  have hAtomicCheck :=
    (Formula.CheckCertificate.disj_iff.mp hLineCheck).1
  have hTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hLineCheck).2
  have hNegationCheck :=
    (Formula.CheckCertificate.disj_iff.mp hTailCheck).1
  have hImplicationTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hTailCheck).2
  have hImplicationCheck :=
    (Formula.CheckCertificate.disj_iff.mp hImplicationTailCheck).1
  have hUniversalCheck :=
    (Formula.CheckCertificate.disj_iff.mp hImplicationTailCheck).2
  have hEvidence :=
    canonical_project_hilbert_trace?_rows_evidence
      hTrace hRow
  cases hEvidence with
  | atomic rowFormula depth kind leftDepth rightDepth
      hLeftDepth hRightDepth =>
      have hAtomic :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            canonical_project_atomic_code_condition_with_ids (trace.depth_sequence ·ₘ point) (trace.code_sequence ·ₘ point)
              leftVariableCodeId rightVariableCodeId
              leftVariableDepthId rightVariableDepthId :=
        canonical_project_atomic_code_condition_with_ids_derives
          depth leftDepth rightDepth kind (trace.depth_sequence ·ₘ point) (trace.code_sequence ·ₘ point)
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId
          hLeftCodeNeRightCode
          hLeftCodeNeLeftDepth
          hRightCodeNeRightDepth
          hCurrentDepthBoundary hCurrentDepth
          hLeftDepth hRightDepth
          hCurrentCodeBoundary hCurrentCode
      unfold canonical_project_formula_line_condition_with_ids
      exact FirstOrder.Derives.disjIntroLeft hAtomic
        (hRightCheck := hTailCheck)
  | negation rowFormula depth premise premiseRow
      hPremiseStart hEarlierRaw hPremiseGet hPremiseDepthCode =>
      have hEarlier : premise < index := by
        simpa using hEarlierRaw
      have hPremiseRow :
          trace.rows[premise]? = some premiseRow := by
        simpa using hPremiseGet
      have hEarlierPoint :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(premise) ∈ₘ point :=
        hEarlierObject premise hEarlier
      have hPremiseDomain :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(premise) ∈ₘ domₘ(trace.code_sequence) :=
        hPremiseDomainObject premise hEarlier
      have hPremiseCode :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ numₘ(premise)) ≐ₘ
              premiseRow.code :=
        FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp)
          (canonical_project_hilbert_trace?_code_value_of_getElem?
            hTrace hPremiseRow)
      have hPremiseCodeBoundary :
          GodelQuotation.Numbered.CodeBoundary premiseRow.code :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hTrace (List.mem_of_getElem? hPremiseRow)
      have hPremiseDepth :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(premise)) ≐ₘ
              numₘ(depth) := by
        have hValue :=
          FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ)
            (by simp)
            (canonical_project_trace_depth_value_of_getElem?
              hPremiseRow)
        simpa [hPremiseDepthCode] using hValue
      have hPremiseCodeApplication :
          GodelQuotation.Numbered.CodeBoundary (trace.code_sequence ·ₘ numₘ(premise)) :=
        canonical_project_hilbert_trace?_code_application_boundary (index := premise) hTrace
      have hDepthAgreement :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(premise)) ≐ₘ (trace.depth_sequence ·ₘ point) :=
        Metatheory.Derives.equality_join
          hPremiseDepth hCurrentDepth
      have hNegationCongruence :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            neg_codeₘ(
              trace.code_sequence ·ₘ numₘ(premise)) ≐ₘ
              neg_codeₘ(premiseRow.code) :=
        canonical_negation_code_term_congr_of_equality (trace.code_sequence ·ₘ numₘ(premise))
          premiseRow.code
          hPremiseCodeApplication.1
          hPremiseCodeBoundary.1 hPremiseCode
      have hCodeAgreement :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ point) ≐ₘ
              neg_codeₘ(
                trace.code_sequence ·ₘ numₘ(premise)) :=
        Metatheory.Derives.equality_join
          hCurrentCode hNegationCongruence
      have hNegation :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            ∃ₘ[SetSort.set, firstPremiseId],
              (x#firstPremiseId ∈ₘ point) ∧ₘ
                (((x#firstPremiseId ∈ₘ domₘ(trace.code_sequence)) ∧ₘ
                    ((trace.depth_sequence ·ₘ x#firstPremiseId) ≐ₘ
                      (trace.depth_sequence ·ₘ point))) ∧ₘ
                  ((trace.code_sequence ·ₘ point) ≐ₘ
                    neg_codeₘ(
                      trace.code_sequence ·ₘ x#firstPremiseId))) :=
        canonical_negation_line_branch_derives_of_witness
          trace.code_sequence trace.depth_sequence
          point (numₘ(premise))
          firstPremiseId
          hCodes hDepths hPoint
          ⟨finite_numeral_term_admissible premise,
            finite_numeral_term_freeSupport premise⟩
          hEarlierPoint hPremiseDomain
          hDepthAgreement hCodeAgreement
      unfold canonical_project_formula_line_condition_with_ids
      exact FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroLeft hNegation
          (hRightCheck := hImplicationTailCheck))
        (hLeftCheck := hAtomicCheck)
  | implication rowFormula depth leftPremise rightPremise
      leftRow rightRow hLeftStart hLeftEarlierRaw
      hRightStart hRightEarlierRaw hLeftGet hRightGet
      hLeftDepthCode hRightDepthCode =>
      have hLeftEarlier : leftPremise < index := by
        simpa using hLeftEarlierRaw
      have hRightEarlier : rightPremise < index := by
        simpa using hRightEarlierRaw
      have hLeftRow :
          trace.rows[leftPremise]? = some leftRow := by
        simpa using hLeftGet
      have hRightRow :
          trace.rows[rightPremise]? = some rightRow := by
        simpa using hRightGet
      have hLeftEarlierPoint :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(leftPremise) ∈ₘ point :=
        hEarlierObject leftPremise hLeftEarlier
      have hRightEarlierPoint :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(rightPremise) ∈ₘ point :=
        hEarlierObject rightPremise hRightEarlier
      have hLeftPremiseDomain :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(leftPremise) ∈ₘ
              domₘ(trace.code_sequence) :=
        hPremiseDomainObject leftPremise hLeftEarlier
      have hRightPremiseDomain :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(rightPremise) ∈ₘ
              domₘ(trace.code_sequence) :=
        hPremiseDomainObject rightPremise hRightEarlier
      have hLeftCode :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ numₘ(leftPremise)) ≐ₘ
              leftRow.code :=
        FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp)
          (canonical_project_hilbert_trace?_code_value_of_getElem?
            hTrace hLeftRow)
      have hRightCode :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ numₘ(rightPremise)) ≐ₘ
              rightRow.code :=
        FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp)
          (canonical_project_hilbert_trace?_code_value_of_getElem?
            hTrace hRightRow)
      have hLeftCodeBoundary :
          GodelQuotation.Numbered.CodeBoundary leftRow.code :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hTrace (List.mem_of_getElem? hLeftRow)
      have hRightCodeBoundary :
          GodelQuotation.Numbered.CodeBoundary rightRow.code :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hTrace (List.mem_of_getElem? hRightRow)
      have hLeftDepth :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(leftPremise)) ≐ₘ
              numₘ(depth) := by
        have hValue :=
          FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ)
            (by simp)
            (canonical_project_trace_depth_value_of_getElem?
              hLeftRow)
        simpa [hLeftDepthCode] using hValue
      have hRightDepth :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(rightPremise)) ≐ₘ
              numₘ(depth) := by
        have hValue :=
          FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ)
            (by simp)
            (canonical_project_trace_depth_value_of_getElem?
              hRightRow)
        simpa [hRightDepthCode] using hValue
      have hLeftCodeApplication :
          GodelQuotation.Numbered.CodeBoundary (trace.code_sequence ·ₘ numₘ(leftPremise)) :=
        canonical_project_hilbert_trace?_code_application_boundary (index := leftPremise) hTrace
      have hRightCodeApplication :
          GodelQuotation.Numbered.CodeBoundary (trace.code_sequence ·ₘ numₘ(rightPremise)) :=
        canonical_project_hilbert_trace?_code_application_boundary (index := rightPremise) hTrace
      have hLeftDepthAgreement :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(leftPremise)) ≐ₘ (trace.depth_sequence ·ₘ point) :=
        Metatheory.Derives.equality_join
          hLeftDepth hCurrentDepth
      have hRightDepthAgreement :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(rightPremise)) ≐ₘ (trace.depth_sequence ·ₘ point) :=
        Metatheory.Derives.equality_join
          hRightDepth hCurrentDepth
      have hImplicationCongruence :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            imp_codeₘ(
              trace.code_sequence ·ₘ numₘ(leftPremise),
              trace.code_sequence ·ₘ numₘ(rightPremise)) ≐ₘ
              imp_codeₘ(leftRow.code, rightRow.code) :=
        canonical_implication_code_term_congr_of_equalities (trace.code_sequence ·ₘ numₘ(leftPremise))
          leftRow.code (trace.code_sequence ·ₘ numₘ(rightPremise))
          rightRow.code
          hLeftCodeApplication.1 hLeftCodeBoundary.1
          hRightCodeApplication.1 hRightCodeBoundary.1
          hLeftCode hRightCode
      have hCodeAgreement :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ point) ≐ₘ
              imp_codeₘ(
                trace.code_sequence ·ₘ numₘ(leftPremise),
                trace.code_sequence ·ₘ numₘ(rightPremise)) :=
        Metatheory.Derives.equality_join
          hCurrentCode hImplicationCongruence
      have hImplication :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            ∃ₘ[SetSort.set, firstPremiseId],
              (x#firstPremiseId ∈ₘ point) ∧ₘ
                (∃ₘ[SetSort.set, secondPremiseId],
                  (x#secondPremiseId ∈ₘ point) ∧ₘ
                    ((((x#firstPremiseId ∈ₘ
                        domₘ(trace.code_sequence)) ∧ₘ
                        (x#secondPremiseId ∈ₘ
                          domₘ(trace.code_sequence))) ∧ₘ
                        (((trace.depth_sequence ·ₘ
                            x#firstPremiseId) ≐ₘ
                          (trace.depth_sequence ·ₘ point)) ∧ₘ
                          ((trace.depth_sequence ·ₘ
                            x#secondPremiseId) ≐ₘ
                            (trace.depth_sequence ·ₘ point)))) ∧ₘ
                      ((trace.code_sequence ·ₘ point) ≐ₘ
                        imp_codeₘ(
                          trace.code_sequence ·ₘ x#firstPremiseId,
                          trace.code_sequence ·ₘ x#secondPremiseId)))) :=
        canonical_implication_line_branch_derives_of_witnesses
          trace.code_sequence trace.depth_sequence
          point (numₘ(leftPremise)) (numₘ(rightPremise))
          firstPremiseId secondPremiseId hPremiseIds
          hCodes hDepths hPoint
          ⟨finite_numeral_term_admissible leftPremise,
            finite_numeral_term_freeSupport leftPremise⟩
          ⟨finite_numeral_term_admissible rightPremise,
            finite_numeral_term_freeSupport rightPremise⟩
          hLeftEarlierPoint hLeftPremiseDomain
          hRightEarlierPoint hRightPremiseDomain
          hLeftDepthAgreement hRightDepthAgreement
          hCodeAgreement
      unfold canonical_project_formula_line_condition_with_ids
      exact FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.disjIntroLeft hImplication
            (hRightCheck := hUniversalCheck))
          (hLeftCheck := hNegationCheck))
        (hLeftCheck := hAtomicCheck)
  | universal rowFormula depth premise premiseRow
      hPremiseStart hEarlierRaw hPremiseGet hPremiseDepthCode =>
      have hEarlier : premise < index := by
        simpa using hEarlierRaw
      have hPremiseRow :
          trace.rows[premise]? = some premiseRow := by
        simpa using hPremiseGet
      have hEarlierPoint :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(premise) ∈ₘ point :=
        hEarlierObject premise hEarlier
      have hPremiseDomain :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(premise) ∈ₘ domₘ(trace.code_sequence) :=
        hPremiseDomainObject premise hEarlier
      have hPremiseCode :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ numₘ(premise)) ≐ₘ
              premiseRow.code :=
        FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp)
          (canonical_project_hilbert_trace?_code_value_of_getElem?
            hTrace hPremiseRow)
      have hPremiseCodeBoundary :
          GodelQuotation.Numbered.CodeBoundary premiseRow.code :=
        canonical_project_hilbert_trace_from?_row_code_boundary
          hTrace (List.mem_of_getElem? hPremiseRow)
      have hPremiseDepth :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(premise)) ≐ₘ
              numₘ(depth + 1) := by
        have hValue :=
          FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ)
            (by simp)
            (canonical_project_trace_depth_value_of_getElem?
              hPremiseRow)
        simpa [hPremiseDepthCode] using hValue
      have hPremiseCodeApplication :
          GodelQuotation.Numbered.CodeBoundary (trace.code_sequence ·ₘ numₘ(premise)) :=
        canonical_project_hilbert_trace?_code_application_boundary (index := premise) hTrace
      have hPremiseDepthSuccessor :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(premise)) ≐ₘ
              Sₘ(numₘ(depth)) := by
        simpa [finite_numeral_term] using hPremiseDepth
      have hCurrentSuccessor :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            Sₘ(trace.depth_sequence ·ₘ point) ≐ₘ
              Sₘ(numₘ(depth)) :=
        successor_term_congr_of_equality (trace.depth_sequence ·ₘ point) (numₘ(depth))
          hCurrentDepthBoundary.1 (finite_numeral_term_admissible depth)
          hCurrentDepth
      have hDepthAgreement :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.depth_sequence ·ₘ numₘ(premise)) ≐ₘ
              Sₘ(trace.depth_sequence ·ₘ point) :=
        Metatheory.Derives.equality_join
          hPremiseDepthSuccessor hCurrentSuccessor
      have hDepthCurrentSymm :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(depth) ≐ₘ (trace.depth_sequence ·ₘ point) :=
        Metatheory.Derives.equality_symm
          hCurrentDepth
      have hBinderNumeral :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth) ≐ₘ
              canonical_binder_variable_code_term (numₘ(depth)) :=
        FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) (canonical_binder_variable_code_numeral_derives
            depth)
      have hBinderNumeralToCurrent :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            canonical_binder_variable_code_term (numₘ(depth)) ≐ₘ
              canonical_binder_variable_code_term (trace.depth_sequence ·ₘ point) :=
        canonical_binder_variable_code_term_congr_of_equality (numₘ(depth)) (trace.depth_sequence ·ₘ point) (finite_numeral_term_admissible depth)
          hCurrentDepthBoundary.1
          hDepthCurrentSymm
      have hNamedCode :
          Term.Admissible (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth)) SetSort.set :=
        variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name depth))
      have hCanonicalCurrentCode :
          Term.Admissible (canonical_binder_variable_code_term (trace.depth_sequence ·ₘ point)) SetSort.set :=
        variable_code_term_admissible _ (successor_term_admissible _ (natural_multiplication_term_admissible _ _ (finite_numeral_term_admissible 2)
              hCurrentDepthBoundary.1))
      have hBinderCode :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth) ≐ₘ
              canonical_binder_variable_code_term (trace.depth_sequence ·ₘ point) :=
        Metatheory.Derives.equality_trans
          hBinderNumeral hBinderNumeralToCurrent
      have hPremiseCodeSymm :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            premiseRow.code ≐ₘ (trace.code_sequence ·ₘ numₘ(premise)) :=
        Metatheory.Derives.equality_symm
          hPremiseCode
      have hUniversalCongruence :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            forall_codeₘ(
              GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth),
              premiseRow.code) ≐ₘ
              forall_codeₘ(
                canonical_binder_variable_code_term (trace.depth_sequence ·ₘ point),
                trace.code_sequence ·ₘ numₘ(premise)) :=
        canonical_universal_code_term_congr_of_equalities (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth))
          (canonical_binder_variable_code_term (trace.depth_sequence ·ₘ point))
          premiseRow.code (trace.code_sequence ·ₘ numₘ(premise))
          hNamedCode hCanonicalCurrentCode
          hPremiseCodeBoundary.1 hPremiseCodeApplication.1
          hBinderCode hPremiseCodeSymm
      have hCodeAgreement :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace.code_sequence ·ₘ point) ≐ₘ
              forall_codeₘ(
                canonical_binder_variable_code_term (trace.depth_sequence ·ₘ point),
                trace.code_sequence ·ₘ numₘ(premise)) :=
        Metatheory.Derives.equality_trans
          hCurrentCode hUniversalCongruence
      have hUniversal :
          Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
            ∃ₘ[SetSort.set, firstPremiseId],
              (x#firstPremiseId ∈ₘ point) ∧ₘ
                (((x#firstPremiseId ∈ₘ
                    domₘ(trace.code_sequence)) ∧ₘ
                    ((trace.depth_sequence ·ₘ x#firstPremiseId) ≐ₘ
                      Sₘ(trace.depth_sequence ·ₘ point))) ∧ₘ
                  ((trace.code_sequence ·ₘ point) ≐ₘ
                    forall_codeₘ(
                      canonical_binder_variable_code_term
                        (trace.depth_sequence ·ₘ point),
                      trace.code_sequence ·ₘ x#firstPremiseId))) :=
        canonical_universal_line_branch_derives_of_witness
          trace.code_sequence trace.depth_sequence
          point (numₘ(premise))
          firstPremiseId
          hCodes hDepths hPoint
          ⟨finite_numeral_term_admissible premise,
            finite_numeral_term_freeSupport premise⟩
          hEarlierPoint hPremiseDomain
          hDepthAgreement hCodeAgreement
      unfold canonical_project_formula_line_condition_with_ids
      exact FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroRight
          (FirstOrder.Derives.disjIntroRight hUniversal
            (hLeftCheck := hImplicationCheck))
          (hLeftCheck := hNegationCheck))
        (hLeftCheck := hAtomicCheck)
/-! ## 从具体行到全称逐行条件 -/
/-- 成功轨迹在一个具体 numeral 位置满足显式 binder 的逐行条件。 -/
private theorem canonical_project_hilbert_trace?_line_condition_at_numeral
    {entryDepth index : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace}
    {row : CanonicalProjectTraceRow} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) (hRow : trace.rows[index]? = some row) (firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hPremiseIds : firstPremiseId ≠ secondPremiseId) (hLeftCodeNeRightCode :
      leftVariableCodeId ≠ rightVariableCodeId) (hLeftCodeNeLeftDepth :
      leftVariableCodeId ≠ leftVariableDepthId) (hRightCodeNeRightDepth :
      rightVariableCodeId ≠ rightVariableDepthId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_formula_line_condition_with_ids
        trace.code_sequence trace.depth_sequence (numₘ(index))
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId := by
  exact
    canonical_project_hilbert_trace?_line_condition_of_index_equality
      hTrace hRow (numₘ(index))
      ⟨finite_numeral_term_admissible index,
        finite_numeral_term_freeSupport index⟩
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(index)))
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      hPremiseIds
      hLeftCodeNeRightCode
      hLeftCodeNeLeftDepth
      hRightCodeNeRightDepth
/--
把具体 numeral 行的合法性沿索引等式运输到受量化的自由索引变量。
逐行条件的全部内部 binder 都已显式列出，因此这里把换名条件集中处理；这让有限
numeral 消去器可以安全地调用闭项行证明，而无需把对象序列应用伪装成闭项。
-/
private theorem canonical_project_formula_line_condition_with_ids_of_index_equality (codes depths : SetTerm) (indexId firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hIndexNeFirstPremise : indexId ≠ firstPremiseId)
    (hIndexNeSecondPremise : indexId ≠ secondPremiseId) (hIndexNeLeftCode : indexId ≠ leftVariableCodeId) (hIndexNeRightCode : indexId ≠ rightVariableCodeId)
    (hIndexNeLeftDepth : indexId ≠ leftVariableDepthId) (hIndexNeRightDepth : indexId ≠ rightVariableDepthId) (hCodesClosed : Term.freeSupport codes = [])
    (hDepthsClosed : Term.freeSupport depths = []) (index : Nat) (hConcrete :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_formula_line_condition_with_ids
          codes depths (numₘ(index))
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory] ((x#indexId) ≐ₘ numₘ(index)) ⟶ₘ
        canonical_project_formula_line_condition_with_ids
          codes depths (x#indexId)
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId := by
  let point : SetTerm := x#indexId
  let body : SetFormula :=
    canonical_project_formula_line_condition_with_ids
      codes depths point
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  have hPoint : Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hPointFresh (binderId : FreeVarId) (hIndexNeBinder : indexId ≠ binderId) : (SetSort.set, binderId) ∉ Term.freeSupport point := by
    intro hMember
    change (SetSort.set, binderId) ∈
        [(SetSort.set, indexId)] at hMember
    have hPair : (SetSort.set, binderId) = (SetSort.set, indexId) :=
      List.mem_singleton.mp hMember
    exact hIndexNeBinder (congrArg Prod.snd hPair).symm
  have hPointFreshFirstPremise : (SetSort.set, firstPremiseId) ∉ Term.freeSupport point := by
    exact hPointFresh firstPremiseId hIndexNeFirstPremise
  have hPointFreshSecondPremise : (SetSort.set, secondPremiseId) ∉ Term.freeSupport point := by
    exact hPointFresh secondPremiseId hIndexNeSecondPremise
  have hPointFreshLeftCode : (SetSort.set, leftVariableCodeId) ∉ Term.freeSupport point := by
    exact hPointFresh leftVariableCodeId hIndexNeLeftCode
  have hPointFreshRightCode : (SetSort.set, rightVariableCodeId) ∉ Term.freeSupport point := by
    exact hPointFresh rightVariableCodeId hIndexNeRightCode
  have hPointFreshLeftDepth : (SetSort.set, leftVariableDepthId) ∉ Term.freeSupport point := by
    exact hPointFresh leftVariableDepthId hIndexNeLeftDepth
  have hPointFreshRightDepth : (SetSort.set, rightVariableDepthId) ∉ Term.freeSupport point := by
    exact hPointFresh rightVariableDepthId hIndexNeRightDepth
  have hFirstPremiseNeIndex : firstPremiseId ≠ indexId :=
    Ne.symm hIndexNeFirstPremise
  have hSecondPremiseNeIndex : secondPremiseId ≠ indexId :=
    Ne.symm hIndexNeSecondPremise
  have hLeftCodeNeIndex : leftVariableCodeId ≠ indexId :=
    Ne.symm hIndexNeLeftCode
  have hRightCodeNeIndex : rightVariableCodeId ≠ indexId :=
    Ne.symm hIndexNeRightCode
  have hLeftDepthNeIndex : leftVariableDepthId ≠ indexId :=
    Ne.symm hIndexNeLeftDepth
  have hRightDepthNeIndex : rightVariableDepthId ≠ indexId :=
    Ne.symm hIndexNeRightDepth
  have hCodesFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set indexId replacement codes =
        codes := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hCodesClosed]
    exact List.not_mem_nil
  have hDepthsFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set indexId replacement depths =
        depths := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hDepthsClosed]
    exact List.not_mem_nil
  have hPointSubstitution (replacement : SetTerm) :
      Term.substituteFree SetSort.set indexId replacement point =
        replacement := by
    simp [point, Term.substituteFree]
  have hNormalize (replacement : SetTerm) (hReplacement : Term.Admissible replacement SetSort.set) (hReplacementFreshFirstPremise :
        (SetSort.set, firstPremiseId) ∉
          Term.freeSupport replacement) (hReplacementFreshSecondPremise : (SetSort.set, secondPremiseId) ∉
          Term.freeSupport replacement) (hReplacementFreshLeftCode : (SetSort.set, leftVariableCodeId) ∉
          Term.freeSupport replacement) (hReplacementFreshRightCode : (SetSort.set, rightVariableCodeId) ∉
          Term.freeSupport replacement) (hReplacementFreshLeftDepth : (SetSort.set, leftVariableDepthId) ∉
          Term.freeSupport replacement) (hReplacementFreshRightDepth : (SetSort.set, rightVariableDepthId) ∉
          Term.freeSupport replacement) :
      Formula.substituteFree SetSort.set indexId replacement body =
        canonical_project_formula_line_condition_with_ids
          codes depths replacement
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId := by
    have hNumeralFixed (number : Nat) :
        Term.substituteFree SetSort.set indexId
            replacement (numₘ(number)) =
          numₘ(number) := by
      apply Term.substituteFree_eq_self_of_not_mem
      rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil
    have hFirstPremiseComm (subformula : SetFormula) :
        Formula.substituteFree SetSort.set indexId replacement (Formula.closeFreeAt SetSort.set firstPremiseId
              0 subformula) =
          Formula.closeFreeAt SetSort.set firstPremiseId
            0 (Formula.substituteFree SetSort.set indexId
              replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
        SetSort.set indexId firstPremiseId 0 replacement subformula
        hIndexNeFirstPremise hReplacement.2
        hReplacementFreshFirstPremise).symm
    have hSecondPremiseComm (subformula : SetFormula) :
        Formula.substituteFree SetSort.set indexId replacement (Formula.closeFreeAt SetSort.set secondPremiseId
              0 subformula) =
          Formula.closeFreeAt SetSort.set secondPremiseId
            0 (Formula.substituteFree SetSort.set indexId
              replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
        SetSort.set indexId secondPremiseId 0 replacement subformula
        hIndexNeSecondPremise hReplacement.2
        hReplacementFreshSecondPremise).symm
    have hLeftCodeComm (subformula : SetFormula) :
        Formula.substituteFree SetSort.set indexId replacement (Formula.closeFreeAt SetSort.set leftVariableCodeId
              0 subformula) =
          Formula.closeFreeAt SetSort.set leftVariableCodeId
            0 (Formula.substituteFree SetSort.set indexId
              replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
        SetSort.set indexId leftVariableCodeId 0 replacement subformula
        hIndexNeLeftCode hReplacement.2
        hReplacementFreshLeftCode).symm
    have hRightCodeComm (subformula : SetFormula) :
        Formula.substituteFree SetSort.set indexId replacement (Formula.closeFreeAt SetSort.set rightVariableCodeId
              0 subformula) =
          Formula.closeFreeAt SetSort.set rightVariableCodeId
            0 (Formula.substituteFree SetSort.set indexId
              replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
        SetSort.set indexId rightVariableCodeId 0 replacement subformula
        hIndexNeRightCode hReplacement.2
        hReplacementFreshRightCode).symm
    have hLeftDepthComm (subformula : SetFormula) :
        Formula.substituteFree SetSort.set indexId replacement (Formula.closeFreeAt SetSort.set leftVariableDepthId
              0 subformula) =
          Formula.closeFreeAt SetSort.set leftVariableDepthId
            0 (Formula.substituteFree SetSort.set indexId
              replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
        SetSort.set indexId leftVariableDepthId 0 replacement subformula
        hIndexNeLeftDepth hReplacement.2
        hReplacementFreshLeftDepth).symm
    have hRightDepthComm (subformula : SetFormula) :
        Formula.substituteFree SetSort.set indexId replacement (Formula.closeFreeAt SetSort.set rightVariableDepthId
              0 subformula) =
          Formula.closeFreeAt SetSort.set rightVariableDepthId
            0 (Formula.substituteFree SetSort.set indexId
              replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
        SetSort.set indexId rightVariableDepthId 0 replacement subformula
        hIndexNeRightDepth hReplacement.2
        hReplacementFreshRightDepth).symm
    simp [body,
      canonical_project_formula_line_condition_with_ids,
      canonical_project_atomic_code_condition_with_ids,
      canonical_scoped_variable_code_condition_with_id,
      Formula.substituteFree, Term.substituteFree,
      GodelQuotation.Numbered.argument_sequence,
      GodelQuotation.standard_sequence_from,
      hFirstPremiseComm, hSecondPremiseComm,
      hLeftCodeComm, hRightCodeComm,
      hLeftDepthComm, hRightDepthComm,
      hCodesFixed, hDepthsFixed, hPointSubstitution,
      hNumeralFixed,
      hFirstPremiseNeIndex, hSecondPremiseNeIndex,
      hLeftCodeNeIndex, hRightCodeNeIndex,
      hLeftDepthNeIndex, hRightDepthNeIndex]
    rfl
  have hEquality :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := GodelQuotation.godel_quotation_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hNumeralFresh (binderId : FreeVarId) :
      (SetSort.set, binderId) ∉
        Term.freeSupport (numₘ(index)) := by
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hBodyAtNumeralAdmissible :
      Formula.Admissible
        (Formula.substituteFree SetSort.set indexId
          (numₘ(index)) body) := by
    rw [hNormalize
      (numₘ(index)) (finite_numeral_term_admissible index)
      (hNumeralFresh firstPremiseId)
      (hNumeralFresh secondPremiseId)
      (hNumeralFresh leftVariableCodeId)
      (hNumeralFresh rightVariableCodeId)
      (hNumeralFresh leftVariableDepthId)
      (hNumeralFresh rightVariableDepthId)]
    exact hConcrete.admissible
  have hBodyCheck : Formula.CheckCertificate body :=
    Formula.check_admissible_complete <|
      Formula.Admissible.substituteFree_source
        SetSort.set indexId
        (finite_numeral_term_admissible index)
        hBodyAtNumeralAdmissible
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := GodelQuotation.godel_quotation_theory) (Γ := Γ) (sort := SetSort.set) (eigen := indexId)
      (left := point) (right := numₘ(index)) (body := body)
      hEquality (hBodyCheck := hBodyCheck)
  have hNumeralFreshFirstPremise : (SetSort.set, firstPremiseId) ∉
        Term.freeSupport (numₘ(index)) :=
    hNumeralFresh firstPremiseId
  have hNumeralFreshSecondPremise : (SetSort.set, secondPremiseId) ∉
        Term.freeSupport (numₘ(index)) :=
    hNumeralFresh secondPremiseId
  have hNumeralFreshLeftCode : (SetSort.set, leftVariableCodeId) ∉
        Term.freeSupport (numₘ(index)) :=
    hNumeralFresh leftVariableCodeId
  have hNumeralFreshRightCode : (SetSort.set, rightVariableCodeId) ∉
        Term.freeSupport (numₘ(index)) :=
    hNumeralFresh rightVariableCodeId
  have hNumeralFreshLeftDepth : (SetSort.set, leftVariableDepthId) ∉
        Term.freeSupport (numₘ(index)) :=
    hNumeralFresh leftVariableDepthId
  have hNumeralFreshRightDepth : (SetSort.set, rightVariableDepthId) ∉
        Term.freeSupport (numₘ(index)) :=
    hNumeralFresh rightVariableDepthId
  have hTransport :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_formula_line_condition_with_ids
          codes depths point
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId ↔ₘ
        canonical_project_formula_line_condition_with_ids
          codes depths (numₘ(index))
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId := by
    simpa only [
      hNormalize point hPoint
        hPointFreshFirstPremise hPointFreshSecondPremise
        hPointFreshLeftCode hPointFreshRightCode
        hPointFreshLeftDepth hPointFreshRightDepth,
      hNormalize (numₘ(index)) (finite_numeral_term_admissible index)
        hNumeralFreshFirstPremise hNumeralFreshSecondPremise
        hNumeralFreshLeftCode hNumeralFreshRightCode
        hNumeralFreshLeftDepth hNumeralFreshRightDepth] using hIff
  have hConcreteInContext :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_formula_line_condition_with_ids
          codes depths (numₘ(index))
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hConcrete
  have hResult :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_formula_line_condition_with_ids
          codes depths point
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId :=
    FirstOrder.Derives.iffElimLeft hTransport hConcreteInContext
  have hImplication :=
    FirstOrder.Derives.impIntro hResult
  simpa [Γ, equality, body, point] using hImplication
/--
成功的外部 canonical trace 在对象标准序列定义域上逐行满足分类条件。
有限 numeral 消去把任意对象索引归约为外部后序轨迹的一行；随后由显式 binder 的
索引等式运输定理恢复受量化索引处的原始逐行条件。
-/
theorem canonical_project_hilbert_trace?_line_conditions_derives
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) (indexId firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hIndexNeFirstPremise : indexId ≠ firstPremiseId)
    (hIndexNeSecondPremise : indexId ≠ secondPremiseId) (hIndexNeLeftCode : indexId ≠ leftVariableCodeId) (hIndexNeRightCode : indexId ≠ rightVariableCodeId)
    (hIndexNeLeftDepth : indexId ≠ leftVariableDepthId) (hIndexNeRightDepth : indexId ≠ rightVariableDepthId) (hPremiseIds : firstPremiseId ≠ secondPremiseId)
    (hLeftCodeNeRightCode :
      leftVariableCodeId ≠ rightVariableCodeId) (hLeftCodeNeLeftDepth :
      leftVariableCodeId ≠ leftVariableDepthId) (hRightCodeNeRightDepth :
      rightVariableCodeId ≠ rightVariableDepthId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      ∀ₘ[SetSort.set, indexId], ((x#indexId ∈ₘ domₘ(trace.code_sequence)) ⟶ₘ
          canonical_project_formula_line_condition_with_ids
            trace.code_sequence trace.depth_sequence (x#indexId)
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId) := by
  let source := trace.code_sequence
  let point : SetTerm := x#indexId
  let conclusion : SetFormula :=
    canonical_project_formula_line_condition_with_ids
      source trace.depth_sequence point
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
  let stepBody : SetFormula := (point ∈ₘ domₘ(source)) ⟶ₘ conclusion
  have hSource :
      Term.Admissible source SetSort.set := by
    simpa [source] using (canonical_project_hilbert_trace_from?_code_sequence_boundary
        hTrace).1
  have hSourceClosed :
      Term.freeSupport source = [] := by
    simpa [source] using (canonical_project_hilbert_trace_from?_code_sequence_boundary
        hTrace).2
  have hDepths :
      Term.Admissible trace.depth_sequence SetSort.set :=
    (canonical_project_trace_depth_sequence_boundary trace).1
  have hDepthsClosed :
      Term.freeSupport trace.depth_sequence = [] := (canonical_project_trace_depth_sequence_boundary trace).2
  have hPoint : Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hConclusionCheck :
      Formula.CheckCertificate conclusion := by
    dsimp [conclusion]
    exact canonical_project_formula_line_condition_with_ids_check
      source trace.depth_sequence point
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      (Term.check_admissible_complete hSource)
      (Term.check_admissible_complete hDepths)
      (Term.check_admissible_complete hPoint)
  have hCases :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        GodelQuotation.stdseq_numeral_member_condition
            trace.rows.length point ⟶ₘ
          conclusion := by
    refine GodelQuotation.stdseq_numeral_member_condition_elim_of_theory
      trace.rows.length point conclusion
      (hConclusionCheck := hConclusionCheck) ?_
    intro rowIndex hRowIndex
    let row : CanonicalProjectTraceRow := trace.rows[rowIndex]
    have hRow :
        trace.rows[rowIndex]? = some row :=
      List.getElem?_eq_some_iff.mpr
        ⟨hRowIndex, rfl⟩
    have hConcrete :
        ⊢ₘ[GodelQuotation.godel_quotation_theory]
          canonical_project_formula_line_condition_with_ids
            source trace.depth_sequence (numₘ(rowIndex))
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId := by
      simpa [source] using
        canonical_project_hilbert_trace?_line_condition_at_numeral
          hTrace hRow
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId
          hPremiseIds
          hLeftCodeNeRightCode
          hLeftCodeNeLeftDepth
          hRightCodeNeRightDepth
    simpa [conclusion, point, source] using
      canonical_project_formula_line_condition_with_ids_of_index_equality
        source trace.depth_sequence
        indexId firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId
        hIndexNeFirstPremise
        hIndexNeSecondPremise
        hIndexNeLeftCode
        hIndexNeRightCode
        hIndexNeLeftDepth
        hIndexNeRightDepth
        hSourceClosed hDepthsClosed
        rowIndex hConcrete
  have hNumeralIff :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (point ∈ₘ numₘ(trace.rows.length)) ↔ₘ
          GodelQuotation.stdseq_numeral_member_condition
            trace.rows.length point :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.stdseq_numeral_member_iff
        trace.rows.length point hPoint)
  have hDomain :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        domₘ(source) ≐ₘ numₘ(trace.rows.length) := by
    simpa [source] using
      canonical_project_hilbert_trace?_code_sequence_domain hTrace
  have hDomainIff :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (point ∈ₘ domₘ(source)) ↔ₘ (point ∈ₘ numₘ(trace.rows.length)) :=
    membership_right_iff_of_equality
      point (domₘ(source)) (numₘ(trace.rows.length))
      hPoint (domain_term_admissible source hSource) (finite_numeral_term_admissible trace.rows.length)
      hDomain
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
          point ∈ₘ numₘ(trace.rows.length) :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hDomainIff)
        hMembership
    have hCondition :
        [point ∈ₘ domₘ(source)] ⊢ₘ[
          GodelQuotation.godel_quotation_theory]
          GodelQuotation.stdseq_numeral_member_condition
            trace.rows.length point :=
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
  simpa [stepBody, conclusion, point, source] using hGeneralized
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
