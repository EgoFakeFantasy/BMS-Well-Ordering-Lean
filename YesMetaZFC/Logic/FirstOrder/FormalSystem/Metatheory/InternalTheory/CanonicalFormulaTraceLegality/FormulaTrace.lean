import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.ShiftCode
/-!
# 规范公式轨迹的整体码条件证书
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
把一个自由序列变量的代入规范化到 trace 核心的各个组件。
这里集中处理末行、逐行全称及逐行内部原子见证的全部 binder。外层 `codes/depths`
存在量词只需分别调用本引理一次，因而不必重复维护同一套捕获规避证明。
-/
theorem canonical_project_formula_trace_condition_with_ids_substitute_free (entryDepth code codes depths replacement
      entryDepthResult codeResult
      codesResult depthsResult : SetTerm) (sourceId lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hSourceNeLastIndex : sourceId ≠ lastIndexId) (hSourceNeIndex : sourceId ≠ indexId)
    (hSourceNeFirstPremise : sourceId ≠ firstPremiseId) (hSourceNeSecondPremise : sourceId ≠ secondPremiseId)
    (hSourceNeLeftCode : sourceId ≠ leftVariableCodeId) (hSourceNeRightCode : sourceId ≠ rightVariableCodeId)
    (hSourceNeLeftDepth : sourceId ≠ leftVariableDepthId) (hSourceNeRightDepth : sourceId ≠ rightVariableDepthId)
    (hReplacement : Term.Admissible replacement SetSort.set) (hReplacementFreshLastIndex : (SetSort.set, lastIndexId) ∉ Term.freeSupport replacement)
    (hReplacementFreshIndex : (SetSort.set, indexId) ∉ Term.freeSupport replacement) (hReplacementFreshFirstPremise :
      (SetSort.set, firstPremiseId) ∉ Term.freeSupport replacement) (hReplacementFreshSecondPremise :
      (SetSort.set, secondPremiseId) ∉ Term.freeSupport replacement) (hReplacementFreshLeftCode :
      (SetSort.set, leftVariableCodeId) ∉ Term.freeSupport replacement) (hReplacementFreshRightCode :
      (SetSort.set, rightVariableCodeId) ∉ Term.freeSupport replacement) (hReplacementFreshLeftDepth :
      (SetSort.set, leftVariableDepthId) ∉ Term.freeSupport replacement) (hReplacementFreshRightDepth :
      (SetSort.set, rightVariableDepthId) ∉ Term.freeSupport replacement) (hEntryDepthSubstitution :
      Term.substituteFree SetSort.set sourceId replacement entryDepth =
        entryDepthResult) (hCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement code =
        codeResult) (hCodesSubstitution :
      Term.substituteFree SetSort.set sourceId replacement codes =
        codesResult) (hDepthsSubstitution :
      Term.substituteFree SetSort.set sourceId replacement depths =
        depthsResult) :
    Formula.substituteFree SetSort.set sourceId replacement (canonical_project_formula_trace_condition_with_ids
          entryDepth code codes depths
          lastIndexId indexId
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId) =
      canonical_project_formula_trace_condition_with_ids
        entryDepthResult codeResult codesResult depthsResult
        lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId := by
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hLastIndexComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set lastIndexId
            0 subformula) =
        Formula.closeFreeAt SetSort.set lastIndexId
          0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId lastIndexId 0 replacement subformula
      hSourceNeLastIndex hReplacement.2
      hReplacementFreshLastIndex).symm
  have hIndexComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set indexId
            0 subformula) =
        Formula.closeFreeAt SetSort.set indexId
          0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId indexId 0 replacement subformula
      hSourceNeIndex hReplacement.2
      hReplacementFreshIndex).symm
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
  have hLeftCodeComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set leftVariableCodeId
            0 subformula) =
        Formula.closeFreeAt SetSort.set leftVariableCodeId
          0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId leftVariableCodeId 0 replacement subformula
      hSourceNeLeftCode hReplacement.2
      hReplacementFreshLeftCode).symm
  have hRightCodeComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set rightVariableCodeId
            0 subformula) =
        Formula.closeFreeAt SetSort.set rightVariableCodeId
          0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId rightVariableCodeId 0 replacement subformula
      hSourceNeRightCode hReplacement.2
      hReplacementFreshRightCode).symm
  have hLeftDepthComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set leftVariableDepthId
            0 subformula) =
        Formula.closeFreeAt SetSort.set leftVariableDepthId
          0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId leftVariableDepthId 0 replacement subformula
      hSourceNeLeftDepth hReplacement.2
      hReplacementFreshLeftDepth).symm
  have hRightDepthComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set rightVariableDepthId
            0 subformula) =
        Formula.closeFreeAt SetSort.set rightVariableDepthId
          0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId rightVariableDepthId 0 replacement subformula
      hSourceNeRightDepth hReplacement.2
      hReplacementFreshRightDepth).symm
  have hLastIndexNeSource : lastIndexId ≠ sourceId :=
    Ne.symm hSourceNeLastIndex
  have hIndexNeSource : indexId ≠ sourceId :=
    Ne.symm hSourceNeIndex
  have hFirstPremiseNeSource : firstPremiseId ≠ sourceId :=
    Ne.symm hSourceNeFirstPremise
  have hSecondPremiseNeSource : secondPremiseId ≠ sourceId :=
    Ne.symm hSourceNeSecondPremise
  have hLeftCodeNeSource : leftVariableCodeId ≠ sourceId :=
    Ne.symm hSourceNeLeftCode
  have hRightCodeNeSource : rightVariableCodeId ≠ sourceId :=
    Ne.symm hSourceNeRightCode
  have hLeftDepthNeSource : leftVariableDepthId ≠ sourceId :=
    Ne.symm hSourceNeLeftDepth
  have hRightDepthNeSource : rightVariableDepthId ≠ sourceId :=
    Ne.symm hSourceNeRightDepth
  simp [canonical_project_formula_trace_condition_with_ids,
    canonical_project_formula_line_condition_with_ids,
    canonical_project_atomic_code_condition_with_ids,
    canonical_scoped_variable_code_condition_with_id,
    canonical_project_formula_terminal_condition,
    Formula.substituteFree, Term.substituteFree, set_variable,
    GodelQuotation.Numbered.argument_sequence,
    GodelQuotation.standard_sequence_from,
    hLastIndexComm, hIndexComm,
    hFirstPremiseComm, hSecondPremiseComm,
    hLeftCodeComm, hRightCodeComm,
    hLeftDepthComm, hRightDepthComm,
    hEntryDepthSubstitution, hCodeSubstitution,
    hCodesSubstitution, hDepthsSubstitution,
    hNumeralFixed,
    hLastIndexNeSource, hIndexNeSource,
    hFirstPremiseNeSource, hSecondPremiseNeSource,
    hLeftCodeNeSource, hRightCodeNeSource,
    hLeftDepthNeSource, hRightDepthNeSource]
  rfl
/--
闭代码项的自由变量代入逐参数穿过显式编号的规范公式码分类条件。
调用方只需固定十个内部 binder 并证明源编号与它们互异；replacement 的闭代码边界
统一提供全部捕获规避新鲜性。该接口供更外层存在量词分类器稳定实例化内部 trace。
-/
theorem canonical_project_formula_code_condition_with_ids_substitute_closed (entryDepth code replacement
      entryDepthResult codeResult : SetTerm) (sourceId codesId depthsId lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hSourceNeCodes : sourceId ≠ codesId) (hSourceNeDepths : sourceId ≠ depthsId)
    (hSourceNeLastIndex : sourceId ≠ lastIndexId) (hSourceNeIndex : sourceId ≠ indexId) (hSourceNeFirstPremise : sourceId ≠ firstPremiseId)
    (hSourceNeSecondPremise : sourceId ≠ secondPremiseId) (hSourceNeLeftCode : sourceId ≠ leftVariableCodeId)
    (hSourceNeRightCode : sourceId ≠ rightVariableCodeId) (hSourceNeLeftDepth : sourceId ≠ leftVariableDepthId)
    (hSourceNeRightDepth : sourceId ≠ rightVariableDepthId) (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement) (hEntryDepthSubstitution :
      Term.substituteFree SetSort.set sourceId replacement entryDepth =
        entryDepthResult) (hCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement code =
        codeResult) :
    Formula.substituteFree SetSort.set sourceId replacement (canonical_project_formula_code_condition_with_ids
          entryDepth code
          codesId depthsId lastIndexId indexId
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId) =
      canonical_project_formula_code_condition_with_ids
        entryDepthResult codeResult
        codesId depthsId lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId := by
  have hReplacementFresh (binderId : FreeVarId) : (SetSort.set, binderId) ∉
        Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hCodesFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#codesId) =
        x#codesId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeCodes]
  have hDepthsFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#depthsId) =
        x#depthsId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeDepths]
  have hTraceSubstitution :
      Formula.substituteFree SetSort.set sourceId replacement (canonical_project_formula_trace_condition_with_ids
            entryDepth code (x#codesId) (x#depthsId)
            lastIndexId indexId
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId) =
        canonical_project_formula_trace_condition_with_ids
          entryDepthResult codeResult (x#codesId) (x#depthsId)
          lastIndexId indexId
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId :=
    canonical_project_formula_trace_condition_with_ids_substitute_free
      entryDepth code (x#codesId) (x#depthsId)
      replacement entryDepthResult codeResult (x#codesId) (x#depthsId)
      sourceId lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      hSourceNeLastIndex hSourceNeIndex
      hSourceNeFirstPremise hSourceNeSecondPremise
      hSourceNeLeftCode hSourceNeRightCode
      hSourceNeLeftDepth hSourceNeRightDepth
      hReplacement.1 (hReplacementFresh lastIndexId) (hReplacementFresh indexId) (hReplacementFresh firstPremiseId) (hReplacementFresh secondPremiseId)
      (hReplacementFresh leftVariableCodeId) (hReplacementFresh rightVariableCodeId) (hReplacementFresh leftVariableDepthId)
      (hReplacementFresh rightVariableDepthId)
      hEntryDepthSubstitution hCodeSubstitution
      hCodesFixed hDepthsFixed
  have hCodesComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set codesId 0 subformula) =
        Formula.closeFreeAt SetSort.set codesId 0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId codesId 0 replacement subformula
      hSourceNeCodes hReplacement.1.2 (hReplacementFresh codesId)).symm
  have hDepthsComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set depthsId 0 subformula) =
        Formula.closeFreeAt SetSort.set depthsId 0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId depthsId 0 replacement subformula
      hSourceNeDepths hReplacement.1.2 (hReplacementFresh depthsId)).symm
  have hOmegaFixed :
      Term.substituteFree SetSort.set sourceId replacement (ωₘ : SetTerm) =
        ωₘ := by
    apply Term.substituteFree_eq_self_of_not_mem
    change (SetSort.set, sourceId) ∉ []
    exact List.not_mem_nil
  have hFormulaCodeSpaceFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (seq₊_spaceₘ(FormulaCodeₘ)) =
        seq₊_spaceₘ(FormulaCodeₘ) := by
    apply Term.substituteFree_eq_self_of_not_mem
    simp [Term.freeSupport, Term.freeSupportList]
  simp [canonical_project_formula_code_condition_with_ids,
    Formula.substituteFree, hCodesComm, hDepthsComm,
    hEntryDepthSubstitution, hCodeSubstitution,
    hTraceSubstitution, hOmegaFixed,
    hFormulaCodeSpaceFixed, hCodesFixed]
/--
成功的外部 canonical trace 直接给出其两条标准序列上的完整对象 trace 条件。
该结论不再暴露外层存在量词的代入细节，因此公式码分类器和后续 schema 分类器都可以
复用同一份正向证据。
-/
theorem canonical_project_hilbert_trace?_trace_condition_with_ids_derives
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) (lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hIndexNeFirstPremise : indexId ≠ firstPremiseId)
    (hIndexNeSecondPremise : indexId ≠ secondPremiseId) (hIndexNeLeftCode : indexId ≠ leftVariableCodeId) (hIndexNeRightCode : indexId ≠ rightVariableCodeId)
    (hIndexNeLeftDepth : indexId ≠ leftVariableDepthId) (hIndexNeRightDepth : indexId ≠ rightVariableDepthId) (hPremiseIds : firstPremiseId ≠ secondPremiseId)
    (hLeftCodeNeRightCode :
      leftVariableCodeId ≠ rightVariableCodeId) (hLeftCodeNeLeftDepth :
      leftVariableCodeId ≠ leftVariableDepthId) (hRightCodeNeRightDepth :
      rightVariableCodeId ≠ rightVariableDepthId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_formula_trace_condition_with_ids (numₘ(entryDepth)) trace.rootCode
        trace.code_sequence trace.depth_sequence
        lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId := by
  have hLastIndex :
      Term.Admissible (numₘ(trace.rootIndex)) SetSort.set :=
    finite_numeral_term_admissible trace.rootIndex
  have hCodesBoundary :=
    canonical_project_hilbert_trace_from?_code_sequence_boundary hTrace
  have hDepthsBoundary :=
    canonical_project_trace_depth_sequence_boundary trace
  have hRootCodeBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary hTrace
  have hCodesFixed :
      Term.substituteFree SetSort.set lastIndexId (numₘ(trace.rootIndex)) trace.code_sequence =
        trace.code_sequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hCodesBoundary.2]
    exact List.not_mem_nil
  have hDepthsFixed :
      Term.substituteFree SetSort.set lastIndexId (numₘ(trace.rootIndex)) trace.depth_sequence =
        trace.depth_sequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hDepthsBoundary.2]
    exact List.not_mem_nil
  have hRootCodeFixed :
      Term.substituteFree SetSort.set lastIndexId (numₘ(trace.rootIndex)) trace.rootCode =
        trace.rootCode := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hRootCodeBoundary.2]
    exact List.not_mem_nil
  have hEntryDepthFixed :
      Term.substituteFree SetSort.set lastIndexId (numₘ(trace.rootIndex)) (numₘ(entryDepth)) =
        numₘ(entryDepth) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  unfold canonical_project_formula_trace_condition_with_ids
  apply FirstOrder.Derives.conjIntro
  · apply FirstOrder.Derives.conjIntro
    · apply FirstOrder.Derives.conjIntro
      · exact FirstOrder.Derives.conjIntro (canonical_project_hilbert_trace?_code_sequence_mem hTrace)
          (canonical_project_hilbert_trace?_depth_sequence_mem hTrace)
      · exact canonical_project_hilbert_trace?_sequence_domains_eq hTrace
    · exact canonical_project_hilbert_trace?_zero_mem_domain hTrace
  · apply FirstOrder.Derives.conjIntro
    · exact canonical_project_hilbert_trace?_line_conditions_derives
        hTrace
        indexId firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId
        hIndexNeFirstPremise
        hIndexNeSecondPremise
        hIndexNeLeftCode
        hIndexNeRightCode
        hIndexNeLeftDepth
        hIndexNeRightDepth
        hPremiseIds
        hLeftCodeNeRightCode
        hLeftCodeNeLeftDepth
        hRightCodeNeRightDepth
    · nd_apply FirstOrder.Derives.exists_intro
        (term := numₘ(trace.rootIndex))
      rw [Formula.openAt_closeFreeAt_eq_substituteFree]
      simpa [canonical_project_formula_terminal_condition,
        Formula.substituteFree, Term.substituteFree,
        set_variable, hCodesFixed, hDepthsFixed,
        hRootCodeFixed, hEntryDepthFixed] using
        canonical_project_hilbert_trace?_terminal_contract hTrace
/--
成功的 external canonical trace 满足带显式 binder 编号的公式码分类条件。
两条标准序列先在 trace 核心中完成验证，再经统一的闭项代入引理封装为外层存在见证。
-/
theorem canonical_project_hilbert_trace?_code_condition_with_ids_derives
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) (codesId depthsId lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hCodesNeDepths : codesId ≠ depthsId) (hCodesNeLastIndex : codesId ≠ lastIndexId)
    (hCodesNeIndex : codesId ≠ indexId) (hCodesNeFirstPremise : codesId ≠ firstPremiseId) (hCodesNeSecondPremise : codesId ≠ secondPremiseId)
    (hCodesNeLeftCode : codesId ≠ leftVariableCodeId) (hCodesNeRightCode : codesId ≠ rightVariableCodeId) (hCodesNeLeftDepth : codesId ≠ leftVariableDepthId)
    (hCodesNeRightDepth : codesId ≠ rightVariableDepthId) (hDepthsNeLastIndex : depthsId ≠ lastIndexId) (hDepthsNeIndex : depthsId ≠ indexId)
    (hDepthsNeFirstPremise : depthsId ≠ firstPremiseId) (hDepthsNeSecondPremise : depthsId ≠ secondPremiseId)
    (hDepthsNeLeftCode : depthsId ≠ leftVariableCodeId) (hDepthsNeRightCode : depthsId ≠ rightVariableCodeId)
    (hDepthsNeLeftDepth : depthsId ≠ leftVariableDepthId) (hDepthsNeRightDepth : depthsId ≠ rightVariableDepthId)
    (hIndexNeFirstPremise : indexId ≠ firstPremiseId) (hIndexNeSecondPremise : indexId ≠ secondPremiseId) (hIndexNeLeftCode : indexId ≠ leftVariableCodeId)
    (hIndexNeRightCode : indexId ≠ rightVariableCodeId) (hIndexNeLeftDepth : indexId ≠ leftVariableDepthId)
    (hIndexNeRightDepth : indexId ≠ rightVariableDepthId) (hPremiseIds : firstPremiseId ≠ secondPremiseId) (hLeftCodeNeRightCode :
      leftVariableCodeId ≠ rightVariableCodeId) (hLeftCodeNeLeftDepth :
      leftVariableCodeId ≠ leftVariableDepthId) (hRightCodeNeRightDepth :
      rightVariableCodeId ≠ rightVariableDepthId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_formula_code_condition_with_ids (numₘ(entryDepth)) trace.rootCode
        codesId depthsId lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId := by
  have hCodesBoundary :=
    canonical_project_hilbert_trace_from?_code_sequence_boundary hTrace
  have hDepthsBoundary :=
    canonical_project_trace_depth_sequence_boundary trace
  have hRootCodeBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary hTrace
  have hCodesFresh (binderId : FreeVarId) : (SetSort.set, binderId) ∉
        Term.freeSupport trace.code_sequence := by
    rw [hCodesBoundary.2]
    exact List.not_mem_nil
  have hDepthsFresh (binderId : FreeVarId) : (SetSort.set, binderId) ∉
        Term.freeSupport trace.depth_sequence := by
    rw [hDepthsBoundary.2]
    exact List.not_mem_nil
  have hEntryDepthFixed (sourceId : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(entryDepth)) =
        numₘ(entryDepth) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hRootCodeFixed (sourceId : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement trace.rootCode =
        trace.rootCode := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hRootCodeBoundary.2]
    exact List.not_mem_nil
  have hCodeSequenceFixed (sourceId : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement
          trace.code_sequence =
        trace.code_sequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hCodesBoundary.2]
    exact List.not_mem_nil
  have hFormulaCodeSpaceFixed :
      Term.substituteFree SetSort.set codesId
          trace.code_sequence
          (seq₊_spaceₘ(FormulaCodeₘ)) =
        seq₊_spaceₘ(FormulaCodeₘ) := by
    apply Term.substituteFree_eq_self_of_not_mem
    simp [Term.freeSupport, Term.freeSupportList]
  have hCodesVariableSubstitution :
      Term.substituteFree SetSort.set codesId
          trace.code_sequence (x#codesId) =
        trace.code_sequence := by
    simp [Term.substituteFree, set_variable]
  have hDepthsVariableFixedUnderCodes :
      Term.substituteFree SetSort.set codesId
          trace.code_sequence (x#depthsId) =
        x#depthsId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hCodesNeDepths]
  have hDepthsVariableSubstitution :
      Term.substituteFree SetSort.set depthsId
          trace.depth_sequence (x#depthsId) =
        trace.depth_sequence := by
    simp [Term.substituteFree, set_variable]
  have hCoreCodesSubstitution :
      Formula.substituteFree SetSort.set codesId
          trace.code_sequence (canonical_project_formula_trace_condition_with_ids (numₘ(entryDepth)) trace.rootCode (x#codesId) (x#depthsId)
            lastIndexId indexId
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId) =
        canonical_project_formula_trace_condition_with_ids (numₘ(entryDepth)) trace.rootCode
          trace.code_sequence (x#depthsId)
          lastIndexId indexId
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId := by
    exact
      canonical_project_formula_trace_condition_with_ids_substitute_free (numₘ(entryDepth)) trace.rootCode (x#codesId) (x#depthsId)
        trace.code_sequence (numₘ(entryDepth)) trace.rootCode
        trace.code_sequence (x#depthsId)
        codesId lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId
        hCodesNeLastIndex hCodesNeIndex
        hCodesNeFirstPremise hCodesNeSecondPremise
        hCodesNeLeftCode hCodesNeRightCode
        hCodesNeLeftDepth hCodesNeRightDepth
        hCodesBoundary.1 (hCodesFresh lastIndexId) (hCodesFresh indexId) (hCodesFresh firstPremiseId) (hCodesFresh secondPremiseId)
        (hCodesFresh leftVariableCodeId) (hCodesFresh rightVariableCodeId) (hCodesFresh leftVariableDepthId) (hCodesFresh rightVariableDepthId)
        (hEntryDepthFixed codesId trace.code_sequence) (hRootCodeFixed codesId trace.code_sequence)
        hCodesVariableSubstitution
        hDepthsVariableFixedUnderCodes
  have hCoreDepthsSubstitution :
      Formula.substituteFree SetSort.set depthsId
          trace.depth_sequence (canonical_project_formula_trace_condition_with_ids (numₘ(entryDepth)) trace.rootCode
            trace.code_sequence (x#depthsId)
            lastIndexId indexId
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId) =
        canonical_project_formula_trace_condition_with_ids (numₘ(entryDepth)) trace.rootCode
          trace.code_sequence trace.depth_sequence
          lastIndexId indexId
          firstPremiseId secondPremiseId
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId := by
    exact
      canonical_project_formula_trace_condition_with_ids_substitute_free (numₘ(entryDepth)) trace.rootCode
        trace.code_sequence (x#depthsId)
        trace.depth_sequence (numₘ(entryDepth)) trace.rootCode
        trace.code_sequence trace.depth_sequence
        depthsId lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId
        hDepthsNeLastIndex hDepthsNeIndex
        hDepthsNeFirstPremise hDepthsNeSecondPremise
        hDepthsNeLeftCode hDepthsNeRightCode
        hDepthsNeLeftDepth hDepthsNeRightDepth
        hDepthsBoundary.1 (hDepthsFresh lastIndexId) (hDepthsFresh indexId) (hDepthsFresh firstPremiseId) (hDepthsFresh secondPremiseId)
        (hDepthsFresh leftVariableCodeId) (hDepthsFresh rightVariableCodeId) (hDepthsFresh leftVariableDepthId) (hDepthsFresh rightVariableDepthId)
        (hEntryDepthFixed depthsId trace.depth_sequence) (hRootCodeFixed depthsId trace.depth_sequence) (hCodeSequenceFixed depthsId trace.depth_sequence)
        hDepthsVariableSubstitution
  have hCodesPastDepths :
      Formula.substituteFree SetSort.set codesId
          trace.code_sequence (∃ₘ[SetSort.set, depthsId],
            canonical_project_formula_trace_condition_with_ids (numₘ(entryDepth)) trace.rootCode (x#codesId) (x#depthsId)
              lastIndexId indexId
              firstPremiseId secondPremiseId
              leftVariableCodeId rightVariableCodeId
              leftVariableDepthId rightVariableDepthId) = (∃ₘ[SetSort.set, depthsId],
          canonical_project_formula_trace_condition_with_ids (numₘ(entryDepth)) trace.rootCode
            trace.code_sequence (x#depthsId)
            lastIndexId indexId
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId) := by
    change
      Formula.substituteFree SetSort.set codesId
          trace.code_sequence (Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set depthsId 0 (canonical_project_formula_trace_condition_with_ids
                (numₘ(entryDepth)) trace.rootCode (x#codesId) (x#depthsId)
                lastIndexId indexId
                firstPremiseId secondPremiseId
                leftVariableCodeId rightVariableCodeId
                leftVariableDepthId rightVariableDepthId))) =
        Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set depthsId 0 (canonical_project_formula_trace_condition_with_ids
              (numₘ(entryDepth)) trace.rootCode
              trace.code_sequence (x#depthsId)
              lastIndexId indexId
              firstPremiseId secondPremiseId
              leftVariableCodeId rightVariableCodeId
              leftVariableDepthId rightVariableDepthId))
    simp only [Formula.substituteFree]
    apply congrArg (fun formula : SetFormula =>
      Formula.existsE SetSort.set formula)
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set codesId depthsId 0 trace.code_sequence _
      hCodesNeDepths hCodesBoundary.1.2 (hCodesFresh depthsId)]
    exact congrArg (Formula.closeFreeAt SetSort.set depthsId 0)
      hCoreCodesSubstitution
  have hEntryDepthOmega :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(entryDepth) ∈ₘ ωₘ :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_omega
        entryDepth)
  have hRootFormulaCode :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        formula_codeₘ(trace.rootCode) :=
    GodelQuotation.gq_is_formula_code_of_mem
      trace.rootCode hRootCodeBoundary.1 (canonical_project_hilbert_trace_from?_root_formula_code_mem
        hTrace)
  have hCore :=
    canonical_project_hilbert_trace?_trace_condition_with_ids_derives
      hTrace
      lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      hIndexNeFirstPremise
      hIndexNeSecondPremise
      hIndexNeLeftCode
      hIndexNeRightCode
      hIndexNeLeftDepth
      hIndexNeRightDepth
      hPremiseIds
      hLeftCodeNeRightCode
      hLeftCodeNeLeftDepth
      hRightCodeNeRightDepth
  unfold canonical_project_formula_code_condition_with_ids
  apply FirstOrder.Derives.conjIntro
  · exact FirstOrder.Derives.conjIntro
      hEntryDepthOmega hRootFormulaCode
  · nd_apply FirstOrder.Derives.exists_intro
      (term := trace.code_sequence)
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    change
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        Formula.substituteFree SetSort.set codesId
            trace.code_sequence
            (x#codesId ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
          Formula.substituteFree SetSort.set codesId
            trace.code_sequence
            (∃ₘ[SetSort.set, depthsId],
              canonical_project_formula_trace_condition_with_ids
                (numₘ(entryDepth)) trace.rootCode
                (x#codesId) (x#depthsId)
                lastIndexId indexId
                firstPremiseId secondPremiseId
                leftVariableCodeId rightVariableCodeId
                leftVariableDepthId rightVariableDepthId)
    apply FirstOrder.Derives.conjIntro
    · simpa [Formula.substituteFree, Term.substituteFree,
        set_variable, hCodesVariableSubstitution,
        hFormulaCodeSpaceFixed] using
        canonical_project_hilbert_trace?_code_sequence_mem
          hTrace
    · rw [hCodesPastDepths]
      nd_apply FirstOrder.Derives.exists_intro
        (term := trace.depth_sequence)
      rw [Formula.openAt_closeFreeAt_eq_substituteFree]
      rw [hCoreDepthsSubstitution]
      exact hCore
/--
从任意基础编号连续分配十个内部 binder，即可装配完整的规范公式码分类证书。
该接口把纯机械的编号互异性集中消除；需要在等式运输前固定内部 binder 的调用方可
直接选择基础编号，公开分类器则选择由候选参数计算出的新鲜基础编号。
-/
theorem canonical_project_hilbert_trace?_code_condition_from_base_derives
    {entryDepth : Nat}
    {formula : SetFormula}
    {trace : CanonicalProjectTrace} (hTrace :
      canonical_project_hilbert_trace?
        entryDepth formula = some trace) (base : FreeVarId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_formula_code_condition_with_ids (numₘ(entryDepth)) trace.rootCode
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9) := by
  have hOffsetNe (left right : Nat) (hOffset : left ≠ right) :
      base + left ≠ base + right := by
    intro hEquality
    exact hOffset (Nat.add_left_cancel hEquality)
  exact
    canonical_project_hilbert_trace?_code_condition_with_ids_derives
      hTrace
      base (base + 1) (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9) (hOffsetNe 0 1 (by omega))
      (hOffsetNe 0 2 (by omega)) (hOffsetNe 0 3 (by omega)) (hOffsetNe 0 4 (by omega)) (hOffsetNe 0 5 (by omega)) (hOffsetNe 0 6 (by omega))
      (hOffsetNe 0 7 (by omega)) (hOffsetNe 0 8 (by omega)) (hOffsetNe 0 9 (by omega)) (hOffsetNe 1 2 (by omega)) (hOffsetNe 1 3 (by omega))
      (hOffsetNe 1 4 (by omega)) (hOffsetNe 1 5 (by omega)) (hOffsetNe 1 6 (by omega)) (hOffsetNe 1 7 (by omega)) (hOffsetNe 1 8 (by omega))
      (hOffsetNe 1 9 (by omega)) (hOffsetNe 3 4 (by omega)) (hOffsetNe 3 5 (by omega)) (hOffsetNe 3 6 (by omega)) (hOffsetNe 3 7 (by omega))
      (hOffsetNe 3 8 (by omega)) (hOffsetNe 3 9 (by omega)) (hOffsetNe 4 5 (by omega)) (hOffsetNe 6 7 (by omega)) (hOffsetNe 6 8 (by omega))
      (hOffsetNe 7 9 (by omega))
/--
连续编号版公式码条件允许把最后一个保留编号作为入口深度孔进行闭项代入。
该规范化定理固定全部内部 binder，只改变入口深度项；因此对象等式可以在不引入
α-改名兼容层的前提下运输整条 canonical trace 证书。
-/
theorem canonical_project_formula_code_condition_from_base_substitute_entry_depth (replacement code : SetTerm) (base : FreeVarId) (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement) (hCode : GodelQuotation.Numbered.CodeBoundary code) :
    Formula.substituteFree SetSort.set (base + 10) replacement (canonical_project_formula_code_condition_with_ids (x#(base + 10)) code
          base (base + 1) (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9)) =
      canonical_project_formula_code_condition_with_ids
        replacement code
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9) := by
  let sourceId := base + 10
  have hSourceNe (offset : Nat) (hOffset : offset < 10) :
      sourceId ≠ base + offset := by
    dsimp [sourceId]
    intro hEquality
    have hTenEq : 10 = offset :=
      Nat.add_left_cancel hEquality
    exact (Nat.ne_of_lt hOffset) hTenEq.symm
  have hReplacementFresh (id : FreeVarId) : (SetSort.set, id) ∉
        Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hCodeFixed :
      Term.substituteFree SetSort.set sourceId replacement code =
        code := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hCode.2]
    exact List.not_mem_nil
  have hEntryDepthSubstitution :
      Term.substituteFree SetSort.set sourceId replacement (x#sourceId) =
        replacement := by
    simp [Term.substituteFree, set_variable]
  have hCodesSubstitution :
      Term.substituteFree SetSort.set sourceId replacement (x#base) =
        x#base := by
    simp [Term.substituteFree, set_variable,
      sourceId]
  have hDepthsSubstitution :
      Term.substituteFree SetSort.set sourceId replacement (x#(base + 1)) =
        x#(base + 1) := by
    simp [Term.substituteFree, set_variable,
      sourceId]
  have hTraceSubstitution :
      Formula.substituteFree SetSort.set sourceId replacement (canonical_project_formula_trace_condition_with_ids (x#sourceId) code (x#base) (x#(base + 1))
            (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9)) =
        canonical_project_formula_trace_condition_with_ids
          replacement code (x#base) (x#(base + 1)) (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9) := by
    exact
      canonical_project_formula_trace_condition_with_ids_substitute_free (x#sourceId) code (x#base) (x#(base + 1))
        replacement replacement code (x#base) (x#(base + 1))
        sourceId (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9) (hSourceNe 2 (by omega)) (hSourceNe 3 (by omega))
        (hSourceNe 4 (by omega)) (hSourceNe 5 (by omega)) (hSourceNe 6 (by omega)) (hSourceNe 7 (by omega)) (hSourceNe 8 (by omega)) (hSourceNe 9 (by omega))
        hReplacement.1 (hReplacementFresh (base + 2)) (hReplacementFresh (base + 3)) (hReplacementFresh (base + 4)) (hReplacementFresh (base + 5))
        (hReplacementFresh (base + 6)) (hReplacementFresh (base + 7)) (hReplacementFresh (base + 8)) (hReplacementFresh (base + 9))
        hEntryDepthSubstitution hCodeFixed
        hCodesSubstitution hDepthsSubstitution
  have hCodesComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set base 0 subformula) =
        Formula.closeFreeAt SetSort.set base 0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId base 0 replacement subformula (hSourceNe 0 (by omega))
      hReplacement.1.2 (hReplacementFresh base)).symm
  have hDepthsComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set (base + 1)
            0 subformula) =
        Formula.closeFreeAt SetSort.set (base + 1) 0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId (base + 1) 0 replacement subformula (hSourceNe 1 (by omega))
      hReplacement.1.2 (hReplacementFresh (base + 1))).symm
  simp [canonical_project_formula_code_condition_with_ids,
    sourceId, Formula.substituteFree, Term.substituteFree,
    set_variable, hCodeFixed, hCodesComm, hDepthsComm,
    hTraceSubstitution]
/--
入口深度的对象等式可运输连续编号版的完整 canonical 公式码条件。
两端深度与公式码均要求闭代码边界，以保证等式替换不会把自由变量带入内部证书
binder；该条件正好匹配 quotation 与对象算术计算产生的标准代码项。
-/
theorem canonical_project_formula_code_condition_from_base_iff_of_entry_depth_equality
    {T : SetTheory} {Γ : Context signature} (left right code : SetTerm) (base : FreeVarId) (hLeft : GodelQuotation.Numbered.CodeBoundary left)
    (hRight : GodelQuotation.Numbered.CodeBoundary right) (hCode : GodelQuotation.Numbered.CodeBoundary code) (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      canonical_project_formula_code_condition_with_ids
          left code
          base (base + 1) (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9) ↔ₘ
        canonical_project_formula_code_condition_with_ids
          right code
          base (base + 1) (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9) := by
  let sourceId := base + 10
  let body :=
    canonical_project_formula_code_condition_with_ids (x#sourceId) code
      base (base + 1) (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9)
  have hBody : Formula.Admissible body := by
    simpa [body] using
      canonical_project_formula_code_condition_with_ids_admissible (x#sourceId) code
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 5) (base + 6) (base + 7) (base + 8) (base + 9) (set_variable_admissible sourceId) hCode.1
  have hTransport :=
    Metatheory.Derives.equality_iff_of_equality (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := sourceId) (left := left) (right := right) (body := body)
      hEquality
  change
    Γ ⊢ₘ[T] (Formula.substituteFree SetSort.set sourceId left body ↔ₘ
        Formula.substituteFree SetSort.set sourceId right body)
    at hTransport
  simpa [body, sourceId,
    canonical_project_formula_code_condition_from_base_substitute_entry_depth
      left code base hLeft hCode,
    canonical_project_formula_code_condition_from_base_substitute_entry_depth
      right code base hRight hCode] using hTransport
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
