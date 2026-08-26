import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.FormulaTrace
/-!
# 规范全称前缀的对象证书
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/-! ## 任意长规范全称前缀的对象合法性 -/
/-- 具体深度的规范 binder 变量码属于对象变量符号集合。 -/
theorem canonical_binder_variable_code_numeral_mem (depth : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_binder_variable_code_term (numₘ(depth)) ∈ₘ VarSymₘ := by
  let namedCode :=
    GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth)
  let canonicalCode :=
    canonical_binder_variable_code_term (numₘ(depth))
  have hNamedBoundary :
      GodelQuotation.Numbered.CodeBoundary namedCode := by
    constructor
    · exact variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name depth))
    · simp [namedCode]
  have hCanonicalBoundary :
      GodelQuotation.Numbered.CodeBoundary canonicalCode := by
    simpa [canonicalCode] using
      canonical_binder_variable_code_numeral_boundary depth
  have hEquality :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        namedCode ≐ₘ canonicalCode := by
    simpa [namedCode, canonicalCode] using
      canonical_binder_variable_code_numeral_derives depth
  exact FirstOrder.Derives.iffElimRight (membership_left_iff_of_equality
      namedCode canonicalCode VarSymₘ
      hNamedBoundary.1 hCanonicalBoundary.1
      variable_symbol_set_term_admissible hEquality) (by
      simpa [namedCode] using
        GodelQuotation.named_variable_code_mem_variable_symbols (GodelQuotation.bound_name depth))
/--
quotation 已求值的全称前缀可同时运输 binder 表示与核心码等式。
左侧每个 binder 直接写入具体奇数名称，右侧使用分类器的对象算术表达式；核心码
则允许由调用方提供任意对象等式。这个接口把“局部骨架正规化”和“任意长外层参数
闭合”彻底分离，供所有公理模式共同复用。
-/
theorem canonical_quoted_forall_prefix_code_from_congr_of_equality (start count : Nat) (leftCore rightCore : SetTerm) (hLeftCore :
      GodelQuotation.Numbered.CodeBoundary leftCore) (hRightCore :
      GodelQuotation.Numbered.CodeBoundary rightCore) (hCoreEquality :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        leftCore ≐ₘ rightCore) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_quoted_forall_prefix_code_from
          start count leftCore ≐ₘ
        canonical_forall_prefix_code_from
          start count rightCore := by
  induction count generalizing start with
  | zero =>
      simpa [
        canonical_quoted_forall_prefix_code_from,
        canonical_forall_prefix_code_from] using hCoreEquality
  | succ count ih =>
      have hQuotedBinder :=
        canonical_quoted_binder_variable_code_boundary start
      have hCanonicalBinder :=
        canonical_binder_variable_code_numeral_boundary start
      have hQuotedBody :=
        canonical_quoted_forall_prefix_code_from_boundary (start + 1) count leftCore hLeftCore
      have hCanonicalBody :=
        canonical_forall_prefix_code_from_boundary (start + 1) count rightCore hRightCore
      have hUniversal :=
        canonical_universal_code_term_congr_of_equalities (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name start))
          (canonical_binder_variable_code_term (numₘ(start))) (canonical_quoted_forall_prefix_code_from (start + 1) count leftCore)
          (canonical_forall_prefix_code_from (start + 1) count rightCore)
          hQuotedBinder.1 hCanonicalBinder.1
          hQuotedBody.1 hCanonicalBody.1 (canonical_binder_variable_code_numeral_derives start) (ih (start + 1))
      simpa only [
        canonical_quoted_forall_prefix_code_from,
        canonical_forall_prefix_code_from] using hUniversal
/-- 从深度零开始的 quotation 前缀可运输任意核心码等式。 -/
theorem canonical_quoted_forall_prefix_code_congr_of_equality (count : Nat) (leftCore rightCore : SetTerm) (hLeftCore :
      GodelQuotation.Numbered.CodeBoundary leftCore) (hRightCore :
      GodelQuotation.Numbered.CodeBoundary rightCore) (hCoreEquality :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        leftCore ≐ₘ rightCore) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_quoted_forall_prefix_code count leftCore ≐ₘ
        canonical_forall_prefix_code count rightCore := by
  exact canonical_quoted_forall_prefix_code_from_congr_of_equality
    0 count leftCore rightCore
    hLeftCore hRightCore hCoreEquality
/-- 规范全称前缀构造保持 `FormulaCodeₘ` 成员关系。 -/
theorem canonical_forall_prefix_code_from_formula_mem (start count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core) (hCoreMember :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        core ∈ₘ FormulaCodeₘ) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_forall_prefix_code_from
        start count core ∈ₘ FormulaCodeₘ := by
  induction count generalizing start with
  | zero =>
      simpa [canonical_forall_prefix_code_from] using hCoreMember
  | succ count ih =>
      have hBodyBoundary :=
        canonical_forall_prefix_code_from_boundary (start + 1) count core hCore
      exact GodelQuotation.gq_formula_code_mem_universal (canonical_binder_variable_code_term (numₘ(start))) (canonical_forall_prefix_code_from
          (start + 1) count core) (canonical_binder_variable_code_numeral_boundary start).1
        hBodyBoundary.1 (canonical_binder_variable_code_numeral_mem start) (ih (start + 1))
/-- 规范全称前缀剥离轨迹的每一项都属于 `FormulaCodeₘ`。 -/
theorem canonical_forall_prefix_trace_terms_from_formula_mem (start count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core)
    (hCoreMember :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        core ∈ₘ FormulaCodeₘ) :
    ∀ code,
      code ∈ canonical_forall_prefix_trace_terms_from
        start count core →
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        code ∈ₘ FormulaCodeₘ := by
  induction count generalizing start with
  | zero =>
      intro code hCode
      simp only [canonical_forall_prefix_trace_terms_from,
        List.mem_singleton] at hCode
      simpa [hCode] using hCoreMember
  | succ count ih =>
      intro code hCode
      simp only [canonical_forall_prefix_trace_terms_from,
        List.mem_cons] at hCode
      rcases hCode with rfl | hCode
      · exact canonical_forall_prefix_code_from_formula_mem
          start (count + 1) core hCore hCoreMember
      · exact ih (start + 1) code hCode
/-- 规范全称前缀的标准剥离序列满足闭代码边界。 -/
theorem canonical_forall_prefix_standard_trace_boundary (count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core) :
    GodelQuotation.Numbered.CodeBoundary (GodelQuotation.standard_sequence (canonical_forall_prefix_trace_terms count core)) := by
  constructor
  · exact GodelQuotation.seq_admissible_m 0 <| by
      intro code hCode
      exact (canonical_forall_prefix_trace_terms_from_boundary
          0 count core hCore code hCode).1
  · exact GodelQuotation.seq_support_nil_m 0 <| by
      intro code hCode
      exact (canonical_forall_prefix_trace_terms_from_boundary
          0 count core hCore code hCode).2
/-- 规范全称前缀的标准剥离序列属于非空公式码序列空间。 -/
theorem canonical_forall_prefix_standard_trace_mem (count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core) (hCoreMember :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        core ∈ₘ FormulaCodeₘ) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      GodelQuotation.standard_sequence (canonical_forall_prefix_trace_terms count core) ∈ₘ
        seq₊_spaceₘ(FormulaCodeₘ) := by
  have hFormulaCodeNonempty :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        FormulaCodeₘ ≠ₘ ∅ₘ := by
    have hImp :
        ⊢ₘ[GodelQuotation.godel_quotation_theory] (core ∈ₘ FormulaCodeₘ) ⟶ₘ (FormulaCodeₘ ≠ₘ ∅ₘ) := by
      apply GodelQuotation.gq_weaken_standard_sequence
      exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFormula))))) (member_implies_set_nonempty
          core FormulaCodeₘ hCore.1
          formula_code_set_term_admissible)
    exact FirstOrder.Derives.impElim hImp hCoreMember
  exact
    GodelQuotation.standard_sequence_mem_nonempty_sequence_space_of_theory (T := GodelQuotation.godel_quotation_theory) (fun _ hFormula => Or.inl hFormula)
      (fun _ hFormula =>
        GodelQuotation.godel_quotation_theory_sentence hFormula)
      FormulaCodeₘ (fun code hCode =>
        (canonical_forall_prefix_trace_terms_from_boundary
          0 count core hCore code hCode).1) (fun code hCode =>
        (canonical_forall_prefix_trace_terms_from_boundary
          0 count core hCore code hCode).2)
      formula_code_set_term_admissible (by native_decide)
      hFormulaCodeNonempty (canonical_forall_prefix_trace_terms_from_formula_mem
        0 count core hCore hCoreMember) (by
        cases count <;>
          simp [canonical_forall_prefix_trace_terms,
            canonical_forall_prefix_trace_terms_from])
/-- 规范全称前缀标准轨迹的定义域是 binder 数量的对象后继。 -/
theorem canonical_forall_prefix_standard_trace_domain (count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      domₘ(GodelQuotation.standard_sequence (canonical_forall_prefix_trace_terms count core)) ≐ₘ
        Sₘ(numₘ(count)) := by
  apply GodelQuotation.gq_weaken_standard_sequence
  simpa [canonical_forall_prefix_trace_terms,
    finite_numeral_term] using (GodelQuotation.standard_sequence_domain_eq_numeral_length (fun code hCode =>
        (canonical_forall_prefix_trace_terms_from_boundary
          0 count core hCore code hCode).1)
      (GodelQuotation.stdseq_element_fresh_of_support_nil
        (fun code hCode =>
          (canonical_forall_prefix_trace_terms_from_boundary
            0 count core hCore code hCode).2) 0)
      (GodelQuotation.stdseq_element_fresh_of_support_nil
        (fun code hCode =>
          (canonical_forall_prefix_trace_terms_from_boundary
            0 count core hCore code hCode).2) 1))
/-- 规范全称前缀标准轨迹的首项求值为完整前缀码。 -/
theorem canonical_forall_prefix_standard_trace_head (count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory] (GodelQuotation.standard_sequence (canonical_forall_prefix_trace_terms count core) ·ₘ
        numₘ(0)) ≐ₘ
          canonical_forall_prefix_code count core := by
  apply GodelQuotation.gq_weaken_standard_sequence
  exact GodelQuotation.standard_sequence_from_apply_getElem?
    0 (canonical_forall_prefix_trace_terms_from_head
      0 count core) (fun code hCode =>
      (canonical_forall_prefix_trace_terms_from_boundary
        0 count core hCore code hCode).1) (fun code hCode =>
      (canonical_forall_prefix_trace_terms_from_boundary
        0 count core hCore code hCode).2) (canonical_forall_prefix_code_from_boundary
      0 count core hCore).1
/-- 规范全称前缀标准轨迹的末项求值为核心码。 -/
theorem canonical_forall_prefix_standard_trace_last (count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory] (GodelQuotation.standard_sequence (canonical_forall_prefix_trace_terms count core) ·ₘ
        numₘ(count)) ≐ₘ core := by
  apply GodelQuotation.gq_weaken_standard_sequence
  simpa [canonical_forall_prefix_trace_terms] using (GodelQuotation.standard_sequence_from_apply_getElem?
      0 (canonical_forall_prefix_trace_terms_from_last
        0 count core) (fun code hCode =>
        (canonical_forall_prefix_trace_terms_from_boundary
          0 count core hCore code hCode).1) (fun code hCode =>
        (canonical_forall_prefix_trace_terms_from_boundary
          0 count core hCore code hCode).2)
      hCore.1)
/-- 标准轨迹在每个具体非末位置满足规范全称剥离方程。 -/
theorem canonical_forall_prefix_standard_trace_step_at_numeral
    {count index : Nat} {core : SetTerm} (hIndex : index < count) (hCore : GodelQuotation.Numbered.CodeBoundary core) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_forall_prefix_step_condition (GodelQuotation.standard_sequence (canonical_forall_prefix_trace_terms count core)) (numₘ(index)) := by
  let terms :=
    canonical_forall_prefix_trace_terms count core
  let trace := GodelQuotation.standard_sequence terms
  rcases canonical_forall_prefix_trace_terms_from_step (start := 0) (core := core) hIndex with
    ⟨body, hCurrentGet, hNextGet⟩
  have hBodyMem : body ∈ terms := by
    rcases List.getElem?_eq_some_iff.mp hNextGet with
      ⟨hNextBound, hNextValue⟩
    rw [← hNextValue]
    exact List.getElem_mem hNextBound
  have hBodyBoundary :
      GodelQuotation.Numbered.CodeBoundary body :=
    canonical_forall_prefix_trace_terms_from_boundary
      0 count core hCore body hBodyMem
  have hTermsBoundary :
      ∀ code, code ∈ terms →
        GodelQuotation.Numbered.CodeBoundary code := by
    intro code hCode
    exact canonical_forall_prefix_trace_terms_from_boundary
      0 count core hCore code hCode
  have hTraceBoundary :
      GodelQuotation.Numbered.CodeBoundary trace := by
    simpa [trace, terms] using
      canonical_forall_prefix_standard_trace_boundary
        count core hCore
  have hBinderBoundary :=
    canonical_binder_variable_code_numeral_boundary index
  have hCurrentCode :
      Term.Admissible (forall_codeₘ(
          canonical_binder_variable_code_term (numₘ(index)),
          body)) SetSort.set :=
    universal_formula_code_term_admissible _ _
      hBinderBoundary.1 hBodyBoundary.1
  have hCurrent :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace ·ₘ numₘ(index)) ≐ₘ
          forall_codeₘ(
            canonical_binder_variable_code_term (numₘ(index)),
            body) := by
    apply GodelQuotation.gq_weaken_standard_sequence
    simpa [trace, terms] using (GodelQuotation.standard_sequence_from_apply_getElem?
        0 (by
          simpa [terms, Nat.zero_add] using hCurrentGet) (fun code hCode => (hTermsBoundary code hCode).1) (fun code hCode => (hTermsBoundary code hCode).2)
        hCurrentCode)
  have hNext :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (trace ·ₘ numₘ(index + 1)) ≐ₘ body := by
    apply GodelQuotation.gq_weaken_standard_sequence
    simpa [trace, terms] using (GodelQuotation.standard_sequence_from_apply_getElem?
        0 (by simpa [terms] using hNextGet) (fun code hCode => (hTermsBoundary code hCode).1) (fun code hCode => (hTermsBoundary code hCode).2)
        hBodyBoundary.1)
  have hNextApplication :
      Term.Admissible (trace ·ₘ Sₘ(numₘ(index))) SetSort.set :=
    function_application_term_admissible
      trace (Sₘ(numₘ(index))) hTraceBoundary.1 (successor_term_admissible _ (finite_numeral_term_admissible index))
  have hBodyToNext :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        body ≐ₘ (trace ·ₘ Sₘ(numₘ(index))) := by
    simpa [finite_numeral_term] using (Metatheory.Derives.equality_symm hNext)
  have hBinderReflexive :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_binder_variable_code_term (numₘ(index)) ≐ₘ
          canonical_binder_variable_code_term (numₘ(index)) :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set)
      (canonical_binder_variable_code_term (numₘ(index)))
  have hUniversalTransport :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        forall_codeₘ(
          canonical_binder_variable_code_term (numₘ(index)),
          body) ≐ₘ
        forall_codeₘ(
          canonical_binder_variable_code_term (numₘ(index)),
          trace ·ₘ Sₘ(numₘ(index))) :=
    canonical_universal_code_term_congr_of_equalities (canonical_binder_variable_code_term (numₘ(index))) (canonical_binder_variable_code_term (numₘ(index)))
      body (trace ·ₘ Sₘ(numₘ(index)))
      hBinderBoundary.1 hBinderBoundary.1
      hBodyBoundary.1 hNextApplication
      hBinderReflexive hBodyToNext
  unfold canonical_forall_prefix_step_condition
  exact Metatheory.Derives.equality_trans (middle :=
      forall_codeₘ(
        canonical_binder_variable_code_term (numₘ(index)),
        body))
    (by simpa [trace] using hCurrent) (by simpa [trace] using hUniversalTransport)
/-- 索引等式把具体 numeral 处的前缀剥离方程运输回自由索引。 -/
private theorem canonical_forall_prefix_step_condition_of_index_equality (trace : SetTerm) (indexId : FreeVarId)
    (hTrace : GodelQuotation.Numbered.CodeBoundary trace) (index : Nat) (hConcrete :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_forall_prefix_step_condition
          trace (numₘ(index))) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory] ((x#indexId ≐ₘ numₘ(index)) ⟶ₘ
        canonical_forall_prefix_step_condition
          trace (x#indexId)) := by
  let point : SetTerm := x#indexId
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let body : SetFormula :=
    canonical_forall_prefix_step_condition trace point
  let Γ : Context signature := [equality]
  have hPoint : Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hEqualityAdmissible :
      Formula.Admissible equality := by
    simpa [equality] using
      Formula.Admissible.equal hPoint (finite_numeral_term_admissible index)
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      canonical_forall_prefix_step_condition_admissible
        trace point hTrace.1 hPoint
  have hTraceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set indexId replacement trace =
        trace := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTrace.2]
    exact List.not_mem_nil
  have hPointSubstitution (replacement : SetTerm) :
      Term.substituteFree SetSort.set indexId replacement point =
        replacement := by
    simp [point, Term.substituteFree]
  have hNumeralFixed (number : Nat) (replacement : SetTerm) :
      Term.substituteFree SetSort.set indexId replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hNormalize (replacement : SetTerm) :
      Formula.substituteFree SetSort.set indexId replacement body =
        canonical_forall_prefix_step_condition
          trace replacement := by
    simp [body, canonical_forall_prefix_step_condition,
      Formula.substituteFree, Term.substituteFree,
      hTraceFixed, hPointSubstitution, hNumeralFixed]
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
  have hTransport :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_forall_prefix_step_condition trace point ↔ₘ
          canonical_forall_prefix_step_condition
            trace (numₘ(index)) := by
    simpa only [hNormalize point,
      hNormalize (numₘ(index))] using hIff
  have hConcreteInContext :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_forall_prefix_step_condition
          trace (numₘ(index)) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hConcrete
  have hResult :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_forall_prefix_step_condition trace point :=
    FirstOrder.Derives.iffElimLeft
      hTransport hConcreteInContext
  have hImplication :=
    FirstOrder.Derives.impIntro hResult
  simpa [Γ, equality, point] using hImplication
/-- 标准全称前缀轨迹在整个 binder 区间上逐点满足剥离方程。 -/
theorem canonical_forall_prefix_standard_trace_pointwise (count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core)
    (indexId : FreeVarId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      ∀ₘ[SetSort.set, indexId], ((x#indexId ∈ₘ numₘ(count)) ⟶ₘ
          canonical_forall_prefix_step_condition (GodelQuotation.standard_sequence (canonical_forall_prefix_trace_terms count core)) (x#indexId)) := by
  let trace :=
    GodelQuotation.standard_sequence (canonical_forall_prefix_trace_terms count core)
  let point : SetTerm := x#indexId
  let conclusion : SetFormula :=
    canonical_forall_prefix_step_condition trace point
  have hTraceBoundary :
      GodelQuotation.Numbered.CodeBoundary trace := by
    simpa [trace] using
      canonical_forall_prefix_standard_trace_boundary
        count core hCore
  have hPoint : Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hCases :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        GodelQuotation.stdseq_numeral_member_condition
            count point ⟶ₘ
          conclusion := by
    nd_apply
      GodelQuotation.stdseq_numeral_member_condition_elim_of_theory
        count point conclusion
    intro index hIndex
    simpa [conclusion, trace, point] using
      canonical_forall_prefix_step_condition_of_index_equality
        trace indexId hTraceBoundary index (canonical_forall_prefix_standard_trace_step_at_numeral
          hIndex hCore)
  have hNumeralIff :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (point ∈ₘ numₘ(count)) ↔ₘ
          GodelQuotation.stdseq_numeral_member_condition
            count point :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.stdseq_numeral_member_iff
        count point hPoint)
  have hMembershipAdmissible :
      Formula.Admissible (point ∈ₘ numₘ(count)) :=
    membership_formula_admissible hPoint (finite_numeral_term_admissible count)
  have hOpen :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (point ∈ₘ numₘ(count)) ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [point ∈ₘ numₘ(count)]
    have hMembership :
        Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
          point ∈ₘ numₘ(count) :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hCondition :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hNumeralIff)
        hMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hTheoryFresh :
      ∀ formula,
        GodelQuotation.godel_quotation_theory formula → (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(GodelQuotation.godel_quotation_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := GodelQuotation.godel_quotation_theory) (Γ := []) (sort := SetSort.set) (eigen := indexId)
      hTheoryFresh (by simp) hOpen
  simpa [trace, point, conclusion] using hGeneralized
/-- 标准序列直接满足带显式索引编号的完整前缀轨迹合同。 -/
theorem canonical_forall_prefix_standard_trace_condition_derives (count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core)
    (hCoreMember :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        core ∈ₘ FormulaCodeₘ) (indexId : FreeVarId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_forall_prefix_trace_condition (numₘ(count))
        core (canonical_forall_prefix_code count core) (GodelQuotation.standard_sequence (canonical_forall_prefix_trace_terms count core))
        indexId := by
  unfold canonical_forall_prefix_trace_condition
  exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (canonical_forall_prefix_standard_trace_mem
        count core hCore hCoreMember) (canonical_forall_prefix_standard_trace_domain
        count core hCore)) (FirstOrder.Derives.conjIntro (canonical_forall_prefix_standard_trace_head
        count core hCore) (FirstOrder.Derives.conjIntro (canonical_forall_prefix_standard_trace_pointwise
          count core hCore indexId) (canonical_forall_prefix_standard_trace_last
          count core hCore)))
/-- 一个自由轨迹变量的闭项代入可穿过规范全称前缀轨迹合同。 -/
private theorem canonical_forall_prefix_trace_condition_substitute_free (binderCount core code trace replacement
      binderCountResult coreResult codeResult traceResult : SetTerm) (sourceId indexId : FreeVarId) (hSourceNeIndex : sourceId ≠ indexId)
    (hReplacement : Term.Admissible replacement SetSort.set) (hReplacementFreshIndex : (SetSort.set, indexId) ∉
        Term.freeSupport replacement) (hBinderCountSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          binderCount =
        binderCountResult) (hCoreSubstitution :
      Term.substituteFree SetSort.set sourceId replacement core =
        coreResult) (hCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement code =
        codeResult) (hTraceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement trace =
        traceResult) :
    Formula.substituteFree SetSort.set sourceId replacement (canonical_forall_prefix_trace_condition
          binderCount core code trace indexId) =
      canonical_forall_prefix_trace_condition
        binderCountResult coreResult codeResult traceResult indexId := by
  have hIndexComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set indexId 0 subformula) =
        Formula.closeFreeAt SetSort.set indexId 0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId indexId 0 replacement subformula
      hSourceNeIndex hReplacement.2
      hReplacementFreshIndex).symm
  have hIndexNeSource : indexId ≠ sourceId :=
    Ne.symm hSourceNeIndex
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  simp [canonical_forall_prefix_trace_condition,
    canonical_forall_prefix_step_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hIndexComm, hIndexNeSource,
    hBinderCountSubstitution, hCoreSubstitution,
    hCodeSubstitution,
    hTraceSubstitution, hNumeralFixed]
/--
闭代码项的自由变量代入逐参数穿过显式编号的规范全称前缀分类条件。
显式 trace/index 编号保持不变，binder 数量、核心码和最终码可同时随代入更新。
-/
theorem canonical_forall_prefix_code_condition_with_ids_substitute_closed (binderCount core code replacement
      binderCountResult coreResult codeResult : SetTerm) (sourceId traceId indexId : FreeVarId) (hSourceNeTrace : sourceId ≠ traceId)
    (hSourceNeIndex : sourceId ≠ indexId) (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement) (hBinderCountSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          binderCount =
        binderCountResult) (hCoreSubstitution :
      Term.substituteFree SetSort.set sourceId replacement core =
        coreResult) (hCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement code =
        codeResult) :
    Formula.substituteFree SetSort.set sourceId replacement (canonical_forall_prefix_code_condition_with_ids
          binderCount core code traceId indexId) =
      canonical_forall_prefix_code_condition_with_ids
        binderCountResult coreResult codeResult traceId indexId := by
  have hReplacementFresh (binderId : FreeVarId) : (SetSort.set, binderId) ∉
        Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hTraceFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#traceId) =
        x#traceId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeTrace]
  have hTraceConditionSubstitution :
      Formula.substituteFree SetSort.set sourceId replacement (canonical_forall_prefix_trace_condition
            binderCount core code (x#traceId) indexId) =
        canonical_forall_prefix_trace_condition
          binderCountResult coreResult codeResult (x#traceId) indexId :=
    canonical_forall_prefix_trace_condition_substitute_free
      binderCount core code (x#traceId) replacement
      binderCountResult coreResult codeResult (x#traceId)
      sourceId indexId hSourceNeIndex hReplacement.1 (hReplacementFresh indexId)
      hBinderCountSubstitution hCoreSubstitution
      hCodeSubstitution hTraceFixed
  have hTraceComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement (Formula.closeFreeAt SetSort.set traceId 0 subformula) =
        Formula.closeFreeAt SetSort.set traceId 0 (Formula.substituteFree SetSort.set sourceId
            replacement subformula) := (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId traceId 0 replacement subformula
      hSourceNeTrace hReplacement.1.2 (hReplacementFresh traceId)).symm
  have hOmegaFixed :
      Term.substituteFree SetSort.set sourceId replacement (ωₘ : SetTerm) =
        ωₘ := by
    apply Term.substituteFree_eq_self_of_not_mem
    change (SetSort.set, sourceId) ∉ []
    exact List.not_mem_nil
  simp [canonical_forall_prefix_code_condition_with_ids,
    Formula.substituteFree, hTraceComm,
    hBinderCountSubstitution, hCoreSubstitution,
    hCodeSubstitution, hTraceConditionSubstitution,
    hOmegaFixed]
/--
核心公式码的正向证书生成带显式 binder 编号的完整规范全称前缀分类证明。
-/
theorem canonical_forall_prefix_code_condition_with_ids_derives (count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core)
    (hCoreMember :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        core ∈ₘ FormulaCodeₘ) (traceId indexId : FreeVarId) (hTraceNeIndex : traceId ≠ indexId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_forall_prefix_code_condition_with_ids (numₘ(count))
        core (canonical_forall_prefix_code count core)
        traceId indexId := by
  let code := canonical_forall_prefix_code count core
  let trace :=
    GodelQuotation.standard_sequence (canonical_forall_prefix_trace_terms count core)
  have hCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary code := by
    simpa [code] using
      canonical_forall_prefix_code_from_boundary
        0 count core hCore
  have hTraceBoundary :
      GodelQuotation.Numbered.CodeBoundary trace := by
    simpa [trace] using
      canonical_forall_prefix_standard_trace_boundary
        count core hCore
  have hCodeMember :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        code ∈ₘ FormulaCodeₘ := by
    simpa [code] using
      canonical_forall_prefix_code_from_formula_mem
        0 count core hCore hCoreMember
  have hCountOmega :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(count) ∈ₘ ωₘ :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_omega
        count)
  have hCoreFormula :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        formula_codeₘ(core) :=
    GodelQuotation.gq_is_formula_code_of_mem
      core hCore.1 hCoreMember
  have hCodeFormula :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        formula_codeₘ(code) :=
    GodelQuotation.gq_is_formula_code_of_mem
      code hCodeBoundary.1 hCodeMember
  have hTraceCondition :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_forall_prefix_trace_condition (numₘ(count)) core code trace indexId := by
    simpa [code, trace] using
      canonical_forall_prefix_standard_trace_condition_derives
        count core hCore hCoreMember indexId
  have hCountFixed :
      Term.substituteFree SetSort.set traceId trace (numₘ(count)) =
        numₘ(count) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hCoreFixed :
      Term.substituteFree SetSort.set traceId trace core =
        core := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hCore.2]
    exact List.not_mem_nil
  have hCodeFixed :
      Term.substituteFree SetSort.set traceId trace code =
        code := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hCodeBoundary.2]
    exact List.not_mem_nil
  have hTraceVariableSubstitution :
      Term.substituteFree SetSort.set traceId trace (x#traceId) =
        trace := by
    simp [Term.substituteFree, set_variable]
  have hTraceFreshIndex : (SetSort.set, indexId) ∉
        Term.freeSupport trace := by
    rw [hTraceBoundary.2]
    exact List.not_mem_nil
  have hTraceSubstitution :
      Formula.substituteFree SetSort.set traceId trace (canonical_forall_prefix_trace_condition (numₘ(count)) core code (x#traceId) indexId) =
        canonical_forall_prefix_trace_condition (numₘ(count)) core code trace indexId :=
    canonical_forall_prefix_trace_condition_substitute_free (numₘ(count)) core code (x#traceId) trace (numₘ(count)) core code trace
      traceId indexId hTraceNeIndex hTraceBoundary.1
      hTraceFreshIndex hCountFixed hCoreFixed hCodeFixed
      hTraceVariableSubstitution
  unfold canonical_forall_prefix_code_condition_with_ids
  apply FirstOrder.Derives.conjIntro
  · exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro
        hCountOmega hCoreFormula) (by simpa [code] using hCodeFormula)
  · nd_apply FirstOrder.Derives.exists_intro
      (term := trace)
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    rw [hTraceSubstitution]
    exact hTraceCondition
/--
固定深度的规范 binder 变量码等于对应具名变量的标准单 token 序列。
等式完全在 quotation 理论中由对象自然数算术与变量码构造得到。
-/
theorem canonical_binder_variable_code_numeral_eq_standard_token_sequence (depth : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_binder_variable_code_term (numₘ(depth)) ≐ₘ
        GodelQuotation.standard_token_sequence
          [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name depth)] := by
  let binder :=
    canonical_binder_variable_code_term (numₘ(depth))
  let namedBinder :=
    GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth)
  have hNamedBinderToBinder :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        namedBinder ≐ₘ binder := by
    simpa [namedBinder, binder] using
      canonical_binder_variable_code_numeral_derives depth
  have hBinderToNamedBinder :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        binder ≐ₘ namedBinder :=
    Metatheory.Derives.equality_symm
      hNamedBinderToBinder
  have hNamedBinderStandard :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        namedBinder ≐ₘ
          GodelQuotation.standard_token_sequence
            [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name depth)] := by
    simpa [namedBinder] using
      GodelQuotation.named_variable_code_eq_standard_token_sequence (GodelQuotation.bound_name depth)
  simpa [binder] using
    Metatheory.Derives.equality_trans
      hBinderToNamedBinder hNamedBinderStandard
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
