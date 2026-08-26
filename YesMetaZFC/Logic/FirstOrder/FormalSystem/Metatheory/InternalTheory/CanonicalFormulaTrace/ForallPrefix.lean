import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTrace.Embedding
/-! # 任意长规范全称前缀的外部证书 -/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/-! ## 任意长规范全称前缀的外部证书 -/
/--
从外部深度 `start` 开始，在 `core` 外依次加入 `count` 个规范全称 binder。
该构造与 `canonical_forall_prefix_code_condition` 的轨迹方向一致：最外层 binder
使用深度 `start`，随后逐层递增。
-/
def canonical_forall_prefix_code_from (start : Nat) : Nat → SetTerm → SetTerm
  | 0, core => core
  | count + 1, core =>
      forall_codeₘ(
        canonical_binder_variable_code_term (numₘ(start)),
        canonical_forall_prefix_code_from (start + 1) count core)
/--
规范全称前缀的逐层剥离列表。
首项是完整前缀码，末项是 `core`，因此列表长度恒为 `count + 1`。
-/
def canonical_forall_prefix_trace_terms_from (start : Nat) : Nat → SetTerm → List SetTerm
  | 0, core => [core]
  | count + 1, core =>
      canonical_forall_prefix_code_from start (count + 1) core ::
        canonical_forall_prefix_trace_terms_from (start + 1) count core
/-- 从深度零开始构造规范全称前缀码。 -/
abbrev canonical_forall_prefix_code (count : Nat) (core : SetTerm) : SetTerm :=
  canonical_forall_prefix_code_from 0 count core
/--
从外部深度 `start` 开始，使用 quotation 已求值的规范 binder 名构造全称前缀码。
它与 `canonical_forall_prefix_code_from` 的区别只在 binder 变量码：这里使用
`named_variable_code (bound_name depth)`，后者使用对象算术表达式
`canonical_binder_variable_code_term (numₘ(depth))`。两者在对象理论中相等，但不是
Lean 定义相等。
-/
def canonical_quoted_forall_prefix_code_from (start : Nat) : Nat → SetTerm → SetTerm
  | 0, core => core
  | count + 1, core =>
      forall_codeₘ(
        GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name start),
        canonical_quoted_forall_prefix_code_from (start + 1) count core)
/-- 从深度零开始构造 quotation 已求值的规范全称前缀码。 -/
abbrev canonical_quoted_forall_prefix_code (count : Nat) (core : SetTerm) : SetTerm :=
  canonical_quoted_forall_prefix_code_from 0 count core
/--
在已有前缀的核心位置追加最内层规范 binder，等价于把前缀长度增加一。
-/
@[simp]
theorem canonical_quoted_forall_prefix_code_from_push_last (start count : Nat) (core : SetTerm) :
    canonical_quoted_forall_prefix_code_from start count (forall_codeₘ(
          GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name (start + count)),
          core)) =
      canonical_quoted_forall_prefix_code_from
        start (count + 1) core := by
  induction count generalizing start with
  | zero =>
      simp [canonical_quoted_forall_prefix_code_from]
  | succ count ih =>
      change
        forall_codeₘ(
          GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name start),
          canonical_quoted_forall_prefix_code_from (start + 1) count (forall_codeₘ(
              GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name (start + (count + 1))),
              core))) =
        forall_codeₘ(
          GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name start),
          canonical_quoted_forall_prefix_code_from (start + 1) (count + 1) core)
      congr 1
      simpa only [show start + (count + 1) = start + 1 + count by omega] using
        ih (start + 1)
/--
项目公式全部 bound 参数的 `forallClosure` quotation，精确等于在开放核心
quotation 外添加同样数量的已求值规范 binder 前缀。
-/
theorem fs_embed_project_formula_forallClosure_quote
    {availableStage depth : Nat} (formula : FsProjectFormula availableStage depth)
    {coreCode : SetTerm} (hCore :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name (GodelQuotation.canonical_bound_names depth)
          depth (Formula.hilbertize SetSort.set (fs_embed_project_formula formula)) =
        some coreCode) :
    GodelQuotation.Numbered.quote? (fs_embed_project_formula (_root_.YesMetaZFC.SetTheory.Definitional.Formula.forallClosure
            depth formula)) =
      some (canonical_quoted_forall_prefix_code depth coreCode) := by
  induction depth generalizing coreCode with
  | zero =>
      simpa [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.forallClosure,
        canonical_quoted_forall_prefix_code,
        canonical_quoted_forall_prefix_code_from,
        GodelQuotation.Numbered.quote?,
        GodelQuotation.Numbered.quote_with?] using hCore
  | succ depth ih =>
      have hCore' :
          GodelQuotation.Numbered.quote_hilbert_with?
              GodelQuotation.free_name
              GodelQuotation.bound_name (GodelQuotation.bound_name depth ::
                GodelQuotation.canonical_bound_names depth) (depth + 1) (Formula.hilbertize SetSort.set (fs_embed_project_formula formula)) =
            some coreCode := by
        simpa only [GodelQuotation.canonical_bound_names] using hCore
      have hBinder :
          GodelQuotation.Numbered.quote_hilbert_with?
              GodelQuotation.free_name
              GodelQuotation.bound_name (GodelQuotation.canonical_bound_names depth)
              depth (Formula.hilbertize SetSort.set (fs_embed_project_formula (_root_.YesMetaZFC.SetTheory.Definitional.Formula.forallE
                    formula))) =
            some (forall_codeₘ(
                GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth),
                coreCode)) := by
        simp only [
          fs_embed_project_formula, Formula.hilbertize,
          GodelQuotation.Numbered.quote_hilbert_with?]
        rw [hCore']
        rfl
      have hClosure := ih (_root_.YesMetaZFC.SetTheory.Definitional.Formula.forallE
          formula)
        hBinder
      have hPrefix :
          canonical_quoted_forall_prefix_code depth (forall_codeₘ(
                GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth),
                coreCode)) =
            canonical_quoted_forall_prefix_code (depth + 1) coreCode := by
        simpa only [
          canonical_quoted_forall_prefix_code,
          Nat.zero_add] using
            canonical_quoted_forall_prefix_code_from_push_last
              0 depth coreCode
      rw [hPrefix] at hClosure
      simpa only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.forallClosure] using
          hClosure
/-- 从深度零开始构造规范全称前缀剥离轨迹。 -/
abbrev canonical_forall_prefix_trace_terms (count : Nat) (core : SetTerm) : List SetTerm :=
  canonical_forall_prefix_trace_terms_from 0 count core
/-- 规范全称前缀剥离轨迹的长度是 binder 数量的后继。 -/
@[simp]
theorem canonical_forall_prefix_trace_terms_from_length (start count : Nat) (core : SetTerm) : (canonical_forall_prefix_trace_terms_from
      start count core).length = count + 1 := by
  induction count generalizing start with
  | zero =>
      simp [canonical_forall_prefix_trace_terms_from]
  | succ count ih =>
      simp [canonical_forall_prefix_trace_terms_from,
        ih (start + 1)]
/-- 规范全称前缀剥离轨迹的首项是完整前缀码。 -/
@[simp]
theorem canonical_forall_prefix_trace_terms_from_head (start count : Nat) (core : SetTerm) : (canonical_forall_prefix_trace_terms_from
      start count core)[0]? =
        some (canonical_forall_prefix_code_from
          start count core) := by
  cases count <;>
    simp [canonical_forall_prefix_trace_terms_from,
      canonical_forall_prefix_code_from]
/-- 规范全称前缀剥离轨迹在末位置处精确取到核心码。 -/
@[simp]
theorem canonical_forall_prefix_trace_terms_from_last (start count : Nat) (core : SetTerm) : (canonical_forall_prefix_trace_terms_from
      start count core)[count]? = some core := by
  induction count generalizing start with
  | zero =>
      simp [canonical_forall_prefix_trace_terms_from]
  | succ count ih =>
      simpa [canonical_forall_prefix_trace_terms_from] using
        ih (start + 1)
/--
剥离轨迹的每个非末位置都由相应深度的规范全称构造连接到下一位置。
-/
theorem canonical_forall_prefix_trace_terms_from_step
    {start count index : Nat} {core : SetTerm} (hIndex : index < count) :
    ∃ body, (canonical_forall_prefix_trace_terms_from
        start count core)[index]? =
          some (forall_codeₘ(
              canonical_binder_variable_code_term (numₘ(start + index)),
              body)) ∧ (canonical_forall_prefix_trace_terms_from
        start count core)[index + 1]? = some body := by
  induction count generalizing start index with
  | zero =>
      exact (Nat.not_lt_zero index hIndex).elim
  | succ count ih =>
      cases index with
      | zero =>
          refine ⟨canonical_forall_prefix_code_from (start + 1) count core, ?_, ?_⟩
          · simp [canonical_forall_prefix_trace_terms_from,
              canonical_forall_prefix_code_from]
          · simpa [canonical_forall_prefix_trace_terms_from] using (canonical_forall_prefix_trace_terms_from_head (start + 1) count core)
      | succ index =>
          have hTail : index < count := by
            omega
          rcases ih (start := start + 1) (index := index) hTail with
            ⟨body, hCurrent, hNext⟩
          refine ⟨body, ?_, ?_⟩
          · simpa [canonical_forall_prefix_trace_terms_from,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              hCurrent
          · simpa [canonical_forall_prefix_trace_terms_from,
              Nat.add_assoc] using hNext
/-- 具体深度的规范 binder 变量码满足统一的闭代码边界。 -/
theorem canonical_binder_variable_code_numeral_boundary (depth : Nat) :
    GodelQuotation.Numbered.CodeBoundary (canonical_binder_variable_code_term (numₘ(depth))) := by
  constructor
  · exact canonical_binder_variable_code_term_admissible (numₘ(depth)) (finite_numeral_term_admissible depth)
  · simp [ Term.freeSupport,
      Term.freeSupportList, finite_numeral_term_freeSupport]
/-- quotation 已求值的具体 binder 变量码满足统一的闭代码边界。 -/
theorem canonical_quoted_binder_variable_code_boundary (depth : Nat) :
    GodelQuotation.Numbered.CodeBoundary (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth)) := by
  constructor
  · exact variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name depth))
  · simp [GodelQuotation.Numbered.named_variable_code]
/-- quotation 已求值的全称前缀构造保持核心码的闭代码边界。 -/
theorem canonical_quoted_forall_prefix_code_from_boundary (start count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core) :
    GodelQuotation.Numbered.CodeBoundary (canonical_quoted_forall_prefix_code_from
        start count core) := by
  induction count generalizing start with
  | zero =>
      simpa [canonical_quoted_forall_prefix_code_from] using hCore
  | succ count ih =>
      have hBinder :=
        canonical_quoted_binder_variable_code_boundary start
      have hBody := ih (start + 1)
      constructor
      · exact universal_formula_code_term_admissible _ _
          hBinder.1 hBody.1
      · simp [canonical_quoted_forall_prefix_code_from,
          hBody.2, Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport]
/-- 规范全称前缀构造保持核心码的闭代码边界。 -/
theorem canonical_forall_prefix_code_from_boundary (start count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core) :
    GodelQuotation.Numbered.CodeBoundary (canonical_forall_prefix_code_from start count core) := by
  induction count generalizing start with
  | zero =>
      simpa [canonical_forall_prefix_code_from] using hCore
  | succ count ih =>
      have hBinder :=
        canonical_binder_variable_code_numeral_boundary start
      have hBody := ih (start + 1)
      constructor
      · exact universal_formula_code_term_admissible _ _
          hBinder.1 hBody.1
      · simp [canonical_forall_prefix_code_from,
          hBody.2, Term.freeSupport,
          Term.freeSupportList,
          finite_numeral_term_freeSupport]
/-- 规范全称前缀剥离轨迹中的每一项都满足闭代码边界。 -/
theorem canonical_forall_prefix_trace_terms_from_boundary (start count : Nat) (core : SetTerm) (hCore : GodelQuotation.Numbered.CodeBoundary core) :
    ∀ code,
      code ∈ canonical_forall_prefix_trace_terms_from
        start count core →
      GodelQuotation.Numbered.CodeBoundary code := by
  induction count generalizing start with
  | zero =>
      intro code hCode
      simp only [canonical_forall_prefix_trace_terms_from,
        List.mem_singleton] at hCode
      simpa [hCode] using hCore
  | succ count ih =>
      intro code hCode
      simp only [canonical_forall_prefix_trace_terms_from,
        List.mem_cons] at hCode
      rcases hCode with rfl | hCode
      · exact canonical_forall_prefix_code_from_boundary
          start (count + 1) core hCore
      · exact ih (start + 1) code hCode
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
