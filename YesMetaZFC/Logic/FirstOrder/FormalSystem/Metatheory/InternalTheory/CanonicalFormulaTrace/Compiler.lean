import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTrace.Core
/-! # 规范项目公式轨迹的可计算编译与深度移位 -/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/-! ## bound 变量深度恢复 -/
/--
把当前入口深度下的 de Bruijn index 恢复为实际 binder 深度。
最新 binder 的 index 为 `0`，因此对应深度 `entryDepth - 1`。
-/
def canonical_project_variable_depth? (entryDepth : Nat) : SetTerm → Option Nat
  | .var (.bvar SetSort.set index) =>
      if index < entryDepth then
        some (entryDepth - index - 1)
      else
        none
  | _ => none
/-- 成功恢复的 binder 深度严格早于当前入口深度。 -/
theorem canonical_project_variable_depth?_lt
    {entryDepth : Nat} {term : SetTerm} {variableDepth : Nat} (hDepth :
      canonical_project_variable_depth? entryDepth term =
        some variableDepth) :
    variableDepth < entryDepth := by
  cases term with
  | var sourceVar =>
      cases sourceVar with
      | bvar sort index =>
          cases sort
          simp only [canonical_project_variable_depth?] at hDepth
          split at hDepth
          next hIndex =>
            simp only [Option.some.injEq] at hDepth
            subst variableDepth
            omega
          next =>
            simp at hDepth
      | fvar sort id =>
          simp [canonical_project_variable_depth?] at hDepth
  | app function arguments =>
      simp [canonical_project_variable_depth?] at hDepth
/-- 规范 binder 环境在一个合法 de Bruijn 位置处恢复相应的 binder 名称。 -/
theorem canonical_bound_names_getElem?_of_lt
    {entryDepth index : Nat} (hIndex : index < entryDepth) : (GodelQuotation.canonical_bound_names entryDepth)[index]? =
      some (GodelQuotation.bound_name (entryDepth - index - 1)) := by
  induction entryDepth generalizing index with
  | zero =>
      omega
  | succ entryDepth ih =>
      cases index with
      | zero =>
          simp [GodelQuotation.canonical_bound_names]
      | succ index =>
          have hIndex' : index < entryDepth := by
            omega
          rw [GodelQuotation.canonical_bound_names,
            List.getElem?_cons_succ,
            ih hIndex']
          congr 2
          omega
/-- 深度恢复成功时，项 quotation 恰为对应规范 binder 变量码。 -/
theorem canonical_project_variable_depth?_quote
    {entryDepth : Nat} {term : SetTerm} {variableDepth : Nat} (hDepth :
      canonical_project_variable_depth? entryDepth term =
        some variableDepth) :
    GodelQuotation.Numbered.quote_term_with?
        GodelQuotation.free_name (GodelQuotation.canonical_bound_names entryDepth)
        term =
      some (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name variableDepth)) := by
  cases term with
  | var sourceVar =>
      cases sourceVar with
      | bvar sort index =>
          cases sort
          simp only [canonical_project_variable_depth?] at hDepth
          split at hDepth
          next hIndex =>
            simp only [Option.some.injEq] at hDepth
            subst variableDepth
            simp [GodelQuotation.Numbered.quote_term_with?,
              canonical_bound_names_getElem?_of_lt hIndex]
          next =>
            simp at hDepth
      | fvar sort id =>
          simp [canonical_project_variable_depth?] at hDepth
  | app function arguments =>
      simp [canonical_project_variable_depth?] at hDepth
/-- 深度恢复成功时，项的 token quotation 是对应规范 binder 的 singleton 串。 -/
theorem canonical_project_variable_depth?_quote_tokens
    {entryDepth : Nat} {term : SetTerm} {variableDepth : Nat} (hDepth :
      canonical_project_variable_depth? entryDepth term =
        some variableDepth) :
    GodelQuotation.Numbered.quote_term_tokens_with?
        GodelQuotation.free_name (GodelQuotation.canonical_bound_names entryDepth)
        term =
      some [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name variableDepth)] := by
  cases term with
  | var sourceVar =>
      cases sourceVar with
      | bvar sort index =>
          cases sort
          simp only [canonical_project_variable_depth?] at hDepth
          split at hDepth
          next hIndex =>
            simp only [Option.some.injEq] at hDepth
            subst variableDepth
            simp [GodelQuotation.Numbered.quote_term_tokens_with?,
              canonical_bound_names_getElem?_of_lt hIndex]
          next =>
            simp at hDepth
      | fvar sort id =>
          simp [canonical_project_variable_depth?] at hDepth
  | app function arguments =>
      simp [canonical_project_variable_depth?] at hDepth
/-! ## 可计算编译 -/
/--
把一个已经 Hilbert 化的项目公式编译成连续后序轨迹。
`start` 是本子树第一行在最终整条轨迹中的绝对编号；递归拼接时据此平移右子树和根行
的前提索引。
-/
def canonical_project_hilbert_trace_from? (start entryDepth : Nat) :
    SetFormula → Option CanonicalProjectTrace
  | .rel RelationSymbol.membership [left, right] => do
      let leftDepth ←
        canonical_project_variable_depth? entryDepth left
      let rightDepth ←
        canonical_project_variable_depth? entryDepth right
      pure <| CanonicalProjectTrace.atomic
        start entryDepth (.rel RelationSymbol.membership [left, right]) (CanonicalProjectTrace.canonical_project_atom_code
          .membership leftDepth rightDepth)
        .membership
        leftDepth rightDepth
  | .rel RelationSymbol.subset [left, right] => do
      let leftDepth ←
        canonical_project_variable_depth? entryDepth left
      let rightDepth ←
        canonical_project_variable_depth? entryDepth right
      pure <| CanonicalProjectTrace.atomic
        start entryDepth (.rel RelationSymbol.subset [left, right]) (CanonicalProjectTrace.canonical_project_atom_code
          .subset leftDepth rightDepth)
        .subset
        leftDepth rightDepth
  | .equal left right => do
      let leftDepth ←
        canonical_project_variable_depth? entryDepth left
      let rightDepth ←
        canonical_project_variable_depth? entryDepth right
      pure <| CanonicalProjectTrace.atomic
        start entryDepth (.equal left right) (CanonicalProjectTrace.canonical_project_atom_code
          .equality leftDepth rightDepth)
        .equality
        leftDepth rightDepth
  | .neg body => do
      let bodyTrace ←
        canonical_project_hilbert_trace_from?
          start entryDepth body
      pure <| CanonicalProjectTrace.negation
        start entryDepth bodyTrace
  | .imp left right => do
      let leftTrace ←
        canonical_project_hilbert_trace_from?
          start entryDepth left
      let rightTrace ←
        canonical_project_hilbert_trace_from? (start + leftTrace.rows.length)
          entryDepth right
      pure <| CanonicalProjectTrace.implication
        start entryDepth leftTrace rightTrace
  | .forallE SetSort.set body => do
      let bodyTrace ←
        canonical_project_hilbert_trace_from?
          start (entryDepth + 1) body
      pure <| CanonicalProjectTrace.universal
        start entryDepth bodyTrace
  | _ => none
/-- 从第零行开始编译一个 Hilbert 公式。 -/
abbrev canonical_project_hilbert_trace? (entryDepth : Nat) (formula : SetFormula) :
    Option CanonicalProjectTrace :=
  canonical_project_hilbert_trace_from?
    0 entryDepth formula
/-! ## 切点深度平移的成对轨迹 -/
/--
把规范 binder 深度沿切点平移一层。
严格小于切点的参数深度保持不变；切点及其后的局部 binder 深度统一取后继。
-/
def canonical_project_shift_depth (cutoff depth : Nat) : Nat :=
  if depth < cutoff then depth else depth + 1
@[simp]
theorem canonical_project_shift_depth_of_lt
    {cutoff depth : Nat} (hDepth : depth < cutoff) :
    canonical_project_shift_depth cutoff depth = depth := by
  simp [canonical_project_shift_depth, hDepth]
@[simp]
theorem canonical_project_shift_depth_of_le
    {cutoff depth : Nat} (hDepth : cutoff ≤ depth) :
    canonical_project_shift_depth cutoff depth = depth + 1 := by
  simp [canonical_project_shift_depth, Nat.not_lt.mpr hDepth]
/--
两个 Hilbert 核公式逐构造同步，并且右式把左式中不低于 `cutoff` 的规范 binder
深度统一平移一层。
该关系只记录编译器真正需要的原子深度读取方程；否定、蕴含和全称量词保持相同
构造树。它是 cutoff-shift 对象分类器的元层证书。
-/
inductive CanonicalProjectFormulaShift (cutoff : Nat) : (entryDepth : Nat) → SetFormula → SetFormula → Prop where
  | equality
      {entryDepth leftDepth rightDepth : Nat}
      {sourceLeft sourceRight targetLeft targetRight : SetTerm} (hSourceLeft :
        canonical_project_variable_depth?
            entryDepth sourceLeft =
          some leftDepth) (hSourceRight :
        canonical_project_variable_depth?
            entryDepth sourceRight =
          some rightDepth) (hTargetLeft :
        canonical_project_variable_depth? (entryDepth + 1) targetLeft =
          some (canonical_project_shift_depth
            cutoff leftDepth)) (hTargetRight :
        canonical_project_variable_depth? (entryDepth + 1) targetRight =
          some (canonical_project_shift_depth
            cutoff rightDepth)) :
      CanonicalProjectFormulaShift cutoff entryDepth (.equal sourceLeft sourceRight) (.equal targetLeft targetRight)
  | membership
      {entryDepth leftDepth rightDepth : Nat}
      {sourceLeft sourceRight targetLeft targetRight : SetTerm} (hSourceLeft :
        canonical_project_variable_depth?
            entryDepth sourceLeft =
          some leftDepth) (hSourceRight :
        canonical_project_variable_depth?
            entryDepth sourceRight =
          some rightDepth) (hTargetLeft :
        canonical_project_variable_depth? (entryDepth + 1) targetLeft =
          some (canonical_project_shift_depth
            cutoff leftDepth)) (hTargetRight :
        canonical_project_variable_depth? (entryDepth + 1) targetRight =
          some (canonical_project_shift_depth
            cutoff rightDepth)) :
      CanonicalProjectFormulaShift cutoff entryDepth (.rel RelationSymbol.membership
          [sourceLeft, sourceRight]) (.rel RelationSymbol.membership
          [targetLeft, targetRight])
  | subset
      {entryDepth leftDepth rightDepth : Nat}
      {sourceLeft sourceRight targetLeft targetRight : SetTerm} (hSourceLeft :
        canonical_project_variable_depth?
            entryDepth sourceLeft =
          some leftDepth) (hSourceRight :
        canonical_project_variable_depth?
            entryDepth sourceRight =
          some rightDepth) (hTargetLeft :
        canonical_project_variable_depth? (entryDepth + 1) targetLeft =
          some (canonical_project_shift_depth
            cutoff leftDepth)) (hTargetRight :
        canonical_project_variable_depth? (entryDepth + 1) targetRight =
          some (canonical_project_shift_depth
            cutoff rightDepth)) :
      CanonicalProjectFormulaShift cutoff entryDepth (.rel RelationSymbol.subset
          [sourceLeft, sourceRight]) (.rel RelationSymbol.subset
          [targetLeft, targetRight])
  | negation
      {entryDepth : Nat}
      {sourceBody targetBody : SetFormula} (body :
        CanonicalProjectFormulaShift cutoff
          entryDepth sourceBody targetBody) :
      CanonicalProjectFormulaShift cutoff entryDepth (.neg sourceBody) (.neg targetBody)
  | implication
      {entryDepth : Nat}
      {sourceLeft sourceRight targetLeft targetRight : SetFormula} (left :
        CanonicalProjectFormulaShift cutoff
          entryDepth sourceLeft targetLeft) (right :
        CanonicalProjectFormulaShift cutoff
          entryDepth sourceRight targetRight) :
      CanonicalProjectFormulaShift cutoff entryDepth (.imp sourceLeft sourceRight) (.imp targetLeft targetRight)
  | universal
      {entryDepth : Nat}
      {sourceBody targetBody : SetFormula} (body :
        CanonicalProjectFormulaShift cutoff (entryDepth + 1) sourceBody targetBody) :
      CanonicalProjectFormulaShift cutoff entryDepth (.forallE SetSort.set sourceBody) (.forallE SetSort.set targetBody)
/--
两棵成功编译的 canonical 轨迹具有同一后序骨架；右轨迹的原子变量与全称 binder
按 `cutoff` 平移，否定和蕴含前提编号保持不变。
-/
inductive CanonicalProjectTraceShift (cutoff : Nat) :
    CanonicalProjectTrace → CanonicalProjectTrace → Prop where
  | atomic (start depth : Nat) (sourceFormula targetFormula : SetFormula) (kind : CanonicalProjectAtomKind) (leftDepth rightDepth : Nat) :
      CanonicalProjectTraceShift cutoff (CanonicalProjectTrace.atomic
          start depth sourceFormula (CanonicalProjectTrace.canonical_project_atom_code
            kind leftDepth rightDepth)
          kind leftDepth rightDepth) (CanonicalProjectTrace.atomic
          start (depth + 1) targetFormula (CanonicalProjectTrace.canonical_project_atom_code
            kind (canonical_project_shift_depth
              cutoff leftDepth) (canonical_project_shift_depth
              cutoff rightDepth))
          kind (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth))
  | negation (start depth : Nat)
      {sourceBody targetBody : CanonicalProjectTrace} (body :
        CanonicalProjectTraceShift cutoff
          sourceBody targetBody) :
      CanonicalProjectTraceShift cutoff (CanonicalProjectTrace.negation
          start depth sourceBody) (CanonicalProjectTrace.negation
          start (depth + 1) targetBody)
  | implication (start depth : Nat)
      {sourceLeft sourceRight targetLeft targetRight :
        CanonicalProjectTrace} (left :
        CanonicalProjectTraceShift cutoff
          sourceLeft targetLeft) (right :
        CanonicalProjectTraceShift cutoff
          sourceRight targetRight) :
      CanonicalProjectTraceShift cutoff (CanonicalProjectTrace.implication
          start depth sourceLeft sourceRight) (CanonicalProjectTrace.implication
          start (depth + 1) targetLeft targetRight)
  | universal (start depth : Nat)
      {sourceBody targetBody : CanonicalProjectTrace} (body :
        CanonicalProjectTraceShift cutoff
          sourceBody targetBody) :
      CanonicalProjectTraceShift cutoff (CanonicalProjectTrace.universal
          start depth sourceBody) (CanonicalProjectTrace.universal
          start (depth + 1) targetBody)
/--
成对 cutoff-shift 轨迹在同一绝对位置上的逐行关系。
复合行保留相同的前提编号；原子行平移变量深度；全称行只把当前 binder 名称
后移一层。该关系是对象层逐行证书与元层递归轨迹之间的稳定接口。
-/
inductive CanonicalProjectTraceRowShift (cutoff : Nat) :
    CanonicalProjectTraceRow → CanonicalProjectTraceRow → Prop where
  | atomic (depth : Nat) (sourceFormula targetFormula : SetFormula) (kind : CanonicalProjectAtomKind) (leftDepth rightDepth : Nat) :
      CanonicalProjectTraceRowShift cutoff
        {
          formula := sourceFormula
          code :=
            CanonicalProjectTrace.canonical_project_atom_code
              kind leftDepth rightDepth
          depth := depth
          rule := .atomic kind leftDepth rightDepth
        }
        {
          formula := targetFormula
          code :=
            CanonicalProjectTrace.canonical_project_atom_code
              kind (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth)
          depth := depth + 1
          rule :=
            .atomic kind (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth)
        }
  | negation (depth sourcePremise targetPremise : Nat) (sourceBodyFormula targetBodyFormula : SetFormula) (sourceBodyCode targetBodyCode : SetTerm)
      (hPremise : sourcePremise = targetPremise) :
      CanonicalProjectTraceRowShift cutoff
        {
          formula := .neg sourceBodyFormula
          code := neg_codeₘ(sourceBodyCode)
          depth := depth
          rule := .negation sourcePremise
        }
        {
          formula := .neg targetBodyFormula
          code := neg_codeₘ(targetBodyCode)
          depth := depth + 1
          rule := .negation targetPremise
        }
  | implication (depth sourceLeftPremise sourceRightPremise
        targetLeftPremise targetRightPremise : Nat) (sourceLeftFormula sourceRightFormula
        targetLeftFormula targetRightFormula : SetFormula) (sourceLeftCode sourceRightCode
        targetLeftCode targetRightCode : SetTerm) (hLeftPremise :
        sourceLeftPremise = targetLeftPremise) (hRightPremise :
        sourceRightPremise = targetRightPremise) :
      CanonicalProjectTraceRowShift cutoff
        {
          formula := .imp sourceLeftFormula sourceRightFormula
          code := imp_codeₘ(sourceLeftCode, sourceRightCode)
          depth := depth
          rule :=
            .implication
              sourceLeftPremise sourceRightPremise
        }
        {
          formula := .imp targetLeftFormula targetRightFormula
          code := imp_codeₘ(targetLeftCode, targetRightCode)
          depth := depth + 1
          rule :=
            .implication
              targetLeftPremise targetRightPremise
        }
  | universal (depth sourcePremise targetPremise : Nat) (sourceBodyFormula targetBodyFormula : SetFormula) (sourceBodyCode targetBodyCode : SetTerm)
      (hPremise : sourcePremise = targetPremise) :
      CanonicalProjectTraceRowShift cutoff
        {
          formula := .forallE SetSort.set sourceBodyFormula
          code :=
            forall_codeₘ(
              GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth),
              sourceBodyCode)
          depth := depth
          rule := .universal sourcePremise
        }
        {
          formula := .forallE SetSort.set targetBodyFormula
          code :=
            forall_codeₘ(
              GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name (depth + 1)),
              targetBodyCode)
          depth := depth + 1
          rule := .universal targetPremise
        }
/-- 两列轨迹行逐位置满足同一个 cutoff-shift 关系。 -/
inductive CanonicalProjectTraceRowsShift (cutoff : Nat) :
    List CanonicalProjectTraceRow →
      List CanonicalProjectTraceRow → Prop where
  | nil :
      CanonicalProjectTraceRowsShift cutoff [] []
  | cons
      {sourceHead targetHead : CanonicalProjectTraceRow}
      {sourceTail targetTail : List CanonicalProjectTraceRow} (head :
        CanonicalProjectTraceRowShift
          cutoff sourceHead targetHead) (tail :
        CanonicalProjectTraceRowsShift
          cutoff sourceTail targetTail) :
      CanonicalProjectTraceRowsShift cutoff (sourceHead :: sourceTail) (targetHead :: targetTail)
namespace CanonicalProjectTraceShift
/-- 成对 cutoff-shift 轨迹具有相同的行数。 -/
theorem rows_length_eq
    {cutoff : Nat}
    {source target : CanonicalProjectTrace} (shift :
      CanonicalProjectTraceShift cutoff source target) :
    source.rows.length = target.rows.length := by
  induction shift with
  | atomic =>
      rfl
  | negation _ _ _ ih =>
      simp [CanonicalProjectTrace.negation, ih]
  | implication _ _ _ _ ihLeft ihRight =>
      simp [CanonicalProjectTrace.implication,
        ihLeft, ihRight]
  | universal _ _ _ ih =>
      simp [CanonicalProjectTrace.universal, ih]
/-- 成对 cutoff-shift 轨迹的根行编号相同。 -/
theorem root_index_eq
    {cutoff : Nat}
    {source target : CanonicalProjectTrace} (shift :
      CanonicalProjectTraceShift cutoff source target) :
    source.rootIndex = target.rootIndex := by
  induction shift with
  | atomic =>
      rfl
  | negation _ _ body ih =>
      simp [CanonicalProjectTrace.negation,
        rows_length_eq body, ih]
  | implication _ _ left right ihLeft ihRight =>
      simp [CanonicalProjectTrace.implication,
        rows_length_eq left, rows_length_eq right,
        ihLeft, ihRight]
  | universal _ _ body ih =>
      simp [CanonicalProjectTrace.universal,
        rows_length_eq body, ih]
/-- 两段逐点对应列表可以同步拼接。 -/
private theorem forall₂_append
    {cutoff : Nat}
    {left₁ left₂ right₁ right₂ :
      List CanonicalProjectTraceRow} (first :
      CanonicalProjectTraceRowsShift
        cutoff left₁ right₁) (second :
      CanonicalProjectTraceRowsShift
        cutoff left₂ right₂) :
    CanonicalProjectTraceRowsShift cutoff (left₁ ++ left₂) (right₁ ++ right₂) := by
  induction first with
  | nil =>
      simpa using second
  | cons head tail ih =>
      exact CanonicalProjectTraceRowsShift.cons
        head ih
/-- 成对 cutoff-shift 轨迹的每个绝对位置满足统一逐行关系。 -/
theorem rows_forall₂
    {cutoff : Nat}
    {source target : CanonicalProjectTrace} (shift :
      CanonicalProjectTraceShift cutoff source target) :
    CanonicalProjectTraceRowsShift cutoff
      source.rows target.rows := by
  induction shift with
  | atomic start depth sourceFormula targetFormula
      kind leftDepth rightDepth =>
      simpa [CanonicalProjectTrace.atomic] using
        CanonicalProjectTraceRowsShift.cons (CanonicalProjectTraceRowShift.atomic (cutoff := cutoff)
            depth sourceFormula targetFormula
            kind leftDepth rightDepth)
          CanonicalProjectTraceRowsShift.nil
  | @negation start depth sourceBody targetBody body ih =>
      have root :
          CanonicalProjectTraceRowShift cutoff
            {
              formula := .neg sourceBody.rootFormula
              code := neg_codeₘ(sourceBody.rootCode)
              depth := depth
              rule := .negation sourceBody.rootIndex
            }
            {
              formula := .neg targetBody.rootFormula
              code := neg_codeₘ(targetBody.rootCode)
              depth := depth + 1
              rule := .negation targetBody.rootIndex
            } :=
        CanonicalProjectTraceRowShift.negation (cutoff := cutoff)
          depth sourceBody.rootIndex targetBody.rootIndex
          sourceBody.rootFormula targetBody.rootFormula
          sourceBody.rootCode targetBody.rootCode (root_index_eq body)
      simpa [CanonicalProjectTrace.negation] using
        forall₂_append ih (CanonicalProjectTraceRowsShift.cons
            root CanonicalProjectTraceRowsShift.nil)
  | @implication start depth
      sourceLeft sourceRight targetLeft targetRight
      left right ihLeft ihRight =>
      have root :
          CanonicalProjectTraceRowShift cutoff
            {
              formula :=
                .imp sourceLeft.rootFormula
                  sourceRight.rootFormula
              code :=
                imp_codeₘ(
                  sourceLeft.rootCode,
                  sourceRight.rootCode)
              depth := depth
              rule :=
                .implication
                  sourceLeft.rootIndex
                  sourceRight.rootIndex
            }
            {
              formula :=
                .imp targetLeft.rootFormula
                  targetRight.rootFormula
              code :=
                imp_codeₘ(
                  targetLeft.rootCode,
                  targetRight.rootCode)
              depth := depth + 1
              rule :=
                .implication
                  targetLeft.rootIndex
                  targetRight.rootIndex
            } :=
        CanonicalProjectTraceRowShift.implication (cutoff := cutoff)
          depth
          sourceLeft.rootIndex sourceRight.rootIndex
          targetLeft.rootIndex targetRight.rootIndex
          sourceLeft.rootFormula sourceRight.rootFormula
          targetLeft.rootFormula targetRight.rootFormula
          sourceLeft.rootCode sourceRight.rootCode
          targetLeft.rootCode targetRight.rootCode (root_index_eq left) (root_index_eq right)
      simpa [CanonicalProjectTrace.implication] using
        forall₂_append (forall₂_append ihLeft ihRight) (CanonicalProjectTraceRowsShift.cons
            root CanonicalProjectTraceRowsShift.nil)
  | @universal start depth sourceBody targetBody body ih =>
      have root :
          CanonicalProjectTraceRowShift cutoff
            {
              formula :=
                .forallE SetSort.set sourceBody.rootFormula
              code :=
                forall_codeₘ(
                  GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth),
                  sourceBody.rootCode)
              depth := depth
              rule := .universal sourceBody.rootIndex
            }
            {
              formula :=
                .forallE SetSort.set targetBody.rootFormula
              code :=
                forall_codeₘ(
                  GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name (depth + 1)),
                  targetBody.rootCode)
              depth := depth + 1
              rule := .universal targetBody.rootIndex
            } :=
        CanonicalProjectTraceRowShift.universal (cutoff := cutoff)
          depth sourceBody.rootIndex targetBody.rootIndex
          sourceBody.rootFormula targetBody.rootFormula
          sourceBody.rootCode targetBody.rootCode (root_index_eq body)
      simpa [CanonicalProjectTrace.universal] using
        forall₂_append ih (CanonicalProjectTraceRowsShift.cons
            root CanonicalProjectTraceRowsShift.nil)
private theorem rows_shift_row_at
    {cutoff : Nat}
    {sourceRows targetRows :
      List CanonicalProjectTraceRow} (rows :
      CanonicalProjectTraceRowsShift
        cutoff sourceRows targetRows)
    {index : Nat}
    {sourceRow : CanonicalProjectTraceRow} (hSourceRow :
      sourceRows[index]? = some sourceRow) :
    ∃ targetRow,
      targetRows[index]? = some targetRow ∧
        CanonicalProjectTraceRowShift
          cutoff sourceRow targetRow := by
  induction rows generalizing index sourceRow with
  | nil =>
      simp at hSourceRow
  | @cons sourceHead targetHead sourceTail targetTail
      headShift tailShift ih =>
      cases index with
      | zero =>
          simp at hSourceRow
          subst sourceRow
          exact ⟨targetHead, by simp, headShift⟩
      | succ previous =>
          simp at hSourceRow
          exact ih hSourceRow
/-- 从源轨迹的某一行可读取目标轨迹同位置的对应行。 -/
theorem row_at
    {cutoff : Nat}
    {source target : CanonicalProjectTrace} (shift :
      CanonicalProjectTraceShift cutoff source target)
    {index : Nat}
    {sourceRow : CanonicalProjectTraceRow} (hSourceRow :
      source.rows[index]? = some sourceRow) :
    ∃ targetRow,
      target.rows[index]? = some targetRow ∧
        CanonicalProjectTraceRowShift
          cutoff sourceRow targetRow :=
  rows_shift_row_at (rows_forall₂ shift) hSourceRow
end CanonicalProjectTraceShift
/--
公式级 cutoff-shift 关系在任意连续起点编译为成对 canonical 轨迹。
左右子树行数由轨迹关系本身保证相等，因此蕴含右子树的绝对起点无需额外重编号。
-/
theorem CanonicalProjectFormulaShift.trace_from?
    {cutoff entryDepth : Nat}
    {sourceFormula targetFormula : SetFormula} (shift :
      CanonicalProjectFormulaShift cutoff
        entryDepth sourceFormula targetFormula) (start : Nat) :
    ∃ sourceTrace targetTrace,
      canonical_project_hilbert_trace_from?
          start entryDepth sourceFormula =
        some sourceTrace ∧
      canonical_project_hilbert_trace_from?
          start (entryDepth + 1) targetFormula =
        some targetTrace ∧
      CanonicalProjectTraceShift cutoff
        sourceTrace targetTrace := by
  induction shift generalizing start with
  | @equality entryDepth leftDepth rightDepth
      sourceLeft sourceRight targetLeft targetRight
      hSourceLeft hSourceRight hTargetLeft hTargetRight =>
      let sourceTrace :=
        CanonicalProjectTrace.atomic
          start entryDepth (.equal sourceLeft sourceRight) (CanonicalProjectTrace.canonical_project_atom_code
            .equality leftDepth rightDepth)
          .equality leftDepth rightDepth
      let targetTrace :=
        CanonicalProjectTrace.atomic
          start (entryDepth + 1) (.equal targetLeft targetRight) (CanonicalProjectTrace.canonical_project_atom_code
            .equality (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth))
          .equality (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth)
      refine ⟨sourceTrace, targetTrace, ?_, ?_, ?_⟩
      · simp [canonical_project_hilbert_trace_from?,
          sourceTrace, hSourceLeft, hSourceRight]
      · simp [canonical_project_hilbert_trace_from?,
          targetTrace, hTargetLeft, hTargetRight]
      · exact .atomic
          start entryDepth (.equal sourceLeft sourceRight) (.equal targetLeft targetRight)
          .equality leftDepth rightDepth
  | @membership entryDepth leftDepth rightDepth
      sourceLeft sourceRight targetLeft targetRight
      hSourceLeft hSourceRight hTargetLeft hTargetRight =>
      let sourceTrace :=
        CanonicalProjectTrace.atomic
          start entryDepth (.rel RelationSymbol.membership
            [sourceLeft, sourceRight]) (CanonicalProjectTrace.canonical_project_atom_code
            .membership leftDepth rightDepth)
          .membership leftDepth rightDepth
      let targetTrace :=
        CanonicalProjectTrace.atomic
          start (entryDepth + 1) (.rel RelationSymbol.membership
            [targetLeft, targetRight]) (CanonicalProjectTrace.canonical_project_atom_code
            .membership (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth))
          .membership (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth)
      refine ⟨sourceTrace, targetTrace, ?_, ?_, ?_⟩
      · simp [canonical_project_hilbert_trace_from?,
          sourceTrace, hSourceLeft, hSourceRight]
      · simp [canonical_project_hilbert_trace_from?,
          targetTrace, hTargetLeft, hTargetRight]
      · exact .atomic
          start entryDepth (.rel RelationSymbol.membership
            [sourceLeft, sourceRight]) (.rel RelationSymbol.membership
            [targetLeft, targetRight])
          .membership leftDepth rightDepth
  | @subset entryDepth leftDepth rightDepth
      sourceLeft sourceRight targetLeft targetRight
      hSourceLeft hSourceRight hTargetLeft hTargetRight =>
      let sourceTrace :=
        CanonicalProjectTrace.atomic
          start entryDepth (.rel RelationSymbol.subset
            [sourceLeft, sourceRight]) (CanonicalProjectTrace.canonical_project_atom_code
            .subset leftDepth rightDepth)
          .subset leftDepth rightDepth
      let targetTrace :=
        CanonicalProjectTrace.atomic
          start (entryDepth + 1) (.rel RelationSymbol.subset
            [targetLeft, targetRight]) (CanonicalProjectTrace.canonical_project_atom_code
            .subset (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth))
          .subset (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth)
      refine ⟨sourceTrace, targetTrace, ?_, ?_, ?_⟩
      · simp [canonical_project_hilbert_trace_from?,
          sourceTrace, hSourceLeft, hSourceRight]
      · simp [canonical_project_hilbert_trace_from?,
          targetTrace, hTargetLeft, hTargetRight]
      · exact .atomic
          start entryDepth (.rel RelationSymbol.subset
            [sourceLeft, sourceRight]) (.rel RelationSymbol.subset
            [targetLeft, targetRight])
          .subset leftDepth rightDepth
  | @negation entryDepth sourceFormula targetFormula body ih =>
      rcases ih start with
        ⟨sourceBody, targetBody,
          hSourceBody, hTargetBody, hBody⟩
      let sourceTrace :=
        CanonicalProjectTrace.negation
          start entryDepth sourceBody
      let targetTrace :=
        CanonicalProjectTrace.negation
          start (entryDepth + 1) targetBody
      refine ⟨sourceTrace, targetTrace, ?_, ?_, ?_⟩
      · simp [canonical_project_hilbert_trace_from?,
          sourceTrace, hSourceBody]
      · simp [canonical_project_hilbert_trace_from?,
          targetTrace, hTargetBody]
      · exact .negation start entryDepth hBody
  | @implication entryDepth
      sourceLeftFormula sourceRightFormula
      targetLeftFormula targetRightFormula
      left right ihLeft ihRight =>
      rcases ihLeft start with
        ⟨sourceLeft, targetLeft,
          hSourceLeft, hTargetLeft, hLeft⟩
      have hLength :=
        CanonicalProjectTraceShift.rows_length_eq hLeft
      rcases ihRight (start + sourceLeft.rows.length) with
        ⟨sourceRight, targetRight,
          hSourceRight, hTargetRight, hRight⟩
      let sourceTrace :=
        CanonicalProjectTrace.implication
          start entryDepth sourceLeft sourceRight
      let targetTrace :=
        CanonicalProjectTrace.implication
          start (entryDepth + 1) targetLeft targetRight
      refine ⟨sourceTrace, targetTrace, ?_, ?_, ?_⟩
      · simp [canonical_project_hilbert_trace_from?,
          sourceTrace, hSourceLeft, hSourceRight]
      · simp [canonical_project_hilbert_trace_from?,
          targetTrace, hTargetLeft, ← hLength, hTargetRight]
      · exact .implication
          start entryDepth hLeft hRight
  | @universal entryDepth sourceFormula targetFormula body ih =>
      rcases ih start with
        ⟨sourceBody, targetBody,
          hSourceBody, hTargetBody, hBody⟩
      let sourceTrace :=
        CanonicalProjectTrace.universal
          start entryDepth sourceBody
      let targetTrace :=
        CanonicalProjectTrace.universal
          start (entryDepth + 1) targetBody
      refine ⟨sourceTrace, targetTrace, ?_, ?_, ?_⟩
      · simp [canonical_project_hilbert_trace_from?,
          sourceTrace, hSourceBody]
      · simp [canonical_project_hilbert_trace_from?,
          targetTrace, Nat.add_assoc, hTargetBody]
      · exact .universal start entryDepth hBody
/-! ## 轨迹可构造性的结构闭包 -/
/-- 一个 Hilbert 公式在任意连续起始位置都能生成规范轨迹。 -/
def CanonicalProjectTraceable (entryDepth : Nat) (formula : SetFormula) : Prop :=
  ∀ start, ∃ trace,
    canonical_project_hilbert_trace_from?
      start entryDepth formula = some trace
/-- 已恢复两端 binder 深度的等式原子可生成规范轨迹。 -/
theorem canonical_project_traceable_equality
    {entryDepth : Nat} {left right : SetTerm} (hLeft :
      ∃ leftDepth,
        canonical_project_variable_depth?
          entryDepth left = some leftDepth) (hRight :
      ∃ rightDepth,
        canonical_project_variable_depth?
          entryDepth right = some rightDepth) :
    CanonicalProjectTraceable entryDepth (.equal left right) := by
  intro start
  rcases hLeft with ⟨leftDepth, hLeftDepth⟩
  rcases hRight with ⟨rightDepth, hRightDepth⟩
  refine ⟨CanonicalProjectTrace.atomic
    start entryDepth (.equal left right) (eq_codeₘ(
      GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name leftDepth),
      GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name rightDepth)))
    .equality leftDepth rightDepth, ?_⟩
  simp [canonical_project_hilbert_trace_from?,
    hLeftDepth, hRightDepth]
/-- 已恢复两端 binder 深度的隶属原子可生成规范轨迹。 -/
theorem canonical_project_traceable_membership
    {entryDepth : Nat} {left right : SetTerm} (hLeft :
      ∃ leftDepth,
        canonical_project_variable_depth?
          entryDepth left = some leftDepth) (hRight :
      ∃ rightDepth,
        canonical_project_variable_depth?
          entryDepth right = some rightDepth) :
    CanonicalProjectTraceable entryDepth (.rel RelationSymbol.membership [left, right]) := by
  intro start
  rcases hLeft with ⟨leftDepth, hLeftDepth⟩
  rcases hRight with ⟨rightDepth, hRightDepth⟩
  refine ⟨CanonicalProjectTrace.atomic
    start entryDepth (.rel RelationSymbol.membership [left, right]) (membership_atomic_formula_code_term (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.bound_name leftDepth)) (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name rightDepth)))
    .membership leftDepth rightDepth, ?_⟩
  simp [canonical_project_hilbert_trace_from?,
    hLeftDepth, hRightDepth]
/-- 已恢复两端 binder 深度的项目子集原子可生成规范轨迹。 -/
theorem canonical_project_traceable_subset
    {entryDepth : Nat} {left right : SetTerm} (hLeft :
      ∃ leftDepth,
        canonical_project_variable_depth?
          entryDepth left = some leftDepth) (hRight :
      ∃ rightDepth,
        canonical_project_variable_depth?
          entryDepth right = some rightDepth) :
    CanonicalProjectTraceable entryDepth (.rel RelationSymbol.subset [left, right]) := by
  intro start
  rcases hLeft with ⟨leftDepth, hLeftDepth⟩
  rcases hRight with ⟨rightDepth, hRightDepth⟩
  refine ⟨CanonicalProjectTrace.atomic
    start entryDepth (.rel RelationSymbol.subset [left, right]) (project_subset_atomic_code_term (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.bound_name leftDepth)) (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name rightDepth)))
    .subset leftDepth rightDepth, ?_⟩
  simp [canonical_project_hilbert_trace_from?,
    hLeftDepth, hRightDepth]
/-- 规范轨迹可构造性对 Hilbert 否定封闭。 -/
theorem CanonicalProjectTraceable.negation
    {entryDepth : Nat} {body : SetFormula} (hBody : CanonicalProjectTraceable entryDepth body) :
    CanonicalProjectTraceable entryDepth (.neg body) := by
  intro start
  rcases hBody start with ⟨bodyTrace, hBodyTrace⟩
  exact ⟨CanonicalProjectTrace.negation
      start entryDepth bodyTrace,
    by simp [canonical_project_hilbert_trace_from?,
      hBodyTrace]⟩
/-- 规范轨迹可构造性对 Hilbert 蕴含封闭。 -/
theorem CanonicalProjectTraceable.implication
    {entryDepth : Nat} {left right : SetFormula} (hLeft : CanonicalProjectTraceable entryDepth left) (hRight : CanonicalProjectTraceable entryDepth right) :
    CanonicalProjectTraceable entryDepth (.imp left right) := by
  intro start
  rcases hLeft start with ⟨leftTrace, hLeftTrace⟩
  rcases hRight (start + leftTrace.rows.length) with
    ⟨rightTrace, hRightTrace⟩
  exact ⟨CanonicalProjectTrace.implication
      start entryDepth leftTrace rightTrace,
    by simp [canonical_project_hilbert_trace_from?,
      hLeftTrace, hRightTrace]⟩
/-- 规范轨迹可构造性对规范全称量词封闭。 -/
theorem CanonicalProjectTraceable.universal
    {entryDepth : Nat} {body : SetFormula} (hBody :
      CanonicalProjectTraceable (entryDepth + 1) body) :
    CanonicalProjectTraceable entryDepth (.forallE SetSort.set body) := by
  intro start
  rcases hBody start with ⟨bodyTrace, hBodyTrace⟩
  exact ⟨CanonicalProjectTrace.universal
      start entryDepth bodyTrace,
    by simp [canonical_project_hilbert_trace_from?,
      hBodyTrace]⟩
/-- Hilbert 闭真式在任意入口深度都可生成规范轨迹。 -/
theorem canonical_project_traceable_hilbert_truth (entryDepth : Nat) :
    CanonicalProjectTraceable entryDepth (Formula.hilbert_truth SetSort.set) := by
  apply CanonicalProjectTraceable.universal
  apply canonical_project_traceable_equality
  · exact ⟨entryDepth, by
      simp [canonical_project_variable_depth?]⟩
  · exact ⟨entryDepth, by
      simp [canonical_project_variable_depth?]⟩
/-- Hilbert 闭假式在任意入口深度都可生成规范轨迹。 -/
theorem canonical_project_traceable_hilbert_falsum (entryDepth : Nat) :
    CanonicalProjectTraceable entryDepth (Formula.hilbert_falsum SetSort.set) := by
  exact (canonical_project_traceable_hilbert_truth
    entryDepth).negation
/-- Hilbert 合取保持规范轨迹可构造性。 -/
theorem CanonicalProjectTraceable.hilbert_conjunction
    {entryDepth : Nat} {left right : SetFormula} (hLeft : CanonicalProjectTraceable entryDepth left) (hRight : CanonicalProjectTraceable entryDepth right) :
    CanonicalProjectTraceable entryDepth (Formula.hilbert_conj left right) := by
  exact (hLeft.implication hRight.negation).negation
/-- Hilbert 双条件保持规范轨迹可构造性。 -/
theorem CanonicalProjectTraceable.hilbert_biconditional
    {entryDepth : Nat} {left right : SetFormula} (hLeft : CanonicalProjectTraceable entryDepth left) (hRight : CanonicalProjectTraceable entryDepth right) :
    CanonicalProjectTraceable entryDepth (Formula.hilbert_iff left right) := by
  exact (hLeft.implication hRight).hilbert_conjunction (hRight.implication hLeft)
namespace CanonicalProjectFormulaShift
/-- Hilbert 闭真式在相邻入口深度满足任意合法切点的同步平移关系。 -/
theorem hilbert_truth
    {cutoff entryDepth : Nat} (hCutoff : cutoff ≤ entryDepth) :
    CanonicalProjectFormulaShift cutoff entryDepth (Formula.hilbert_truth SetSort.set) (Formula.hilbert_truth SetSort.set) := by
  apply CanonicalProjectFormulaShift.universal
  apply CanonicalProjectFormulaShift.equality (leftDepth := entryDepth) (rightDepth := entryDepth)
  · simp [
      canonical_project_variable_depth?]
  · simp [
      canonical_project_variable_depth?]
  · simp [
      canonical_project_variable_depth?,
      canonical_project_shift_depth_of_le hCutoff]
  · simp [
      canonical_project_variable_depth?,
      canonical_project_shift_depth_of_le hCutoff]
/-- Hilbert 闭假式保持 cutoff-shift。 -/
theorem hilbert_falsum
    {cutoff entryDepth : Nat} (hCutoff : cutoff ≤ entryDepth) :
    CanonicalProjectFormulaShift cutoff entryDepth (Formula.hilbert_falsum SetSort.set) (Formula.hilbert_falsum SetSort.set) := by
  exact (hilbert_truth hCutoff).negation
/-- Hilbert 合取逐分量保持 cutoff-shift。 -/
theorem hilbert_conjunction
    {cutoff entryDepth : Nat}
    {sourceLeft sourceRight targetLeft targetRight : SetFormula} (left :
      CanonicalProjectFormulaShift cutoff entryDepth
        sourceLeft targetLeft) (right :
      CanonicalProjectFormulaShift cutoff entryDepth
        sourceRight targetRight) :
    CanonicalProjectFormulaShift cutoff entryDepth (Formula.hilbert_conj sourceLeft sourceRight) (Formula.hilbert_conj targetLeft targetRight) := by
  exact (left.implication right.negation).negation
/-- Hilbert 双条件逐分量保持 cutoff-shift。 -/
theorem hilbert_biconditional
    {cutoff entryDepth : Nat}
    {sourceLeft sourceRight targetLeft targetRight : SetFormula} (left :
      CanonicalProjectFormulaShift cutoff entryDepth
        sourceLeft targetLeft) (right :
      CanonicalProjectFormulaShift cutoff entryDepth
        sourceRight targetRight) :
    CanonicalProjectFormulaShift cutoff entryDepth (Formula.hilbert_iff sourceLeft sourceRight) (Formula.hilbert_iff targetLeft targetRight) := by
  exact (left.implication right).hilbert_conjunction (right.implication left)
/-- 公式级 cutoff-shift 的左右规范 Hilbert token quotation 同时成功。 -/
theorem quote_hilbert_tokens_exists
    {cutoff entryDepth : Nat}
    {sourceFormula targetFormula : SetFormula} (shift :
      CanonicalProjectFormulaShift cutoff entryDepth
        sourceFormula targetFormula) :
    ∃ sourceTokens targetTokens,
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name (GodelQuotation.canonical_bound_names entryDepth)
          entryDepth sourceFormula =
        some sourceTokens ∧
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name (GodelQuotation.canonical_bound_names (entryDepth + 1)) (entryDepth + 1) targetFormula =
        some targetTokens := by
  induction shift with
  | @equality entryDepth leftDepth rightDepth
      sourceLeft sourceRight targetLeft targetRight
      hSourceLeft hSourceRight hTargetLeft hTargetRight =>
      have hSourceLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceLeft
      have hSourceRightTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceRight
      have hTargetLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetLeft
      have hTargetRightTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetRight
      let sourceLeftTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name leftDepth)]
      let sourceRightTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name rightDepth)]
      let targetLeftTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name (canonical_project_shift_depth cutoff leftDepth))]
      let targetRightTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name (canonical_project_shift_depth cutoff rightDepth))]
      refine
        ⟨GodelQuotation.Numbered.equality_tokens
            sourceLeftTokens sourceRightTokens,
          GodelQuotation.Numbered.equality_tokens
            targetLeftTokens targetRightTokens,
          ?_, ?_⟩
      · simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
          hSourceLeftTokens, hSourceRightTokens,
          sourceLeftTokens, sourceRightTokens,
          GodelQuotation.Numbered.equality_tokens]
      · simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
          hTargetLeftTokens, hTargetRightTokens,
          targetLeftTokens, targetRightTokens,
          GodelQuotation.Numbered.equality_tokens]
  | @membership entryDepth leftDepth rightDepth
      sourceLeft sourceRight targetLeft targetRight
      hSourceLeft hSourceRight hTargetLeft hTargetRight =>
      have hSourceLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceLeft
      have hSourceRightTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceRight
      have hTargetLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetLeft
      have hTargetRightTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetRight
      let sourceLeftTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name leftDepth)]
      let sourceRightTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name rightDepth)]
      let targetLeftTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name (canonical_project_shift_depth cutoff leftDepth))]
      let targetRightTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name (canonical_project_shift_depth cutoff rightDepth))]
      refine
        ⟨GodelQuotation.Numbered.membership_tokens
            sourceLeftTokens sourceRightTokens,
          GodelQuotation.Numbered.membership_tokens
            targetLeftTokens targetRightTokens,
          ?_, ?_⟩
      · simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
          GodelQuotation.Numbered.quote_relation_tokens_with?,
          hSourceLeftTokens, hSourceRightTokens,
          sourceLeftTokens, sourceRightTokens,
          GodelQuotation.Numbered.membership_tokens]
      · simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
          GodelQuotation.Numbered.quote_relation_tokens_with?,
          hTargetLeftTokens, hTargetRightTokens,
          targetLeftTokens, targetRightTokens,
          GodelQuotation.Numbered.membership_tokens]
  | @subset entryDepth leftDepth rightDepth
      sourceLeft sourceRight targetLeft targetRight
      hSourceLeft hSourceRight hTargetLeft hTargetRight =>
      have hSourceLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceLeft
      have hSourceRightTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceRight
      have hTargetLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetLeft
      have hTargetRightTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetRight
      let sourceLeftTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name leftDepth)]
      let sourceRightTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name rightDepth)]
      let targetLeftTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name (canonical_project_shift_depth cutoff leftDepth))]
      let targetRightTokens :=
        [GodelQuotation.Numbered.variable_token (GodelQuotation.bound_name (canonical_project_shift_depth cutoff rightDepth))]
      let sourceArgumentTokens : List (List Nat) :=
        [sourceLeftTokens, sourceRightTokens]
      let targetArgumentTokens : List (List Nat) :=
        [targetLeftTokens, targetRightTokens]
      refine
        ⟨GodelQuotation.Numbered.predicate_application_tokens
            1 RelationSymbol.subset.ctorIdx
            sourceArgumentTokens,
          GodelQuotation.Numbered.predicate_application_tokens
            1 RelationSymbol.subset.ctorIdx
            targetArgumentTokens,
          ?_, ?_⟩
      · simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
          GodelQuotation.Numbered.quote_relation_tokens_with?,
          hSourceLeftTokens, hSourceRightTokens,
          sourceLeftTokens, sourceRightTokens, sourceArgumentTokens,
          GodelQuotation.Numbered.predicate_application_tokens,
          GodelQuotation.fs_relation_kind_eq_predicate (relation := RelationSymbol.subset) (by decide)]
      · simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
          GodelQuotation.Numbered.quote_relation_tokens_with?,
          hTargetLeftTokens, hTargetRightTokens,
          targetLeftTokens, targetRightTokens, targetArgumentTokens,
          GodelQuotation.Numbered.predicate_application_tokens,
          GodelQuotation.fs_relation_kind_eq_predicate (relation := RelationSymbol.subset) (by decide)]
  | @negation entryDepth sourceBody targetBody body ih =>
      rcases ih with ⟨sourceTokens, targetTokens,
        hSourceTokens, hTargetTokens⟩
      refine
        ⟨GodelQuotation.Numbered.negation_tokens sourceTokens,
          GodelQuotation.Numbered.negation_tokens targetTokens,
          ?_, ?_⟩
      · simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
          hSourceTokens]
      · simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
          hTargetTokens]
  | @implication entryDepth sourceLeft sourceRight
      targetLeft targetRight left right ihLeft ihRight =>
      rcases ihLeft with
        ⟨sourceLeftTokens, targetLeftTokens,
          hSourceLeftTokens, hTargetLeftTokens⟩
      rcases ihRight with
        ⟨sourceRightTokens, targetRightTokens,
          hSourceRightTokens, hTargetRightTokens⟩
      refine
        ⟨GodelQuotation.Numbered.implication_tokens
            sourceLeftTokens sourceRightTokens,
          GodelQuotation.Numbered.implication_tokens
            targetLeftTokens targetRightTokens,
          ?_, ?_⟩
      · simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
          hSourceLeftTokens, hSourceRightTokens]
      · simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
          hTargetLeftTokens, hTargetRightTokens]
  | @universal entryDepth sourceBody targetBody body ih =>
      rcases ih with ⟨sourceTokens, targetTokens,
        hSourceTokens, hTargetTokens⟩
      change
        GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name
            GodelQuotation.bound_name (GodelQuotation.bound_name entryDepth ::
              GodelQuotation.canonical_bound_names entryDepth) (entryDepth + 1) sourceBody =
          some sourceTokens at hSourceTokens
      change
        GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name
            GodelQuotation.bound_name (GodelQuotation.bound_name (entryDepth + 1) ::
              GodelQuotation.canonical_bound_names (entryDepth + 1)) (entryDepth + 1 + 1) targetBody =
          some targetTokens at hTargetTokens
      refine
        ⟨GodelQuotation.Numbered.universal_tokens (GodelQuotation.bound_name entryDepth) sourceTokens,
          GodelQuotation.Numbered.universal_tokens (GodelQuotation.bound_name (entryDepth + 1)) targetTokens,
          ?_, ?_⟩
      · simp only [
          GodelQuotation.Numbered.quote_hilbert_tokens_with?]
        simp [hSourceTokens]
      · simp only [
          GodelQuotation.Numbered.quote_hilbert_tokens_with?]
        simp [hTargetTokens]
/--
公式级 cutoff-shift 保持规范 Hilbert quotation 的 token 数量。
变量 token 的数值允许变化，但每个变量仍占一个 token；否定、蕴含与全称构造只在
对应子串外添加同样数量的固定符号。
-/
theorem quote_hilbert_tokens_length_eq
    {cutoff entryDepth : Nat}
    {sourceFormula targetFormula : SetFormula} (shift :
      CanonicalProjectFormulaShift cutoff entryDepth
        sourceFormula targetFormula)
    {sourceTokens targetTokens : List Nat} (hSource :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name (GodelQuotation.canonical_bound_names entryDepth)
          entryDepth sourceFormula =
        some sourceTokens) (hTarget :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name (GodelQuotation.canonical_bound_names (entryDepth + 1)) (entryDepth + 1) targetFormula =
        some targetTokens) :
    sourceTokens.length = targetTokens.length := by
  induction shift generalizing sourceTokens targetTokens with
  | equality hSourceLeft hSourceRight hTargetLeft hTargetRight =>
      have hSourceLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceLeft
      have hSourceRightTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceRight
      have hTargetLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetLeft
      have hTargetRightTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetRight
      simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
        hSourceLeftTokens, hSourceRightTokens,
        hTargetLeftTokens, hTargetRightTokens,
        GodelQuotation.Numbered.equality_tokens] at hSource hTarget
      subst sourceTokens
      subst targetTokens
      simp
  | membership hSourceLeft hSourceRight hTargetLeft hTargetRight =>
      have hSourceLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceLeft
      have hSourceRightTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceRight
      have hTargetLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetLeft
      have hTargetRightTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetRight
      simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
        GodelQuotation.Numbered.quote_relation_tokens_with?,
        hSourceLeftTokens, hSourceRightTokens,
        hTargetLeftTokens, hTargetRightTokens,
        GodelQuotation.Numbered.membership_tokens] at hSource hTarget
      subst sourceTokens
      subst targetTokens
      simp
  | subset hSourceLeft hSourceRight hTargetLeft hTargetRight =>
      have hSourceLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceLeft
      have hSourceRightTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceRight
      have hTargetLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetLeft
      have hTargetRightTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetRight
      simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
        GodelQuotation.Numbered.quote_relation_tokens_with?,
        hSourceLeftTokens, hSourceRightTokens,
        hTargetLeftTokens, hTargetRightTokens,
        GodelQuotation.Numbered.predicate_application_tokens,
        GodelQuotation.fs_relation_kind_eq_predicate (relation := RelationSymbol.subset) (by decide)]
        at hSource hTarget
      subst sourceTokens
      subst targetTokens
      simp
  | @negation entryDepth sourceBody targetBody body ih =>
      simp only [
        GodelQuotation.Numbered.quote_hilbert_tokens_with?]
        at hSource hTarget
      cases hSourceBody :
          GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name
             GodelQuotation.bound_name (GodelQuotation.canonical_bound_names entryDepth)
             entryDepth sourceBody with
      | none =>
          simp [hSourceBody] at hSource
      | some sourceBodyTokens =>
          cases hTargetBody :
              GodelQuotation.Numbered.quote_hilbert_tokens_with?
                GodelQuotation.free_name
                GodelQuotation.bound_name (GodelQuotation.canonical_bound_names (entryDepth + 1)) (entryDepth + 1) targetBody with
          | none =>
              simp [hTargetBody] at hTarget
          | some targetBodyTokens =>
              simp [hSourceBody] at hSource
              simp [hTargetBody] at hTarget
              subst sourceTokens
              subst targetTokens
              simpa [GodelQuotation.Numbered.negation_tokens] using
                ih hSourceBody hTargetBody
  | @implication entryDepth sourceLeft sourceRight
      targetLeft targetRight left right ihLeft ihRight =>
      simp only [
        GodelQuotation.Numbered.quote_hilbert_tokens_with?]
        at hSource hTarget
      cases hSourceLeft :
          GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name
             GodelQuotation.bound_name (GodelQuotation.canonical_bound_names entryDepth)
             entryDepth sourceLeft with
      | none =>
          simp [hSourceLeft] at hSource
      | some sourceLeftTokens =>
          cases hSourceRight :
              GodelQuotation.Numbered.quote_hilbert_tokens_with?
                GodelQuotation.free_name
                 GodelQuotation.bound_name (GodelQuotation.canonical_bound_names entryDepth)
                 entryDepth sourceRight with
          | none =>
              simp [hSourceLeft, hSourceRight] at hSource
          | some sourceRightTokens =>
              cases hTargetLeft :
                  GodelQuotation.Numbered.quote_hilbert_tokens_with?
                    GodelQuotation.free_name
                    GodelQuotation.bound_name (GodelQuotation.canonical_bound_names (entryDepth + 1)) (entryDepth + 1) targetLeft with
              | none =>
                  simp [hTargetLeft] at hTarget
              | some targetLeftTokens =>
                  cases hTargetRight :
                      GodelQuotation.Numbered.quote_hilbert_tokens_with?
                        GodelQuotation.free_name
                        GodelQuotation.bound_name (GodelQuotation.canonical_bound_names (entryDepth + 1)) (entryDepth + 1) targetRight with
                  | none =>
                      simp [hTargetLeft, hTargetRight] at hTarget
                  | some targetRightTokens =>
                      simp [hSourceLeft, hSourceRight] at hSource
                      simp [hTargetLeft, hTargetRight] at hTarget
                      subst sourceTokens
                      subst targetTokens
                      have hLeftLength :=
                        ihLeft hSourceLeft hTargetLeft
                      have hRightLength :=
                        ihRight hSourceRight hTargetRight
                      simp [GodelQuotation.Numbered.implication_tokens,
                        hLeftLength, hRightLength]
  | @universal entryDepth sourceBody targetBody body ih =>
      simp only [
        GodelQuotation.Numbered.quote_hilbert_tokens_with?]
        at hSource hTarget
      cases hSourceBody :
          GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name
            GodelQuotation.bound_name (GodelQuotation.bound_name entryDepth ::
               GodelQuotation.canonical_bound_names entryDepth) (entryDepth + 1) sourceBody with
      | none =>
          simp [hSourceBody] at hSource
      | some sourceBodyTokens =>
          cases hTargetBody :
              GodelQuotation.Numbered.quote_hilbert_tokens_with?
                GodelQuotation.free_name
                GodelQuotation.bound_name (GodelQuotation.bound_name (entryDepth + 1) ::
                   GodelQuotation.canonical_bound_names (entryDepth + 1)) (entryDepth + 2) targetBody with
          | none =>
              simp [hTargetBody] at hTarget
          | some targetBodyTokens =>
              simp [hSourceBody] at hSource
              simp [hTargetBody] at hTarget
              subst sourceTokens
              subst targetTokens
              have hBodyLength :
                  sourceBodyTokens.length =
                    targetBodyTokens.length := by
                simpa [GodelQuotation.canonical_bound_names,
                  Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using
                  ih hSourceBody hTargetBody
              simp [GodelQuotation.Numbered.universal_tokens,
                hBodyLength]
end CanonicalProjectFormulaShift
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
