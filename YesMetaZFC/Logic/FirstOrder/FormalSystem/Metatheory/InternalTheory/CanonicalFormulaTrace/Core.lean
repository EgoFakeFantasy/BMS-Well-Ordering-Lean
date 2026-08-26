import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaClassifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNumbering
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence
/-!
# 规范纯集合论公式的外部构造轨迹
对象层 `canonical_project_formula_code_condition` 使用两个有限序列记录公式码和 quotation
深度。本模块给出与之对应的可计算外部编译器：
* 公式先进入 Hilbert 片段；
* 每个原子、否定、蕴含和全称量词按后序遍历生成一行；
* 复合行显式记录严格更早的前提行编号；
* 原子行只接受 bound 变量之间的等式、隶属与项目子集关系；
* 根行代码与任意入口深度下的规范 `quote_hilbert_with?` 字面一致。
该轨迹不是新的公理接口，而是后续把外部 schema quotation 装配成对象有限序列证书的
可计算数据层。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/-! ## 轨迹数据 -/
/-- 规范项目公式允许的三类原子。 -/
inductive CanonicalProjectAtomKind where
  | equality
  | membership
  | subset
  deriving Repr, DecidableEq
/-- 一行公式构造的外部标签；前提编号使用整条轨迹中的绝对位置。 -/
inductive CanonicalProjectTraceRule where
  | atomic (kind : CanonicalProjectAtomKind) (leftDepth rightDepth : Nat)
  | negation (premise : Nat)
  | implication (leftPremise rightPremise : Nat)
  | universal (premise : Nat)
  deriving Repr, DecidableEq
/-- 一行同时记录公式码、该子公式的入口深度和构造标签。 -/
structure CanonicalProjectTraceRow where
  formula : SetFormula
  code : SetTerm
  depth : Nat
  rule : CanonicalProjectTraceRule
/-- 一棵 Hilbert 公式树编译所得的连续后序轨迹。 -/
structure CanonicalProjectTrace where
  rows : List CanonicalProjectTraceRow
  rootIndex : Nat
  rootFormula : SetFormula
  rootCode : SetTerm
namespace CanonicalProjectTrace
/-! ## 对象有限序列见证 -/
/-- 轨迹逐行抽取所得的公式码列表。 -/
def code_terms (trace : CanonicalProjectTrace) : List SetTerm :=
  trace.rows.map CanonicalProjectTraceRow.code
/-- 轨迹逐行抽取所得的入口深度 numeral 列表。 -/
def depth_terms (trace : CanonicalProjectTrace) : List SetTerm :=
  trace.rows.map fun row => numₘ(row.depth)
/-- 公式码列表对应的标准对象有限序列。 -/
def code_sequence (trace : CanonicalProjectTrace) : SetTerm :=
  GodelQuotation.standard_sequence trace.code_terms
/-- 入口深度列表对应的标准对象有限序列。 -/
def depth_sequence (trace : CanonicalProjectTrace) : SetTerm :=
  GodelQuotation.standard_sequence trace.depth_terms
/-- 三类规范项目原子在给定变量深度处的公式码。 -/
@[simp]
def canonical_project_atom_code (kind : CanonicalProjectAtomKind) (leftDepth rightDepth : Nat) : SetTerm :=
  let leftCode :=
    GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name leftDepth)
  let rightCode :=
    GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name rightDepth)
  match kind with
  | .equality => eq_codeₘ(leftCode, rightCode)
  | .membership =>
      membership_atomic_formula_code_term leftCode rightCode
  | .subset =>
      project_subset_atomic_code_term leftCode rightCode
/-- 单行原子轨迹。 -/
def atomic (start depth : Nat) (formula : SetFormula) (code : SetTerm) (kind : CanonicalProjectAtomKind) (leftDepth rightDepth : Nat) :
    CanonicalProjectTrace where
  rows := [{
    formula := formula
    code := code
    depth := depth
    rule := .atomic kind leftDepth rightDepth
  }]
  rootIndex := start
  rootFormula := formula
  rootCode := code
/-- 在已有子轨迹之后追加否定根行。 -/
def negation (start depth : Nat) (bodyTrace : CanonicalProjectTrace) :
    CanonicalProjectTrace where
  rows :=
    bodyTrace.rows ++ [{
      formula := .neg bodyTrace.rootFormula
      code := neg_codeₘ(bodyTrace.rootCode)
      depth := depth
      rule := .negation bodyTrace.rootIndex
    }]
  rootIndex := start + bodyTrace.rows.length
  rootFormula := .neg bodyTrace.rootFormula
  rootCode := neg_codeₘ(bodyTrace.rootCode)
/-- 依次拼接左右子轨迹后追加蕴含根行。 -/
def implication (start depth : Nat) (leftTrace rightTrace : CanonicalProjectTrace) :
    CanonicalProjectTrace where
  rows :=
    leftTrace.rows ++ rightTrace.rows ++ [{
      formula := .imp
        leftTrace.rootFormula rightTrace.rootFormula
      code := imp_codeₘ(
        leftTrace.rootCode, rightTrace.rootCode)
      depth := depth
      rule := .implication
        leftTrace.rootIndex rightTrace.rootIndex
    }]
  rootIndex :=
    start + leftTrace.rows.length + rightTrace.rows.length
  rootFormula :=
    .imp leftTrace.rootFormula rightTrace.rootFormula
  rootCode :=
    imp_codeₘ(leftTrace.rootCode, rightTrace.rootCode)
/-- 在量词体轨迹之后追加规范全称量词根行。 -/
def universal (start depth : Nat) (bodyTrace : CanonicalProjectTrace) :
    CanonicalProjectTrace where
  rows :=
    bodyTrace.rows ++ [{
      formula := .forallE SetSort.set bodyTrace.rootFormula
      code := forall_codeₘ(
        GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth),
        bodyTrace.rootCode)
      depth := depth
      rule := .universal bodyTrace.rootIndex
    }]
  rootIndex := start + bodyTrace.rows.length
  rootFormula :=
    .forallE SetSort.set bodyTrace.rootFormula
  rootCode :=
    forall_codeₘ(
      GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth),
      bodyTrace.rootCode)
/-! ## 强归纳行证据 -/
/--
一行相对于连续片段起点的归纳构造证据。

复合行直接保存它实际引用的前驱行，而不再把前驱代码与深度拆成两条平行列表上的
存在见证。这样后续对象合法性证明可以直接消费前驱行的代码、深度和读取方程。
-/
inductive RowEvidenceFrom (trace : CanonicalProjectTrace) (start index : Nat) :
    CanonicalProjectTraceRow → Prop where
  | atomic
      (formula : SetFormula) (depth : Nat)
      (kind : CanonicalProjectAtomKind)
      (leftDepth rightDepth : Nat)
      (left_lt : leftDepth < depth)
      (right_lt : rightDepth < depth) :
      RowEvidenceFrom trace start index {
        formula := formula
        code := canonical_project_atom_code kind leftDepth rightDepth
        depth := depth
        rule := .atomic kind leftDepth rightDepth
      }
  | negation
      (formula : SetFormula) (depth premise : Nat)
      (premiseRow : CanonicalProjectTraceRow)
      (premise_start : start ≤ premise)
      (premise_lt : premise - start < index)
      (premise_get :
        trace.rows[premise - start]? = some premiseRow)
      (premise_depth :
        numₘ(premiseRow.depth) = numₘ(depth)) :
      RowEvidenceFrom trace start index {
        formula := formula
        code := neg_codeₘ(premiseRow.code)
        depth := depth
        rule := .negation premise
      }
  | implication
      (formula : SetFormula) (depth leftPremise rightPremise : Nat)
      (leftRow rightRow : CanonicalProjectTraceRow)
      (left_start : start ≤ leftPremise)
      (left_lt : leftPremise - start < index)
      (right_start : start ≤ rightPremise)
      (right_lt : rightPremise - start < index)
      (left_get :
        trace.rows[leftPremise - start]? = some leftRow)
      (right_get :
        trace.rows[rightPremise - start]? = some rightRow)
      (left_depth :
        numₘ(leftRow.depth) = numₘ(depth))
      (right_depth :
        numₘ(rightRow.depth) = numₘ(depth)) :
      RowEvidenceFrom trace start index {
        formula := formula
        code := imp_codeₘ(leftRow.code, rightRow.code)
        depth := depth
        rule := .implication leftPremise rightPremise
      }
  | universal
      (formula : SetFormula) (depth premise : Nat)
      (premiseRow : CanonicalProjectTraceRow)
      (premise_start : start ≤ premise)
      (premise_lt : premise - start < index)
      (premise_get :
        trace.rows[premise - start]? = some premiseRow)
      (premise_depth :
        numₘ(premiseRow.depth) = numₘ(depth + 1)) :
      RowEvidenceFrom trace start index {
        formula := formula
        code := forall_codeₘ(
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name depth),
          premiseRow.code)
        depth := depth
        rule := .universal premise
      }

/--
连续轨迹的每一行都携带由真实前驱行生成的归纳证据。
该接口取代平行代码/深度列表上的外置合同，严格更早性由局部索引直接表达。
-/
def RowsEvidenceFrom (trace : CanonicalProjectTrace) (start : Nat) : Prop :=
  ∀ ⦃index : Nat⦄ ⦃row : CanonicalProjectTraceRow⦄,
    trace.rows[index]? = some row →
      trace.RowEvidenceFrom start index row

/-- 原子标签从归纳证据中直接恢复深度界与代码形状。 -/
theorem RowEvidenceFrom.atomic_view
    {trace : CanonicalProjectTrace}
    {start index : Nat}
    {row : CanonicalProjectTraceRow}
    {kind : CanonicalProjectAtomKind}
    {leftDepth rightDepth : Nat}
    (evidence : trace.RowEvidenceFrom start index row)
    (hRule : row.rule = .atomic kind leftDepth rightDepth) :
    leftDepth < row.depth ∧
      rightDepth < row.depth ∧
      row.code =
        canonical_project_atom_code
          kind leftDepth rightDepth := by
  cases evidence <;> simp_all

/-- 否定标签恢复其真实前驱行，而不是两条平行列表上的分离见证。 -/
theorem RowEvidenceFrom.negation_view
    {trace : CanonicalProjectTrace}
    {start index premise : Nat}
    {row : CanonicalProjectTraceRow}
    (evidence : trace.RowEvidenceFrom start index row)
    (hRule : row.rule = .negation premise) :
    ∃ premiseRow,
      start ≤ premise ∧
        premise - start < index ∧
        trace.rows[premise - start]? = some premiseRow ∧
        numₘ(premiseRow.depth) = numₘ(row.depth) ∧
        row.code = neg_codeₘ(premiseRow.code) := by
  cases evidence <;> simp_all

/-- 蕴含标签同时恢复两个真实前驱行。 -/
theorem RowEvidenceFrom.implication_view
    {trace : CanonicalProjectTrace}
    {start index leftPremise rightPremise : Nat}
    {row : CanonicalProjectTraceRow}
    (evidence : trace.RowEvidenceFrom start index row)
    (hRule :
      row.rule =
        .implication leftPremise rightPremise) :
    ∃ leftRow rightRow,
      start ≤ leftPremise ∧
        leftPremise - start < index ∧
        start ≤ rightPremise ∧
        rightPremise - start < index ∧
        trace.rows[leftPremise - start]? = some leftRow ∧
        trace.rows[rightPremise - start]? = some rightRow ∧
        numₘ(leftRow.depth) = numₘ(row.depth) ∧
        numₘ(rightRow.depth) = numₘ(row.depth) ∧
        row.code = imp_codeₘ(leftRow.code, rightRow.code) := by
  cases evidence <;> simp_all

/-- 全称标签恢复深一层的真实量词体前驱行。 -/
theorem RowEvidenceFrom.universal_view
    {trace : CanonicalProjectTrace}
    {start index premise : Nat}
    {row : CanonicalProjectTraceRow}
    (evidence : trace.RowEvidenceFrom start index row)
    (hRule : row.rule = .universal premise) :
    ∃ premiseRow,
      start ≤ premise ∧
        premise - start < index ∧
        trace.rows[premise - start]? = some premiseRow ∧
        numₘ(premiseRow.depth) =
          numₘ(row.depth + 1) ∧
        row.code =
          forall_codeₘ(
            GodelQuotation.Numbered.named_variable_code
              (GodelQuotation.bound_name row.depth),
            premiseRow.code) := by
  cases evidence <;> simp_all

/-- 向轨迹末尾追加行不会改变旧行的归纳证据。 -/
theorem row_evidence_from_append_suffix
    {source target : CanonicalProjectTrace}
    {suffix : List CanonicalProjectTraceRow}
    {start index : Nat}
    {row : CanonicalProjectTraceRow}
    (hRows : target.rows = source.rows ++ suffix)
    (evidence : source.RowEvidenceFrom start index row) :
    target.RowEvidenceFrom start index row := by
  have lift_get
      {premiseIndex : Nat}
      {premiseRow : CanonicalProjectTraceRow}
      (hGet : source.rows[premiseIndex]? = some premiseRow) :
      target.rows[premiseIndex]? = some premiseRow := by
    rw [hRows, List.getElem?_append_left
      (List.getElem?_eq_some_iff.mp hGet).1]
    exact hGet
  cases evidence with
  | atomic formula depth kind leftDepth rightDepth hLeft hRight =>
      exact .atomic formula depth kind leftDepth rightDepth hLeft hRight
  | negation formula depth premise premiseRow hStart hEarlier hGet hDepth =>
      exact .negation formula depth premise premiseRow
        hStart hEarlier (lift_get hGet) hDepth
  | implication formula depth leftPremise rightPremise
      leftRow rightRow hLeftStart hLeftEarlier
      hRightStart hRightEarlier hLeftGet hRightGet
      hLeftDepth hRightDepth =>
      exact .implication formula depth leftPremise rightPremise
        leftRow rightRow hLeftStart hLeftEarlier
        hRightStart hRightEarlier
        (lift_get hLeftGet) (lift_get hRightGet)
        hLeftDepth hRightDepth
  | universal formula depth premise premiseRow hStart hEarlier hGet hDepth =>
      exact .universal formula depth premise premiseRow
        hStart hEarlier (lift_get hGet) hDepth

/--
在片段前插入前缀时，右侧片段的归纳证据整体平移到合并轨迹。
这里只处理一次局部索引算术，后续逐行证明不再重复该运输。
-/
theorem row_evidence_from_prepend_prefix
    {source target : CanonicalProjectTrace}
    {leading suffix : List CanonicalProjectTraceRow}
    {start index : Nat}
    {row : CanonicalProjectTraceRow}
    (hRows : target.rows = leading ++ source.rows ++ suffix)
    (evidence :
      source.RowEvidenceFrom
        (start + leading.length) index row) :
    target.RowEvidenceFrom
      start (leading.length + index) row := by
  have lift_get
      {premise : Nat}
      {premiseRow : CanonicalProjectTraceRow}
      (hStart : start + leading.length ≤ premise)
      (hGet :
        source.rows[premise - (start + leading.length)]? =
          some premiseRow) :
      target.rows[premise - start]? = some premiseRow := by
    have hLocal :
        premise - (start + leading.length) <
          source.rows.length :=
      (List.getElem?_eq_some_iff.mp hGet).1
    have hOffset :
        premise - start =
          leading.length +
            (premise - (start + leading.length)) := by
      omega
    rw [hRows, List.append_assoc, hOffset,
      List.getElem?_append_right]
    · simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left hLocal]
      exact hGet
    · simp
  cases evidence with
  | atomic formula depth kind leftDepth rightDepth hLeft hRight =>
      exact .atomic formula depth kind leftDepth rightDepth hLeft hRight
  | negation formula depth premise premiseRow hStart hEarlier hGet hDepth =>
      exact .negation formula depth premise premiseRow
        (by omega) (by omega) (lift_get hStart hGet) hDepth
  | implication formula depth leftPremise rightPremise
      leftRow rightRow hLeftStart hLeftEarlier
      hRightStart hRightEarlier hLeftGet hRightGet
      hLeftDepth hRightDepth =>
      exact .implication formula depth leftPremise rightPremise
        leftRow rightRow (by omega) (by omega)
        (by omega) (by omega)
        (lift_get hLeftStart hLeftGet)
        (lift_get hRightStart hRightGet)
        hLeftDepth hRightDepth
  | universal formula depth premise premiseRow hStart hEarlier hGet hDepth =>
      exact .universal formula depth premise premiseRow
        (by omega) (by omega) (lift_get hStart hGet) hDepth

/-- 同一位置的代码与深度读取可合并恢复为一条真实轨迹行。 -/
theorem row_of_code_depth_getElem?
    {trace : CanonicalProjectTrace}
    {index : Nat}
    {code depthCode : SetTerm}
    (hCode : trace.code_terms[index]? = some code)
    (hDepth : trace.depth_terms[index]? = some depthCode) :
    ∃ row,
      trace.rows[index]? = some row ∧
        row.code = code ∧
        numₘ(row.depth) = depthCode := by
  have hIndex : index < trace.rows.length := by
    simpa [code_terms] using
      (List.getElem?_eq_some_iff.mp hCode).1
  let row := trace.rows[index]'hIndex
  have hRow : trace.rows[index]? = some row := by
    exact List.getElem?_eq_getElem hIndex
  refine ⟨row, hRow, ?_, ?_⟩
  · simpa [code_terms, hRow] using hCode
  · simpa [depth_terms, hRow] using hDepth

/-- 单行原子轨迹直接产生归纳行证据。 -/
theorem atomic_rows_evidence
    (start depth : Nat) (formula : SetFormula)
    (kind : CanonicalProjectAtomKind)
    (leftDepth rightDepth : Nat)
    (hLeft : leftDepth < depth)
    (hRight : rightDepth < depth) :
    (atomic start depth formula
      (canonical_project_atom_code kind leftDepth rightDepth)
      kind leftDepth rightDepth).RowsEvidenceFrom start := by
  intro index row hRow
  have hIndex :
      index <
        (atomic start depth formula
          (canonical_project_atom_code kind leftDepth rightDepth)
          kind leftDepth rightDepth).rows.length :=
    (List.getElem?_eq_some_iff.mp hRow).1
  have hIndexZero : index = 0 := by
    simpa [atomic] using hIndex
  subst index
  have hRowEquality : ({
        formula := formula
        code := canonical_project_atom_code
          kind leftDepth rightDepth
        depth := depth
        rule := .atomic kind leftDepth rightDepth
      } : CanonicalProjectTraceRow) = row :=
    Option.some.inj <| by simpa [atomic] using hRow
  subst row
  exact .atomic formula depth kind leftDepth rightDepth
    hLeft hRight

/-- 在合法子轨迹后追加否定根行。 -/
theorem negation_rows_evidence
    {start depth : Nat}
    (bodyTrace : CanonicalProjectTrace)
    (hRows : bodyTrace.RowsEvidenceFrom start)
    (hRootBounds :
      start ≤ bodyTrace.rootIndex ∧
        bodyTrace.rootIndex <
          start + bodyTrace.rows.length)
    (hRootCode :
      bodyTrace.code_terms[
        bodyTrace.rootIndex - start]? =
          some bodyTrace.rootCode)
    (hRootDepth :
      bodyTrace.depth_terms[
        bodyTrace.rootIndex - start]? =
          some numₘ(depth)) :
    (negation start depth bodyTrace).RowsEvidenceFrom start := by
  intro index row hRow
  have hIndex :
      index < (negation start depth bodyTrace).rows.length :=
    (List.getElem?_eq_some_iff.mp hRow).1
  by_cases hOld : index < bodyTrace.rows.length
  · have hBodyRow :
        bodyTrace.rows[index]? = some row := by
      rw [← List.getElem?_append_left hOld]
      simpa [negation] using hRow
    exact row_evidence_from_append_suffix
      (source := bodyTrace)
      (target := negation start depth bodyTrace)
      (suffix := [{
        formula := .neg bodyTrace.rootFormula
        code := neg_codeₘ(bodyTrace.rootCode)
        depth := depth
        rule := .negation bodyTrace.rootIndex
      }])
      (by simp [negation]) (hRows hBodyRow)
  · have hRootIndex : index = bodyTrace.rows.length := by
      simp [negation] at hIndex
      omega
    subst index
    have hRowEquality : ({
          formula := .neg bodyTrace.rootFormula
          code := neg_codeₘ(bodyTrace.rootCode)
          depth := depth
          rule := .negation bodyTrace.rootIndex
        } : CanonicalProjectTraceRow) = row :=
      Option.some.inj <| by simpa [negation] using hRow
    subst row
    rcases row_of_code_depth_getElem?
        hRootCode hRootDepth with
      ⟨premiseRow, hPremise, hPremiseCode, hPremiseDepth⟩
    have hPremiseTarget :
        (negation start depth bodyTrace).rows[
            bodyTrace.rootIndex - start]? =
          some premiseRow := by
      rw [negation, List.getElem?_append_left
        (List.getElem?_eq_some_iff.mp hPremise).1]
      exact hPremise
    simpa [hPremiseCode] using
      (RowEvidenceFrom.negation
        (trace := negation start depth bodyTrace)
        (.neg bodyTrace.rootFormula) depth
        bodyTrace.rootIndex premiseRow
        hRootBounds.1 (by omega)
        hPremiseTarget hPremiseDepth)

/-- 在合法量词体轨迹后追加全称根行。 -/
theorem universal_rows_evidence
    {start depth : Nat}
    (bodyTrace : CanonicalProjectTrace)
    (hRows : bodyTrace.RowsEvidenceFrom start)
    (hRootBounds :
      start ≤ bodyTrace.rootIndex ∧
        bodyTrace.rootIndex <
          start + bodyTrace.rows.length)
    (hRootCode :
      bodyTrace.code_terms[
        bodyTrace.rootIndex - start]? =
          some bodyTrace.rootCode)
    (hRootDepth :
      bodyTrace.depth_terms[
        bodyTrace.rootIndex - start]? =
          some numₘ(depth + 1)) :
    (universal start depth bodyTrace).RowsEvidenceFrom start := by
  intro index row hRow
  have hIndex :
      index < (universal start depth bodyTrace).rows.length :=
    (List.getElem?_eq_some_iff.mp hRow).1
  by_cases hOld : index < bodyTrace.rows.length
  · have hBodyRow :
        bodyTrace.rows[index]? = some row := by
      rw [← List.getElem?_append_left hOld]
      simpa [universal] using hRow
    exact row_evidence_from_append_suffix
      (source := bodyTrace)
      (target := universal start depth bodyTrace)
      (suffix := [{
        formula := .forallE SetSort.set bodyTrace.rootFormula
        code := forall_codeₘ(
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name depth),
          bodyTrace.rootCode)
        depth := depth
        rule := .universal bodyTrace.rootIndex
      }])
      (by simp [universal]) (hRows hBodyRow)
  · have hRootIndex : index = bodyTrace.rows.length := by
      simp [universal] at hIndex
      omega
    subst index
    have hRowEquality : ({
          formula := .forallE SetSort.set bodyTrace.rootFormula
          code := forall_codeₘ(
            GodelQuotation.Numbered.named_variable_code
              (GodelQuotation.bound_name depth),
            bodyTrace.rootCode)
          depth := depth
          rule := .universal bodyTrace.rootIndex
        } : CanonicalProjectTraceRow) = row :=
      Option.some.inj <| by simpa [universal] using hRow
    subst row
    rcases row_of_code_depth_getElem?
        hRootCode hRootDepth with
      ⟨premiseRow, hPremise, hPremiseCode, hPremiseDepth⟩
    have hPremiseTarget :
        (universal start depth bodyTrace).rows[
            bodyTrace.rootIndex - start]? =
          some premiseRow := by
      rw [universal, List.getElem?_append_left
        (List.getElem?_eq_some_iff.mp hPremise).1]
      exact hPremise
    simpa [hPremiseCode] using
      (RowEvidenceFrom.universal
        (trace := universal start depth bodyTrace)
        (.forallE SetSort.set bodyTrace.rootFormula)
        depth bodyTrace.rootIndex premiseRow
        hRootBounds.1 (by omega)
        hPremiseTarget hPremiseDepth)

/-- 拼接两条合法子轨迹并追加蕴含根行。 -/
theorem implication_rows_evidence
    {start depth : Nat}
    (leftTrace rightTrace : CanonicalProjectTrace)
    (hLeftRows : leftTrace.RowsEvidenceFrom start)
    (hRightRows :
      rightTrace.RowsEvidenceFrom
        (start + leftTrace.rows.length))
    (hLeftRootBounds :
      start ≤ leftTrace.rootIndex ∧
        leftTrace.rootIndex <
          start + leftTrace.rows.length)
    (hRightRootBounds :
      start + leftTrace.rows.length ≤
          rightTrace.rootIndex ∧
        rightTrace.rootIndex <
          start + leftTrace.rows.length +
            rightTrace.rows.length)
    (hLeftRootCode :
      leftTrace.code_terms[
        leftTrace.rootIndex - start]? =
          some leftTrace.rootCode)
    (hRightRootCode :
      rightTrace.code_terms[
        rightTrace.rootIndex -
          (start + leftTrace.rows.length)]? =
            some rightTrace.rootCode)
    (hLeftRootDepth :
      leftTrace.depth_terms[
        leftTrace.rootIndex - start]? =
          some numₘ(depth))
    (hRightRootDepth :
      rightTrace.depth_terms[
        rightTrace.rootIndex -
          (start + leftTrace.rows.length)]? =
            some numₘ(depth)) :
    (implication start depth
      leftTrace rightTrace).RowsEvidenceFrom start := by
  intro index row hRow
  have hIndex :
      index <
        (implication start depth
          leftTrace rightTrace).rows.length :=
    (List.getElem?_eq_some_iff.mp hRow).1
  by_cases hLeft : index < leftTrace.rows.length
  · have hLeftRow :
        leftTrace.rows[index]? = some row := by
      rw [← List.getElem?_append_left hLeft]
      simpa [implication, List.append_assoc] using hRow
    exact row_evidence_from_append_suffix
      (source := leftTrace)
      (target := implication start depth leftTrace rightTrace)
      (suffix := rightTrace.rows ++ [{
        formula := .imp
          leftTrace.rootFormula rightTrace.rootFormula
        code := imp_codeₘ(
          leftTrace.rootCode, rightTrace.rootCode)
        depth := depth
        rule := .implication
          leftTrace.rootIndex rightTrace.rootIndex
      }])
      (by simp [implication, List.append_assoc])
      (hLeftRows hLeftRow)
  · have hLeftLe : leftTrace.rows.length ≤ index :=
      Nat.le_of_not_gt hLeft
    by_cases hChildren :
        index <
          leftTrace.rows.length + rightTrace.rows.length
    · let rightIndex := index - leftTrace.rows.length
      have hRightIndex :
          rightIndex < rightTrace.rows.length := by
        dsimp [rightIndex]
        omega
      have hCombinedIndex :
          index < (leftTrace.rows ++ rightTrace.rows).length := by
        simpa using hChildren
      have hCombinedRow :
          (leftTrace.rows ++ rightTrace.rows)[index]? =
            some row := by
        rw [← List.getElem?_append_left hCombinedIndex]
        simpa [implication] using hRow
      have hRightRow :
          rightTrace.rows[rightIndex]? = some row := by
        rw [List.getElem?_append_right] at hCombinedRow
        · simpa [rightIndex] using hCombinedRow
        · exact hLeftLe
      have shifted :=
        row_evidence_from_prepend_prefix
          (source := rightTrace)
          (target := implication start depth
            leftTrace rightTrace)
          (leading := leftTrace.rows)
          (suffix := [{
            formula := .imp
              leftTrace.rootFormula rightTrace.rootFormula
            code := imp_codeₘ(
              leftTrace.rootCode, rightTrace.rootCode)
            depth := depth
            rule := .implication
              leftTrace.rootIndex rightTrace.rootIndex
          }])
          (by simp [implication, List.append_assoc])
          (hRightRows hRightRow)
      have hIndexSplit :
          leftTrace.rows.length + rightIndex = index := by
        dsimp [rightIndex]
        omega
      simpa [hIndexSplit] using shifted
    · have hRootIndex :
          index =
            leftTrace.rows.length +
              rightTrace.rows.length := by
        simp [implication] at hIndex
        omega
      subst index
      have hRowEquality : ({
            formula := .imp
              leftTrace.rootFormula rightTrace.rootFormula
            code := imp_codeₘ(
              leftTrace.rootCode, rightTrace.rootCode)
            depth := depth
            rule := .implication
              leftTrace.rootIndex rightTrace.rootIndex
          } : CanonicalProjectTraceRow) = row :=
        Option.some.inj <| by
          simpa [implication] using hRow
      subst row
      rcases row_of_code_depth_getElem?
          hLeftRootCode hLeftRootDepth with
        ⟨leftRow, hLeftGet, hLeftCode, hLeftDepth⟩
      rcases row_of_code_depth_getElem?
          hRightRootCode hRightRootDepth with
        ⟨rightRow, hRightGet, hRightCode, hRightDepth⟩
      have hLeftTarget :
          (implication start depth leftTrace rightTrace).rows[
              leftTrace.rootIndex - start]? =
            some leftRow := by
        rw [implication, List.append_assoc,
          List.getElem?_append_left
            (List.getElem?_eq_some_iff.mp hLeftGet).1]
        exact hLeftGet
      have hRightOffset :
          rightTrace.rootIndex - start =
            leftTrace.rows.length +
              (rightTrace.rootIndex -
                (start + leftTrace.rows.length)) := by
        omega
      have hRightTarget :
          (implication start depth leftTrace rightTrace).rows[
              rightTrace.rootIndex - start]? =
            some rightRow := by
        rw [implication, List.append_assoc, hRightOffset,
          List.getElem?_append_right]
        · simp only [Nat.add_sub_cancel_left]
          rw [List.getElem?_append_left
            (List.getElem?_eq_some_iff.mp hRightGet).1]
          exact hRightGet
        · simp
      simpa [hLeftCode, hRightCode] using
        (RowEvidenceFrom.implication
          (trace := implication start depth
            leftTrace rightTrace)
          (.imp leftTrace.rootFormula rightTrace.rootFormula)
          depth leftTrace.rootIndex rightTrace.rootIndex
          leftRow rightRow
          hLeftRootBounds.1 (by omega)
          (by omega) (by omega)
          hLeftTarget hRightTarget
          hLeftDepth hRightDepth)
end CanonicalProjectTrace
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
