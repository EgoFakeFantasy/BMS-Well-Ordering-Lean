import YesMetaZFC.Logic.FirstOrder.Context.Basic
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution
import YesMetaZFC.Logic.FirstOrder.Admissibility.CheckAttr

/-!
# 一阶公共良构性边界
底层 `Formula` 保持为原始 AST。本模块在推导核之前提供 proof-carrying 的良构性
谓词，用于隔离：
* 函数、关系参数的 sort/arity 正确性；
* locally nameless bound 变量没有越界；
* 理论和有限上下文只包含可进入完备性构造的公式。
这里允许 free variable 存在，因为 Henkin witness 在证明论阶段正是通过新鲜
free variable 表示的。真正无 free variable 的句子由 `Formula.Sentence` 单独表示。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Scope
/-- 不同顺序压入两个 sort 只改变逐 sort 的计数，结果相同。 -/
theorem push_comm {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (scope : Scope σ) (left right : σ.SortSymbol) :
    push (push scope left) right = push (push scope right) left := by
  by_cases hEqual : left = right
  · subst right
    rfl
  · funext sort
    by_cases hLeft : sort = left
    · have hRight : sort ≠ right := by
        intro hSort
        exact hEqual (hLeft.symm.trans hSort)
      simp [push, hLeft, hEqual]
    · by_cases hRight : sort = right
      · have hRightLeft : right ≠ left := by
          intro hSort
          exact hEqual hSort.symm
        simp [push, hRight, hRightLeft]
      · simp [push, hLeft, hRight]
end Scope
namespace Term
/-- 项在任意 bound scope 下的 proof-carrying 良构性边界。 -/
def AdmissibleAt {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (scope : Scope σ) (term : Term σ) (sort : σ.SortSymbol) : Prop :=
  TermWellSorted term sort ∧ TermScoped scope term
/-- 项在空 bound scope 下良构，即 sort 正确且没有悬空 bound variable。 -/
def Admissible {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (term : Term σ) (sort : σ.SortSymbol) : Prop :=
  TermWellSorted term sort ∧ TermScoped Scope.empty term
end Term
/-- 关系与函数实参在任意 bound scope 下逐位置良构。 -/
def ArgsAdmissibleAt {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (scope : Scope σ) (arguments : List (Term σ))
    (sorts : List σ.SortSymbol) : Prop :=
  ArgsWellSorted arguments sorts ∧
    ∀ term, term ∈ arguments → TermScoped scope term
/--
关系与函数符号的实参列表在空 bound scope 下良构。
该结构把逐位置 sort/arity 证明与所有实参的 scope 证明绑在一起，作为原子公式和
函数项公共构造器的 proof-carrying 输入。
-/
def ArgsAdmissible {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (arguments : List (Term σ)) (sorts : List σ.SortSymbol) : Prop :=
  ArgsWellSorted arguments sorts ∧
    ∀ term, term ∈ arguments → TermScoped Scope.empty term

namespace ArgsAdmissible
theorem nil {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] :
    ArgsAdmissible ([] : List (Term σ)) [] := by
  constructor
  · exact .nil
  · intro term hTerm
    cases hTerm
theorem cons {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {term : Term σ} {terms : List (Term σ)}
    {sort : σ.SortSymbol} {sorts : List σ.SortSymbol} (hTerm : Term.Admissible term sort) (hTerms : ArgsAdmissible terms sorts) :
    ArgsAdmissible (term :: terms) (sort :: sorts) := by
  constructor
  · exact .cons hTerm.1 hTerms.1
  · intro candidate hCandidate
    rcases List.mem_cons.mp hCandidate with rfl | hCandidate
    · exact hTerm.2
    · exact hTerms.2 candidate hCandidate

end ArgsAdmissible
namespace ArgsAdmissibleAt
theorem nil {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} :
    ArgsAdmissibleAt scope ([] : List (Term σ)) [] :=
  ⟨.nil, by simp⟩
theorem cons {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} {term : Term σ} {terms : List (Term σ)}
    {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (hTerm : Term.AdmissibleAt scope term sort)
    (hTerms : ArgsAdmissibleAt scope terms sorts) :
    ArgsAdmissibleAt scope (term :: terms) (sort :: sorts) :=
  ⟨.cons hTerm.1 hTerms.1, by
    intro candidate hCandidate
    rcases List.mem_cons.mp hCandidate with rfl | hCandidate
    · exact hTerm.2
    · exact hTerms.2 candidate hCandidate⟩
end ArgsAdmissibleAt
namespace Term
/-- scope 计数逐 sort 增大时，原 scope 证书仍然有效。 -/
theorem scoped_mono {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {small large : Scope σ} {term : Term σ} (hTerm : TermScoped small term) (hScope : ∀ sort, small sort ≤ large sort) :
    TermScoped large term := by
  induction hTerm with
  | bvar hIndex =>
      exact TermScoped.bvar (Nat.lt_of_lt_of_le hIndex (hScope _))
  | fvar sort id =>
      exact TermScoped.fvar sort id
  | app function arguments =>
      rename_i hArguments ih
      exact TermScoped.app function arguments (fun argument hArgument => ih argument hArgument)
namespace AdmissibleAt
/-- scope 逐 sort 扩大时，proof-carrying 项证书保持成立。 -/
theorem mono {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {small large : Scope σ}
    {term : Term σ} {sort : σ.SortSymbol}
    (hTerm : Term.AdmissibleAt small term sort)
    (hScope : ∀ current, small current ≤ large current) :
    Term.AdmissibleAt large term sort :=
  ⟨hTerm.1, Term.scoped_mono hTerm.2 hScope⟩
/-- 向 scope 压入一个 binder 后，已有项证书可直接复用。 -/
theorem push {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {term : Term σ} {termSort : σ.SortSymbol}
    (sort : σ.SortSymbol)
    (hTerm : Term.AdmissibleAt scope term termSort) :
    Term.AdmissibleAt (Scope.push scope sort) term termSort :=
  mono hTerm <| by
    intro current
    by_cases hCurrent : current = sort
    · subst current
      simp [Scope.push]
    · simp [Scope.push, hCurrent]
/-- 闭项可提升到任意更大的 bound scope。 -/
theorem of_admissible {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {term : Term σ} {sort : σ.SortSymbol}
    (hTerm : Term.Admissible term sort) :
    Term.AdmissibleAt scope term sort :=
  ⟨hTerm.1, Term.scoped_mono hTerm.2 (fun _ => Nat.zero_le _)⟩
/-- scope 中已有位置构成 proof-carrying bound variable。 -/
theorem bvar {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {sort : σ.SortSymbol} {index : Nat} (hIndex : index < scope sort) :
    Term.AdmissibleAt scope (.var (.bvar sort index)) sort :=
  ⟨.bvar sort index, .bvar hIndex⟩
/-- free variable 不消耗 bound scope。 -/
theorem fvar {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    (sort : σ.SortSymbol) (id : FreeVarId) :
    Term.AdmissibleAt scope (.var (.fvar sort id)) sort :=
  ⟨.fvar sort id, .fvar sort id⟩
/-- proof-carrying 实参列表构成同 scope 下的函数应用。 -/
theorem app {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    (function : σ.FuncSymbol) {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissibleAt scope arguments (σ.funcDomain function)) :
    Term.AdmissibleAt scope (.app function arguments)
      (σ.funcCodomain function) :=
  ⟨.app function hArguments.1,
    .app function arguments hArguments.2⟩
end AdmissibleAt
/-- 从原始项中读取其构造出来的目标 sort。 -/
def inferredSort {σ : Signature.{u, v, w}} : Term σ → σ.SortSymbol
  | .var value => value.sort
  | .app function _ => σ.funcCodomain function
mutual
  /-- 可计算检查项是否具有指定 sort。 -/
  def check_wellSorted {σ : Signature.{u, v, w}}
      [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) : Term σ → Bool
    | .var (.bvar variableSort _) => decide (variableSort = sort)
    | .var (.fvar variableSort _) => decide (variableSort = sort)
    | .app function arguments =>
        decide (σ.funcCodomain function = sort) &&
          check_args_wellSorted arguments (σ.funcDomain function)
  def check_args_wellSorted {σ : Signature.{u, v, w}}
      [DecidableEq σ.SortSymbol] :
      List (Term σ) → List σ.SortSymbol → Bool
    | [], [] => true
    | term :: terms, sort :: sorts =>
        check_wellSorted sort term && check_args_wellSorted terms sorts
    | _, _ => false
end
mutual
  /-- `check_wellSorted` 通过时给出项的 sort 正确性证书。 -/
  theorem check_wellSorted_sound {σ : Signature.{u, v, w}}
      [DecidableEq σ.SortSymbol] {sort : σ.SortSymbol} {term : Term σ} (hCheck : check_wellSorted sort term = true) :
      TermWellSorted term sort := by
    cases term with
    | var value =>
        cases value with
        | bvar variableSort index =>
            have hSort : variableSort = sort := by
              simpa [check_wellSorted] using hCheck
            cases hSort
            exact TermWellSorted.bvar sort index
        | fvar variableSort id =>
            have hSort : variableSort = sort := by
              simpa [check_wellSorted] using hCheck
            cases hSort
            exact TermWellSorted.fvar sort id
    | app function arguments =>
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hCodomain, hArguments⟩
        have hSort : σ.funcCodomain function = sort :=
          of_decide_eq_true hCodomain
        cases hSort
        exact TermWellSorted.app function (check_args_wellSorted_sound hArguments)
  theorem check_args_wellSorted_sound {σ : Signature.{u, v, w}}
      [DecidableEq σ.SortSymbol] {arguments : List (Term σ)}
      {sorts : List σ.SortSymbol} (hCheck : check_args_wellSorted arguments sorts = true) :
      ArgsWellSorted arguments sorts := by
    cases arguments with
    | nil =>
        cases sorts with
        | nil =>
            exact .nil
        | cons _ _ =>
            simp [check_args_wellSorted] at hCheck
    | cons term terms =>
        cases sorts with
        | nil =>
            simp [check_args_wellSorted] at hCheck
        | cons sort sorts =>
            rcases Bool.and_eq_true_iff.mp hCheck with ⟨hTerm, hRest⟩
            exact ArgsWellSorted.cons (check_wellSorted_sound hTerm) (check_args_wellSorted_sound hRest)
end
mutual
  /-- sort 正确的项必通过可计算 sort 检查。 -/
  theorem check_wellSorted_complete
      {σ : Signature.{u, v, w}}
      [DecidableEq σ.SortSymbol]
      {sort : σ.SortSymbol} {term : Term σ}
      (hTerm : TermWellSorted term sort) :
      check_wellSorted sort term = true := by
    cases hTerm with
    | bvar =>
        simp [check_wellSorted]
    | fvar =>
        simp [check_wellSorted]
    | app function hArguments =>
        simp [check_wellSorted,
          check_args_wellSorted_complete hArguments]
  /-- 逐位置 sort 正确的实参列表必通过可计算检查。 -/
  theorem check_args_wellSorted_complete
      {σ : Signature.{u, v, w}}
      [DecidableEq σ.SortSymbol]
      {arguments : List (Term σ)}
      {sorts : List σ.SortSymbol}
      (hArguments :
        ArgsWellSorted arguments sorts) :
      check_args_wellSorted arguments sorts =
        true := by
    cases hArguments with
    | nil =>
        rfl
    | cons hTerm hRest =>
        simp [check_args_wellSorted,
          check_wellSorted_complete hTerm,
          check_args_wellSorted_complete hRest]
end
mutual
  /-- 可计算检查项在给定逐 sort bound scope 下是否无越界变量。 -/
  def check_scoped {σ : Signature.{u, v, w}}
      [DecidableEq σ.SortSymbol] (scope : Scope σ) : Term σ → Bool
    | .var (.bvar sort index) => decide (index < scope sort)
    | .var (.fvar _ _) => true
    | .app _ arguments => check_args_scoped scope arguments
  /-- 可计算检查项列表在给定 bound scope 下是否全部无越界变量。 -/
  def check_args_scoped {σ : Signature.{u, v, w}}
      [DecidableEq σ.SortSymbol] (scope : Scope σ) :
      List (Term σ) → Bool
    | [] => true
    | term :: terms =>
        check_scoped scope term && check_args_scoped scope terms
end
mutual
  /-- `check_scoped` 通过时给出项的 scope 正确性证书。 -/
  theorem check_scoped_sound {σ : Signature.{u, v, w}}
      [DecidableEq σ.SortSymbol] {scope : Scope σ} {term : Term σ} (hCheck : check_scoped scope term = true) :
      TermScoped scope term := by
    cases term with
    | var value =>
        cases value with
        | bvar sort index =>
            exact TermScoped.bvar <| by
              simpa [check_scoped] using of_decide_eq_true hCheck
        | fvar sort id =>
            exact TermScoped.fvar sort id
    | app function arguments =>
        exact TermScoped.app function arguments (check_args_scoped_sound hCheck)
  /-- `check_args_scoped` 通过时，列表中的每个项都给出 scope 正确性证书。 -/
  theorem check_args_scoped_sound {σ : Signature.{u, v, w}}
      [DecidableEq σ.SortSymbol] {scope : Scope σ}
      {arguments : List (Term σ)} (hCheck : check_args_scoped scope arguments = true) :
      ∀ term, term ∈ arguments → TermScoped scope term := by
    cases arguments with
    | nil =>
        intro term hTerm
        cases hTerm
    | cons head tail =>
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hTail⟩
        intro term hTerm
        rcases List.mem_cons.mp hTerm with rfl | hTerm
        · exact check_scoped_sound hHead
        · exact check_args_scoped_sound hTail term hTerm
end
/-- scope 正确的项必通过可计算 scope 检查。 -/
theorem check_scoped_complete
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {scope : Scope σ} {term : Term σ}
    (hTerm : TermScoped scope term) :
    check_scoped scope term = true := by
  induction hTerm with
  | bvar hIndex =>
      simp [check_scoped, hIndex]
  | fvar =>
      rfl
  | app function arguments hArguments ih =>
      have hList :
          check_args_scoped scope arguments =
            true := by
        induction arguments with
        | nil =>
            rfl
        | cons head tail ihTail =>
            have hHead :=
              ih head (by simp)
            have hRest :
                ∀ term, term ∈ tail →
                  check_scoped scope term =
                    true := by
              intro candidate hCandidate
              exact ih candidate
                (by simp [hCandidate])
            have hTailScoped :
                ∀ term, term ∈ tail →
                  TermScoped scope term := by
              intro candidate hCandidate
              exact hArguments candidate
                (by simp [hCandidate])
            simp [check_args_scoped,
              hHead,
              ihTail hTailScoped hRest]
      simpa [check_scoped] using hList

/-- 全部 scope 正确的实参列表必通过可计算检查。 -/
theorem check_args_scoped_complete
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {scope : Scope σ}
    {arguments : List (Term σ)}
    (hArguments :
      ∀ term, term ∈ arguments →
        TermScoped scope term) :
    check_args_scoped scope arguments = true := by
  induction arguments with
  | nil =>
      rfl
  | cons head tail ih =>
      have hHead :=
        hArguments head (by simp)
      have hTail :
          ∀ term, term ∈ tail →
            TermScoped scope term := by
        intro term hTerm
        exact hArguments term (by simp [hTerm])
      simp [check_args_scoped,
        check_scoped_complete hHead,
        ih hTail]
/-- 对闭项同时执行 sort 与 bound-scope 检查。 -/
def check_admissible {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (term : Term σ) : Bool :=
  check_wellSorted sort term && check_scoped Scope.empty term
/-- 项的可计算合法证书。证书本身只保存纯函数检查成功这一事实。 -/
abbrev CheckCertificate {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (term : Term σ) (sort : σ.SortSymbol) : Prop :=
  check_admissible sort term = true
/-- 项检查成功可恢复原有 proof-layer 合法性命题。 -/
theorem check_admissible_sound
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {sort : σ.SortSymbol} {term : Term σ}
    (hCheck : CheckCertificate term sort) :
    Admissible term sort := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hSort, hScope⟩
  exact ⟨check_wellSorted_sound hSort, check_scoped_sound hScope⟩
/-- proof-layer 合法项必通过纯函数检查。 -/
theorem check_admissible_complete
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {sort : σ.SortSymbol} {term : Term σ}
    (hTerm : Admissible term sort) :
    CheckCertificate term sort :=
  Bool.and_eq_true_iff.mpr
    ⟨check_wellSorted_complete hTerm.1,
      check_scoped_complete hTerm.2⟩
/-- 已有 proof-layer 项合法性可直接进入项目计算证书 simp 集。 -/
@[term_check]
theorem check_certificate_of_admissible
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {sort : σ.SortSymbol} {term : Term σ}
    (hTerm : Admissible term sort) :
    CheckCertificate term sort :=
  check_admissible_complete hTerm
namespace CheckCertificate
/-- 计算证书的命题视图。 -/
theorem admissible
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {sort : σ.SortSymbol} {term : Term σ}
    (hCheck : CheckCertificate term sort) :
    Admissible term sort :=
  check_admissible_sound hCheck

/-- 自由变量项的合法性由结构直接决定，不要求调用方提交 sort/scope 证明。 -/
@[term_check]
theorem fvar
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    (sort : σ.SortSymbol) (id : FreeVarId) :
    CheckCertificate (Term.var (.fvar sort id)) sort :=
  check_admissible_complete
    ⟨TermWellSorted.fvar sort id, TermScoped.fvar sort id⟩
end CheckCertificate
/--
关闭 free variable 会在目标 sort 的 bound scope 中增加一个位置，并保持原项的
scope 正确性。`depth` 必须落在原 scope 已经经过的目标 sort binder 数量内。
-/
theorem closeFreeAt_scoped {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ} {term : Term σ}
    {target : σ.SortSymbol} {id : FreeVarId} {depth : Nat} (hTerm : TermScoped scope term) (hDepth : depth ≤ scope target) :
    TermScoped (Scope.push scope target) (Term.closeFreeAt target id depth term) := by
  induction hTerm with
  | bvar hIndex =>
      rename_i sort idx
      by_cases hSort : sort = target
      · subst sort
        by_cases hClose : depth ≤ idx
        · have hNew : idx + 1 < (Scope.push scope target) target := by
            simp [Scope.push]
            omega
          simpa [Term.closeFreeAt, hClose] using (TermScoped.bvar (ctx := Scope.push scope target) hNew)
        · have hNew : idx < (Scope.push scope target) target := by
            simp [Scope.push]
            omega
          simpa [Term.closeFreeAt, hClose] using (TermScoped.bvar (ctx := Scope.push scope target) hNew)
      · have hNew : idx < (Scope.push scope target) sort := by
          simpa [Scope.push, hSort] using hIndex
        simpa [Term.closeFreeAt, hSort] using (TermScoped.bvar (ctx := Scope.push scope target) hNew)
  | fvar sort freeId =>
      by_cases hClose : sort = target ∧ freeId = id
      · have hNew : depth < (Scope.push scope target) target := by
          simp [Scope.push]
          omega
        simpa [Term.closeFreeAt, hClose] using (TermScoped.bvar (ctx := Scope.push scope target) hNew)
      · simpa [Term.closeFreeAt, hClose] using (TermScoped.fvar (ctx := Scope.push scope target) sort freeId)
  | app function arguments =>
      rename_i hArguments ih
      have hArgumentsClosed :
          ∀ argument, argument ∈
            arguments.map (Term.closeFreeAt target id depth) →
              TermScoped (Scope.push scope target) argument := by
        intro argument hArgument
        rcases List.mem_map.mp hArgument with ⟨source, hSource, rfl⟩
        exact ih source hSource
      simpa [Term.closeFreeAt] using (TermScoped.app function (arguments.map (Term.closeFreeAt target id depth))
          hArgumentsClosed)
/--
打开指定 binder 时，replacement 使用 bound-closed 项，因此不会把其内部
bound variable 捕获到新的量词下。
-/
theorem openAt_scoped {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ} {term replacement : Term σ}
    {target : σ.SortSymbol} {depth : Nat} (hTerm : TermScoped (Scope.push scope target) term) (hReplacement : TermScoped Scope.empty replacement)
    (hDepth : depth ≤ scope target) :
    TermScoped scope (Term.openAt target depth replacement term) := by
  induction hTerm with
  | bvar hIndex =>
      rename_i sort index
      by_cases hSort : sort = target
      · subst sort
        by_cases hEqual : index = depth
        · have hReplacement' : TermScoped scope replacement :=
            Term.scoped_mono hReplacement (fun _ => Nat.zero_le _)
          simpa [Term.openAt, hEqual] using hReplacement'
        · by_cases hAbove : depth < index
          · have hIndex' : index - 1 < scope target := by
              simp [Scope.push] at hIndex
              omega
            simpa [Term.openAt, hEqual, hAbove] using (TermScoped.bvar (ctx := scope) hIndex')
          · have hIndex' : index < scope target := by
              simp [Scope.push] at hIndex
              omega
            simpa [Term.openAt, hEqual, hAbove] using (TermScoped.bvar (ctx := scope) hIndex')
      · have hIndex' : index < scope sort := by
          simpa [Scope.push, hSort] using hIndex
        simpa [Term.openAt, hSort] using (TermScoped.bvar (ctx := scope) hIndex')
  | fvar sort freeId =>
      simpa [Term.openAt] using (TermScoped.fvar (ctx := scope) sort freeId)
  | app function arguments =>
      rename_i hArguments ih
      have hArgumentsOpened :
          ∀ argument, argument ∈
            arguments.map (Term.openAt target depth replacement) →
              TermScoped scope argument := by
        intro argument hArgument
        rcases List.mem_map.mp hArgument with ⟨source, hSource, rfl⟩
        exact ih source hSource
      simpa [Term.openAt] using (TermScoped.app function (arguments.map (Term.openAt target depth replacement))
          hArgumentsOpened)
end Term
/-- 同一原始项的 sort 证书唯一。 -/
theorem TermWellSorted.sort_unique
    {σ : Signature.{u, v, w}} {term : Term σ}
    {left right : σ.SortSymbol} (hLeft : TermWellSorted term left) (hRight : TermWellSorted term right) :
    left = right := by
  cases hLeft <;> cases hRight <;> rfl
/-- sort 正确性证书与项语法记录的目标 sort 一致。 -/
theorem TermWellSorted.inferredSort_eq
    {σ : Signature.{u, v, w}}
    {term : Term σ} {sort : σ.SortSymbol}
    (hTerm : TermWellSorted term sort) :
    term.inferredSort = sort := by
  cases hTerm <;> rfl
mutual
/-- `openAt` 保持项的 sort 正确性。 -/
theorem TermWellSorted.openAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {term replacement : Term σ}
    {sort target : σ.SortSymbol} (depth : Nat) (hTerm : TermWellSorted term sort) (hReplacement : TermWellSorted replacement target) :
    TermWellSorted (Term.openAt target depth replacement term) sort := by
  cases hTerm with
  | bvar =>
      rename_i index
      by_cases hSort : sort = target
      · subst sort
        by_cases hEqual : index = depth
        · simpa [Term.openAt, hEqual] using hReplacement
        · by_cases hAbove : depth < index
          · simpa [Term.openAt, hEqual, hAbove] using (TermWellSorted.bvar target (index - 1))
          · simpa [Term.openAt, hEqual, hAbove] using (TermWellSorted.bvar target index)
      · simpa [Term.openAt, hSort] using (TermWellSorted.bvar sort index)
  | fvar =>
      rename_i id
      simpa [Term.openAt] using (TermWellSorted.fvar sort id)
  | app function hArguments =>
      simpa [Term.openAt] using (TermWellSorted.app function (ArgsWellSorted.openAt target depth hReplacement hArguments))
/-- `openAt` 逐项保持参数列表的 sort 正确性。 -/
theorem ArgsWellSorted.openAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {arguments : List (Term σ)}
    {sorts : List σ.SortSymbol} {replacement : Term σ} (target : σ.SortSymbol) (depth : Nat) (hReplacement : TermWellSorted replacement target)
    (hArguments : ArgsWellSorted arguments sorts) :
    ArgsWellSorted (arguments.map (Term.openAt target depth replacement)) sorts := by
  cases hArguments with
  | nil =>
      exact .nil
  | cons hTerm hRest =>
      exact .cons (TermWellSorted.openAt depth hTerm hReplacement) (ArgsWellSorted.openAt target depth hReplacement hRest)
end
mutual
/-- `closeFreeAt` 保持项的 sort 正确性。 -/
theorem TermWellSorted.closeFreeAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {term : Term σ} {sort : σ.SortSymbol} (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (hTerm : TermWellSorted term sort) :
    TermWellSorted (Term.closeFreeAt target id depth term) sort := by
  cases hTerm with
  | bvar =>
      rename_i index
      by_cases hClose : sort = target ∧ depth ≤ index
      · simpa [Term.closeFreeAt, hClose] using (TermWellSorted.bvar sort (index + 1))
      · simpa [Term.closeFreeAt, hClose] using (TermWellSorted.bvar sort index)
  | fvar =>
      rename_i freeId
      by_cases hClose : sort = target ∧ freeId = id
      · simpa [Term.closeFreeAt, hClose] using (TermWellSorted.bvar sort depth)
      · simpa [Term.closeFreeAt, hClose] using (TermWellSorted.fvar sort freeId)
  | app function hArguments =>
      simpa [Term.closeFreeAt] using (TermWellSorted.app function (ArgsWellSorted.closeFreeAt target id depth hArguments))
/-- `closeFreeAt` 逐项保持参数列表的 sort 正确性。 -/
theorem ArgsWellSorted.closeFreeAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {arguments : List (Term σ)}
    {sorts : List σ.SortSymbol} (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (hArguments : ArgsWellSorted arguments sorts) :
    ArgsWellSorted (arguments.map (Term.closeFreeAt target id depth)) sorts := by
  cases hArguments with
  | nil =>
      exact .nil
  | cons hTerm hRest =>
      exact .cons (TermWellSorted.closeFreeAt target id depth hTerm) (ArgsWellSorted.closeFreeAt target id depth hRest)
end
mutual
/-- `substituteFree` 在替换项 sort 匹配时保持项的 sort 正确性。 -/
theorem TermWellSorted.substituteFree {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {term replacement : Term σ}
    {sort target : σ.SortSymbol} (id : FreeVarId) (hTerm : TermWellSorted term sort) (hReplacement : TermWellSorted replacement target) :
    TermWellSorted (Term.substituteFree target id replacement term) sort := by
  cases hTerm with
  | bvar =>
      rename_i index
      simpa [Term.substituteFree] using (TermWellSorted.bvar sort index)
  | fvar =>
      rename_i freeId
      by_cases hSubstitute : sort = target ∧ freeId = id
      · rcases hSubstitute with ⟨rfl, rfl⟩
        simpa [Term.substituteFree] using hReplacement
      · simpa [Term.substituteFree, hSubstitute] using (TermWellSorted.fvar sort freeId)
  | app function hArguments =>
      simpa [Term.substituteFree] using (TermWellSorted.app function (ArgsWellSorted.substituteFree target id hReplacement hArguments))
/-- `substituteFree` 逐项保持参数列表的 sort 正确性。 -/
theorem ArgsWellSorted.substituteFree {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {arguments : List (Term σ)}
    {sorts : List σ.SortSymbol} {replacement : Term σ} (target : σ.SortSymbol) (id : FreeVarId) (hReplacement : TermWellSorted replacement target)
    (hArguments : ArgsWellSorted arguments sorts) :
    ArgsWellSorted (arguments.map (Term.substituteFree target id replacement)) sorts := by
  cases hArguments with
  | nil =>
      exact .nil
  | cons hTerm hRest =>
      exact .cons (TermWellSorted.substituteFree id hTerm hReplacement) (ArgsWellSorted.substituteFree target id hReplacement hRest)
end
/--
若自由变量替换后的项 sort 正确，则原项也具有同一 sort。
目标自由变量分支由 replacement 的 sort 唯一性恢复；因此该反演不是语法恒等式，
而是 `TermWellSorted.sort_unique` 的实质应用。
-/
theorem TermWellSorted.substituteFree_source
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {term replacement : Term σ} {sort target : σ.SortSymbol} (id : FreeVarId) (hReplacement : TermWellSorted replacement target) (hSubstituted :
      TermWellSorted (Term.substituteFree target id replacement term) sort) :
    TermWellSorted term sort := by
  refine Term.rec (motive_1 := fun term =>
      ∀ sort,
        TermWellSorted (Term.substituteFree target id replacement term) sort →
          TermWellSorted term sort) (motive_2 := fun arguments =>
      ∀ sorts,
        ArgsWellSorted (arguments.map (Term.substituteFree target id replacement)) sorts →
          ArgsWellSorted arguments sorts)
    ?_ ?_ ?_ ?_ term sort hSubstituted
  · intro value resultSort hResult
    cases value with
    | bvar variableSort index =>
        simpa [Term.substituteFree] using hResult
    | fvar variableSort freeId =>
        by_cases hTarget : variableSort = target ∧ freeId = id
        · have hReplacementResult :
              TermWellSorted replacement resultSort := by
            simpa [Term.substituteFree, hTarget] using hResult
          have hSort : variableSort = resultSort :=
            hTarget.1.trans (TermWellSorted.sort_unique
                hReplacement hReplacementResult)
          simpa [hSort] using (TermWellSorted.fvar variableSort freeId)
        · simpa [Term.substituteFree, hTarget] using hResult
  · intro function arguments ihArguments resultSort hResult
    simp only [Term.substituteFree] at hResult
    cases hResult with
    | app _ hArguments =>
        exact TermWellSorted.app function (ihArguments (σ.funcDomain function) hArguments)
  · intro sorts hArguments
    cases hArguments
    exact .nil
  · intro head tail ihHead ihTail sorts hArguments
    cases hArguments with
    | cons hHead hTail =>
        exact .cons (ihHead _ hHead) (ihTail _ hTail)
/-- 对参数列表逐项反演 `substituteFree` 的 sort 正确性。 -/
theorem ArgsWellSorted.substituteFree_source
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {arguments : List (Term σ)} {sorts : List σ.SortSymbol}
    {replacement : Term σ} (target : σ.SortSymbol) (id : FreeVarId) (hReplacement : TermWellSorted replacement target) (hSubstituted :
      ArgsWellSorted (arguments.map (Term.substituteFree target id replacement)) sorts) :
    ArgsWellSorted arguments sorts := by
  induction arguments generalizing sorts with
  | nil =>
      cases hSubstituted
      exact .nil
  | cons argument arguments ih =>
      cases hSubstituted with
      | cons hArgument hArguments =>
          exact .cons (TermWellSorted.substituteFree_source
              id hReplacement hArgument) (ih hArguments)
namespace Term
/--
`substituteFree` 只接受 bound-closed replacement，因此穿过任意量词 scope 时不会
捕获 replacement 中的 de Bruijn 变量。
-/
theorem substituteFree_scoped {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ} {term replacement : Term σ}
    {target : σ.SortSymbol} {id : FreeVarId} (hTerm : TermScoped scope term) (hReplacement : TermScoped Scope.empty replacement) :
    TermScoped scope (Term.substituteFree target id replacement term) := by
  induction hTerm with
  | bvar hIndex =>
      simpa [Term.substituteFree] using (TermScoped.bvar (ctx := scope) hIndex)
  | fvar sort freeId =>
      by_cases hSubstitute : sort = target ∧ freeId = id
      · have hReplacement' : TermScoped scope replacement :=
          Term.scoped_mono hReplacement (fun _ => Nat.zero_le _)
        simpa [Term.substituteFree, hSubstitute] using hReplacement'
      · simpa [Term.substituteFree, hSubstitute] using (TermScoped.fvar (ctx := scope) sort freeId)
  | app function arguments =>
      rename_i hArguments ih
      have hArgumentsSubstituted :
          ∀ argument, argument ∈
            arguments.map (Term.substituteFree target id replacement) →
              TermScoped scope argument := by
        intro argument hArgument
        rcases List.mem_map.mp hArgument with ⟨source, hSource, rfl⟩
        exact ih source hSource
      simpa [Term.substituteFree] using (TermScoped.app function (arguments.map (Term.substituteFree target id replacement))
          hArgumentsSubstituted)
/--
若替换后的项在给定 scope 下合法，则原项同样合法。
被替换位置原本是 free variable，本身不消耗 bound scope；所以该方向不要求
replacement 的 scope 证书。
-/
theorem substituteFree_scoped_source
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} {term replacement : Term σ}
    {target : σ.SortSymbol} {id : FreeVarId} (hSubstituted :
      TermScoped scope (Term.substituteFree target id replacement term)) :
    TermScoped scope term := by
  refine Term.rec (motive_1 := fun term =>
      ∀ scope,
        TermScoped scope (Term.substituteFree target id replacement term) →
          TermScoped scope term) (motive_2 := fun terms =>
      ∀ scope, (∀ term,
          term ∈ terms.map (Term.substituteFree target id replacement) →
            TermScoped scope term) →
          ∀ term, term ∈ terms → TermScoped scope term)
    ?_ ?_ ?_ ?_ term scope hSubstituted
  · intro value currentScope hResult
    cases value with
    | bvar sort index =>
        simpa [Term.substituteFree] using hResult
    | fvar sort freeId =>
        by_cases hTarget : sort = target ∧ freeId = id
        · exact TermScoped.fvar sort freeId
        · simpa [Term.substituteFree, hTarget] using hResult
  · intro function arguments ihArguments currentScope hResult
    simp only [Term.substituteFree] at hResult
    cases hResult with
    | app _ _ hArguments =>
        exact TermScoped.app function arguments (ihArguments currentScope hArguments)
  · intro currentScope _ term hMember
    cases hMember
  · intro head tail ihHead ihTail currentScope hTerms source hMember
    rcases List.mem_cons.mp hMember with hSource | hMember
    · subst source
      exact ihHead currentScope <| hTerms (Term.substituteFree target id replacement head) (by simp)
    · exact ihTail currentScope (by
          intro substituted hSubstitutedMember
          exact hTerms substituted (by
            simp only [List.map_cons, List.mem_cons]
            exact Or.inr hSubstitutedMember))
        source hMember
namespace AdmissibleAt
/-- 深度零处关闭自由变量，同时把对应 binder 压入 scope。 -/
theorem closeFreeAt_zero {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {term : Term σ} {sort : σ.SortSymbol}
    (target : σ.SortSymbol) (id : FreeVarId)
    (hTerm : Term.AdmissibleAt scope term sort) :
    Term.AdmissibleAt (Scope.push scope target)
      (Term.closeFreeAt target id 0 term) sort :=
  ⟨TermWellSorted.closeFreeAt target id 0 hTerm.1,
    Term.closeFreeAt_scoped hTerm.2 (Nat.zero_le _)⟩
end AdmissibleAt
end Term
namespace ArgsAdmissibleAt
/-- 深度零处逐项关闭实参列表，并同步压入对应 binder。 -/
theorem closeFreeAt_zero {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {arguments : List (Term σ)} {sorts : List σ.SortSymbol}
    (target : σ.SortSymbol) (id : FreeVarId)
    (hArguments : ArgsAdmissibleAt scope arguments sorts) :
    ArgsAdmissibleAt (Scope.push scope target)
      (arguments.map (Term.closeFreeAt target id 0)) sorts :=
  ⟨ArgsWellSorted.closeFreeAt target id 0 hArguments.1, by
    intro term hTerm
    rcases List.mem_map.mp hTerm with ⟨source, hSource, rfl⟩
    exact Term.closeFreeAt_scoped
      (hArguments.2 source hSource) (Nat.zero_le _)⟩
end ArgsAdmissibleAt
namespace Formula
/-- scope 计数逐 sort 增大时，原公式的 scope 证书仍然有效。 -/
theorem scoped_mono {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {small large : Scope σ}
    {formula : Formula σ} (hFormula : FormulaScoped small formula) (hScope : ∀ sort, small sort ≤ large sort) :
    FormulaScoped large formula := by
  induction hFormula generalizing large with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments hArguments =>
      exact .rel relation arguments fun term hTerm =>
        Term.scoped_mono (hArguments term hTerm) hScope
  | equal hLeft hRight =>
      exact .equal (Term.scoped_mono hLeft hScope) (Term.scoped_mono hRight hScope)
  | neg hBody ih =>
      exact .neg (ih hScope)
  | conj hLeft hRight ihLeft ihRight =>
      exact .conj (ihLeft hScope) (ihRight hScope)
  | disj hLeft hRight ihLeft ihRight =>
      exact .disj (ihLeft hScope) (ihRight hScope)
  | imp hLeft hRight ihLeft ihRight =>
      exact .imp (ihLeft hScope) (ihRight hScope)
  | iff hLeft hRight ihLeft ihRight =>
      exact .iff (ihLeft hScope) (ihRight hScope)
  | forallE sort hBody ih =>
      apply FormulaScoped.forallE
      apply ih
      intro current
      by_cases hCurrent : current = sort
      · subst current
        simp [Scope.push, hScope]
      · simp [Scope.push, hCurrent, hScope]
  | existsE sort hBody ih =>
      apply FormulaScoped.existsE
      apply ih
      intro current
      by_cases hCurrent : current = sort
      · subst current
        simp [Scope.push, hScope]
      · simp [Scope.push, hCurrent, hScope]
/-- 可计算检查公式的 sort/arity 正确性。 -/
def check_wellFormed {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] : Formula σ → Bool
  | .falsum => true
  | .truth => true
  | .rel relation arguments =>
      Term.check_args_wellSorted arguments (σ.relDomain relation)
  | .equal left right =>
      Term.check_wellSorted left.inferredSort left &&
        Term.check_wellSorted left.inferredSort right
  | .neg body => check_wellFormed body
  | .conj left right =>
      check_wellFormed left && check_wellFormed right
  | .disj left right =>
      check_wellFormed left && check_wellFormed right
  | .imp left right =>
      check_wellFormed left && check_wellFormed right
  | .iff left right =>
      check_wellFormed left && check_wellFormed right
  | .forallE _ body => check_wellFormed body
  | .existsE _ body => check_wellFormed body
/-- 可计算检查公式在给定逐 sort bound scope 下是否无越界变量。 -/
def check_scoped {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (scope : Scope σ) : Formula σ → Bool
  | .falsum => true
  | .truth => true
  | .rel _ arguments => Term.check_args_scoped scope arguments
  | .equal left right =>
      Term.check_scoped scope left && Term.check_scoped scope right
  | .neg body => check_scoped scope body
  | .conj left right =>
      check_scoped scope left && check_scoped scope right
  | .disj left right =>
      check_scoped scope left && check_scoped scope right
  | .imp left right =>
      check_scoped scope left && check_scoped scope right
  | .iff left right =>
      check_scoped scope left && check_scoped scope right
  | .forallE sort body => check_scoped (Scope.push scope sort) body
  | .existsE sort body => check_scoped (Scope.push scope sort) body
/-- `check_wellFormed` 通过时给出公式的 sort/arity 正确性证书。 -/
theorem check_wellFormed_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {formula : Formula σ} (hCheck : check_wellFormed formula = true) :
    FormulaWellFormed formula := by
  induction formula with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      exact .rel relation (Term.check_args_wellSorted_sound hCheck)
  | equal left right =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .equal (Term.check_wellSorted_sound hLeft) (Term.check_wellSorted_sound hRight)
  | neg body ih =>
      exact .neg (ih hCheck)
  | conj left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .conj (ihLeft hLeft) (ihRight hRight)
  | disj left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .disj (ihLeft hLeft) (ihRight hRight)
  | imp left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .imp (ihLeft hLeft) (ihRight hRight)
  | iff left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .iff (ihLeft hLeft) (ihRight hRight)
  | forallE sort body ih =>
      exact .forallE sort (ih hCheck)
  | existsE sort body ih =>
      exact .existsE sort (ih hCheck)
/-- `check_scoped` 通过时给出公式的 scope 正确性证书。 -/
theorem check_scoped_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ} {formula : Formula σ} (hCheck : check_scoped scope formula = true) :
    FormulaScoped scope formula := by
  induction formula generalizing scope with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      exact FormulaScoped.rel relation arguments (Term.check_args_scoped_sound hCheck)
  | equal left right =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .equal (Term.check_scoped_sound hLeft) (Term.check_scoped_sound hRight)
  | neg body ih =>
      exact .neg (ih hCheck)
  | conj left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .conj (ihLeft hLeft) (ihRight hRight)
  | disj left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .disj (ihLeft hLeft) (ihRight hRight)
  | imp left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .imp (ihLeft hLeft) (ihRight hRight)
  | iff left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .iff (ihLeft hLeft) (ihRight hRight)
  | forallE sort body ih =>
      exact .forallE sort (ih hCheck)
  | existsE sort body ih =>
      exact .existsE sort (ih hCheck)
/-- 良构公式必通过可计算 sort/arity 检查。 -/
theorem check_wellFormed_complete
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ}
    (hFormula : FormulaWellFormed formula) :
    check_wellFormed formula = true := by
  induction hFormula with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation hArguments =>
      exact Term.check_args_wellSorted_complete
        hArguments
  | @equal left right sort hLeft hRight =>
      have hSort :
          left.inferredSort = sort :=
        hLeft.inferredSort_eq
      rw [check_wellFormed, hSort]
      exact Bool.and_eq_true_iff.mpr
        ⟨Term.check_wellSorted_complete hLeft,
          Term.check_wellSorted_complete hRight⟩
  | neg hBody ih =>
      simpa [check_wellFormed] using ih
  | conj hLeft hRight ihLeft ihRight
  | disj hLeft hRight ihLeft ihRight
  | imp hLeft hRight ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      simp [check_wellFormed, ihLeft, ihRight]
  | forallE sort hBody ih
  | existsE sort hBody ih =>
      simpa [check_wellFormed] using ih

/-- scope 正确的公式必通过可计算 scope 检查。 -/
theorem check_scoped_complete
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {scope : Scope σ}
    {formula : Formula σ}
    (hFormula : FormulaScoped scope formula) :
    check_scoped scope formula = true := by
  induction hFormula with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments hArguments =>
      exact Term.check_args_scoped_complete
        hArguments
  | equal hLeft hRight =>
      simp [check_scoped,
        Term.check_scoped_complete hLeft,
        Term.check_scoped_complete hRight]
  | neg hBody ih =>
      simpa [check_scoped] using ih
  | conj hLeft hRight ihLeft ihRight
  | disj hLeft hRight ihLeft ihRight
  | imp hLeft hRight ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      simp [check_scoped, ihLeft, ihRight]
  | forallE sort hBody ih
  | existsE sort hBody ih =>
      simpa [check_scoped] using ih
/-- `closeFreeAt` 保持公式的 sort/arity 正确性。 -/
theorem FormulaWellFormed.wf_closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {formula : Formula σ} (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (hFormula : FormulaWellFormed formula) :
    FormulaWellFormed (Formula.closeFreeAt target id depth formula) := by
  induction formula generalizing depth with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      cases hFormula with
      | rel _ hArguments =>
          exact .rel relation (ArgsWellSorted.closeFreeAt target id depth hArguments)
  | equal left right =>
      cases hFormula with
      | equal hLeft hRight =>
          exact .equal (TermWellSorted.closeFreeAt target id depth hLeft) (TermWellSorted.closeFreeAt target id depth hRight)
  | neg body ih =>
      cases hFormula with
      | neg hBody =>
          exact .neg (ih depth hBody)
  | conj left right ihLeft ihRight =>
      cases hFormula with
      | conj hLeft hRight =>
          exact .conj (ihLeft depth hLeft) (ihRight depth hRight)
  | disj left right ihLeft ihRight =>
      cases hFormula with
      | disj hLeft hRight =>
          exact .disj (ihLeft depth hLeft) (ihRight depth hRight)
  | imp left right ihLeft ihRight =>
      cases hFormula with
      | imp hLeft hRight =>
          exact .imp (ihLeft depth hLeft) (ihRight depth hRight)
  | iff left right ihLeft ihRight =>
      cases hFormula with
      | iff hLeft hRight =>
          exact .iff (ihLeft depth hLeft) (ihRight depth hRight)
  | forallE binder body ih =>
      cases hFormula with
      | forallE _ hBody =>
          exact .forallE binder (ih (if binder = target then depth + 1 else depth) hBody)
  | existsE binder body ih =>
      cases hFormula with
      | existsE _ hBody =>
          exact .existsE binder (ih (if binder = target then depth + 1 else depth) hBody)
/-- `openAt` 保持公式的 sort/arity 正确性。 -/
theorem FormulaWellFormed.wf_openAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {term : Term σ}
    {target : σ.SortSymbol} (depth : Nat) (hFormula : FormulaWellFormed formula) (hReplacement : TermWellSorted term target) :
    FormulaWellFormed (Formula.openAt target depth term formula) := by
  induction formula generalizing depth with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      cases hFormula with
      | rel _ hArguments =>
          exact .rel relation (ArgsWellSorted.openAt target depth hReplacement hArguments)
  | equal left right =>
      cases hFormula with
      | equal hLeft hRight =>
          exact .equal (TermWellSorted.openAt depth hLeft hReplacement) (TermWellSorted.openAt depth hRight hReplacement)
  | neg body ih =>
      cases hFormula with
      | neg hBody =>
          exact .neg (ih depth hBody)
  | conj left right ihLeft ihRight =>
      cases hFormula with
      | conj hLeft hRight =>
          exact .conj (ihLeft depth hLeft) (ihRight depth hRight)
  | disj left right ihLeft ihRight =>
      cases hFormula with
      | disj hLeft hRight =>
          exact .disj (ihLeft depth hLeft) (ihRight depth hRight)
  | imp left right ihLeft ihRight =>
      cases hFormula with
      | imp hLeft hRight =>
          exact .imp (ihLeft depth hLeft) (ihRight depth hRight)
  | iff left right ihLeft ihRight =>
      cases hFormula with
      | iff hLeft hRight =>
          exact .iff (ihLeft depth hLeft) (ihRight depth hRight)
  | forallE binder body ih =>
      cases hFormula with
      | forallE _ hBody =>
          exact .forallE binder (ih (if binder = target then depth + 1 else depth) hBody)
  | existsE binder body ih =>
      cases hFormula with
      | existsE _ hBody =>
          exact .existsE binder (ih (if binder = target then depth + 1 else depth) hBody)
/-- `substituteFree` 在 replacement sort 匹配时保持公式的 sort/arity 正确性。 -/
theorem FormulaWellFormed.wf_substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {replacement : Term σ} (target : σ.SortSymbol) (id : FreeVarId) (hFormula : FormulaWellFormed formula)
    (hReplacement : TermWellSorted replacement target) :
    FormulaWellFormed (Formula.substituteFree target id replacement formula) := by
  induction formula with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      cases hFormula with
      | rel _ hArguments =>
          exact .rel relation (ArgsWellSorted.substituteFree target id hReplacement hArguments)
  | equal left right =>
      cases hFormula with
      | equal hLeft hRight =>
          exact .equal (TermWellSorted.substituteFree id hLeft hReplacement) (TermWellSorted.substituteFree id hRight hReplacement)
  | neg body ih =>
      cases hFormula with
      | neg hBody =>
          exact .neg (ih hBody)
  | conj left right ihLeft ihRight =>
      cases hFormula with
      | conj hLeft hRight =>
          exact .conj (ihLeft hLeft) (ihRight hRight)
  | disj left right ihLeft ihRight =>
      cases hFormula with
      | disj hLeft hRight =>
          exact .disj (ihLeft hLeft) (ihRight hRight)
  | imp left right ihLeft ihRight =>
      cases hFormula with
      | imp hLeft hRight =>
          exact .imp (ihLeft hLeft) (ihRight hRight)
  | iff left right ihLeft ihRight =>
      cases hFormula with
      | iff hLeft hRight =>
          exact .iff (ihLeft hLeft) (ihRight hRight)
  | forallE binder body ih =>
      cases hFormula with
      | forallE _ hBody =>
          exact .forallE binder (ih hBody)
  | existsE binder body ih =>
      cases hFormula with
      | existsE _ hBody =>
          exact .existsE binder (ih hBody)
/--
若自由变量替换后的公式 sort/arity 正确，则原公式同样正确。
该定理与 `wf_substituteFree` 组成双向的良构性接口；等词模板和关系模板因此可以
先在具体闭项实例上检查，再反演回含占位自由变量的通用模板。
-/
theorem FormulaWellFormed.substituteFree_source
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {replacement : Term σ} (target : σ.SortSymbol) (id : FreeVarId) (hReplacement : TermWellSorted replacement target) (hSubstituted :
      FormulaWellFormed (Formula.substituteFree target id replacement formula)) :
    FormulaWellFormed formula := by
  induction formula with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      cases hSubstituted with
      | rel _ hArguments =>
          exact .rel relation (ArgsWellSorted.substituteFree_source
              target id hReplacement hArguments)
  | equal left right =>
      cases hSubstituted with
      | equal hLeft hRight =>
          exact .equal (TermWellSorted.substituteFree_source
              id hReplacement hLeft) (TermWellSorted.substituteFree_source
              id hReplacement hRight)
  | neg body ih =>
      cases hSubstituted with
      | neg hBody =>
          exact .neg (ih hBody)
  | conj left right ihLeft ihRight =>
      cases hSubstituted with
      | conj hLeft hRight =>
          exact .conj (ihLeft hLeft) (ihRight hRight)
  | disj left right ihLeft ihRight =>
      cases hSubstituted with
      | disj hLeft hRight =>
          exact .disj (ihLeft hLeft) (ihRight hRight)
  | imp left right ihLeft ihRight =>
      cases hSubstituted with
      | imp hLeft hRight =>
          exact .imp (ihLeft hLeft) (ihRight hRight)
  | iff left right ihLeft ihRight =>
      cases hSubstituted with
      | iff hLeft hRight =>
          exact .iff (ihLeft hLeft) (ihRight hRight)
  | forallE binder body ih =>
      cases hSubstituted with
      | forallE _ hBody =>
          exact .forallE binder (ih hBody)
  | existsE binder body ih =>
      cases hSubstituted with
      | existsE _ hBody =>
          exact .existsE binder (ih hBody)
/--
`closeFreeAt` 把一个 free variable 变为新增的目标 sort binder，并保持公式的
scope 正确性。
-/
theorem FormulaScoped.sc_closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} {formula : Formula σ}
    {target : σ.SortSymbol} {id : FreeVarId} {depth : Nat} (hFormula : FormulaScoped scope formula) (hDepth : depth ≤ scope target) :
    FormulaScoped (Scope.push scope target) (Formula.closeFreeAt target id depth formula) := by
  induction formula generalizing scope depth with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      cases hFormula with
      | rel _ _ hArguments =>
          apply FormulaScoped.rel
          intro argument hArgument
          rcases List.mem_map.mp hArgument with ⟨source, hSource, rfl⟩
          exact Term.closeFreeAt_scoped (hArguments source hSource) hDepth
  | equal left right =>
      cases hFormula with
      | equal hLeft hRight =>
          exact .equal (Term.closeFreeAt_scoped hLeft hDepth) (Term.closeFreeAt_scoped hRight hDepth)
  | neg body ih =>
      cases hFormula with
      | neg hBody =>
          exact .neg (ih hBody hDepth)
  | conj left right ihLeft ihRight =>
      cases hFormula with
      | conj hLeft hRight =>
          exact .conj (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | disj left right ihLeft ihRight =>
      cases hFormula with
      | disj hLeft hRight =>
          exact .disj (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | imp left right ihLeft ihRight =>
      cases hFormula with
      | imp hLeft hRight =>
          exact .imp (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | iff left right ihLeft ihRight =>
      cases hFormula with
      | iff hLeft hRight =>
          exact .iff (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | forallE binder body ih =>
      cases hFormula with
      | forallE _ hBody =>
          apply FormulaScoped.forallE
          have hDepthBody : (if binder = target then depth + 1 else depth) ≤ (Scope.push scope binder) target := by
            by_cases hBinder : binder = target
            · subst binder
              simp [Scope.push]
              omega
            · have hTarget : target ≠ binder := by
                intro hEqual
                exact hBinder hEqual.symm
              simpa [Scope.push, hBinder, hTarget] using hDepth
          have hClosed := ih hBody hDepthBody
          rw [Scope.push_comm scope binder target] at hClosed
          exact hClosed
  | existsE binder body ih =>
      cases hFormula with
      | existsE _ hBody =>
          apply FormulaScoped.existsE
          have hDepthBody : (if binder = target then depth + 1 else depth) ≤ (Scope.push scope binder) target := by
            by_cases hBinder : binder = target
            · subst binder
              simp [Scope.push]
              omega
            · have hTarget : target ≠ binder := by
                intro hEqual
                exact hBinder hEqual.symm
              simpa [Scope.push, hBinder, hTarget] using hDepth
          have hClosed := ih hBody hDepthBody
          rw [Scope.push_comm scope binder target] at hClosed
          exact hClosed
/-- `openAt` 把空 scope 的替换项插入公式后，保持公式的 scope 正确性。 -/
theorem FormulaScoped.sc_openAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} {formula : Formula σ} {term : Term σ}
    {target : σ.SortSymbol} {depth : Nat} (hFormula : FormulaScoped (Scope.push scope target) formula) (hReplacement : TermScoped Scope.empty term)
    (hDepth : depth ≤ scope target) :
    FormulaScoped scope (Formula.openAt target depth term formula) := by
  induction formula generalizing scope depth with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      cases hFormula with
      | rel _ _ hArguments =>
          apply FormulaScoped.rel
          intro argument hArgument
          rcases List.mem_map.mp hArgument with ⟨source, hSource, rfl⟩
          exact Term.openAt_scoped (hArguments source hSource) hReplacement hDepth
  | equal left right =>
      cases hFormula with
      | equal hLeft hRight =>
          exact .equal (Term.openAt_scoped hLeft hReplacement hDepth) (Term.openAt_scoped hRight hReplacement hDepth)
  | neg body ih =>
      cases hFormula with
      | neg hBody =>
          exact .neg (ih hBody hDepth)
  | conj left right ihLeft ihRight =>
      cases hFormula with
      | conj hLeft hRight =>
          exact .conj (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | disj left right ihLeft ihRight =>
      cases hFormula with
      | disj hLeft hRight =>
          exact .disj (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | imp left right ihLeft ihRight =>
      cases hFormula with
      | imp hLeft hRight =>
          exact .imp (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | iff left right ihLeft ihRight =>
      cases hFormula with
      | iff hLeft hRight =>
          exact .iff (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | forallE binder body ih =>
      cases hFormula with
      | forallE _ hBody =>
          apply FormulaScoped.forallE
          have hDepthBody : (if binder = target then depth + 1 else depth) ≤ (Scope.push scope binder) target := by
            by_cases hBinder : binder = target
            · subst binder
              simp [Scope.push]
              omega
            · have hTarget : target ≠ binder := by
                intro hEqual
                exact hBinder hEqual.symm
              simpa [Scope.push, hBinder, hTarget] using hDepth
          have hBodyScope :
              FormulaScoped (Scope.push (Scope.push scope binder) target) body := by
            rw [← Scope.push_comm scope target binder]
            exact hBody
          exact ih hBodyScope hDepthBody
  | existsE binder body ih =>
      cases hFormula with
      | existsE _ hBody =>
          apply FormulaScoped.existsE
          have hDepthBody : (if binder = target then depth + 1 else depth) ≤ (Scope.push scope binder) target := by
            by_cases hBinder : binder = target
            · subst binder
              simp [Scope.push]
              omega
            · have hTarget : target ≠ binder := by
                intro hEqual
                exact hBinder hEqual.symm
              simpa [Scope.push, hBinder, hTarget] using hDepth
          have hBodyScope :
              FormulaScoped (Scope.push (Scope.push scope binder) target) body := by
            rw [← Scope.push_comm scope target binder]
            exact hBody
          exact ih hBodyScope hDepthBody
/--
`substituteFree` 使用 bound-closed replacement，因此穿过公式中的量词时保持
scope 正确性且不会发生捕获。
-/
theorem FormulaScoped.sc_substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} {formula : Formula σ} {replacement : Term σ}
    {target : σ.SortSymbol} {id : FreeVarId} (hFormula : FormulaScoped scope formula) (hReplacement : TermScoped Scope.empty replacement) :
    FormulaScoped scope (Formula.substituteFree target id replacement formula) := by
  induction formula generalizing scope with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      cases hFormula with
      | rel _ _ hArguments =>
          apply FormulaScoped.rel
          intro argument hArgument
          rcases List.mem_map.mp hArgument with ⟨source, hSource, rfl⟩
          exact Term.substituteFree_scoped (hArguments source hSource) hReplacement
  | equal left right =>
      cases hFormula with
      | equal hLeft hRight =>
          exact .equal (Term.substituteFree_scoped hLeft hReplacement) (Term.substituteFree_scoped hRight hReplacement)
  | neg body ih =>
      cases hFormula with
      | neg hBody =>
          exact .neg (ih hBody)
  | conj left right ihLeft ihRight =>
      cases hFormula with
      | conj hLeft hRight =>
          exact .conj (ihLeft hLeft) (ihRight hRight)
  | disj left right ihLeft ihRight =>
      cases hFormula with
      | disj hLeft hRight =>
          exact .disj (ihLeft hLeft) (ihRight hRight)
  | imp left right ihLeft ihRight =>
      cases hFormula with
      | imp hLeft hRight =>
          exact .imp (ihLeft hLeft) (ihRight hRight)
  | iff left right ihLeft ihRight =>
      cases hFormula with
      | iff hLeft hRight =>
          exact .iff (ihLeft hLeft) (ihRight hRight)
  | forallE binder body ih =>
      cases hFormula with
      | forallE _ hBody =>
          exact .forallE binder (ih hBody)
  | existsE binder body ih =>
      cases hFormula with
      | existsE _ hBody =>
          exact .existsE binder (ih hBody)
/-- 替换后公式的 scope 合法性可反演回原公式。 -/
theorem FormulaScoped.substituteFree_source
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} {formula : Formula σ} {replacement : Term σ}
    {target : σ.SortSymbol} {id : FreeVarId} (hSubstituted :
      FormulaScoped scope (Formula.substituteFree target id replacement formula)) :
    FormulaScoped scope formula := by
  induction formula generalizing scope with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      cases hSubstituted with
      | rel _ _ hArguments =>
          exact FormulaScoped.rel relation arguments (by
            intro argument hArgument
            apply Term.substituteFree_scoped_source
            exact hArguments (Term.substituteFree target id replacement argument) (List.mem_map.mpr ⟨argument, hArgument, rfl⟩))
  | equal left right =>
      cases hSubstituted with
      | equal hLeft hRight =>
          exact .equal (Term.substituteFree_scoped_source hLeft) (Term.substituteFree_scoped_source hRight)
  | neg body ih =>
      cases hSubstituted with
      | neg hBody =>
          exact .neg (ih hBody)
  | conj left right ihLeft ihRight =>
      cases hSubstituted with
      | conj hLeft hRight =>
          exact .conj (ihLeft hLeft) (ihRight hRight)
  | disj left right ihLeft ihRight =>
      cases hSubstituted with
      | disj hLeft hRight =>
          exact .disj (ihLeft hLeft) (ihRight hRight)
  | imp left right ihLeft ihRight =>
      cases hSubstituted with
      | imp hLeft hRight =>
          exact .imp (ihLeft hLeft) (ihRight hRight)
  | iff left right ihLeft ihRight =>
      cases hSubstituted with
      | iff hLeft hRight =>
          exact .iff (ihLeft hLeft) (ihRight hRight)
  | forallE binder body ih =>
      cases hSubstituted with
      | forallE _ hBody =>
          exact .forallE binder (ih hBody)
  | existsE binder body ih =>
      cases hSubstituted with
      | existsE _ hBody =>
          exact .existsE binder (ih hBody)
/-- 公式可进入证明层的良构性：sort/arity 正确且没有悬空 bound variable。 -/
def AdmissibleAt {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (scope : Scope σ) (formula : Formula σ) : Prop :=
  FormulaWellFormed formula ∧ FormulaScoped scope formula
/-- 公式可进入证明层的良构性：sort/arity 正确且没有悬空 bound variable。 -/
def Admissible {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (formula : Formula σ) : Prop :=
  FormulaWellFormed formula ∧ FormulaScoped Scope.empty formula
/-- 无 free variable 的良构公式；开放公式仍由 `Admissible` 表示。 -/
def Sentence {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (formula : Formula σ) : Prop :=
  Admissible formula ∧ freeSupport formula = []
/-- 对 raw 公式执行完整的 proof-layer 良构性检查。 -/
def check_admissible {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (formula : Formula σ) : Bool :=
  check_wellFormed formula && check_scoped Scope.empty formula
/-- `check_admissible` 通过时给出公开的 admissibility 证书。 -/
theorem check_admissible_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {formula : Formula σ} (hCheck : check_admissible formula = true) :
    Admissible formula := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hWellFormed, hScoped⟩
  exact ⟨check_wellFormed_sound hWellFormed, check_scoped_sound hScoped⟩
/-- admissible 公式必通过公开的完整可计算检查。 -/
theorem check_admissible_complete
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ}
    (hFormula : Admissible formula) :
    check_admissible formula = true := by
  exact Bool.and_eq_true_iff.mpr
    ⟨check_wellFormed_complete hFormula.1,
      check_scoped_complete hFormula.2⟩
/-- 公式的可计算合法证书。证书本身只保存纯函数检查成功这一事实。 -/
abbrev CheckCertificate {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (formula : Formula σ) : Prop :=
  check_admissible formula = true
/-- 已有 proof-layer 公式合法性可直接转成计算证书。 -/
theorem check_certificate_of_admissible
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ}
    (hFormula : Admissible formula) :
    CheckCertificate formula :=
  check_admissible_complete hFormula
namespace CheckCertificate
/-- 计算证书与原 proof-layer 良构性命题完全等价。 -/
theorem iff_admissible
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ} :
    CheckCertificate formula ↔ Admissible formula :=
  ⟨check_admissible_sound, check_admissible_complete⟩
/-- 计算证书直接恢复公式良构性。 -/
theorem admissible
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ}
    (hCheck : CheckCertificate formula) :
    Admissible formula :=
  check_admissible_sound hCheck
/-- 计算证书直接恢复 sort/arity 良构性。 -/
theorem wellFormed
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ}
    (hCheck : CheckCertificate formula) :
    FormulaWellFormed formula :=
  hCheck.admissible.1
end CheckCertificate
/-- 自动化和完备性层共同消费的 proof-carrying raw 公式。 -/
structure WF_Payload (σ : Signature.{u, v, w}) [DecidableEq σ.SortSymbol] where
  formula : Formula σ
  admissible : Admissible formula
/-- 从通过计算检查的 raw 公式构造公共 proof-carrying payload。 -/
def wf_payload_of_check {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (formula : Formula σ) (hCheck : check_admissible formula = true) :
    WF_Payload σ where
  formula := formula
  admissible := check_admissible_sound hCheck
namespace Admissible
/-- 合法实参列表组成合法关系原子。 -/
theorem rel {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {relation : σ.RelSymbol} {arguments : List (Term σ)} (hArguments :
      ArgsAdmissible arguments (σ.relDomain relation)) :
    Admissible (.rel relation arguments) :=
  ⟨.rel relation hArguments.1,
    .rel relation arguments hArguments.2⟩
/-- 两个同 sort 的 admissible 项组成 admissible 等式。 -/
theorem equal {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {sort : σ.SortSymbol} {left right : Term σ} (hLeft : Term.Admissible left sort) (hRight : Term.Admissible right sort) :
    Admissible (.equal left right) :=
  ⟨.equal hLeft.1 hRight.1, .equal hLeft.2 hRight.2⟩
/-- 关闭 free variable 并加入对应全称量词后得到 admissible 公式。 -/
theorem forall_closeFreeAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {formula : Formula σ} (target : σ.SortSymbol) (id : FreeVarId) (hFormula : Admissible formula) :
    Admissible (Formula.forallE target (Formula.closeFreeAt target id 0 formula)) := by
  constructor
  · exact .forallE target (FormulaWellFormed.wf_closeFreeAt target id 0 hFormula.1)
  · exact .forallE target <| by
      simpa [Scope.empty] using
        FormulaScoped.sc_closeFreeAt hFormula.2 (Nat.zero_le 0)
/-- 关闭 free variable 并加入对应存在量词后得到 admissible 公式。 -/
theorem exists_closeFreeAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {formula : Formula σ} (target : σ.SortSymbol) (id : FreeVarId) (hFormula : Admissible formula) :
    Admissible (Formula.existsE target (Formula.closeFreeAt target id 0 formula)) := by
  constructor
  · exact .existsE target (FormulaWellFormed.wf_closeFreeAt target id 0 hFormula.1)
  · exact .existsE target <| by
      simpa [Scope.empty] using
        FormulaScoped.sc_closeFreeAt hFormula.2 (Nat.zero_le 0)
/-- 全称消去实例化保持公式 admissibility。 -/
theorem forall_openAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {body : Formula σ} {term : Term σ} (target : σ.SortSymbol) (hFormula : Admissible (Formula.forallE target body))
    (hTerm : Term.Admissible term target) :
    Admissible (Formula.openAt target 0 term body) := by
  rcases hFormula with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | forallE _ hBodyWellFormed =>
      cases hScoped with
      | forallE _ hBodyScoped =>
          exact ⟨
            FormulaWellFormed.wf_openAt 0 hBodyWellFormed hTerm.1,
            FormulaScoped.sc_openAt hBodyScoped hTerm.2 (Nat.zero_le 0)⟩
/-- 存在引入实例化保持公式 admissibility。 -/
theorem exists_openAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {body : Formula σ} {term : Term σ} (target : σ.SortSymbol) (hFormula : Admissible (Formula.existsE target body))
    (hTerm : Term.Admissible term target) :
    Admissible (Formula.openAt target 0 term body) := by
  rcases hFormula with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | existsE _ hBodyWellFormed =>
      cases hScoped with
      | existsE _ hBodyScoped =>
          exact ⟨
            FormulaWellFormed.wf_openAt 0 hBodyWellFormed hTerm.1,
            FormulaScoped.sc_openAt hBodyScoped hTerm.2 (Nat.zero_le 0)⟩
/-- 等词替换所需的自由变量替换保持公式 admissibility。 -/
theorem substituteFree {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {formula : Formula σ} {replacement : Term σ} (target : σ.SortSymbol) (id : FreeVarId) (hFormula : Admissible formula)
    (hReplacement : Term.Admissible replacement target) :
    Admissible (Formula.substituteFree target id replacement formula) :=
  ⟨FormulaWellFormed.wf_substituteFree target id hFormula.1 hReplacement.1,
    FormulaScoped.sc_substituteFree hFormula.2 hReplacement.2⟩
/--
自由变量替换后 admissible 可反演出原公式 admissible。
这条接口与 `substituteFree` 的正向保持配对，尤其用于从闭项实例恢复等词或关系
模板的合法性。
-/
theorem substituteFree_source {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {formula : Formula σ}
    {replacement : Term σ} (target : σ.SortSymbol) (id : FreeVarId) (hReplacement : Term.Admissible replacement target) (hSubstituted :
      Admissible (Formula.substituteFree target id replacement formula)) :
    Admissible formula :=
  ⟨FormulaWellFormed.substituteFree_source
      target id hReplacement.1 hSubstituted.1,
    FormulaScoped.substituteFree_source hSubstituted.2⟩
theorem neg {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ : Formula σ} (hφ : Admissible φ) : Admissible (.neg φ) :=
  ⟨.neg hφ.1, .neg hφ.2⟩
/-- admissible 否定式的内部公式仍然 admissible。 -/
theorem neg_body {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ : Formula σ} (hNeg : Admissible (.neg φ)) :
    Admissible φ := by
  rcases hNeg with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | neg hφ =>
      cases hScoped with
      | neg hφScoped =>
          exact ⟨hφ, hφScoped⟩
theorem conj {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hφ : Admissible φ) (hψ : Admissible ψ) :
    Admissible (.conj φ ψ) :=
  ⟨.conj hφ.1 hψ.1, .conj hφ.2 hψ.2⟩
/-- admissible 合取式的左侧公式仍然 admissible。 -/
theorem conj_left {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hConj : Admissible (.conj φ ψ)) :
    Admissible φ := by
  rcases hConj with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | conj hφ _ =>
      cases hScoped with
      | conj hφScoped _ =>
          exact ⟨hφ, hφScoped⟩
/-- admissible 合取式的右侧公式仍然 admissible。 -/
theorem conj_right {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hConj : Admissible (.conj φ ψ)) :
    Admissible ψ := by
  rcases hConj with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | conj _ hψ =>
      cases hScoped with
      | conj _ hψScoped =>
          exact ⟨hψ, hψScoped⟩
theorem disj {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hφ : Admissible φ) (hψ : Admissible ψ) :
    Admissible (.disj φ ψ) :=
  ⟨.disj hφ.1 hψ.1, .disj hφ.2 hψ.2⟩
/-- admissible 析取式的左侧公式仍然 admissible。 -/
theorem disj_left {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hDisj : Admissible (.disj φ ψ)) :
    Admissible φ := by
  rcases hDisj with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | disj hφ _ =>
      cases hScoped with
      | disj hφScoped _ =>
          exact ⟨hφ, hφScoped⟩
/-- admissible 析取式的右侧公式仍然 admissible。 -/
theorem disj_right {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hDisj : Admissible (.disj φ ψ)) :
    Admissible ψ := by
  rcases hDisj with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | disj _ hψ =>
      cases hScoped with
      | disj _ hψScoped =>
          exact ⟨hψ, hψScoped⟩
theorem imp {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hφ : Admissible φ) (hψ : Admissible ψ) :
    Admissible (.imp φ ψ) :=
  ⟨.imp hφ.1 hψ.1, .imp hφ.2 hψ.2⟩
/-- admissible 蕴含式的前件仍然 admissible。 -/
theorem imp_left {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hImp : Admissible (.imp φ ψ)) :
    Admissible φ := by
  rcases hImp with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | imp hφ _ =>
      cases hScoped with
      | imp hφScoped _ =>
          exact ⟨hφ, hφScoped⟩
/-- admissible 蕴含式的后件仍然 admissible。 -/
theorem imp_right {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hImp : Admissible (.imp φ ψ)) :
    Admissible ψ := by
  rcases hImp with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | imp _ hψ =>
      cases hScoped with
      | imp _ hψScoped =>
          exact ⟨hψ, hψScoped⟩
theorem iff {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hφ : Admissible φ) (hψ : Admissible ψ) :
    Admissible (.iff φ ψ) :=
  ⟨.iff hφ.1 hψ.1, .iff hφ.2 hψ.2⟩
/-- admissible 双条件的左侧公式仍然 admissible。 -/
theorem iff_left {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hIff : Admissible (.iff φ ψ)) :
    Admissible φ := by
  rcases hIff with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | iff hφ _ =>
      cases hScoped with
      | iff hφScoped _ =>
          exact ⟨hφ, hφScoped⟩
/-- admissible 双条件的右侧公式仍然 admissible。 -/
theorem iff_right {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Formula σ} (hIff : Admissible (.iff φ ψ)) :
    Admissible ψ := by
  rcases hIff with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | iff _ hψ =>
      cases hScoped with
      | iff _ hψScoped =>
          exact ⟨hψ, hψScoped⟩
theorem falsum {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] :
    Admissible (Formula.falsum : Formula σ) :=
  ⟨.falsum, .falsum⟩
theorem truth {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] :
    Admissible (Formula.truth : Formula σ) :=
  ⟨.truth, .truth⟩
end Admissible
namespace CheckCertificate
/-- 两个同 sort 的项证书组成等式公式证书。 -/
theorem equal
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {sort : σ.SortSymbol} {left right : Term σ}
    (hLeft : Term.CheckCertificate left sort)
    (hRight : Term.CheckCertificate right sort) :
    CheckCertificate (.equal left right) :=
  check_admissible_complete <|
    Formula.Admissible.equal hLeft.admissible hRight.admissible
/-- 否定保持公式计算证书。 -/
theorem neg
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ}
    (hFormula : CheckCertificate formula) :
    CheckCertificate (.neg formula) :=
  check_admissible_complete <|
    Formula.Admissible.neg hFormula.admissible
/-- 合取保持公式计算证书。 -/
theorem conj
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : Formula σ}
    (hLeft : CheckCertificate left)
    (hRight : CheckCertificate right) :
    CheckCertificate (.conj left right) :=
  check_admissible_complete <|
    Formula.Admissible.conj hLeft.admissible hRight.admissible
/-- 两个同 sort 等式的合取可直接由四个项边界计算。 -/
theorem conj_equal_of_admissible
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {sort : σ.SortSymbol}
    {left₁ right₁ left₂ right₂ : Term σ}
    (hLeft₁ : Term.Admissible left₁ sort)
    (hRight₁ : Term.Admissible right₁ sort)
    (hLeft₂ : Term.Admissible left₂ sort)
    (hRight₂ : Term.Admissible right₂ sort) :
    CheckCertificate
      (.conj (.equal left₁ right₁) (.equal left₂ right₂)) :=
  check_admissible_complete <|
    Formula.Admissible.conj
      (Formula.Admissible.equal hLeft₁ hRight₁)
      (Formula.Admissible.equal hLeft₂ hRight₂)
/-- 析取保持公式计算证书。 -/
theorem disj
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : Formula σ}
    (hLeft : CheckCertificate left)
    (hRight : CheckCertificate right) :
    CheckCertificate (.disj left right) :=
  check_admissible_complete <|
    Formula.Admissible.disj hLeft.admissible hRight.admissible
/-- 蕴含保持公式计算证书。 -/
theorem imp
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {antecedent consequent : Formula σ}
    (hAntecedent : CheckCertificate antecedent)
    (hConsequent : CheckCertificate consequent) :
    CheckCertificate (.imp antecedent consequent) :=
  check_admissible_complete <|
    Formula.Admissible.imp
      hAntecedent.admissible hConsequent.admissible
/-- 双条件保持公式计算证书。 -/
theorem iff
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : Formula σ}
    (hLeft : CheckCertificate left)
    (hRight : CheckCertificate right) :
    CheckCertificate (.iff left right) :=
  check_admissible_complete <|
    Formula.Admissible.iff hLeft.admissible hRight.admissible
end CheckCertificate
namespace AdmissibleAt
/-- scope 逐 sort 扩大时，proof-carrying 公式证书保持成立。 -/
theorem mono {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {small large : Scope σ}
    {formula : Formula σ} (hFormula : AdmissibleAt small formula)
    (hScope : ∀ current, small current ≤ large current) :
    AdmissibleAt large formula :=
  ⟨hFormula.1, Formula.scoped_mono hFormula.2 hScope⟩
/-- 向 scope 压入一个 binder 后，已有公式证书可直接复用。 -/
theorem push {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {formula : Formula σ} (sort : σ.SortSymbol)
    (hFormula : AdmissibleAt scope formula) :
    AdmissibleAt (Scope.push scope sort) formula :=
  mono hFormula <| by
    intro current
    by_cases hCurrent : current = sort
    · subst current
      simp [Scope.push]
    · simp [Scope.push, hCurrent]
/-- 深度零处关闭自由变量，同时把对应 binder 压入 scope。 -/
theorem closeFreeAt_zero {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {formula : Formula σ} (target : σ.SortSymbol) (id : FreeVarId)
    (hFormula : AdmissibleAt scope formula) :
    AdmissibleAt (Scope.push scope target)
      (Formula.closeFreeAt target id 0 formula) :=
  ⟨FormulaWellFormed.wf_closeFreeAt target id 0 hFormula.1,
    FormulaScoped.sc_closeFreeAt hFormula.2 (Nat.zero_le _)⟩
/-- 闭公式可提升到任意更大的 bound scope。 -/
theorem of_admissible {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {formula : Formula σ} (hFormula : Admissible formula) :
    AdmissibleAt scope formula :=
  ⟨hFormula.1,
    Formula.scoped_mono hFormula.2 (fun _ => Nat.zero_le _)⟩
/-- 同 scope 下的 proof-carrying 实参构成关系原子。 -/
theorem rel {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {relation : σ.RelSymbol} {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissibleAt scope arguments (σ.relDomain relation)) :
    AdmissibleAt scope (.rel relation arguments) :=
  ⟨.rel relation hArguments.1,
    .rel relation arguments hArguments.2⟩
/-- 同 scope 下两个同 sort 项构成等式。 -/
theorem equal {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {sort : σ.SortSymbol} {left right : Term σ}
    (hLeft : Term.AdmissibleAt scope left sort)
    (hRight : Term.AdmissibleAt scope right sort) :
    AdmissibleAt scope (.equal left right) :=
  ⟨.equal hLeft.1 hRight.1, .equal hLeft.2 hRight.2⟩
theorem neg {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {formula : Formula σ} (hFormula : AdmissibleAt scope formula) :
    AdmissibleAt scope (.neg formula) :=
  ⟨.neg hFormula.1, .neg hFormula.2⟩
theorem conj {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {left right : Formula σ} (hLeft : AdmissibleAt scope left)
    (hRight : AdmissibleAt scope right) :
    AdmissibleAt scope (.conj left right) :=
  ⟨.conj hLeft.1 hRight.1, .conj hLeft.2 hRight.2⟩
theorem disj {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {left right : Formula σ} (hLeft : AdmissibleAt scope left)
    (hRight : AdmissibleAt scope right) :
    AdmissibleAt scope (.disj left right) :=
  ⟨.disj hLeft.1 hRight.1, .disj hLeft.2 hRight.2⟩
theorem imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {left right : Formula σ} (hLeft : AdmissibleAt scope left)
    (hRight : AdmissibleAt scope right) :
    AdmissibleAt scope (.imp left right) :=
  ⟨.imp hLeft.1 hRight.1, .imp hLeft.2 hRight.2⟩
theorem iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    {left right : Formula σ} (hLeft : AdmissibleAt scope left)
    (hRight : AdmissibleAt scope right) :
    AdmissibleAt scope (.iff left right) :=
  ⟨.iff hLeft.1 hRight.1, .iff hLeft.2 hRight.2⟩
theorem forallE {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    (sort : σ.SortSymbol) {body : Formula σ}
    (hBody : AdmissibleAt (Scope.push scope sort) body) :
    AdmissibleAt scope (.forallE sort body) :=
  ⟨.forallE sort hBody.1, .forallE sort hBody.2⟩
theorem existsE {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ}
    (sort : σ.SortSymbol) {body : Formula σ}
    (hBody : AdmissibleAt (Scope.push scope sort) body) :
    AdmissibleAt scope (.existsE sort body) :=
  ⟨.existsE sort hBody.1, .existsE sort hBody.2⟩
theorem falsum {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ} :
    AdmissibleAt scope (Formula.falsum : Formula σ) :=
  ⟨.falsum, .falsum⟩
theorem truth {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {scope : Scope σ} :
    AdmissibleAt scope (Formula.truth : Formula σ) :=
  ⟨.truth, .truth⟩
end AdmissibleAt
/-- 在当前 scope 下递归构造公式、项与实参列表的 proof-carrying 证书。 -/
macro "prove_admissible_at" : tactic =>
  `(tactic|
    repeat'
      first
      | assumption
      | exact Formula.AdmissibleAt.of_admissible (by assumption)
      | exact Term.AdmissibleAt.of_admissible (by assumption)
      | exact Formula.AdmissibleAt.push _ (by assumption)
      | exact Term.AdmissibleAt.push _ (by assumption)
      | apply Formula.AdmissibleAt.closeFreeAt_zero
      | apply Term.AdmissibleAt.closeFreeAt_zero
      | exact Formula.AdmissibleAt.falsum
      | exact Formula.AdmissibleAt.truth
      | apply Formula.AdmissibleAt.neg
      | apply Formula.AdmissibleAt.conj
      | apply Formula.AdmissibleAt.disj
      | apply Formula.AdmissibleAt.imp
      | apply Formula.AdmissibleAt.iff
      | apply Formula.AdmissibleAt.forallE
      | apply Formula.AdmissibleAt.existsE
      | apply Formula.AdmissibleAt.rel
      | apply Formula.AdmissibleAt.equal
      | exact ArgsAdmissibleAt.nil
      | apply ArgsAdmissibleAt.cons
      | apply ArgsAdmissibleAt.closeFreeAt_zero
      | exact Term.AdmissibleAt.fvar _ _
      | apply Term.AdmissibleAt.bvar <;>
          simp [Scope.push, Scope.empty]
      | apply Term.AdmissibleAt.app)
/--
递归构造闭公式的 proof-carrying admissibility 证书。
量词分支自动维护 bound scope；原子分支直接消费签名中的 arity/sort 数据。
-/
macro "prove_admissible" : tactic =>
  `(tactic|
    change Formula.AdmissibleAt Scope.empty _ <;>
      prove_admissible_at)
/-- 递归构造闭项的 proof-carrying admissibility 证书。 -/
macro "prove_term_admissible" : tactic =>
  `(tactic|
    change Term.AdmissibleAt Scope.empty _ _ <;>
      prove_admissible_at)
end Formula
namespace Context
/-- 有限上下文的每个公式都满足证明层良构性边界。 -/
def Admissible {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (context : Context σ) : Prop :=
  ∀ formula, formula ∈ context → Formula.Admissible formula
theorem admissible_nil {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] :
    Admissible ([] : Context σ) := by
  intro formula hFormula
  cases hFormula
theorem admissible_cons {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {context : Context σ} (hFormula : Formula.Admissible formula) (hContext : Admissible context) :
    Admissible (formula :: context) := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hFormula
  · exact hContext ψ hψ
/-- 大上下文 admissible 时，其任意子上下文同样 admissible。 -/
theorem admissible_of_subset {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {small large : Context σ} (hSubset : ∀ formula, formula ∈ small → formula ∈ large) (hLarge : Admissible large) :
    Admissible small := by
  intro formula hFormula
  exact hLarge formula (hSubset formula hFormula)
end Context
namespace Theory
/-- 理论谓词的每个成员都满足证明层良构性边界。 -/
def Admissible {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (theory : Theory σ) : Prop :=
  ∀ formula, theory formula → Formula.Admissible formula
theorem admissible_insert {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ : Formula σ} {T : Theory σ} (hφ : Formula.Admissible φ) (hT : Admissible T) :
    Admissible (insert φ T) := by
  intro formula hFormula
  rcases hFormula with rfl | hFormula
  · exact hφ
  · exact hT formula hFormula
theorem admissible_ofList {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {formulas : List (Formula σ)} (hFormulas : ∀ formula, formula ∈ formulas → Formula.Admissible formula) :
    Admissible (fun formula => formula ∈ formulas) := by
  intro formula hFormula
  exact hFormulas formula hFormula
/-- 大理论 admissible 时，其任意子理论同样 admissible。 -/
theorem admissible_of_subset {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {small large : Theory σ} (hSubset : ∀ formula, small formula → large formula) (hLarge : Admissible large) :
    Admissible small := by
  intro formula hFormula
  exact hLarge formula (hSubset formula hFormula)
end Theory
end FirstOrder
end Logic
end YesMetaZFC
