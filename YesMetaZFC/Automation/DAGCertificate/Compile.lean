import YesMetaZFC.Automation.DAGCertificate.Syntax
import YesMetaZFC.Automation.LogicSoundness

/-!
# 原始证书语法到内在语法的检查编译

编译器以 `Option` 表达拒绝；成功分支直接返回排序与作用域均由类型保证的 AST。
因此下游只消费编译结果，不再重复携带良构、闭合或变量索引合法性证明。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace Compile

open _root_.YesMetaZFC.Logic

universe x

variable {σ : Signature}

/-- 一个排序未知、但已内在类型化的项。 -/
structure SomeTerm (σ : Signature)
    (bound free : Logic.FirstOrder.SortContext σ) where
  sort : σ.SortSymbol
  term : Logic.FirstOrder.Term σ bound free sort

/-- 自由变量的稳定证书编号表。 -/
structure FreeRegistry (σ : Signature) where
  entries : List (σ.SortSymbol × Nat) := []

namespace FreeRegistry

def context (registry : FreeRegistry σ) :
    Logic.FirstOrder.SortContext σ :=
  registry.entries.map Prod.fst

def empty : FreeRegistry σ := {}

def insert [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (entry : σ.SortSymbol × Nat) :
    FreeRegistry σ :=
  if registry.entries.contains entry then registry
  else { entries := entry :: registry.entries }

def ofSupport [DecidableEq σ.SortSymbol]
    (support : List (σ.SortSymbol × Nat)) : FreeRegistry σ :=
  support.foldl insert empty

def ofClauses [DecidableEq σ.SortSymbol]
    (clauses : List (Clause σ)) : FreeRegistry σ :=
  ofSupport (clauses.flatMap Clause.freeSupport)

def findEntries? [DecidableEq σ.SortSymbol] :
    (entries : List (σ.SortSymbol × Nat)) →
    (sort : σ.SortSymbol) → Nat →
      Option (Logic.FirstOrder.Variable (entries.map Prod.fst) sort)
  | [], _, _ => none
  | (headSort, headId) :: tail, sort, id =>
      if hSort : headSort = sort then
        if _hId : headId = id then
          by
            subst sort
            exact some .here
        else
          (findEntries? tail sort id).map .there
      else
        (findEntries? tail sort id).map .there

def find? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (sort : σ.SortSymbol) (id : Nat) :
    Option (Logic.FirstOrder.Variable registry.context sort) :=
  findEntries? registry.entries sort id

/-- 按 registry 的稳定编号生成 typed assignment。 -/
private def assignmentIn
    {Carrier : σ.SortSymbol → Type x}
    (values : ∀ sort, Nat → Carrier sort) :
    (entries : List (σ.SortSymbol × Nat)) →
      {sort : σ.SortSymbol} →
        Logic.FirstOrder.Variable (entries.map Prod.fst) sort → Carrier sort
  | [], _, entry => nomatch entry
  | (headSort, headId) :: _, _, .here => values headSort headId
  | _ :: tail, _, .there previous => assignmentIn values tail previous

def assignment
    {Carrier : σ.SortSymbol → Type x}
    (registry : FreeRegistry σ)
    (values : ∀ sort, Nat → Carrier sort) :
    {sort : σ.SortSymbol} →
      Logic.FirstOrder.Variable registry.context sort → Carrier sort :=
  assignmentIn values registry.entries

private theorem assignmentIn_findEntries?
    [DecidableEq σ.SortSymbol]
    {Carrier : σ.SortSymbol → Type x}
    (values : ∀ sort, Nat → Carrier sort) :
    ∀ entries {sort id entry},
      findEntries? entries sort id = some entry →
        assignmentIn values entries entry = values sort id := by
  intro entries
  induction entries with
  | nil =>
      intro sort id entry hFind
      simp [findEntries?] at hFind
  | cons head tail ih =>
      rcases head with ⟨headSort, headId⟩
      intro sort id entry hFind
      simp only [findEntries?] at hFind
      split at hFind
      · subst sort
        split at hFind
        · subst id
          simp at hFind
          subst entry
          rfl
        · cases hTail : findEntries? tail headSort id with
          | none => simp [hTail] at hFind
          | some previous =>
              simp [hTail] at hFind
              subst entry
              simpa [assignmentIn] using ih hTail
      · cases hTail : findEntries? tail sort id with
        | none => simp [hTail] at hFind
        | some previous =>
            simp [hTail] at hFind
            subst entry
            simpa [assignmentIn] using ih hTail

/-- `find?` 与 registry assignment 的稳定编号语义一致。 -/
theorem assignment_find?
    [DecidableEq σ.SortSymbol]
    {Carrier : σ.SortSymbol → Type x}
    (registry : FreeRegistry σ)
    (values : ∀ sort, Nat → Carrier sort)
    {sort : σ.SortSymbol} {id : Nat}
    {entry : Logic.FirstOrder.Variable registry.context sort}
    (hFind : registry.find? sort id = some entry) :
    registry.assignment values entry = values sort id :=
  assignmentIn_findEntries? values registry.entries hFind

/-- 插入保持旧成员，并把新成员纳入 registry。 -/
@[simp] theorem mem_entries_insert_iff
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (inserted target : σ.SortSymbol × Nat) :
    target ∈ (registry.insert inserted).entries ↔
      target = inserted ∨ target ∈ registry.entries := by
  unfold insert
  split <;> simp_all

/-- `foldl insert` 的成员恰是输入支持集与初始 registry 成员之并。 -/
theorem mem_entries_foldl_insert_iff
    [DecidableEq σ.SortSymbol]
    (support : List (σ.SortSymbol × Nat))
    (registry : FreeRegistry σ) (target : σ.SortSymbol × Nat) :
    target ∈ (support.foldl insert registry).entries ↔
      target ∈ support ∨ target ∈ registry.entries := by
  induction support generalizing registry with
  | nil => simp
  | cons head tail ih =>
      simp [List.foldl, ih, or_assoc, or_left_comm]

/-- `ofSupport` 不丢失支持集中的任何变量。 -/
theorem mem_entries_of_mem_support
    [DecidableEq σ.SortSymbol]
    {support : List (σ.SortSymbol × Nat)} {target : σ.SortSymbol × Nat}
    (hTarget : target ∈ support) :
    target ∈ (ofSupport support).entries := by
  simpa [ofSupport, empty, mem_entries_foldl_insert_iff] using hTarget

/-- registry 列表成员总能取得对应的内在变量索引。 -/
theorem findEntries?_exists_of_mem
    [DecidableEq σ.SortSymbol] :
    ∀ {entries : List (σ.SortSymbol × Nat)} {sort : σ.SortSymbol} {id : Nat},
      (sort, id) ∈ entries →
        ∃ entry, findEntries? entries sort id = some entry
  | [], sort, id, hMem => by simp at hMem
  | (headSort, headId) :: tail, sort, id, hMem => by
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      rcases hMem with hHead | hTail
      · rcases hHead with ⟨rfl, rfl⟩
        exact ⟨.here, by simp [findEntries?]⟩
      · rcases findEntries?_exists_of_mem hTail with ⟨entry, hFind⟩
        by_cases hSort : headSort = sort
        · subst headSort
          by_cases hId : headId = id
          · subst headId
            exact ⟨.here, by simp [findEntries?]⟩
          · exact ⟨.there entry, by simp [findEntries?, hId, hFind]⟩
        · exact ⟨.there entry, by simp [findEntries?, hSort, hFind]⟩

/-- registry 成员总能经稳定查找取得 typed 变量。 -/
theorem find?_exists_of_mem_entries
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) {sort : σ.SortSymbol} {id : Nat}
    (hMem : (sort, id) ∈ registry.entries) :
    ∃ entry, registry.find? sort id = some entry :=
  findEntries?_exists_of_mem hMem

end FreeRegistry

/-- bound 上下文中的带排序索引查找。 -/
def boundVariable? [DecidableEq σ.SortSymbol] :
    (bound : Logic.FirstOrder.SortContext σ) →
    (sort : σ.SortSymbol) → Nat →
      Option (Logic.FirstOrder.Variable bound sort)
  | [], _, _ => none
  | headSort :: _, sort, 0 =>
      if h : headSort = sort then
        h ▸ some Logic.FirstOrder.Variable.here
      else
        none
  | headSort :: tail, sort, index + 1 =>
      (boundVariable? tail sort index).map
        (Logic.FirstOrder.Variable.there (t := headSort))

/-- raw bound 查找成功时，内在索引查找必成功。 -/
theorem boundVariable?_exists_of_lookupBound?
    [DecidableEq σ.SortSymbol] :
    ∀ {bound : Logic.FirstOrder.SortContext σ} {sort : σ.SortSymbol}
      {index : Nat},
      Term.lookupBound? bound index = some sort →
        ∃ entry, boundVariable? bound sort index = some entry
  | [], sort, index, hLookup => by
      simp [Term.lookupBound?] at hLookup
  | headSort :: tail, sort, 0, hLookup => by
      simp [Term.lookupBound?] at hLookup
      subst sort
      exact ⟨.here, by simp [boundVariable?]⟩
  | headSort :: tail, sort, index + 1, hLookup => by
      change Term.lookupBound? tail index = some sort at hLookup
      rcases boundVariable?_exists_of_lookupBound? hLookup with
        ⟨entry, hEntry⟩
      exact ⟨.there entry, by simp [boundVariable?, hEntry]⟩
  termination_by bound sort index _ => index

mutual

def term? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ) :
    Term σ → Option (SomeTerm σ bound registry.context)
  | .var (.bvar sort index) => do
      let entry ← boundVariable? bound sort index
      pure ⟨sort, .bvar entry⟩
  | .var (.fvar sort id) => do
      let entry ← registry.find? sort id
      pure ⟨sort, .fvar entry⟩
  | .app function arguments => do
      let compiled ← arguments? registry bound
        (σ.funcDomain function) arguments
      pure ⟨σ.funcCodomain function, .app function compiled⟩
  termination_by term => term.weight
  decreasing_by
    simp [Term.weight]

def arguments? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ) :
    (sorts : List σ.SortSymbol) → List (Term σ) →
      Option (Logic.FirstOrder.Arguments σ bound registry.context sorts)
  | [], [] => some .nil
  | sort :: sorts, term :: terms => do
      let compiledTerm ← term? registry bound term
      let compiledTerms ← arguments? registry bound sorts terms
      if h : compiledTerm.sort = sort then
        pure (.cons (h ▸ compiledTerm.term) compiledTerms)
      else
        none
  | _, _ => none
  termination_by _ terms => Term.weightList terms
  decreasing_by
    all_goals simp [Term.weightList] <;> omega

end

/-- bound 变量编译方程。 -/
@[simp] theorem term?_bvar [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ)
    (sort : σ.SortSymbol) (index : Nat) :
    term? registry bound (.var (.bvar sort index)) = (do
      let entry ← boundVariable? bound sort index
      pure ⟨sort, .bvar entry⟩) := by
  unfold term?
  rfl

/-- free 变量编译方程。 -/
@[simp] theorem term?_fvar [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ)
    (sort : σ.SortSymbol) (id : Nat) :
    term? registry bound (.var (.fvar sort id)) = (do
      let entry ← registry.find? sort id
      pure ⟨sort, .fvar entry⟩) := by
  unfold term?
  rfl

/-- 函数应用编译方程。 -/
@[simp] theorem term?_app [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ)
    (function : σ.FuncSymbol) (arguments : List (Term σ)) :
    term? registry bound (.app function arguments) = (do
      let compiled ← arguments? registry bound
        (σ.funcDomain function) arguments
      pure ⟨σ.funcCodomain function, .app function compiled⟩) := by
  unfold term?
  rfl

/-- 空参数列是零元符号编译的公共快路径。 -/
@[simp] theorem arguments?_nil [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ) :
    arguments? registry bound [] [] = some .nil := by
  unfold arguments?
  rfl

/-- 非空排序列表不能编译空参数列。 -/
@[simp] theorem arguments?_cons_nil [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ)
    (sort : σ.SortSymbol) (sorts : List σ.SortSymbol) :
    arguments? registry bound (sort :: sorts) [] = none := by
  unfold arguments?
  rfl

/-- 空排序列表不能编译非空参数列。 -/
@[simp] theorem arguments?_nil_cons [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ)
    (term : Term σ) (terms : List (Term σ)) :
    arguments? registry bound [] (term :: terms) = none := by
  unfold arguments?
  rfl

/-- 非空参数列编译方程。 -/
@[simp] theorem arguments?_cons [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ)
    (sort : σ.SortSymbol) (sorts : List σ.SortSymbol)
    (term : Term σ) (terms : List (Term σ)) :
    arguments? registry bound (sort :: sorts) (term :: terms) = (do
      let compiledTerm ← term? registry bound term
      let compiledTerms ← arguments? registry bound sorts terms
      if h : compiledTerm.sort = sort then
        pure (.cons (h ▸ compiledTerm.term) compiledTerms)
      else
        none) := by
  conv =>
    lhs
    unfold arguments?

mutual

/-- raw 排序推断与自由支持集覆盖共同保证 typed 项编译成功。 -/
theorem term?_exists_of_inferSortWith
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ) :
    ∀ (raw : Term σ) (sort : σ.SortSymbol),
      Term.inferSortWith bound raw = some sort →
      (∀ entry, entry ∈ raw.freeSupport → entry ∈ registry.entries) →
        ∃ term : Logic.FirstOrder.Term σ bound registry.context sort,
          term? registry bound raw = some ⟨sort, term⟩
  | .var (.bvar rawSort index), sort, hInfer, _hSupport => by
      simp only [Term.inferSortWith] at hInfer
      split at hInfer
      · rename_i hLookup
        have hSort : rawSort = sort := Option.some.inj hInfer
        subst sort
        rcases boundVariable?_exists_of_lookupBound? hLookup with
          ⟨entry, hEntry⟩
        exact ⟨.bvar entry, by simp [hEntry]⟩
      · simp at hInfer
  | .var (.fvar rawSort id), sort, hInfer, hSupport => by
      have hSort : rawSort = sort := by
        simpa [Term.inferSortWith] using Option.some.inj hInfer
      subst sort
      have hMem : (rawSort, id) ∈ registry.entries :=
        hSupport (rawSort, id) (by simp [Term.freeSupport])
      rcases registry.find?_exists_of_mem_entries hMem with
        ⟨entry, hFind⟩
      exact ⟨.fvar entry, by simp [hFind]⟩
  | .app function arguments, sort, hInfer, hSupport => by
      cases hArguments : Term.inferSortListWith bound arguments with
      | none =>
          simp [Term.inferSortWith, hArguments] at hInfer
      | some argumentSorts =>
          by_cases hDomain : argumentSorts = σ.funcDomain function
          · have hSort : σ.funcCodomain function = sort := by
              simpa [Term.inferSortWith, hArguments, hDomain] using hInfer
            subst sort
            have hArgumentsDomain :
                Term.inferSortListWith bound arguments =
                  some (σ.funcDomain function) := by
              simpa [hDomain] using hArguments
            rcases arguments?_exists_of_inferSortListWith registry bound
                arguments (σ.funcDomain function) hArgumentsDomain
                (by simpa [Term.freeSupport] using hSupport) with
              ⟨compiledArguments, hCompile⟩
            exact ⟨.app function compiledArguments, by simp [hCompile]⟩
          · simp [Term.inferSortWith, hArguments, hDomain] at hInfer
  termination_by raw sort _ _ => raw.weight
  decreasing_by
    simp [Term.weight]

/-- raw 参数列排序推断与支持集覆盖共同保证 typed 参数编译成功。 -/
theorem arguments?_exists_of_inferSortListWith
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (bound : Logic.FirstOrder.SortContext σ) :
    ∀ (raw : List (Term σ)) (sorts : List σ.SortSymbol),
      Term.inferSortListWith bound raw = some sorts →
      (∀ entry, entry ∈ raw.flatMap Term.freeSupport →
        entry ∈ registry.entries) →
        ∃ arguments : Logic.FirstOrder.Arguments σ bound
            registry.context sorts,
          arguments? registry bound sorts raw = some arguments
  | [], sorts, hInfer, _hSupport => by
      simp [Term.inferSortListWith] at hInfer
      subst sorts
      exact ⟨.nil, by simp⟩
  | head :: tail, sorts, hInfer, hSupport => by
      cases hHead : Term.inferSortWith bound head with
      | none =>
          simp [Term.inferSortListWith, hHead] at hInfer
      | some headSort =>
          cases hTail : Term.inferSortListWith bound tail with
          | none =>
              simp [Term.inferSortListWith, hHead, hTail] at hInfer
          | some tailSorts =>
              have hSorts : headSort :: tailSorts = sorts := by
                simpa [Term.inferSortListWith, hHead, hTail] using hInfer
              subst sorts
              rcases term?_exists_of_inferSortWith registry bound
                  head headSort hHead
                  (by
                    intro entry hEntry
                    apply hSupport entry
                    simp [hEntry]) with
                ⟨compiledHead, hCompileHead⟩
              rcases arguments?_exists_of_inferSortListWith registry bound
                  tail tailSorts hTail
                  (by
                    intro entry hEntry
                    apply hSupport entry
                    simp [hEntry]) with
                ⟨compiledTail, hCompileTail⟩
              exact ⟨.cons compiledHead compiledTail, by
                simp [hCompileHead, hCompileTail]⟩
  termination_by raw sorts _ _ => Term.weightList raw
  decreasing_by
    all_goals simp [Term.weightList]
    all_goals omega

end

def formula? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    (bound : Logic.FirstOrder.SortContext σ) →
    Formula σ →
      Option (Logic.FirstOrder.Formula σ bound registry.context)
  | _, .falsum => some .falsum
  | _, .truth => some .truth
  | bound, .rel relation arguments => do
      let compiled ← arguments? registry bound
        (σ.relDomain relation) arguments
      pure (.rel relation compiled)
  | bound, .equal left right => do
      let compiledLeft ← term? registry bound left
      let compiledRight ← term? registry bound right
      if h : compiledLeft.sort = compiledRight.sort then
        pure (.equal (h ▸ compiledLeft.term) compiledRight.term)
      else
        none
  | bound, .neg body =>
      Logic.FirstOrder.Formula.neg <$> formula? registry bound body
  | bound, .conj left right => do
      let compiledLeft ← formula? registry bound left
      let compiledRight ← formula? registry bound right
      pure (.conj compiledLeft compiledRight)
  | bound, .disj left right => do
      let compiledLeft ← formula? registry bound left
      let compiledRight ← formula? registry bound right
      pure (.disj compiledLeft compiledRight)
  | bound, .imp left right => do
      let compiledLeft ← formula? registry bound left
      let compiledRight ← formula? registry bound right
      pure (.imp compiledLeft compiledRight)
  | bound, .iff left right => do
      let compiledLeft ← formula? registry bound left
      let compiledRight ← formula? registry bound right
      pure (.iff compiledLeft compiledRight)
  | bound, .forallE sort body => do
      let compiled ← formula? registry (sort :: bound) body
      pure (.forallE sort compiled)
  | bound, .existsE sort body => do
      let compiled ← formula? registry (sort :: bound) body
      pure (.existsE sort compiled)

def sentence? [DecidableEq σ.SortSymbol]
    (formula : Formula σ) : Option (Logic.FirstOrder.Sentence σ) :=
  formula? FreeRegistry.empty [] formula

def sentenceList? [DecidableEq σ.SortSymbol] :
    List (Formula σ) → Option (List (Logic.FirstOrder.Sentence σ))
  | [] => some []
  | formula :: rest => do
      let compiled ← sentence? formula
      let compiledRest ← sentenceList? rest
      pure (compiled :: compiledRest)

/-- 原始公式问题的唯一内在闭句编译结果。 -/
def compileProblem? [DecidableEq σ.SortSymbol]
    (raw : Problem σ) : Option (LogicSoundness.DeepProblem σ) := do
  let premises ← sentenceList? raw.premises
  let target ← sentence? raw.target
  pure { premises := premises, target := target }

/-- 成功后只暴露内在闭句问题及其编译等式；构造子不对外开放。 -/
structure CheckedProblem [DecidableEq σ.SortSymbol]
    (raw : Problem σ) where
  private mkInternal ::
  problem : LogicSoundness.DeepProblem σ
  compiled : compileProblem? raw = some problem

namespace CheckedProblem

def compile? [DecidableEq σ.SortSymbol]
    (raw : Problem σ) : Option (CheckedProblem raw) :=
  match hCompile : compileProblem? raw with
  | none => none
  | some problem => some ⟨problem, hCompile⟩

/-- 已知精确编译结果时直接建立 checked 边界，不重复运行编译器。 -/
def of_compilation [DecidableEq σ.SortSymbol]
    {raw : Problem σ} {problem : LogicSoundness.DeepProblem σ}
    (hCompile : compileProblem? raw = some problem) :
    CheckedProblem raw :=
  ⟨problem, hCompile⟩

@[simp] theorem of_compilation_problem [DecidableEq σ.SortSymbol]
    {raw : Problem σ} {problem : LogicSoundness.DeepProblem σ}
    (hCompile : compileProblem? raw = some problem) :
    (of_compilation hCompile).problem = problem :=
  rfl

/-- 同一个原始问题的 checked 编译结果由编译等式唯一确定。 -/
theorem problem_eq_of_compilation [DecidableEq σ.SortSymbol]
    {raw : Problem σ} (checked : CheckedProblem raw)
    {problem : LogicSoundness.DeepProblem σ}
    (hCompile : compileProblem? raw = some problem) :
    checked.problem = problem := by
  exact Option.some.inj (checked.compiled.symm.trans hCompile)

def check [DecidableEq σ.SortSymbol] (raw : Problem σ) : Bool :=
  (compile? raw).isSome

def of_check [DecidableEq σ.SortSymbol]
    {raw : Problem σ} (h : check raw = true) : CheckedProblem raw := by
  unfold check at h
  cases hCompile : compile? raw with
  | none => simp [hCompile] at h
  | some compiled => exact compiled

end CheckedProblem

/-- 以注册表上下文编译一个原始字句。 -/
def clauseFormula? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (clause : Clause σ) :
    Option (Logic.FirstOrder.OpenFormula σ registry.context) :=
  formula? registry [] clause.toFormula

/-- 逐层量化 free 上下文，得到闭句。 -/
def forallFree :
    {free : Logic.FirstOrder.SortContext σ} →
    Logic.FirstOrder.OpenFormula σ free → Logic.FirstOrder.Sentence σ
  | [], formula => formula
  | sort :: _rest, formula =>
      forallFree (formula.forallFreeTop sort)

def clauseSentence? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (clause : Clause σ) :
    Option (Logic.FirstOrder.Sentence σ) := do
  let formula ← clauseFormula? registry clause
  pure (forallFree formula)

/-- 初始字句集编译后的统一 free 注册表与闭句列表。 -/
structure ClauseCompilation (σ : Signature) where
  registry : FreeRegistry σ
  clauses : List (Logic.FirstOrder.Sentence σ)

def compileClauses? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    List (Clause σ) → Option (List (Logic.FirstOrder.Sentence σ))
  | [] => some []
  | clause :: rest => do
      let compiled ← clauseSentence? registry clause
      let compiledRest ← compileClauses? registry rest
      pure (compiled :: compiledRest)

/-- 原始初始字句集的唯一内在闭句编译结果。 -/
def compileClauseProblem? [DecidableEq σ.SortSymbol]
    (raw : ClauseProblem σ) : Option (ClauseCompilation σ) := do
  let source := raw.initialClauses.toList
  let registry := FreeRegistry.ofClauses source
  let clauses ← compileClauses? registry source
  pure { registry := registry, clauses := clauses }

/-- 成功编译的初始字句集及其编译等式。 -/
structure CheckedClauseProblem [DecidableEq σ.SortSymbol]
    (raw : ClauseProblem σ) where
  private mkInternal ::
  compilation : ClauseCompilation σ
  compiled : compileClauseProblem? raw = some compilation

namespace CheckedClauseProblem

def registry [DecidableEq σ.SortSymbol]
    {raw : ClauseProblem σ} (checked : CheckedClauseProblem raw) :
    FreeRegistry σ :=
  checked.compilation.registry

def clauses [DecidableEq σ.SortSymbol]
    {raw : ClauseProblem σ} (checked : CheckedClauseProblem raw) :
    List (Logic.FirstOrder.Sentence σ) :=
  checked.compilation.clauses

def compile? [DecidableEq σ.SortSymbol]
    (raw : ClauseProblem σ) : Option (CheckedClauseProblem raw) :=
  match hCompile : compileClauseProblem? raw with
  | none => none
  | some compilation => some ⟨compilation, hCompile⟩

def of_compilation [DecidableEq σ.SortSymbol]
    {raw : ClauseProblem σ} {compilation : ClauseCompilation σ}
    (hCompile : compileClauseProblem? raw = some compilation) :
    CheckedClauseProblem raw :=
  ⟨compilation, hCompile⟩

theorem compilation_eq_of_compilation [DecidableEq σ.SortSymbol]
    {raw : ClauseProblem σ} (checked : CheckedClauseProblem raw)
    {compilation : ClauseCompilation σ}
    (hCompile : compileClauseProblem? raw = some compilation) :
    checked.compilation = compilation := by
  exact Option.some.inj (checked.compiled.symm.trans hCompile)

def check [DecidableEq σ.SortSymbol]
    (raw : ClauseProblem σ) : Bool :=
  (compile? raw).isSome

def of_check [DecidableEq σ.SortSymbol]
    {raw : ClauseProblem σ} (h : check raw = true) :
    CheckedClauseProblem raw := by
  unfold check at h
  cases hCompile : compile? raw with
  | none => simp [hCompile] at h
  | some compiled => exact compiled

end CheckedClauseProblem

end Compile
end DAGCertificate
end Automation
end YesMetaZFC
