import YesMetaZFC.Automation.DAGCertificate.CompileSupport
import YesMetaZFC.Automation.DAGCertificate.CompileSemantics

/-!
# DAG 字句的单 registry 内在编译

本层只编译初始字句与全部节点结论。每个结果携带原始字句和唯一编译等式，后续局部
规则 replay 直接消费 typed formula，不再重复展开 raw syntax 的良构检查。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace Compile

open _root_.YesMetaZFC.Logic

universe x

variable {σ : Signature}

/-- 固定 registry 下成功编译的单个开字句。 -/
structure CompiledClause [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) where
  raw : Clause σ
  formula : Logic.FirstOrder.OpenFormula σ registry.context
  compiled : clauseFormula? registry raw = some formula

namespace CompiledClause

/-- 把 free 上下文逐层关闭后的内在闭句。 -/
def sentence [DecidableEq σ.SortSymbol]
    {registry : FreeRegistry σ} (compiled : CompiledClause registry) :
    Logic.FirstOrder.Sentence σ :=
  forallFree compiled.formula

/-- 编译字句在指定结构中全称有效。 -/
def TrueIn [DecidableEq σ.SortSymbol]
    {registry : FreeRegistry σ}
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (compiled : CompiledClause registry) : Prop :=
  compiled.sentence.TrueIn M

/-- 同一 registry 下相同 raw 字句的内在公式唯一。 -/
theorem formula_eq_of_raw_eq [DecidableEq σ.SortSymbol]
    {registry : FreeRegistry σ} {left right : CompiledClause registry}
    (hRaw : left.raw = right.raw) : left.formula = right.formula := by
  rcases left with ⟨leftRaw, leftFormula, hLeft⟩
  rcases right with ⟨rightRaw, rightFormula, hRight⟩
  simp only at hRaw ⊢
  subst rightRaw
  exact Option.some.inj (hLeft.symm.trans hRight)

/-- raw 字句相等时全称有效性可零成本传输。 -/
theorem trueIn_iff_of_raw_eq [DecidableEq σ.SortSymbol]
    {registry : FreeRegistry σ}
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {left right : CompiledClause registry}
    (hRaw : left.raw = right.raw) :
    left.TrueIn M ↔ right.TrueIn M := by
  have hFormula := formula_eq_of_raw_eq hRaw
  simp [TrueIn, sentence, hFormula]

end CompiledClause

/-- 单字句 checked 编译。 -/
def compileClause? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (raw : Clause σ) :
    Option (CompiledClause registry) :=
  match hCompile : clauseFormula? registry raw with
  | none => none
  | some formula => some ⟨raw, formula, hCompile⟩

/-- 单字句编译结果保留原始字句。 -/
theorem compileClause?_raw [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) {raw : Clause σ}
    {compiled : CompiledClause registry}
    (hCompile : compileClause? registry raw = some compiled) :
    compiled.raw = raw := by
  unfold compileClause? at hCompile
  split at hCompile
  · simp at hCompile
  · simp at hCompile
    subst compiled
    rfl

/-- 保序编译字句列表。 -/
def compileClauseList? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    List (Clause σ) → Option (List (CompiledClause registry))
  | [] => some []
  | clause :: rest => do
      let compiled ← compileClause? registry clause
      let compiledRest ← compileClauseList? registry rest
      pure (compiled :: compiledRest)

/-- 保序编译字句数组。 -/
def compileClauseArray? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (clauses : Array (Clause σ)) :
    Option (Array (CompiledClause registry)) := do
  let compiled ← compileClauseList? registry clauses.toList
  pure compiled.toArray

/-- 成功列表编译保持原字句顺序。 -/
theorem compileClauseList?_raws [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    ∀ {raw compiled},
      compileClauseList? registry raw = some compiled →
        compiled.map CompiledClause.raw = raw
  | [], compiled, hCompile => by
      simp [compileClauseList?] at hCompile
      subst compiled
      rfl
  | clause :: rest, compiled, hCompile => by
      cases hClause : compileClause? registry clause with
      | none => simp [compileClauseList?, hClause] at hCompile
      | some compiledClause =>
          cases hRest : compileClauseList? registry rest with
          | none => simp [compileClauseList?, hClause, hRest] at hCompile
          | some compiledRest =>
              simp [compileClauseList?, hClause, hRest] at hCompile
              subst compiled
              have hHead : compiledClause.raw = clause :=
                compileClause?_raw registry hClause
              simp [hHead, compileClauseList?_raws registry hRest]

/-- 成功数组编译保持原字句顺序。 -/
theorem compileClauseArray?_raws [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) {raw : Array (Clause σ)}
    {compiled : Array (CompiledClause registry)}
    (hCompile : compileClauseArray? registry raw = some compiled) :
    compiled.map CompiledClause.raw = raw := by
  unfold compileClauseArray? at hCompile
  cases hList : compileClauseList? registry raw.toList with
  | none => simp [hList] at hCompile
  | some compiledList =>
      simp [hList] at hCompile
      subst compiled
      apply Array.toList_inj.mp
      simpa [Array.toList_map] using compileClauseList?_raws registry hList

/-- 整张证书所有 replay 阶段共用的唯一 registry。 -/
def dagReplayRegistry [DecidableEq σ.SortSymbol]
    (dag : DAG σ) : FreeRegistry σ :=
  FreeRegistry.ofSupport dag.replaySupport

/-- 整张 DAG 的初始字句与节点结论编译结果。 -/
structure DAGClauseCompilation [DecidableEq σ.SortSymbol]
    (dag : DAG σ) where
  registry : FreeRegistry σ
  registry_eq : registry = dagReplayRegistry dag
  initialClauses : Array (CompiledClause registry)
  nodes : Array (CompiledClause registry)

/-- 以唯一 clause registry 编译整张 DAG 的字句表面。 -/
def compileDAGClauses? [DecidableEq σ.SortSymbol]
    (dag : DAG σ) : Option (DAGClauseCompilation dag) := do
  let registry := dagReplayRegistry dag
  let initialClauses ← compileClauseArray? registry dag.problem.initialClauses
  let nodes ← compileClauseArray? registry (dag.nodes.map Node.conclusion)
  pure {
    registry := registry
    registry_eq := rfl
    initialClauses := initialClauses
    nodes := nodes
  }

/-- 整图编译保持初始字句数组。 -/
theorem compileDAGClauses?_initial_raws [DecidableEq σ.SortSymbol]
    {dag : DAG σ} {compilation : DAGClauseCompilation dag}
    (hCompile : compileDAGClauses? dag = some compilation) :
    compilation.initialClauses.map CompiledClause.raw =
      dag.problem.initialClauses := by
  unfold compileDAGClauses? at hCompile
  let registry := dagReplayRegistry dag
  cases hInitial : compileClauseArray? registry
      dag.problem.initialClauses with
  | none => simp [registry, hInitial] at hCompile
  | some initialClauses =>
      cases hNodes : compileClauseArray? registry
          (dag.nodes.map Node.conclusion) with
      | none => simp [registry, hInitial, hNodes] at hCompile
      | some nodes =>
          simp [registry, hInitial, hNodes] at hCompile
          subst compilation
          exact compileClauseArray?_raws registry hInitial

/-- 整图编译保持节点结论数组。 -/
theorem compileDAGClauses?_node_raws [DecidableEq σ.SortSymbol]
    {dag : DAG σ} {compilation : DAGClauseCompilation dag}
    (hCompile : compileDAGClauses? dag = some compilation) :
    compilation.nodes.map CompiledClause.raw =
      dag.nodes.map Node.conclusion := by
  unfold compileDAGClauses? at hCompile
  let registry := dagReplayRegistry dag
  cases hInitial : compileClauseArray? registry
      dag.problem.initialClauses with
  | none => simp [registry, hInitial] at hCompile
  | some initialClauses =>
      cases hNodes : compileClauseArray? registry
          (dag.nodes.map Node.conclusion) with
      | none => simp [registry, hInitial, hNodes] at hCompile
      | some nodes =>
          simp [registry, hInitial, hNodes] at hCompile
          subst compilation
          exact compileClauseArray?_raws registry hNodes

/-- 成功编译的整图字句层；构造只能来自计算等式。 -/
structure CheckedDAGClauses [DecidableEq σ.SortSymbol]
    (dag : DAG σ) where
  private mkInternal ::
  compilation : DAGClauseCompilation dag
  compiled : compileDAGClauses? dag = some compilation

namespace CheckedDAGClauses

def compile? [DecidableEq σ.SortSymbol]
    (dag : DAG σ) : Option (CheckedDAGClauses dag) :=
  match hCompile : compileDAGClauses? dag with
  | none => none
  | some compilation => some ⟨compilation, hCompile⟩

def compileCheck [DecidableEq σ.SortSymbol]
    (dag : DAG σ) : Bool :=
  match compile? dag with
  | none => false
  | some _ => true

def ofCompileCheck [DecidableEq σ.SortSymbol]
    {dag : DAG σ} (hCheck : compileCheck dag = true) :
    CheckedDAGClauses dag := by
  cases hCompile : compile? dag with
  | none =>
      simp [compileCheck, hCompile] at hCheck
  | some checked =>
      exact checked

def of_compilation [DecidableEq σ.SortSymbol]
    {dag : DAG σ} {compilation : DAGClauseCompilation dag}
    (hCompile : compileDAGClauses? dag = some compilation) :
    CheckedDAGClauses dag :=
  ⟨compilation, hCompile⟩

theorem initial_raws [DecidableEq σ.SortSymbol]
    {dag : DAG σ} (checked : CheckedDAGClauses dag) :
    checked.compilation.initialClauses.map CompiledClause.raw =
      dag.problem.initialClauses :=
  compileDAGClauses?_initial_raws checked.compiled

theorem initial_size [DecidableEq σ.SortSymbol]
    {dag : DAG σ} (checked : CheckedDAGClauses dag) :
    checked.compilation.initialClauses.size =
      dag.problem.initialClauses.size := by
  have hSize := congrArg Array.size checked.initial_raws
  simpa using hSize

/-- 与原问题初始字句同索引的 compiled clause。 -/
def initialAt [DecidableEq σ.SortSymbol]
    {dag : DAG σ} (checked : CheckedDAGClauses dag)
    (index : Nat) (hIndex : index < dag.problem.initialClauses.size) :
    CompiledClause checked.compilation.registry :=
  checked.compilation.initialClauses[index]'(by
    simpa [checked.initial_size] using hIndex)

theorem initialAt_raw [DecidableEq σ.SortSymbol]
    {dag : DAG σ} (checked : CheckedDAGClauses dag)
    (index : Nat) (hIndex : index < dag.problem.initialClauses.size) :
    (checked.initialAt index hIndex).raw =
      dag.problem.initialClauses[index]'hIndex := by
  have hCompiledIndex :
      index < checked.compilation.initialClauses.size := by
    simpa [checked.initial_size] using hIndex
  have hCompiledGet :
      checked.compilation.initialClauses[index]? =
        some (checked.initialAt index hIndex) :=
    Array.getElem?_eq_some_iff.mpr ⟨hCompiledIndex, rfl⟩
  have hRawGet :
      dag.problem.initialClauses[index]? =
        some (dag.problem.initialClauses[index]'hIndex) :=
    Array.getElem?_eq_some_iff.mpr ⟨hIndex, rfl⟩
  have hAt := congrArg (fun values => values[index]?) checked.initial_raws
  simp [Array.getElem?_map, hCompiledGet, hRawGet] at hAt
  exact hAt

theorem node_raws [DecidableEq σ.SortSymbol]
    {dag : DAG σ} (checked : CheckedDAGClauses dag) :
    checked.compilation.nodes.map CompiledClause.raw =
      dag.nodes.map Node.conclusion :=
  compileDAGClauses?_node_raws checked.compiled

theorem node_size [DecidableEq σ.SortSymbol]
    {dag : DAG σ} (checked : CheckedDAGClauses dag) :
    checked.compilation.nodes.size = dag.nodes.size := by
  have hSize := congrArg Array.size checked.node_raws
  simpa using hSize

/-- 与原 DAG 节点同索引的 compiled clause。 -/
def nodeAt [DecidableEq σ.SortSymbol]
    {dag : DAG σ} (checked : CheckedDAGClauses dag)
    (index : Nat) (hIndex : index < dag.nodes.size) :
    CompiledClause checked.compilation.registry :=
  checked.compilation.nodes[index]'(by simpa [checked.node_size] using hIndex)

theorem nodeAt_raw [DecidableEq σ.SortSymbol]
    {dag : DAG σ} (checked : CheckedDAGClauses dag)
    (index : Nat) (hIndex : index < dag.nodes.size) :
    (checked.nodeAt index hIndex).raw =
      (dag.nodeAt index hIndex).conclusion := by
  have hCompiledIndex : index < checked.compilation.nodes.size := by
    simpa [checked.node_size] using hIndex
  have hCompiledGet :
      checked.compilation.nodes[index]? =
        some (checked.nodeAt index hIndex) := by
    exact Array.getElem?_eq_some_iff.mpr ⟨hCompiledIndex, rfl⟩
  have hNodeGet :
      dag.nodes[index]? = some (dag.nodeAt index hIndex) := by
    apply Array.getElem?_eq_some_iff.mpr
    refine ⟨hIndex, ?_⟩
    change dag.nodes[index] = dag.nodes[index]
    rfl
  have hAt := congrArg (fun values => values[index]?) checked.node_raws
  simp [Array.getElem?_map, hCompiledGet, hNodeGet] at hAt
  exact hAt

end CheckedDAGClauses

end Compile
end DAGCertificate
end Automation
end YesMetaZFC
