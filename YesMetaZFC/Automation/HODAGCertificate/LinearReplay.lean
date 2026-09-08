import YesMetaZFC.Automation.HODAGCertificate
import YesMetaZFC.Automation.DAGCertificate.LinearReplay

/-!
# 高阶 DAG 的线性契约回放

本层把节点 payload、父快照与 guard 合并到同一次数组遍历中。根节点和拓扑信息
各自只检查一次，避免旧整图 checker 展开成巨型依赖式布尔归约。
-/

namespace YesMetaZFC
namespace Automation
namespace HODAGCertificate
namespace DAG
namespace LinearReplay

variable {σ : Signature}

/-- 单节点回放同时覆盖 payload、父快照和 guard。 -/
def nodeCheck [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (node : Node σ) : Bool :=
  node.check dag.problem &&
    (node.payload.parentClauses.all fun parent =>
      dag.parentSnapshotChecked parent) &&
      (dag.localNodeGuardsOk node && dag.propInitialLinksOk node)

/-- 所有局部证书字段共用一次顺序节点扫描。 -/
def nodesChecked [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.nodes.all (nodeCheck dag)

theorem denseIds_eq_true_of_listCheck
    {dag : DAG σ} {nodes : List (Node σ)}
    (hNodes : dag.nodes.toList = nodes)
    (hChecked : dag.graphView.denseIdsListCheck nodes = true) :
    dag.denseIds = true := by
  simpa [denseIds] using
    DenseDAG.View.denseIds_eq_true_of_listCheck hNodes hChecked

theorem parentsBefore_eq_true_of_listCheck
    {dag : DAG σ} {nodes : List (Node σ)}
    (hNodes : dag.nodes.toList = nodes)
    (hChecked : dag.graphView.parentsBeforeListCheck nodes = true) :
    dag.parentsBefore = true := by
  simpa [parentsBefore] using
    DenseDAG.View.parentsBefore_eq_true_of_listCheck hNodes hChecked

theorem nodesChecked_eq_true_of_chunks
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {nodes : List (Node σ)}
    (hNodes : dag.nodes.toList = nodes)
    (checked :
      DAGCertificate.DAG.CheckedListChunks (nodeCheck dag) nodes) :
    nodesChecked dag = true := by
  unfold nodesChecked
  rw [← Array.all_toList, hNodes]
  exact checked.all_eq_true

private theorem node_fields_of_nodesChecked
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hNodes : nodesChecked dag = true) (index : Nat)
    (hIndex : index < dag.nodes.size) :
    ((dag.nodeAt index hIndex).check dag.problem = true ∧
      ((dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        dag.parentSnapshotChecked parent) = true) ∧
      (dag.localNodeGuardsOk (dag.nodeAt index hIndex) = true ∧
        dag.propInitialLinksOk (dag.nodeAt index hIndex) = true) := by
  have hAt := Array.all_eq_true.mp hNodes index hIndex
  simpa [nodesChecked, nodeCheck, DAG.nodeAt] using! hAt

/-- 单次节点扫描恢复原高阶 DAG 契约消费的三个全局字段。 -/
theorem dag_fields_of_nodesChecked
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hNodes : nodesChecked dag = true) :
    dag.payloadsChecked = true ∧
      dag.parentSnapshotsChecked = true ∧
        dag.guardsChecked = true := by
  have hPayloads : dag.payloadsChecked = true := by
    apply Array.all_eq_true.mpr
    intro index hIndex
    exact (node_fields_of_nodesChecked hNodes index hIndex).1.1
  have hSnapshots : dag.parentSnapshotsChecked = true := by
    apply Array.all_eq_true.mpr
    intro index hIndex
    exact (node_fields_of_nodesChecked hNodes index hIndex).1.2
  have hGuards : dag.guardsChecked = true := by
    apply Array.all_eq_true.mpr
    intro index hIndex
    exact Bool.and_eq_true_iff.mpr
      (node_fields_of_nodesChecked hNodes index hIndex).2
  exact ⟨hPayloads, hSnapshots, hGuards⟩

/-- 高阶 DAG 的固定阶段线性 checker。 -/
def coreCheck [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.rootExists &&
    dag.rootClosed &&
      dag.denseIds &&
        dag.parentsBefore &&
          nodesChecked dag

theorem coreCheck_eq_true_of_components
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ)
    (hRootExists : dag.rootExists = true)
    (hRootClosed : dag.rootClosed = true)
    (hDenseIds : dag.denseIds = true)
    (hParentsBefore : dag.parentsBefore = true)
    (hNodes : nodesChecked dag = true) :
    coreCheck dag = true := by
  simp [coreCheck, hRootExists, hRootClosed, hDenseIds,
    hParentsBefore, hNodes]

/-- 线性 checker 真值直接产生完整高阶 DAG 契约。 -/
theorem contract_of_coreCheck
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hCore : coreCheck dag = true) :
    DAG.Contract dag := by
  have hFields :
      ((((dag.rootExists = true ∧ dag.rootClosed = true) ∧
          dag.denseIds = true) ∧ dag.parentsBefore = true) ∧
            nodesChecked dag = true) := by
    simpa [coreCheck] using hCore
  rcases hFields with
    ⟨⟨⟨⟨hRootExists, hRootClosed⟩, hDenseIds⟩, hParentsBefore⟩,
      hNodes⟩
  rcases dag_fields_of_nodesChecked hNodes with
    ⟨hPayloads, hSnapshots, hGuards⟩
  have hRootSize : dag.root < dag.nodes.size := by
    exact of_decide_eq_true hRootExists
  have hRootData :
      (∃ conclusion,
          (dag.nodeAt dag.root hRootSize).conclusion? dag.problem =
            some conclusion ∧ conclusion.isEmpty = true) ∧
        (dag.nodeAt dag.root hRootSize).unguarded = true := by
    unfold DAG.rootClosed at hRootClosed
    rw [dag.node?_eq_some_nodeAt hRootSize] at hRootClosed
    cases hConclusion :
        (dag.nodeAt dag.root hRootSize).conclusion? dag.problem with
    | none =>
        simp [Node.globallyClosed, hConclusion] at hRootClosed
    | some conclusion =>
        have hConclusionFields :
            (dag.nodeAt dag.root hRootSize).unguarded = true ∧
              conclusion.isEmpty = true :=
          Bool.and_eq_true_iff.mp (by
            simpa [Node.globallyClosed, hConclusion] using hRootClosed)
        exact
          ⟨⟨conclusion, rfl, hConclusionFields.2⟩,
            hConclusionFields.1⟩
  refine {
    root_exists := hRootSize
    root_closed := hRootClosed
    root_conclusion := hRootData.1
    root_unguarded := hRootData.2
    dense_ids := hDenseIds
    parents_before := DAG.parentsBefore_of_eq_true hParentsBefore
    payloads_checked := hPayloads
    parent_snapshots_checked := hSnapshots
    guards_checked := hGuards
    node_contract := ?_
  }
  intro index hIndex
  exact {
    node_id := DAG.denseIds_of_eq_true hDenseIds index hIndex
    node_checked :=
      DAG.payloadsChecked_of_eq_true hPayloads index hIndex
    guards_checked :=
      DAG.guardsChecked_of_eq_true hGuards index hIndex
    prop_initial_links_checked :=
      DAG.propInitialLinksChecked_of_eq_true hGuards index hIndex
  }

end LinearReplay
end DAG
end HODAGCertificate
end Automation
end YesMetaZFC
