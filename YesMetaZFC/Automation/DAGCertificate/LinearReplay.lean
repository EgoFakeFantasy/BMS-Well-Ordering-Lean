import YesMetaZFC.Automation.AvatarRegistrySoundness

/-!
# DAG 的线性阶段回放

本层把逐节点 payload、父快照和 guard 检查合并为单次数组遍历，并把结果提升为
`DAG.Contract`。具体回放日程由连续证书竞技场提供，本层不再定义证明携带的节点脊柱。

source 唯一性和 AVATAR 全局 registry 仍是独立证书阶段：它们各自有不同的数据结构
与复杂度边界，不应隐藏在“逐节点线性扫描”的名义下。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace DAG
namespace LinearReplay

variable {σ : Signature}

/-- 单个节点在结构回放阶段需要共同复算的三个局部检查。 -/
def nodeCheck [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (node : Node σ) : Bool :=
  node.check dag.problem &&
    dag.nodeParentSnapshotsChecked node &&
      dag.nodeGuardsChecked node

/-- 三个局部阶段真值组合为单节点线性检查真值。 -/
theorem nodeCheck_eq_true_of_components
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (node : Node σ)
    (hPayload : node.check dag.problem = true)
    (hParents : dag.nodeParentSnapshotsChecked node = true)
    (hGuards : dag.nodeGuardsChecked node = true) :
    nodeCheck dag node = true := by
  simp [nodeCheck, hPayload, hParents, hGuards]

/-- payload、父快照与 guard 共用一次数组遍历。 -/
def nodesChecked [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.nodes.all (nodeCheck dag)

/--
顺序节点块恢复原数组节点 checker。

`hNodes` 只在线性边界绑定一次 concrete 节点列表；块内从表头消费节点，不再按不断增长的
数组下标重新规约 quoted `List.toArray` 前缀。
-/
theorem nodesChecked_eq_true_of_chunks
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {nodes : List (Node σ)}
    (hNodes : dag.nodes.toList = nodes)
    (checked : CheckedListChunks (nodeCheck dag) nodes) :
    nodesChecked dag = true := by
  unfold nodesChecked
  rw [← Array.all_toList, hNodes]
  exact checked.all_eq_true

/-- 节点语义检查的连续半开区间。 -/
def nodesCheckedRange [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (start stop : Nat) : Bool :=
  dag.nodes.all (nodeCheck dag) start stop

/-- 专用节点证明可作为长度一的连续区间签名接入统一日程。 -/
theorem nodesCheckedRange_singleton_eq_true
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {index : Nat}
    (hIndex : index < dag.nodes.size)
    (hNode : nodeCheck dag (dag.nodeAt index hIndex) = true) :
    nodesCheckedRange dag index (index + 1) = true := by
  apply Array.all_iff_forall.mpr
  intro current hCurrent hRange
  have hEq : current = index := by
    omega
  subst current
  simpa [DAG.nodeAt] using hNode

/--
按少量连续区间携带节点语义真值。

证明大小只随区间数增长；每个区间内部仍由同一个数组 checker 线性计算。
-/
inductive CheckedNodeRanges
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : Nat → Prop where
  | done : CheckedNodeRanges dag dag.nodes.size
  | cons {start stop : Nat} :
      nodesCheckedRange dag start stop = true →
        CheckedNodeRanges dag stop →
          CheckedNodeRanges dag start

namespace CheckedNodeRanges

theorem nodeCheck_eq_true
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {start : Nat}
    (checked : CheckedNodeRanges dag start) :
    ∀ {index : Nat} (hIndex : index < dag.nodes.size),
      start ≤ index →
        nodeCheck dag (dag.nodes[index]'hIndex) = true := by
  induction checked with
  | done =>
      intro index hIndex hStart
      omega
  | @cons start stop hRange _ ih =>
      intro index hIndex hStart
      by_cases hStop : index < stop
      · exact (Array.all_iff_forall.mp hRange) index hIndex
          ⟨hStart, hStop⟩
      · exact ih hIndex (Nat.le_of_not_gt hStop)

end CheckedNodeRanges

/-- 连续区间签名恢复完整节点语义 checker 真值。 -/
theorem nodesChecked_eq_true_of_ranges
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (checked : CheckedNodeRanges dag 0) :
    nodesChecked dag = true := by
  apply Array.all_eq_true.mpr
  intro index hIndex
  exact checked.nodeCheck_eq_true hIndex (Nat.zero_le index)

/-- 结构回放的线性 soundness 骨架。source 键规范性由宿主 audit 独立处理。 -/
def coreCheck [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.rootExists &&
    dag.rootClosed &&
      dag.denseIds &&
        dag.parentsBefore &&
          nodesChecked dag

/-- 固定数量的阶段签名组合为线性结构 checker 真值。 -/
theorem coreCheck_eq_true_of_components
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ)
    (hRootExists : dag.rootExists = true)
    (hRootClosed : dag.rootClosed = true)
    (hDenseIds : dag.denseIds = true)
    (hParentsBefore : dag.parentsBefore = true)
    (hNodes : nodesChecked dag = true) :
    coreCheck dag = true := by
  simp [coreCheck, hRootExists, hRootClosed, hDenseIds,
    hParentsBefore, hNodes]

theorem node_fields_of_nodesChecked
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hNodes : nodesChecked dag = true) (index : Nat)
    (hIndex : index < dag.nodes.size) :
    ((dag.nodeAt index hIndex).check dag.problem = true ∧
      dag.nodeParentSnapshotsChecked (dag.nodeAt index hIndex) = true) ∧
      dag.nodeGuardsChecked (dag.nodeAt index hIndex) = true := by
  have hAt := Array.all_eq_true.mp hNodes index hIndex
  simpa [nodesChecked, nodeCheck, DAG.nodeAt] using hAt

/-- 一次节点扫描导出原 DAG 公共接口的三个逐节点阶段。 -/
theorem dag_fields_of_nodesChecked
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hNodes : nodesChecked dag = true) :
    dag.payloadsChecked = true ∧
      dag.parentSnapshotsChecked = true ∧
        dag.guardsChecked = true := by
  have hPayloads : dag.payloadsChecked = true := by
    apply Array.all_eq_true.mpr
    intro index hIndex
    exact (node_fields_of_nodesChecked hNodes index hIndex).1.1
  have hParentSnapshots : dag.parentSnapshotsChecked = true := by
    apply Array.all_eq_true.mpr
    intro index hIndex
    exact (node_fields_of_nodesChecked hNodes index hIndex).1.2
  have hGuards : dag.guardsChecked = true := by
    apply Array.all_eq_true.mpr
    intro index hIndex
    exact (node_fields_of_nodesChecked hNodes index hIndex).2
  exact ⟨hPayloads, hParentSnapshots, hGuards⟩

/-- 一次结构扫描产生完整 DAG soundness 合同，不重新执行任何 checker。 -/
theorem contract_of_coreCheck
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
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
    ⟨hPayloads, hParentSnapshots, hGuards⟩
  have hRootSize : dag.root < dag.nodes.size := by
    simpa [DAG.rootExists, DAG.graphView, DenseDAG.View.rootExists] using
      hRootExists
  have hRootFields :
      (dag.nodeAt dag.root hRootSize).globallyClosed = true ∧
        (dag.nodeAt dag.root hRootSize).payload.rootClosureEligible = true := by
    simpa [DAG.rootClosed, dag.node?_eq_some_nodeAt hRootSize] using
      hRootClosed
  have hRootConclusion :
      (dag.nodeAt dag.root hRootSize).unguarded = true ∧
        (dag.nodeAt dag.root hRootSize).conclusion.isEmpty = true := by
    simpa [Node.globallyClosed, Node.guardedConclusion,
      GuardedClause.globallyEmpty, Guards.GuardedClause.globallyEmpty,
      GuardedClause.unguarded, Guards.GuardedClause.unguarded,
      Node.unguarded] using hRootFields.1
  refine {
    root_exists := hRootSize
    root_closed := hRootClosed
    root_unguarded := hRootConclusion.1
    root_conclusion_empty := hRootConclusion.2
    dense_ids := hDenseIds
    parents_before := DAG.parentsBefore_of_eq_true hParentsBefore
    payloads_checked := hPayloads
    parent_snapshots_checked := hParentSnapshots
    guards_checked := hGuards
    node_contract := ?_
  }
  intro index hIndex
  have hNodeChecked :
      (dag.nodeAt index hIndex).check dag.problem = true :=
    DAG.payloadsChecked_of_eq_true hPayloads index hIndex
  rcases Node.fields_of_check_eq_true hNodeChecked with
    ⟨hRuleTags, hPayload⟩
  exact {
    node_id := DAG.denseIds_of_eq_true hDenseIds index hIndex
    node_checked := hNodeChecked
    rule_tags_ok := hRuleTags
    payload_checked := hPayload
    guards_checked := DAG.guardsChecked_of_eq_true hGuards index hIndex
    prop_initial_links_checked :=
      DAG.propInitialLinksChecked_of_eq_true hGuards index hIndex
    guarded_soundness_supported := fun hSupported =>
      DAG.guardedSoundnessSupported_of_eq_true hSupported index hIndex
  }

/-- AVATAR 节点能力与局部 registry 共用一次数组遍历。 -/
def avatarNodeCheck [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (node : Node σ) : Bool :=
  nodeAvatarSoundnessSupported node && nodeAvatarRegistryLocalCheck node

def avatarNodesChecked [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.nodes.all avatarNodeCheck

/-!
Arena 的融合节点 checker。`includeAvatar` 是整张 DAG 的一次性模式位；
不能在每个节点里重新规约 `dag.avatarSoundnessSupported`，否则会把线性扫描
退化为对节点数组的重复扫描。
-/
def arenaNodeCheckPlain [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (node : Node σ) : Bool :=
  nodeCheck dag node

def arenaNodeCheckAvatar [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (node : Node σ) : Bool :=
  nodeCheck dag node && avatarNodeCheck node

def arenaNodeCheck [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (includeAvatar : Bool) (dag : DAG σ)
    (node : Node σ) : Bool :=
  if includeAvatar then arenaNodeCheckAvatar dag node
  else arenaNodeCheckPlain dag node

theorem arenaNodeCheckAvatar_eq_true_of_components
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (node : Node σ)
    (hNode : nodeCheck dag node = true)
    (hAvatar : avatarNodeCheck node = true) :
    arenaNodeCheckAvatar dag node = true := by
  simp [arenaNodeCheckAvatar, hNode, hAvatar]

def arenaNodesChecked [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (includeAvatar : Bool) (dag : DAG σ) : Bool :=
  if includeAvatar then
    dag.nodes.all (arenaNodeCheckAvatar dag)
  else
    dag.nodes.all (arenaNodeCheckPlain dag)

theorem arenaNodesChecked_eq_true_of_plain_chunks
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    {dag : DAG σ} {nodes : List (Node σ)}
    (hNodes : dag.nodes.toList = nodes)
    (checked : CheckedListChunks (nodeCheck dag) nodes) :
    arenaNodesChecked false dag = true := by
  unfold arenaNodesChecked
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← Array.all_toList, hNodes]
  exact checked.all_eq_true

theorem arenaNodesChecked_eq_true_of_avatar_chunks
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {nodes : List (Node σ)}
    (hNodes : dag.nodes.toList = nodes)
    (checked : CheckedListChunks (arenaNodeCheckAvatar dag) nodes) :
    arenaNodesChecked true dag = true := by
  unfold arenaNodesChecked
  simp only [↓reduceIte]
  rw [← Array.all_toList, hNodes]
  exact checked.all_eq_true

theorem nodesChecked_eq_true_of_arenaNodesChecked
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {includeAvatar : Bool} {dag : DAG σ}
    (hArena : arenaNodesChecked includeAvatar dag = true) :
    nodesChecked dag = true := by
  cases includeAvatar with
  | false =>
      simpa [arenaNodesChecked, arenaNodeCheckPlain, nodesChecked] using hArena
  | true =>
      apply Array.all_eq_true.mpr
      intro index hIndex
      have hAt := Array.all_eq_true.mp hArena index hIndex
      have hFields :
          nodeCheck dag (dag.nodeAt index hIndex) = true ∧
            avatarNodeCheck (dag.nodeAt index hIndex) = true := by
        simpa [arenaNodesChecked, arenaNodeCheckAvatar, DAG.nodeAt] using hAt
      exact hFields.1

theorem avatarNodesChecked_eq_true_of_arenaNodesChecked
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hArena : arenaNodesChecked true dag = true) :
    avatarNodesChecked dag = true := by
  apply Array.all_eq_true.mpr
  intro index hIndex
  have hAt := Array.all_eq_true.mp hArena index hIndex
  have hFields :
      nodeCheck dag (dag.nodeAt index hIndex) = true ∧
        avatarNodeCheck (dag.nodeAt index hIndex) = true := by
    simpa [arenaNodesChecked, arenaNodeCheckAvatar, DAG.nodeAt] using hAt
  exact hFields.2

/-- 顺序节点块恢复 AVATAR 能力与局部 registry 的联合检查。 -/
theorem avatarNodesChecked_eq_true_of_chunks
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {nodes : List (Node σ)}
    (hNodes : dag.nodes.toList = nodes)
    (checked : CheckedListChunks avatarNodeCheck nodes) :
    avatarNodesChecked dag = true := by
  unfold avatarNodesChecked
  rw [← Array.all_toList, hNodes]
  exact checked.all_eq_true

/--
AVATAR 线性节点阶段加独立的全局 registry 一致性阶段。
全局阶段使用宿主提供的连续 selector 槽位表，逐条 registry entry 做一次槽位读取。
-/
def avatarCheck [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ)
    (registry : AvatarSelectorComponent.Registry σ) : Bool :=
  avatarNodesChecked dag &&
    AvatarSelectorComponent.Registry.check registry dag.avatarSelectorRegistry

theorem avatar_fields_of_components
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    {registry : AvatarSelectorComponent.Registry σ}
    (hNodes : avatarNodesChecked dag = true)
    (hRegistry :
      AvatarSelectorComponent.Registry.check registry
        dag.avatarSelectorRegistry = true) :
    dag.avatarSoundnessSupported = true ∧
      DAG.avatarRegistryCheckWith dag registry = true := by
  have hSupported : dag.avatarSoundnessSupported = true := by
    apply Array.all_eq_true.mpr
    intro index hIndex
    have hAt := Array.all_eq_true.mp hNodes index hIndex
    exact (Bool.and_eq_true_iff.mp <|
      by simpa [avatarNodesChecked, avatarNodeCheck] using hAt).1
  have hLocal : dag.nodes.all nodeAvatarRegistryLocalCheck = true := by
    apply Array.all_eq_true.mpr
    intro index hIndex
    have hAt := Array.all_eq_true.mp hNodes index hIndex
    exact (Bool.and_eq_true_iff.mp <|
      by simpa [avatarNodesChecked, avatarNodeCheck] using hAt).2
  exact ⟨hSupported, Bool.and_eq_true_iff.mpr ⟨hLocal, hRegistry⟩⟩

theorem avatar_fields_of_check
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    {registry : AvatarSelectorComponent.Registry σ}
    (hCheck : avatarCheck dag registry = true) :
    dag.avatarSoundnessSupported = true ∧
      DAG.avatarRegistryCheckWith dag registry = true := by
  have hFields :
      avatarNodesChecked dag = true ∧
        AvatarSelectorComponent.Registry.check registry
          dag.avatarSelectorRegistry = true := by
    simpa [avatarCheck] using hCheck
  exact avatar_fields_of_components hFields.1 hFields.2

end LinearReplay
end DAG
end DAGCertificate
end Automation
end YesMetaZFC
