import Lean
/-!
# 自动化公共稠密 DAG 内核
本模块只描述节点数组、稳定编号与父边拓扑，不知道任何字句、checker 或语义。
一阶与高阶证书通过各自的节点投影复用同一套可计算检查和拓扑归纳。
-/
namespace YesMetaZFC
namespace Automation
namespace DenseDAG
universe u
structure View (Node : Type u) where
  nodes : Array Node
  root : Nat
  node_id : Node → Nat
  node_parents : Node → Array Nat
namespace View
variable {Node : Type u}
def node? (view : View Node) (id : Nat) : Option Node :=
  view.nodes[id]?
def nodeAt (view : View Node) (index : Nat) (hIndex : index < view.nodes.size) : Node :=
  view.nodes[index]'hIndex
@[simp]
theorem node?_eq_some_nodeAt (view : View Node) {index : Nat} (hIndex : index < view.nodes.size) :
    view.node? index = some (view.nodeAt index hIndex) := by
  simp [node?, nodeAt]
def rootExists (view : View Node) : Bool :=
  view.root < view.nodes.size
def denseIdChecked (view : View Node) (index : Nat) (node : Node) : Bool :=
  view.node_id node == index
def denseIds (view : View Node) : Bool := (view.nodes.mapIdx view.denseIdChecked).all fun ok => ok

private theorem nat_eq_of_beq_eq_true {left right : Nat}
    (h : (left == right) = true) : left = right := by
  simpa using h

/--
在已绑定的连续节点列表上顺序检查稠密编号。

这里显式携带当前编号，不使用标准库 `List.mapIdx`。后者以不断增长的 `Array` 作为
累加器，内核反射时每轮规约 `acc.size` 会把本应线性的扫描放大为平方。
-/
def denseIdsListCheckFrom (view : View Node) : Nat → List Node → Bool
  | _, [] => true
  | index, node :: rest =>
      view.denseIdChecked index node &&
        view.denseIdsListCheckFrom (index + 1) rest

def denseIdsListCheck (view : View Node) (nodes : List Node) : Bool :=
  view.denseIdsListCheckFrom 0 nodes

private theorem denseIdsListCheckFrom_sound
    (view : View Node) :
    ∀ {start : Nat} {nodes : List Node},
      view.denseIdsListCheckFrom start nodes = true →
        ∀ offset node, nodes[offset]? = some node →
          view.node_id node = start + offset
  | start, [], hChecked, offset, node, hNode => by
      simp at hNode
  | start, head :: tail, hChecked, offset, node, hNode => by
      have hFields :
          view.denseIdChecked start head = true ∧
            view.denseIdsListCheckFrom (start + 1) tail = true := by
        simpa [denseIdsListCheckFrom] using hChecked
      cases offset with
      | zero =>
          simp at hNode
          subst node
          exact nat_eq_of_beq_eq_true (by simpa [denseIdChecked] using hFields.1)
      | succ offset =>
          have hTail : tail[offset]? = some node := by
            simpa using hNode
          have hId :=
            denseIdsListCheckFrom_sound view hFields.2 offset node hTail
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hId

theorem denseIds_eq_true_of_listCheck {view : View Node} {nodes : List Node}
    (hNodes : view.nodes.toList = nodes)
    (hChecked : view.denseIdsListCheck nodes = true) :
    view.denseIds = true := by
  unfold denseIds
  apply Array.all_eq_true.mpr
  intro index hIndex
  have hNodeIndex : index < view.nodes.size := by
    simpa using hIndex
  have hNode :
      nodes[index]? = some (view.nodeAt index hNodeIndex) := by
    rw [← hNodes]
    simp [nodeAt, hNodeIndex]
  have hLinear : view.denseIdsListCheckFrom 0 nodes = true := by
    simpa [denseIdsListCheck] using hChecked
  have hId :=
    denseIdsListCheckFrom_sound view (start := 0) (nodes := nodes)
      hLinear index (view.nodeAt index hNodeIndex) hNode
  simpa [Array.getElem_mapIdx, denseIdChecked, nodeAt] using hId
theorem denseIds_of_eq_true {view : View Node} (hDense : view.denseIds = true) :
    ∀ index (hIndex : index < view.nodes.size),
      view.node_id (view.nodeAt index hIndex) = index := by
  intro index hIndex
  let checks := view.nodes.mapIdx view.denseIdChecked
  have hAll : ∀ index (hIndex : index < checks.size), checks[index] = true := by
    simpa [denseIds, checks] using (Array.all_eq_true.mp hDense)
  have hMapIndex : index < checks.size := by
    simpa [checks, Array.size_mapIdx] using hIndex
  have hCheck := hAll index hMapIndex
  have hGet :
      checks[index] = (view.node_id (view.nodeAt index hIndex) == index) := by
    simp [checks, denseIdChecked, nodeAt, Array.getElem_mapIdx]
  rw [hGet] at hCheck
  exact nat_eq_of_beq_eq_true hCheck
def nodeParentsBefore (view : View Node) (index : Nat) (node : Node) : Bool := (view.node_parents node).toList.all fun parent => decide (parent < index)
def parentsBefore (view : View Node) : Bool := (view.nodes.mapIdx view.nodeParentsBefore).all fun ok => ok

/-- 在已绑定的连续节点列表上顺序检查父边拓扑。 -/
def parentsBeforeListCheckFrom (view : View Node) : Nat → List Node → Bool
  | _, [] => true
  | index, node :: rest =>
      view.nodeParentsBefore index node &&
        view.parentsBeforeListCheckFrom (index + 1) rest

def parentsBeforeListCheck (view : View Node) (nodes : List Node) : Bool :=
  view.parentsBeforeListCheckFrom 0 nodes

private theorem parentsBeforeListCheckFrom_sound
    (view : View Node) :
    ∀ {start : Nat} {nodes : List Node},
      view.parentsBeforeListCheckFrom start nodes = true →
        ∀ offset node, nodes[offset]? = some node →
          view.nodeParentsBefore (start + offset) node = true
  | start, [], hChecked, offset, node, hNode => by
      simp at hNode
  | start, head :: tail, hChecked, offset, node, hNode => by
      have hFields :
          view.nodeParentsBefore start head = true ∧
            view.parentsBeforeListCheckFrom (start + 1) tail = true := by
        simpa [parentsBeforeListCheckFrom] using hChecked
      cases offset with
      | zero =>
          simp at hNode
          subst node
          simpa using hFields.1
      | succ offset =>
          have hTail : tail[offset]? = some node := by
            simpa using hNode
          have hCheck :=
            parentsBeforeListCheckFrom_sound view hFields.2 offset node hTail
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCheck

theorem parentsBefore_eq_true_of_listCheck {view : View Node} {nodes : List Node}
    (hNodes : view.nodes.toList = nodes)
    (hChecked : view.parentsBeforeListCheck nodes = true) :
    view.parentsBefore = true := by
  unfold parentsBefore
  apply Array.all_eq_true.mpr
  intro index hIndex
  have hNodeIndex : index < view.nodes.size := by
    simpa using hIndex
  have hNode :
      nodes[index]? = some (view.nodeAt index hNodeIndex) := by
    rw [← hNodes]
    simp [nodeAt, hNodeIndex]
  have hLinear : view.parentsBeforeListCheckFrom 0 nodes = true := by
    simpa [parentsBeforeListCheck] using hChecked
  have hCheck :=
    parentsBeforeListCheckFrom_sound view (start := 0) (nodes := nodes)
      hLinear index (view.nodeAt index hNodeIndex) hNode
  simpa [Array.getElem_mapIdx, nodeParentsBefore, nodeAt] using hCheck

def ParentsBefore (view : View Node) : Prop :=
  ∀ index (hIndex : index < view.nodes.size),
    ∀ parent,
      parent ∈ (view.node_parents (view.nodeAt index hIndex)).toList →
        parent < index
theorem parentsBefore_of_eq_true {view : View Node} (hParents : view.parentsBefore = true) : view.ParentsBefore := by
  intro index hIndex parent hParent
  have hAll := Array.all_eq_true.mp hParents
  have hMapIndex : index < (view.nodes.mapIdx view.nodeParentsBefore).size := by
    simpa using hIndex
  have hNodeCheck :
      view.nodeParentsBefore index (view.nodeAt index hIndex) = true := by
    simpa [parentsBefore, nodeAt, Array.getElem_mapIdx] using
      hAll index hMapIndex
  have hParentCheck :=
    List.all_eq_true.mp hNodeCheck parent hParent
  simpa [nodeParentsBefore] using hParentCheck
/--
节点性质只依赖父节点性质时，按 dense 数组顺序完成拓扑归纳。
-/
theorem topologicalInduction (view : View Node) (hParents : view.ParentsBefore)
    {P : ∀ index, index < view.nodes.size → Node → Prop} (hStep :
      ∀ index (hIndex : index < view.nodes.size), (∀ parent (hParent :
              parent ∈ (view.node_parents (view.nodeAt index hIndex)).toList),
            P parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex) (view.nodeAt parent
                (Nat.lt_trans (hParents index hIndex parent hParent) hIndex))) →
          P index hIndex (view.nodeAt index hIndex)) :
    ∀ index (hIndex : index < view.nodes.size),
      P index hIndex (view.nodeAt index hIndex) := by
  intro index
  refine Nat.strongRecOn index ?_
  intro current ih hCurrent
  exact hStep current hCurrent fun parent hParent =>
    let hParentLt := hParents current hCurrent parent hParent
    ih parent hParentLt (Nat.lt_trans hParentLt hCurrent)
theorem rootByTopologicalInduction (view : View Node) (hRoot : view.root < view.nodes.size) (hParents : view.ParentsBefore)
    {P : ∀ index, index < view.nodes.size → Node → Prop} (hStep :
      ∀ index (hIndex : index < view.nodes.size), (∀ parent (hParent :
              parent ∈ (view.node_parents (view.nodeAt index hIndex)).toList),
            P parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex) (view.nodeAt parent
                (Nat.lt_trans (hParents index hIndex parent hParent) hIndex))) →
          P index hIndex (view.nodeAt index hIndex)) :
    P view.root hRoot (view.nodeAt view.root hRoot) :=
  view.topologicalInduction hParents hStep view.root hRoot
end View
end DenseDAG
end Automation
end YesMetaZFC
