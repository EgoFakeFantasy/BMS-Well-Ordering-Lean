import YesMetaZFC.Automation.DAGCertificate.Payload

/-!
# AVATAR selector 注册表

本模块只保存 AVATAR 分解与全图 selector 注册表的有限结构检查。它不解释对象公式，
也不携带环境参数；语义重放由后续内在类型编译层统一承担。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate

section DAGCertificateSignature

variable {σ : Signature}

namespace Clause

def Covers (source : Clause σ) (components : List (Clause σ)) : Prop :=
  (∀ literal, literal ∈ source.literals.toList →
    ∃ component, component ∈ components ∧
      literal ∈ component.literals.toList) ∧
  ∀ component, component ∈ components →
    ∀ literal, literal ∈ component.literals.toList →
      literal ∈ source.literals.toList

def SupportDisjoint (left right : Clause σ) : Prop :=
  ∀ entry, entry ∈ left.freeSupport → entry ∈ right.freeSupport → False

def PairwiseSupportDisjoint : List (Clause σ) → Prop
  | [] => True
  | head :: tail =>
      (∀ other, other ∈ tail →
        SupportDisjoint head other) ∧
      PairwiseSupportDisjoint tail

private def partitionIndices (partitions : Array (Array Nat)) : List Nat :=
  partitions.toList.flatMap Array.toList

/-- 检查每个 source literal 索引至少出现在一个 partition 中。 -/
def partitionCoversCheck
    (sourceSize : Nat) (partitions : @& Array (Array Nat)) : Bool :=
  let indices := partitionIndices partitions
  (List.range sourceSize).all indices.contains

theorem partitionCoversCheck_sound
    {source : Clause σ} {partitions : Array (Array Nat)}
    (hCheck : partitionCoversCheck source.literals.size partitions = true) :
    Covers source
      (partitions.toList.map (Clause.atIndices source)) := by
  let indices := partitionIndices partitions
  have hAll :
      (List.range source.literals.size).all indices.contains = true := by
    simpa [partitionCoversCheck, indices] using hCheck
  constructor
  · intro literal hLiteral
    have hArray : literal ∈ source.literals :=
      Array.mem_def.mpr hLiteral
    rcases Array.mem_iff_getElem?.mp hArray with ⟨index, hGet⟩
    have hIndex : index < source.literals.size :=
      (Array.getElem?_eq_some_iff.mp hGet).1
    have hContains : indices.contains index = true :=
      List.all_eq_true.mp hAll index (List.mem_range.mpr hIndex)
    have hFlat : index ∈ indices :=
      List.contains_iff_mem.mp (by simpa using hContains)
    rcases List.mem_flatMap.mp hFlat with
      ⟨partition, hPartition, hIndexPartition⟩
    refine ⟨Clause.atIndices source partition,
      List.mem_map.mpr ⟨partition, hPartition, rfl⟩, ?_⟩
    change literal ∈
      (partition.filterMap fun i => source.literals[i]?).toList
    apply Array.mem_def.mp
    exact Array.mem_filterMap.mpr
      ⟨index, Array.mem_def.mpr hIndexPartition, hGet⟩
  · intro component hComponent literal hLiteral
    rcases List.mem_map.mp hComponent with
      ⟨partition, _hPartition, rfl⟩
    have hArray : literal ∈
        partition.filterMap fun i => source.literals[i]? :=
      Array.mem_def.mpr hLiteral
    rcases Array.mem_filterMap.mp hArray with
      ⟨_index, _hIndex, hGet⟩
    exact Array.mem_def.mp (Array.mem_of_getElem? hGet)

/-- 检查两个原始字句的自由变量支持不交。 -/
def supportsDisjointCheck [DecidableEq σ.SortSymbol]
    (left right : Clause σ) : Bool :=
  left.freeSupport.all fun key =>
    !right.freeSupport.contains key

theorem supportsDisjointCheck_sound [DecidableEq σ.SortSymbol]
    {left right : Clause σ}
    (hCheck : supportsDisjointCheck left right = true) :
    SupportDisjoint left right := by
  intro entry hLeft hRight
  have hNotMem : ¬ entry ∈ right.freeSupport := by
    simpa [supportsDisjointCheck] using
      List.all_eq_true.mp hCheck entry hLeft
  exact hNotMem hRight

/-- 检查 component 字句的自由变量支持两两不交。 -/
def pairwiseSupportDisjointCheck [DecidableEq σ.SortSymbol] :
    List (Clause σ) → Bool
  | [] => true
  | head :: tail =>
      tail.all (supportsDisjointCheck head) &&
      pairwiseSupportDisjointCheck tail

theorem pairwiseSupportDisjointCheck_sound [DecidableEq σ.SortSymbol]
    {components : List (Clause σ)}
    (hCheck : pairwiseSupportDisjointCheck components = true) :
    PairwiseSupportDisjoint components := by
  induction components with
  | nil =>
      trivial
  | cons head tail ih =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hTail⟩
      constructor
      · intro other hOther
        exact supportsDisjointCheck_sound
          (List.all_eq_true.mp hHead other hOther)
      · exact ih hTail

end Clause

/-- selector 与其对象层 component 的有限配对。 -/
structure AvatarSelectorComponent (σ : Signature) where
  selector : GuardLit
  component : Clause σ

namespace AvatarSelectorComponent

def ofLists {σ : Signature} :
    List GuardLit → List (Clause σ) → List (AvatarSelectorComponent σ)
  | selector :: selectors, component :: components =>
      ⟨selector, component⟩ :: ofLists selectors components
  | _, _ => []

theorem selectors_ofLists {σ : Signature} :
    ∀ {selectors : List GuardLit} {components : List (Clause σ)},
      selectors.length = components.length →
        (ofLists selectors components).map AvatarSelectorComponent.selector =
          selectors
  | [], [], _hLength => rfl
  | [], _ :: _, hLength => by simp at hLength
  | _ :: _, [], hLength => by simp at hLength
  | selector :: selectors, component :: components, hLength => by
      simp only [List.length_cons, Nat.succ.injEq] at hLength
      simp [ofLists, selectors_ofLists hLength]

theorem components_ofLists {σ : Signature} :
    ∀ {selectors : List GuardLit} {components : List (Clause σ)},
      selectors.length = components.length →
        (ofLists selectors components).map AvatarSelectorComponent.component =
          components
  | [], [], _hLength => rfl
  | [], _ :: _, hLength => by simp at hLength
  | _ :: _, [], hLength => by simp at hLength
  | selector :: selectors, component :: components, hLength => by
      simp only [List.length_cons, Nat.succ.injEq] at hLength
      simp [ofLists, components_ofLists hLength]

theorem getElem?_ofLists {σ : Signature}
    {selectors : List GuardLit} {components : List (Clause σ)}
    {index : Nat} {selector : GuardLit} {component : Clause σ}
    (hSelector : selectors[index]? = some selector)
    (hComponent : components[index]? = some component) :
    (ofLists selectors components)[index]? =
      some ⟨selector, component⟩ := by
  induction index generalizing selectors components with
  | zero =>
      cases selectors <;> cases components <;>
        simp [ofLists] at hSelector hComponent ⊢
      exact ⟨hSelector, hComponent⟩
  | succ index ih =>
      cases selectors <;> cases components <;>
        simp [ofLists] at hSelector hComponent ⊢
      exact ih hSelector hComponent

def selectorClause {σ : Signature}
    (entries : List (AvatarSelectorComponent σ)) :
    PropResolution.Clause :=
  (entries.map AvatarSelectorComponent.selector).toArray

/-- 同一 selector 变量在整张图中只能对应同一个 component。 -/
def Compatible {σ : Signature}
    (entries : List (AvatarSelectorComponent σ)) : Prop :=
  ∀ left, left ∈ entries → ∀ right, right ∈ entries →
    left.selector.var = right.selector.var →
      left.component = right.component

/-- 连续 selector 槽位表。 -/
structure Registry (σ : Signature) where
  slots : Array (Option (Clause σ)) := #[]
  deriving Inhabited

namespace Registry

def maxVarSucc {σ : Signature} :
    List (AvatarSelectorComponent σ) → Nat
  | [] => 0
  | entry :: rest =>
      Nat.max (entry.selector.var + 1) (maxVarSucc rest)

/-- 第一次出现的 component 占据槽位；冲突的重复项由 `check` 拒绝。 -/
def build {σ : Signature}
    (entries : List (AvatarSelectorComponent σ)) : Registry σ := Id.run do
  let mut slots : Array (Option (Clause σ)) :=
    Array.replicate (maxVarSucc entries) none
  for entry in entries do
    let index := entry.selector.var
    match slots[index]? with
    | some none =>
        slots := slots.setIfInBounds index (some entry.component)
    | _ =>
        pure ()
  return { slots := slots }

def entryCheck [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (registry : Registry σ) (entry : AvatarSelectorComponent σ) : Bool :=
  match registry.slots[entry.selector.var]? with
  | some (some component) => component.eq entry.component
  | _ => false

def entriesCheck [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (registry : Registry σ) : List (AvatarSelectorComponent σ) → Bool
  | [] => true
  | entry :: rest =>
      registry.entryCheck entry && registry.entriesCheck rest

def check [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (registry : Registry σ)
    (entries : List (AvatarSelectorComponent σ)) : Bool :=
  registry.entriesCheck entries

private theorem entryCheck_of_check [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {registry : Registry σ} {entries : List (AvatarSelectorComponent σ)}
    (h : registry.check entries = true)
    {entry : AvatarSelectorComponent σ} (hEntry : entry ∈ entries) :
    registry.entryCheck entry = true := by
  induction entries with
  | nil => simp at hEntry
  | cons head tail ih =>
      rcases Bool.and_eq_true_iff.mp h with ⟨hHead, hTail⟩
      rcases List.mem_cons.mp hEntry with rfl | hEntry
      · exact hHead
      · exact ih hTail hEntry

theorem check_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {registry : Registry σ} {entries : List (AvatarSelectorComponent σ)}
    (h : registry.check entries = true) : Compatible entries := by
  intro left hLeft right hRight hVariable
  have hLeftCheck := entryCheck_of_check h hLeft
  have hRightCheck := entryCheck_of_check h hRight
  have hSlot :
      registry.slots[right.selector.var]? =
        registry.slots[left.selector.var]? := by
    simp [hVariable]
  cases hLookup : registry.slots[left.selector.var]? with
  | none =>
      simp [entryCheck, hLookup] at hLeftCheck
  | some slot =>
      cases slot with
      | none =>
          simp [entryCheck, hLookup] at hLeftCheck
      | some component =>
          have hLeftEq : component.eq left.component = true := by
            simpa [entryCheck, hLookup] using hLeftCheck
          have hRightEq : component.eq right.component = true := by
            simpa [entryCheck, hLookup, hSlot] using hRightCheck
          exact
            (Clause.eq_sound component left.component hLeftEq).symm.trans
              (Clause.eq_sound component right.component hRightEq)

end Registry
end AvatarSelectorComponent

namespace AvatarSplitPayload

def componentClauses (payload : AvatarSplitPayload σ) : List (Clause σ) :=
  payload.partitions.toList.map (Clause.atIndices payload.source.clause)

def selectorComponents (payload : AvatarSplitPayload σ) :
    List (AvatarSelectorComponent σ) :=
  AvatarSelectorComponent.ofLists payload.selectors.toList
    payload.componentClauses

structure RegistryContract (payload : AvatarSplitPayload σ) : Prop where
  aligned :
    payload.selectors.toList.length = payload.componentClauses.length
  covers :
    Clause.Covers payload.source.clause payload.componentClauses
  pairwiseDisjoint :
    Clause.PairwiseSupportDisjoint payload.componentClauses
  selectorsPositive :
    ∀ selector, selector ∈ payload.selectors.toList →
      selector.positive = true

/-- 单个 split 的全部有限分解条件。 -/
def registryCheck [DecidableEq σ.SortSymbol]
    (payload : AvatarSplitPayload σ) : Bool :=
  payload.selectors.size == payload.partitions.size &&
    Clause.partitionCoversCheck payload.source.clause.literals.size
      payload.partitions &&
    Clause.pairwiseSupportDisjointCheck payload.componentClauses &&
      payload.selectors.all fun selector => selector.positive

theorem registryCheck_sound [DecidableEq σ.SortSymbol]
    {payload : AvatarSplitPayload σ}
    (hCheck : registryCheck payload = true) :
    RegistryContract payload := by
  simp only [registryCheck, Bool.and_eq_true_iff] at hCheck
  rcases hCheck with
    ⟨⟨⟨hAligned, hCovers⟩, hDisjoint⟩, hPositive⟩
  exact {
    aligned := by
      simpa [componentClauses] using hAligned
    covers := Clause.partitionCoversCheck_sound hCovers
    pairwiseDisjoint :=
      Clause.pairwiseSupportDisjointCheck_sound hDisjoint
    selectorsPositive := by
      intro selector hSelector
      have hArray : selector ∈ payload.selectors :=
        Array.mem_def.mpr hSelector
      rcases Array.mem_iff_getElem.mp hArray with
        ⟨index, hIndex, hGet⟩
      have hAt := Array.all_eq_true.mp hPositive index hIndex
      simpa [hGet] using hAt
  }

theorem RegistryContract.selectorComponentsPositive
    {payload : AvatarSplitPayload σ}
    (hContract : RegistryContract payload) :
    ∀ entry, entry ∈ payload.selectorComponents →
      entry.selector.positive = true := by
  intro entry hEntry
  apply hContract.selectorsPositive
  have hMapped :
      entry.selector ∈
        payload.selectorComponents.map AvatarSelectorComponent.selector :=
    List.mem_map.mpr ⟨entry, hEntry, rfl⟩
  have hProjection :
      payload.selectorComponents.map AvatarSelectorComponent.selector =
        payload.selectors.toList := by
    simpa [selectorComponents] using
      AvatarSelectorComponent.selectors_ofLists hContract.aligned
  rw [hProjection] at hMapped
  exact hMapped

theorem selectorComponent_mem
    {payload : AvatarSplitPayload σ}
    {index : Nat} {indices : Array Nat} {selector : GuardLit}
    (hIndices : payload.partitions[index]? = some indices)
    (hSelector : AvatarSplit.selectorAt? payload.selectors index = some selector) :
    ⟨selector, Clause.atIndices payload.source.clause indices⟩ ∈
      payload.selectorComponents := by
  have hSelectorList :
      payload.selectors.toList[index]? = some selector := by
    simpa [AvatarSplit.selectorAt?] using hSelector
  have hComponentList :
      payload.componentClauses[index]? =
        some (Clause.atIndices payload.source.clause indices) := by
    have hPartitionList :
        payload.partitions.toList[index]? = some indices := by
      simpa using hIndices
    simp [componentClauses, hPartitionList]
  have hEntryGet :
      payload.selectorComponents[index]? =
        some ⟨selector, Clause.atIndices payload.source.clause indices⟩ :=
    AvatarSelectorComponent.getElem?_ofLists hSelectorList hComponentList
  rcases List.getElem?_eq_some_iff.mp hEntryGet with
    ⟨hIndex, hGet⟩
  rw [← hGet]
  exact List.getElem_mem hIndex

end AvatarSplitPayload

namespace PropInitialJustification

def avatarSoundnessSupported : PropInitialJustification σ → Bool
  | .parentClause _ => true
  | .guardActivationClause _ => true
  | .propLearnedClause _ => true
  | .avatarSkeleton _ => true

end PropInitialJustification

namespace PropositionalClosurePayload

def avatarSoundnessSupported (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialJustifications.all
    PropInitialJustification.avatarSoundnessSupported

end PropositionalClosurePayload

namespace Payload

def avatarSelectorComponents : Payload σ →
    List (AvatarSelectorComponent σ)
  | .avatarSplit payload => payload.selectorComponents
  | _ => []

def avatarRegistryLocalCheck [DecidableEq σ.SortSymbol] :
    Payload σ → Bool
  | .avatarSplit payload => payload.registryCheck
  | _ => true

/-- AVATAR 回放当前允许的有限 payload 片段。 -/
def avatarSoundnessSupported : Payload σ → Bool
  | .source _ => true
  | .avatarSplit _ => true
  | .avatarComponent _ => true
  | .localRule payload => payload.guardedSoundnessSupported
  | .theoryConflict _ => true
  | .propositionalLearnedClause _ => true
  | .residualCdcl payload => payload.avatarSoundnessSupported

end Payload

namespace DAG

def avatarSelectorRegistry (dag : DAG σ) :
    List (AvatarSelectorComponent σ) :=
  dag.nodes.toList.flatMap fun node =>
    node.payload.avatarSelectorComponents

def nodeAvatarRegistryLocalCheck [DecidableEq σ.SortSymbol]
    (node : Node σ) : Bool :=
  node.payload.avatarRegistryLocalCheck

def nodeAvatarSoundnessSupported (node : Node σ) : Bool :=
  node.payload.avatarSoundnessSupported

def avatarSoundnessSupported (dag : DAG σ) : Bool :=
  dag.nodes.all nodeAvatarSoundnessSupported

/-- AVATAR 的逐 split 局部检查与全图 selector 唯一性检查。 -/
def avatarRegistryCheckWith [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (registry : AvatarSelectorComponent.Registry σ) : Bool :=
  dag.nodes.all nodeAvatarRegistryLocalCheck &&
    registry.check dag.avatarSelectorRegistry

theorem mem_avatarSelectorRegistry_of_split
    {dag : DAG σ} {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    {entry : AvatarSelectorComponent σ}
    (hNode : dag.node? splitId = some splitNode)
    (hPayload : splitNode.payload = .avatarSplit payload)
    (hEntry : entry ∈ payload.selectorComponents) :
    entry ∈ dag.avatarSelectorRegistry := by
  have hNodeMem : splitNode ∈ dag.nodes.toList := by
    rcases getElem?_eq_some_iff.mp hNode with ⟨hIndex, hGet⟩
    have hArray : splitNode ∈ dag.nodes := by
      rw [← hGet]
      exact Array.getElem_mem hIndex
    exact Array.mem_def.mp hArray
  unfold avatarSelectorRegistry
  apply List.mem_flatMap.mpr
  exact ⟨splitNode, hNodeMem, by
    simpa [Payload.avatarSelectorComponents, hPayload] using hEntry⟩

theorem avatarSplitRegistryCheck_of_eq_true
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    {dag : DAG σ}
    {registry : AvatarSelectorComponent.Registry σ}
    (hCheck : avatarRegistryCheckWith dag registry = true)
    {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    (hNode : dag.node? splitId = some splitNode)
    (hPayload : splitNode.payload = .avatarSplit payload) :
    payload.registryCheck = true := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hNodes, _hCompatible⟩
  rcases getElem?_eq_some_iff.mp hNode with ⟨hIndex, hGet⟩
  have hAt := Array.all_eq_true.mp hNodes splitId hIndex
  have hGet' : dag.nodes[splitId] = splitNode := by
    simpa [graphView] using! hGet
  rw [hGet'] at hAt
  simpa [hPayload, nodeAvatarRegistryLocalCheck,
    Payload.avatarRegistryLocalCheck] using hAt

theorem avatarSplitRegistryContract
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    {dag : DAG σ}
    {registry : AvatarSelectorComponent.Registry σ}
    (hCheck : avatarRegistryCheckWith dag registry = true)
    {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    (hNode : dag.node? splitId = some splitNode)
    (hPayload : splitNode.payload = .avatarSplit payload) :
    AvatarSplitPayload.RegistryContract payload :=
  AvatarSplitPayload.registryCheck_sound
    (avatarSplitRegistryCheck_of_eq_true hCheck hNode hPayload)

theorem avatarSelectorRegistry_positive
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    {dag : DAG σ}
    {registry : AvatarSelectorComponent.Registry σ}
    (hCheck : avatarRegistryCheckWith dag registry = true) :
    ∀ entry, entry ∈ dag.avatarSelectorRegistry →
      entry.selector.positive = true := by
  intro entry hEntry
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hNodes, _hCompatible⟩
  rcases List.mem_flatMap.mp hEntry with
    ⟨node, hNodeMem, hPayloadEntry⟩
  have hNodeLocal : node.payload.avatarRegistryLocalCheck = true := by
    have hArray : node ∈ dag.nodes := Array.mem_def.mpr hNodeMem
    rcases Array.mem_iff_getElem.mp hArray with
      ⟨index, hIndex, hGet⟩
    have hAt := Array.all_eq_true.mp hNodes index hIndex
    simpa [hGet, nodeAvatarRegistryLocalCheck] using hAt
  cases hPayload : node.payload with
  | avatarSplit payload =>
      have hLocal : payload.registryCheck = true := by
        simpa [Payload.avatarRegistryLocalCheck, hPayload] using hNodeLocal
      have hEntryLocal : entry ∈ payload.selectorComponents := by
        simpa [Payload.avatarSelectorComponents, hPayload] using hPayloadEntry
      exact AvatarSplitPayload.RegistryContract.selectorComponentsPositive
        (AvatarSplitPayload.registryCheck_sound hLocal) entry hEntryLocal
  | source _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | avatarComponent _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | localRule _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | theoryConflict _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | propositionalLearnedClause _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | residualCdcl _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry

theorem avatarSelectorRegistry_compatible
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    {dag : DAG σ}
    {registry : AvatarSelectorComponent.Registry σ}
    (hCheck : avatarRegistryCheckWith dag registry = true) :
    AvatarSelectorComponent.Compatible dag.avatarSelectorRegistry :=
  AvatarSelectorComponent.Registry.check_sound
    (Bool.and_eq_true_iff.mp hCheck).2

end DAG

end DAGCertificateSignature

end DAGCertificate
end Automation
end YesMetaZFC
