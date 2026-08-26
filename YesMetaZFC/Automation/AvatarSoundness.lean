import YesMetaZFC.Automation.DAGCertificate
import YesMetaZFC.Automation.Guards
/-!
# AVATAR fixed-bound-stack 整图 soundness
AVATAR selector 不能解释为“component 在当前自由变量环境下为真”。DAG 的 guarded
不变量固定一个命题 valuation，却量化所有自由变量环境，因此 selector 的正确含义是：
> 在固定 LN bound stack 上，该 component 对所有自由变量环境都成立。
本模块证明有限变量不交 components 的主分解定理，把它连接到命题 selector
skeleton，并给出 residual CDCL 专用的 AVATAR 整图拓扑 soundness 与空 root
contradiction。通用 guarded 主线仍不开放 `avatarComponent`；这里使用独立的
fixed-bound-stack 支持判定，并显式消费全局 selector registry 的 component/split
语义合同。checker 到全局 registry 构造的桥接可以随后独立强化。
-/
namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
universe x
open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.Automation.LogicSoundness
namespace Clause
def ValidOnBoundStack {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (clause : Clause σ) : Prop :=
  ∀ env, Logic.FirstOrder.Env.SameBoundStack env base → Satisfies env clause
def Covers {σ : Signature} (source : Clause σ) (components : List (Clause σ)) : Prop := (∀ literal, literal ∈ source.literals.toList →
    ∃ component, component ∈ components ∧ literal ∈ component.literals.toList) ∧
  ∀ component, component ∈ components →
    ∀ literal, literal ∈ component.literals.toList →
      literal ∈ source.literals.toList
def PairwiseSupportDisjoint {σ : Signature} : List (Clause σ) → Prop
  | [] => True
  | clause :: rest =>
      (∀ other, other ∈ rest →
        Logic.FirstOrder.FreeVariable.Support.Disjoint
          clause.freeSupport other.freeSupport) ∧
      PairwiseSupportDisjoint rest
theorem satisfies_iff_exists_component_of_covers {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {source : Clause σ} {components : List (Clause σ)} (hCovers : Covers source components) :
    Satisfies env source ↔
      ∃ component, component ∈ components ∧ Satisfies env component := by
  constructor
  · intro hSource
    rcases satisfies_iff_exists_literal.mp hSource with
      ⟨literal, hMem, hLiteral⟩
    rcases hCovers.1 literal hMem with
      ⟨component, hComponent, hLiteralMem⟩
    exact
      ⟨component, hComponent,
        satisfies_iff_exists_literal.mpr
          ⟨literal, hLiteralMem, hLiteral⟩⟩
  · rintro ⟨component, hComponent, hSat⟩
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    exact satisfies_iff_exists_literal.mpr
      ⟨literal, hCovers.2 component hComponent literal hMem, hLiteral⟩
private theorem exists_counterexample_of_not_valid {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {base : SetLevel.EnvAt.{x} M} {clause : Clause σ} (hNotValid : ¬ ValidOnBoundStack base clause) :
    ∃ env, Logic.FirstOrder.Env.SameBoundStack env base ∧
      ¬ Satisfies env clause := by
  apply Classical.byContradiction
  intro hNoCounterexample
  apply hNotValid
  intro env hBound
  apply Classical.byContradiction
  intro hNotSat
  exact hNoCounterexample ⟨env, hBound, hNotSat⟩
/--
若每个两两变量不交的 component 都不是全环境有效的，则可合并各自反例环境，
得到一个同时否定所有 components 的共同环境。
-/
theorem exists_common_counterexample {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (components : List (Clause σ))
    (hDisjoint : PairwiseSupportDisjoint components) (hNotValid : ∀ component, component ∈ components →
      ¬ ValidOnBoundStack base component) :
    ∃ env, Logic.FirstOrder.Env.SameBoundStack env base ∧
      ∀ component, component ∈ components → ¬ Satisfies env component := by
  induction components with
  | nil =>
      exact
        ⟨base, Logic.FirstOrder.Env.SameBoundStack.refl base,
          by
            intro component hMem
            cases hMem⟩
  | cons head tail ih =>
      rcases hDisjoint with ⟨hHeadDisjoint, hTailDisjoint⟩
      rcases exists_counterexample_of_not_valid (hNotValid head List.mem_cons_self) with
        ⟨headEnv, hHeadBound, hHeadFalse⟩
      have hTailNotValid : ∀ component, component ∈ tail →
          ¬ ValidOnBoundStack base component := by
        intro component hMem
        exact hNotValid component (List.mem_cons_of_mem head hMem)
      rcases ih hTailDisjoint hTailNotValid with
        ⟨tailEnv, hTailBound, hTailFalse⟩
      let merged :=
        Logic.FirstOrder.Env.overlay head.freeSupport headEnv tailEnv
      refine ⟨merged, ?_, ?_⟩
      · exact hTailBound
      · intro component hMem
        rcases List.mem_cons.mp hMem with hEq | hTailMem
        · cases hEq
          intro hSat
          have hBound :
              Logic.FirstOrder.Env.SameBoundStack tailEnv headEnv :=
            hTailBound.trans hHeadBound.symm
          have hAgree :=
            Logic.FirstOrder.Env.overlay_agreesOn_source (support := head.freeSupport) hBound
          exact hHeadFalse ((satisfies_iff_of_agreesOn head hAgree).mp hSat)
        · intro hSat
          have hAgree :=
            Logic.FirstOrder.Env.overlay_agreesOn_base_of_disjoint (source := headEnv) (base := tailEnv) (hHeadDisjoint component hTailMem)
          exact hTailFalse component hTailMem ((satisfies_iff_of_agreesOn component hAgree).mp hSat)
/--
AVATAR component decomposition 主定理。
当 components 双向覆盖 source 且自由变量支持两两不交时，source 在固定 bound stack
上全环境有效，当且仅当某个 component 在该 bound stack 上全环境有效。
-/
theorem validOnBoundStack_iff_exists_component {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (source : Clause σ)
    (components : List (Clause σ)) (hCovers : Covers source components) (hDisjoint : PairwiseSupportDisjoint components) :
    ValidOnBoundStack base source ↔
      ∃ component, component ∈ components ∧
        ValidOnBoundStack base component := by
  constructor
  · intro hSource
    apply Classical.byContradiction
    intro hNoComponent
    have hNotValid : ∀ component, component ∈ components →
        ¬ ValidOnBoundStack base component := by
      intro component hMem hValid
      exact hNoComponent ⟨component, hMem, hValid⟩
    rcases exists_common_counterexample base components hDisjoint hNotValid with
      ⟨env, hBound, hFalse⟩
    have hSourceSat := hSource env hBound
    rcases (satisfies_iff_exists_component_of_covers hCovers).mp hSourceSat with
      ⟨component, hMem, hSat⟩
    exact hFalse component hMem hSat
  · rintro ⟨component, hMem, hValid⟩ env hBound
    apply (satisfies_iff_exists_component_of_covers hCovers).mpr
    exact ⟨component, hMem, hValid env hBound⟩
end Clause
namespace Node
/--
固定模型与 LN bound stack 的 guarded 节点不变量。
AVATAR selector valuation 依赖当前模型与 bound stack，因此这里先固定二者，再只量化
具有同一 bound stack 的自由变量环境，避免把单个反模型诱导的 valuation 错误提升为
跨模型不变量。
-/
def BoundStackGuardedInvariant {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (node : Node σ) : Prop :=
  ∀ env, Logic.FirstOrder.Env.SameBoundStack env base →
    GuardsHold valuation node.guards → Clause.Satisfies env node.conclusion
theorem boundStackGuardedInvariant_of_selector {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation)
    (node : Node σ) (selector : GuardLit) (hGuardEq : Guards.eq node.guards #[selector] = true) (hSemantic :
      selector.Holds valuation ↔
        Clause.ValidOnBoundStack base node.conclusion) :
    BoundStackGuardedInvariant base valuation node := by
  intro env hBound hGuards
  have hSingleton : GuardsHold valuation #[selector] :=
    GuardsHold.of_guardSetEq hGuardEq hGuards
  have hSelectorMem :
      selector ∈ (Guards.canonical #[selector]).toList := by
    apply PropResolution.mem_canonicalClause_of_mem
    simp
  exact (hSemantic.mp (hSingleton selector hSelectorMem)) env hBound
end Node
namespace PropInitialJustification
def avatarSoundnessSupported {σ : Signature} :
    PropInitialJustification σ → Bool
  | .parentClause _ => true
  | .guardActivationClause _ => true
  | .propLearnedClause _ => true
  | .avatarSkeleton _ => true
end PropInitialJustification
namespace PropositionalClosurePayload
def avatarSoundnessSupported {σ : Signature} (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialJustifications.all
    PropInitialJustification.avatarSoundnessSupported
end PropositionalClosurePayload
namespace Payload
/--
AVATAR fixed-bound-stack 整图允许的 payload。
所有 substitution 与 standardize-apart 版本都通过固定 bound-stack 环境搬运合同回放。
-/
def avatarSoundnessSupported {σ : Signature} : Payload σ → Bool
  | .source _ => true
  | .avatarSplit _ => true
  | .avatarComponent _ => true
  | .localRule payload => payload.guardedSoundnessSupported
  | .theoryConflict _ => true
  | .propositionalLearnedClause _ => true
  | .residualCdcl payload => payload.avatarSoundnessSupported
end Payload
namespace DAG
def nodeAvatarSoundnessSupported {σ : Signature} (node : Node σ) : Bool :=
  node.payload.avatarSoundnessSupported
def avatarSoundnessSupported {σ : Signature} (dag : DAG σ) : Bool :=
  dag.nodes.all nodeAvatarSoundnessSupported
def BoundStackGuardedInvariant {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (dag : DAG σ) (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) : Prop :=
  ∀ index (hIndex : index < dag.nodes.size),
    Node.BoundStackGuardedInvariant base valuation (dag.nodeAt index hIndex)
theorem avatarSoundnessSupported_of_eq_true {σ : Signature} {dag : DAG σ} (hSupported : dag.avatarSoundnessSupported = true) :
    ∀ index (hIndex : index < dag.nodes.size), (dag.nodeAt index hIndex).payload.avatarSoundnessSupported = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hSupported
  simpa [avatarSoundnessSupported, nodeAvatarSoundnessSupported, nodeAt] using
    hAll index hIndex
theorem avatarSoundnessSupported_eq_true_of_nodes {σ : Signature} (dag : DAG σ) (checked : CheckedList nodeAvatarSoundnessSupported dag.nodes.toList) :
    dag.avatarSoundnessSupported = true := by
  change dag.nodes.all nodeAvatarSoundnessSupported = true
  rw [← Array.all_toList]
  exact checked.all_eq_true
end DAG
/-! ## Selector valuation -/
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
      selectors.length = components.length → (ofLists selectors components).map AvatarSelectorComponent.selector =
          selectors
  | [], [], _hLength => rfl
  | [], _ :: _, hLength => by simp at hLength
  | _ :: _, [], hLength => by simp at hLength
  | selector :: selectors, component :: components, hLength => by
      simp only [List.length_cons, Nat.succ.injEq] at hLength
      simp [ofLists, selectors_ofLists hLength]
theorem components_ofLists {σ : Signature} :
    ∀ {selectors : List GuardLit} {components : List (Clause σ)},
      selectors.length = components.length → (ofLists selectors components).map AvatarSelectorComponent.component =
          components
  | [], [], _hLength => rfl
  | [], _ :: _, hLength => by simp at hLength
  | _ :: _, [], hLength => by simp at hLength
  | selector :: selectors, component :: components, hLength => by
      simp only [List.length_cons, Nat.succ.injEq] at hLength
      simp [ofLists, components_ofLists hLength]
theorem getElem?_ofLists {σ : Signature}
    {selectors : List GuardLit} {components : List (Clause σ)}
    {index : Nat} {selector : GuardLit} {component : Clause σ} (hSelector : selectors[index]? = some selector)
    (hComponent : components[index]? = some component) : (ofLists selectors components)[index]? =
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
def selectorClause {σ : Signature} (entries : List (AvatarSelectorComponent σ)) : PropResolution.Clause :=
  (entries.map AvatarSelectorComponent.selector).toArray
/--
固定 bound stack 上的 AVATAR selector valuation。
一个命题变量为真，当且仅当某个登记在该变量下的 component 对所有同 bound stack
环境都成立。这里刻意不读取“当前自由变量环境”。
-/
def valuation {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (entries : List (AvatarSelectorComponent σ)) :
    PropResolution.Valuation :=
  fun selectorVar =>
    ∃ entry, entry ∈ entries ∧ entry.selector.var = selectorVar ∧
      Clause.ValidOnBoundStack base entry.component
def Compatible {σ : Signature} (entries : List (AvatarSelectorComponent σ)) : Prop :=
  ∀ left, left ∈ entries → ∀ right, right ∈ entries →
    left.selector.var = right.selector.var → left.component = right.component
/--
selector valuation 的逐项精确语义。
在正 selector 与映射一致性合同下，一个 selector 为真当且仅当它自己的 component
在固定 bound stack 上全环境有效。
-/
theorem holds_valuation_iff_component_valid {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (entries : List (AvatarSelectorComponent σ))
    (hPositive : ∀ item, item ∈ entries → item.selector.positive = true) (hCompatible : Compatible entries) {entry : AvatarSelectorComponent σ}
    (hEntry : entry ∈ entries) :
    entry.selector.Holds (valuation base entries) ↔
      Clause.ValidOnBoundStack base entry.component := by
  constructor
  · intro hSelector
    have hValue : valuation base entries entry.selector.var := by
      simpa [PropResolution.Lit.Holds, hPositive entry hEntry] using hSelector
    rcases hValue with
      ⟨validEntry, hValidEntry, hVariable, hValid⟩
    have hComponent :
        validEntry.component = entry.component :=
      hCompatible validEntry hValidEntry entry hEntry hVariable
    simpa only [hComponent] using hValid
  · intro hValid
    have hValue : valuation base entries entry.selector.var :=
      ⟨entry, hEntry, rfl, hValid⟩
    simpa [PropResolution.Lit.Holds, hPositive entry hEntry] using hValue
theorem selectorClause_satisfies_iff_exists_valid {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (entries : List (AvatarSelectorComponent σ))
    (hPositive : ∀ entry, entry ∈ entries → entry.selector.positive = true) :
    PropResolution.Clause.Satisfies (valuation base entries) (selectorClause entries) ↔
      ∃ entry, entry ∈ entries ∧
        Clause.ValidOnBoundStack base entry.component := by
  constructor
  · rintro ⟨selector, hSelectorMem, hSelector⟩
    have hSelectorMem' :
        selector ∈ entries.map AvatarSelectorComponent.selector := by
      simpa [selectorClause] using hSelectorMem
    rcases List.mem_map.mp hSelectorMem' with
      ⟨entry, hEntryMem, hEntrySelector⟩
    cases hEntrySelector
    have hValue : valuation base entries entry.selector.var := by
      simpa [PropResolution.Lit.Holds, hPositive entry hEntryMem] using hSelector
    rcases hValue with ⟨validEntry, hValidMem, _hVariable, hValid⟩
    exact ⟨validEntry, hValidMem, hValid⟩
  · rintro ⟨entry, hEntryMem, hValid⟩
    refine ⟨entry.selector, ?_, ?_⟩
    · have hMapped :
          entry.selector ∈ entries.map AvatarSelectorComponent.selector :=
        List.mem_map.mpr ⟨entry, hEntryMem, rfl⟩
      simpa [selectorClause] using hMapped
    · have hValue : valuation base entries entry.selector.var :=
        ⟨entry, hEntryMem, rfl, hValid⟩
      simpa [PropResolution.Lit.Holds, hPositive entry hEntryMem] using hValue
end AvatarSelectorComponent
namespace AvatarSplitPayload
def componentClauses {σ : Signature} (payload : AvatarSplitPayload σ) :
    List (Clause σ) :=
  payload.partitions.toList.map (Clause.atIndices payload.source.clause)
def selectorComponents {σ : Signature} (payload : AvatarSplitPayload σ) :
    List (AvatarSelectorComponent σ) :=
  AvatarSelectorComponent.ofLists payload.selectors.toList payload.componentClauses
structure DecompositionContract {σ : Signature} (payload : AvatarSplitPayload σ) :
    Prop where
  aligned :
    payload.selectors.toList.length = payload.componentClauses.length
  covers :
    Clause.Covers payload.source.clause payload.componentClauses
  pairwiseDisjoint :
    Clause.PairwiseSupportDisjoint payload.componentClauses
  selectorsPositive :
    ∀ selector, selector ∈ payload.selectors.toList → selector.positive = true
  selectorCompatible :
    AvatarSelectorComponent.Compatible payload.selectorComponents
theorem selectorClause_selectorComponents {σ : Signature}
    {payload : AvatarSplitPayload σ} (hAligned :
      payload.selectors.toList.length = payload.componentClauses.length) :
    AvatarSelectorComponent.selectorClause payload.selectorComponents =
      payload.selectors := by
  unfold selectorComponents AvatarSelectorComponent.selectorClause
  rw [AvatarSelectorComponent.selectors_ofLists hAligned]
theorem components_selectorComponents {σ : Signature}
    {payload : AvatarSplitPayload σ} (hAligned :
      payload.selectors.toList.length = payload.componentClauses.length) :
    payload.selectorComponents.map AvatarSelectorComponent.component =
      payload.componentClauses :=
  AvatarSelectorComponent.components_ofLists hAligned
theorem selectorComponents_positive {σ : Signature}
    {payload : AvatarSplitPayload σ} (hContract : DecompositionContract payload) :
    ∀ entry, entry ∈ payload.selectorComponents →
      entry.selector.positive = true := by
  intro entry hEntry
  apply hContract.selectorsPositive
  have hMapped :
      entry.selector ∈
        payload.selectorComponents.map AvatarSelectorComponent.selector :=
    List.mem_map.mpr ⟨entry, hEntry, rfl⟩
  have hSelectorProjection :
      payload.selectorComponents.map AvatarSelectorComponent.selector =
        payload.selectors.toList := by
    simpa [selectorComponents] using
      AvatarSelectorComponent.selectors_ofLists hContract.aligned
  rw [hSelectorProjection] at hMapped
  exact hMapped
theorem selector_holds_iff_component_valid {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) {payload : AvatarSplitPayload σ}
    (hContract : DecompositionContract payload)
    {entry : AvatarSelectorComponent σ} (hEntry : entry ∈ payload.selectorComponents) :
    entry.selector.Holds (AvatarSelectorComponent.valuation base payload.selectorComponents) ↔
      Clause.ValidOnBoundStack base entry.component :=
  AvatarSelectorComponent.holds_valuation_iff_component_valid
    base payload.selectorComponents (selectorComponents_positive hContract)
    hContract.selectorCompatible hEntry
theorem check_source {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {payload : AvatarSplitPayload σ}
    {conclusion : Clause σ} (hCheck : payload.check parents conclusion = true) :
    payload.source.id ∈ parents.toList ∧
      payload.source.clause = conclusion := by
  unfold check at hCheck
  simp only [Bool.and_eq_true] at hCheck
  exact
    ⟨ParentClause.mem_toList_of_idIn hCheck.1.2,
      Clause.eq_sound _ _ hCheck.2⟩
end AvatarSplitPayload
namespace AvatarComponentPayload
theorem check_split_mem {σ : Signature}
    {parents : Array NodeId} {payload : AvatarComponentPayload σ} (hCheck : payload.check parents = true) :
    payload.split ∈ parents.toList := by
  unfold check at hCheck
  simp only [Bool.and_eq_true] at hCheck
  have hArray : payload.split ∈ parents := by
    simpa using hCheck.2
  exact Array.mem_def.mp hArray
end AvatarComponentPayload
namespace DAG
theorem avatarSplitNodeOk_sound {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {node : Node σ}
    {payload : AvatarSplitPayload σ} (hOk : dag.avatarSplitNodeOk node payload = true) :
    node.unguarded = true ∧
      dag.parentSnapshotChecked payload.source = true ∧
        ∃ sourceNode initialIndex,
          dag.node? payload.source.id = some sourceNode ∧
            sourceNode.unguarded = true ∧
              sourceNode.payload = .source initialIndex := by
  unfold avatarSplitNodeOk at hOk
  split at hOk <;> simp_all
  split at hOk <;> simp_all
theorem avatarComponentNodeOk_sound {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {node : Node σ}
    {payload : AvatarComponentPayload σ} (hOk : dag.avatarComponentNodeOk node payload = true) :
    ∃ splitNode splitPayload indices selector,
      dag.node? payload.split = some splitNode ∧
        splitNode.payload = .avatarSplit splitPayload ∧
          splitPayload.partitions[payload.componentIndex]? = some indices ∧
            AvatarSplit.selectorAt? splitPayload.selectors
                payload.componentIndex =
              some selector ∧
              splitNode.unguarded = true ∧
                node.conclusion =
                    Clause.atIndices splitNode.conclusion indices ∧
                  Guards.eq node.guards #[selector] = true := by
  unfold avatarComponentNodeOk at hOk
  split at hOk <;> simp_all
  split at hOk <;> simp_all
  split at hOk <;> simp_all
  exact Clause.eq_sound _ _ hOk.2.1
end DAG
/--
全局 selector registry 对 component 槽位应提供的精确语义。
当前专用拓扑步骤只消费这个合同；后续跨 split 的 registry checker 可以独立证明它，
无需把局部 selector valuation 固化进 DAG 的通用 guarded 不变量。
-/
def AvatarComponentSelectorSemantics {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} (dag : DAG σ) (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) : Prop :=
  ∀ {splitId splitNode splitPayload componentIndex indices selector},
    dag.node? splitId = some splitNode →
      splitNode.payload = .avatarSplit splitPayload →
        splitPayload.partitions[componentIndex]? = some indices →
          AvatarSplit.selectorAt? splitPayload.selectors componentIndex =
              some selector → (selector.Holds valuation ↔
              Clause.ValidOnBoundStack base (Clause.atIndices splitPayload.source.clause indices))
/--
全局 selector registry 对 split skeleton 应提供的语义。
这里使用 canonical skeleton，因为 residual CDCL checker 会把 payload selector 表规范化后
登记为 initial clause。
-/
def AvatarSplitSelectorSemantics {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} (dag : DAG σ) (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) : Prop :=
  ∀ {splitId splitNode splitPayload},
    dag.node? splitId = some splitNode →
      splitNode.payload = .avatarSplit splitPayload → (Clause.ValidOnBoundStack base splitPayload.source.clause ↔
          PropResolution.Clause.Satisfies valuation (PropResolution.canonicalClause splitPayload.selectors))
def AvatarComponentSelectorSemanticsAt {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} (dag : DAG σ) (splitId componentIndex : Nat)
    (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) : Prop :=
  ∀ {splitNode splitPayload indices selector},
    dag.node? splitId = some splitNode →
      splitNode.payload = .avatarSplit splitPayload →
        splitPayload.partitions[componentIndex]? = some indices →
          AvatarSplit.selectorAt? splitPayload.selectors componentIndex =
              some selector → (selector.Holds valuation ↔
              Clause.ValidOnBoundStack base (Clause.atIndices splitPayload.source.clause indices))
namespace AvatarComponentSelectorSemantics
theorem atSlot {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {dag : DAG σ} {base : SetLevel.EnvAt.{x} M}
    {valuation : PropResolution.Valuation} (hSemantics : AvatarComponentSelectorSemantics dag base valuation) (splitId componentIndex : Nat) :
    AvatarComponentSelectorSemanticsAt
      dag splitId componentIndex base valuation :=
  fun {_ _ _ _} hNode hPayload hIndices hSelector =>
    hSemantics hNode hPayload hIndices hSelector
end AvatarComponentSelectorSemantics
namespace AvatarSplitPayload
end AvatarSplitPayload
namespace CheckedDAG
theorem sourceBoundStackGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (hProblem : cert.dag.problem.Valid base)
    (index : Nat) (hIndex : index < cert.dag.nodes.size) (_hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (initialIndex : Nat) (hSource :
      (cert.dag.nodeAt index hIndex).payload = .source initialIndex) :
    Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hSource] at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with
    ⟨_hParentsEmpty, hSourceCheck⟩
  cases hLookup : cert.dag.problem.initialClauses[initialIndex]? with
  | none =>
      simp [hLookup] at hSourceCheck
  | some initial =>
      have hConclusion : (cert.dag.nodeAt index hIndex).conclusion = initial :=
        Clause.eq_sound _ initial (by
          simpa [Payload.check, hLookup] using hSourceCheck)
      intro env hBound _hGuards
      rw [hConclusion]
      exact hProblem env hBound initialIndex initial hLookup
theorem avatarSplitSnapshotChecked {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) (index : Nat) (hIndex : index < cert.dag.nodes.size) (payload : AvatarSplitPayload σ) (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .avatarSplit payload) :
    cert.dag.parentSnapshotChecked payload.source = true := by
  have hAllNodes := Array.all_eq_true.mp cert.contract.parent_snapshots_checked
  have hNode : ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hPayload] at hNode
  simpa [Payload.parentClauses, AvatarSplitPayload.parentClauses] using hNode
theorem avatarSplitBoundStackGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : AvatarSplitPayload σ) (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .avatarSplit payload) :
    Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hPayload] at hPayloadCheck
  have hSplitCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  rcases AvatarSplitPayload.check_source hSplitCheck with
    ⟨hSourceMem, hDescriptorConclusion⟩
  let hSourceLt :=
    cert.contract.parents_before index hIndex payload.source.id hSourceMem
  let hSourceSize := Nat.lt_trans hSourceLt hIndex
  have hSourceInvariant :
      Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt payload.source.id hSourceSize) :=
    hParents payload.source.id hSourceMem
  have hSnapshot :=
    cert.avatarSplitSnapshotChecked index hIndex payload hPayload
  have hSourceClause :=
    cert.parentClause_eq_nodeAt_of_snapshot
      payload.source hSourceSize hSnapshot
  have hNodeOk : cert.dag.avatarSplitNodeOk (cert.dag.nodeAt index hIndex) payload = true := by
    have hGuards := (cert.contract.node_contract index hIndex).guards_checked
    simpa [DAG.localNodeGuardsOk, hPayload] using hGuards
  rcases DAG.avatarSplitNodeOk_sound hNodeOk with
    ⟨_hDescriptorUnguarded, _hSnapshot', sourceNode, _initialIndex,
      hSourceSome, hSourceUnguarded, _hSourcePayload⟩
  have hSourceNodeEq :
      sourceNode = cert.dag.nodeAt payload.source.id hSourceSize := by
    exact Option.some.inj (hSourceSome.symm.trans (cert.dag.node?_eq_some_nodeAt hSourceSize))
  have hSourceUnguarded' : (cert.dag.nodeAt payload.source.id hSourceSize).unguarded = true := by
    simpa [← hSourceNodeEq] using hSourceUnguarded
  have hSourceGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt payload.source.id hSourceSize).guards :=
    Node.GuardsHold.of_isEmpty (by
      simpa [Node.unguarded] using hSourceUnguarded')
  have hConclusion : (cert.dag.nodeAt payload.source.id hSourceSize).conclusion = (cert.dag.nodeAt index hIndex).conclusion := by
    exact hSourceClause.symm.trans hDescriptorConclusion
  intro env hBound _hGuards
  have hSourceSat := hSourceInvariant env hBound hSourceGuards
  simpa [hConclusion] using hSourceSat
/--
component 节点的固定 bound-stack 拓扑步骤。
结论字句和 singleton guard 均由父 split descriptor 机械复算；selector 的对象语义
只通过当前 split/component 槽位的精确语义合同消费。
-/
theorem avatarComponentBoundStackGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (_hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : AvatarComponentPayload σ) (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .avatarComponent payload) (hSelectorSemantics :
      AvatarComponentSelectorSemanticsAt cert.dag payload.split
        payload.componentIndex base valuation) :
    Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hPayload] at hPayloadCheck
  have hComponentCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents = true := by
    simpa [Payload.check] using hPayloadCheck
  have hSplitMem :=
    AvatarComponentPayload.check_split_mem hComponentCheck
  let hSplitLt :=
    cert.contract.parents_before index hIndex payload.split hSplitMem
  let hSplitSize := Nat.lt_trans hSplitLt hIndex
  have hNodeOk : cert.dag.avatarComponentNodeOk (cert.dag.nodeAt index hIndex) payload = true := by
    have hGuards := (cert.contract.node_contract index hIndex).guards_checked
    simpa [DAG.localNodeGuardsOk, hPayload] using hGuards
  rcases DAG.avatarComponentNodeOk_sound hNodeOk with
    ⟨splitNode, splitPayload, indices, selector, hSplitSome,
      hSplitPayload, hIndices, hSelector, _hSplitUnguarded,
      hComponentConclusion, hGuardEq⟩
  have hSplitNodeEq :
      splitNode = cert.dag.nodeAt payload.split hSplitSize := by
    exact Option.some.inj (hSplitSome.symm.trans (cert.dag.node?_eq_some_nodeAt hSplitSize))
  have hSplitPayload' : (cert.dag.nodeAt payload.split hSplitSize).payload =
        .avatarSplit splitPayload := by
    simpa [← hSplitNodeEq] using hSplitPayload
  have hSplitPayloadCheck := (cert.contract.node_contract payload.split hSplitSize).payload_checked
  rw [hSplitPayload'] at hSplitPayloadCheck
  have hSplitCheck :
      splitPayload.check (cert.dag.nodeAt payload.split hSplitSize).parents (cert.dag.nodeAt payload.split hSplitSize).conclusion = true := by
    simpa [Payload.check] using hSplitPayloadCheck
  have hSplitSourceConclusion := (AvatarSplitPayload.check_source hSplitCheck).2
  have hSplitConclusion :
      splitNode.conclusion = splitPayload.source.clause := by
    calc
      splitNode.conclusion = (cert.dag.nodeAt payload.split hSplitSize).conclusion := by
            simp [hSplitNodeEq]
      _ = splitPayload.source.clause := hSplitSourceConclusion.symm
  have hSemanticSource :=
    hSelectorSemantics (splitNode := splitNode) (splitPayload := splitPayload) (indices := indices) (selector := selector)
      hSplitSome hSplitPayload hIndices hSelector
  have hSemantic :
      selector.Holds valuation ↔
        Clause.ValidOnBoundStack base (cert.dag.nodeAt index hIndex).conclusion := by
    simpa [hComponentConclusion, hSplitConclusion] using hSemanticSource
  exact
    Node.boundStackGuardedInvariant_of_selector
      base valuation (cert.dag.nodeAt index hIndex) selector
      hGuardEq hSemantic
theorem avatarComponentBoundStackGuardedTopologicalStepOfRegistry
    {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (hSelectorSemantics :
      AvatarComponentSelectorSemantics cert.dag base valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size) (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : AvatarComponentPayload σ) (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .avatarComponent payload) :
    Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt index hIndex) := by
  apply cert.avatarComponentBoundStackGuardedTopologicalStep
    base valuation index hIndex hParents payload hPayload
  exact hSelectorSemantics.atSlot payload.split payload.componentIndex
theorem theoryConflictBoundStackGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : TheoryConflictPayload σ) (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .theoryConflict payload) :
    Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hPayload] at hPayloadCheck
  have hTheoryCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold TheoryConflictPayload.check at hTheoryCheck
  rcases Bool.and_eq_true_iff.mp hTheoryCheck with
    ⟨hPrefix, _hConclusionEmpty⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with
    ⟨hParentIn, hConflictEmpty⟩
  have hParentMem :
      payload.conflict.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentIn
  let hParentSize := Nat.lt_trans (cert.contract.parents_before index hIndex payload.conflict.id hParentMem) hIndex
  have hConflictInvariant :
      Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt payload.conflict.id hParentSize) :=
    hParents payload.conflict.id hParentMem
  have hSnapshot :=
    cert.theoryConflictSnapshotChecked index hIndex payload hPayload
  have hConflictClause :=
    cert.parentClause_eq_nodeAt_of_snapshot
      payload.conflict hParentSize hSnapshot
  have hConflictNodeEmpty : (cert.dag.nodeAt payload.conflict.id hParentSize).conclusion.isEmpty = true := by
    rw [← hConflictClause]
    exact hConflictEmpty
  intro env hBound hGuards
  have hConflictGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt payload.conflict.id hParentSize).guards :=
    cert.parentGuardsHold_of_theoryConflictNodeGuardsOk
      index hIndex payload hPayload payload.conflict.id hParentMem hParentSize hGuards
  have hConflictSat :=
    hConflictInvariant env hBound hConflictGuards
  exact False.elim (Clause.not_satisfies_of_isEmpty hConflictNodeEmpty hConflictSat)
theorem propositionalLearnedClauseBoundStackGuardedTopologicalStep
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : PropositionalLearnedClausePayload) (hPayload :
      (cert.dag.nodeAt index hIndex).payload =
        .propositionalLearnedClause payload) :
    Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hPayload] at hPayloadCheck
  have hLearnedCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold PropositionalLearnedClausePayload.check at hLearnedCheck
  rcases Bool.and_eq_true_iff.mp hLearnedCheck with
    ⟨hParentIn, _hConclusionEmpty⟩
  have hParentMem :
      payload.conflict ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
    have hArray :
        payload.conflict ∈ (cert.dag.nodeAt index hIndex).parents := by
      simpa using hParentIn
    exact Array.mem_def.mp hArray
  let hParentSize := Nat.lt_trans (cert.contract.parents_before index hIndex payload.conflict hParentMem) hIndex
  have hConflictInvariant :
      Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt payload.conflict hParentSize) :=
    hParents payload.conflict hParentMem
  have hGuardCheck := (cert.contract.node_contract index hIndex).guards_checked
  have hConflictNodeSome :
      cert.dag.node? payload.conflict =
        some (cert.dag.nodeAt payload.conflict hParentSize) :=
    cert.dag.node?_eq_some_nodeAt hParentSize
  simp [DAG.localNodeGuardsOk, hPayload, hConflictNodeSome] at hGuardCheck
  rcases hGuardCheck with ⟨_hNodeEmpty, hConflictFields⟩
  rcases hConflictFields with ⟨hConflictPrefix, _hLearnedEq⟩
  rcases hConflictPrefix with ⟨hConflictTheory, hGuardEq⟩
  have hConflictEmpty : (cert.dag.nodeAt payload.conflict hParentSize).conclusion.isEmpty = true := by
    have hTheory : (cert.dag.nodeAt payload.conflict hParentSize).unguarded = false ∧
          (cert.dag.nodeAt payload.conflict hParentSize).conclusion.isEmpty = true := by
      simpa [Node.theoryConflict, GuardedClause.theoryConflict,
        Guards.GuardedClause.theoryConflict, Node.guardedConclusion,
        GuardedClause.unguarded, Guards.GuardedClause.unguarded, Node.unguarded]
        using hConflictTheory
    exact hTheory.2
  intro env hBound hGuards
  have hConflictGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt payload.conflict hParentSize).guards :=
    Node.GuardsHold.of_guardSetEq hGuardEq hGuards
  have hConflictSat :=
    hConflictInvariant env hBound hConflictGuards
  exact False.elim (Clause.not_satisfies_of_isEmpty hConflictEmpty hConflictSat)
private theorem avatarPropClosureJustificationCheckAt {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {payload : PropositionalClosurePayload σ} (hCheck : payload.justificationsCheck parents = true)
    {slot : Nat} (hSlot : slot < payload.initialClauses.size) :
    ∃ hJust : slot < payload.initialJustifications.size, (payload.initialJustifications[slot]).check parents payload.atomMap
        payload.initialClauses[slot] = true := by
  have hListCheck :=
    PropositionalClosurePayload.justificationsListCheck_eq_true_of_check hCheck
  unfold PropositionalClosurePayload.justificationsCheck at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hSizeBool, _hBody⟩
  have hSizeEq :
      payload.initialClauses.size = payload.initialJustifications.size := by
    by_cases hEq :
        payload.initialClauses.size = payload.initialJustifications.size
    · exact hEq
    · have hFalse : (payload.initialClauses.size ==
            payload.initialJustifications.size) = false := by
        simp [hEq]
      rw [hFalse] at hSizeBool
      cases hSizeBool
  have hJust : slot < payload.initialJustifications.size := by
    simpa [hSizeEq] using hSlot
  refine ⟨hJust, ?_⟩
  have hAt :=
    PropositionalClosurePayload.justificationsListCheck_at
      parents payload.atomMap hListCheck slot (by simpa using hSlot) (by simpa using hJust)
  simpa using hAt
private theorem avatarPropClosureJustificationSupportedAt {σ : Signature}
    {payload : PropositionalClosurePayload σ} (hSupported : payload.avatarSoundnessSupported = true)
    {slot : Nat} (hSlot : slot < payload.initialJustifications.size) : (payload.initialJustifications[slot]).avatarSoundnessSupported = true := by
  have hAll := Array.all_eq_true.mp hSupported
  simpa [PropositionalClosurePayload.avatarSoundnessSupported] using
    hAll slot hSlot
/--
AVATAR residual CDCL 的 fixed-bound-stack 拓扑步骤。
前三类 initial 复用 guarded residual 的对象/guard 链接；`avatarSkeleton` 额外消费
split descriptor 的全局 selector skeleton 语义。
-/
theorem residualCdclAvatarBoundStackGuardedTopologicalStep
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (hSplitSemantics :
      AvatarSplitSelectorSemantics cert.dag base valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size) (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : PropositionalClosurePayload σ) (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .residualCdcl payload) (hPayloadSupported : payload.avatarSoundnessSupported = true) :
    Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hPayload] at hPayloadCheck
  have hResidualCheck : (!((cert.dag.nodeAt index hIndex).parents.isEmpty) && (cert.dag.nodeAt index hIndex).conclusion.isEmpty &&
            payload.check (cert.dag.nodeAt index hIndex).parents) = true := by
    simpa [Payload.check] using hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hResidualCheck with
    ⟨_hResidualPrefix, hClosureCheck⟩
  have hClosureParts := hClosureCheck
  unfold PropositionalClosurePayload.check at hClosureParts
  simp at hClosureParts
  rcases hClosureParts with ⟨hClosureParts, _hVerifiedStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hRetainedStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hGeneratedStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hClauseStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hStepsStats⟩
  rcases hClosureParts with
    ⟨hCheckedUnsatProof, hJustificationsCheckProof⟩
  have hCheckedUnsat :
      PropResolution.checkedUnsat payload.initialClauses payload.proof = true :=
    hCheckedUnsatProof
  have hJustificationsCheck :
      payload.justificationsCheck (cert.dag.nodeAt index hIndex).parents = true :=
    hJustificationsCheckProof
  have hInitialLinks := (cert.contract.node_contract index hIndex).prop_initial_links_checked
  have hDagInitials :
      payload.initialJustifications.all (fun justification =>
          cert.dag.propInitialJustificationDagOk (cert.dag.nodeAt index hIndex).parents justification) = true := by
    simpa [DAG.propInitialLinksOk, hPayload] using hInitialLinks
  intro env hBound _hGuards
  have hInitialSatisfies :
      ∀ initial, initial ∈ payload.initialClauses.toList →
        PropResolution.Clause.Satisfies (PropLiteralLink.valuation valuation payload.atomMap env)
          initial.clause := by
    intro initial hInitialMem
    have hInitialArray : initial ∈ payload.initialClauses :=
      Array.mem_def.mpr hInitialMem
    rcases Array.mem_iff_getElem.mp hInitialArray with
      ⟨slot, hSlot, hInitialGet⟩
    rcases avatarPropClosureJustificationCheckAt
        hJustificationsCheck hSlot with
      ⟨hJustSlot, hJustificationCheck⟩
    have hJustificationSupported :=
      avatarPropClosureJustificationSupportedAt
        hPayloadSupported hJustSlot
    have hDagOk := (Array.all_eq_true.mp hDagInitials) slot hJustSlot
    cases hJustification : payload.initialJustifications[slot] with
    | parentClause link =>
        have hCheck :
            link.check (cert.dag.nodeAt index hIndex).parents
              payload.atomMap initial = true := by
          simpa [PropInitialJustification.check, hJustification, hInitialGet]
            using hJustificationCheck
        unfold PropParentClauseLink.check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with
          ⟨hCheckPrefix, hLiteralChecks⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hCheckPrefix, hInitialEqBool⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hParentInBool, hObjectEqBool⟩
        have hInitialEq : initial.clause = link.encodedClause :=
          PropResolution.clauseEq_eq.mp hInitialEqBool
        have hObjectEq : link.parent.clause = link.objectClause :=
          Clause.eq_sound link.parent.clause link.objectClause hObjectEqBool
        have hDagParent :
            cert.dag.propParentInitialLinkOk (cert.dag.nodeAt index hIndex).parents link = true := by
          simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
        have hParentMem :
            link.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
          ParentClause.mem_toList_of_idIn hParentInBool
        let hParentSize := Nat.lt_trans (cert.contract.parents_before index hIndex link.parent.id hParentMem) hIndex
        have hParentNodeSome :
            cert.dag.node? link.parent.id =
              some (cert.dag.nodeAt link.parent.id hParentSize) :=
          cert.dag.node?_eq_some_nodeAt hParentSize
        unfold DAG.propParentInitialLinkOk at hDagParent
        rw [hParentNodeSome] at hDagParent
        rcases Bool.and_eq_true_iff.mp hDagParent with
          ⟨hDagParentPrefix, hParentUnguarded⟩
        rcases Bool.and_eq_true_iff.mp hDagParentPrefix with
          ⟨_hParentContains, hSnapshot⟩
        have hParentInvariant :
            Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt link.parent.id hParentSize) :=
          hParents link.parent.id hParentMem
        have hParentGuards :
            Node.GuardsHold valuation (cert.dag.nodeAt link.parent.id hParentSize).guards :=
          Node.GuardsHold.of_isEmpty (by
            simpa [Node.unguarded] using hParentUnguarded)
        have hParentSat :=
          hParentInvariant env hBound hParentGuards
        have hSnapshotClause :=
          cert.parentClause_eq_nodeAt_of_snapshot
            link.parent hParentSize hSnapshot
        have hObjectSat : Clause.Satisfies env link.objectClause := by
          have hObjectConclusion :
              link.objectClause = (cert.dag.nodeAt link.parent.id hParentSize).conclusion :=
            hObjectEq.symm.trans hSnapshotClause
          simpa only [hObjectConclusion] using hParentSat
        have hEncodedSat :=
          PropParentClauseLink.encodedClause_satisfies_of_object (base := valuation) (atomMap := payload.atomMap)
            hLiteralChecks hObjectSat
        simpa only [hInitialEq] using hEncodedSat
    | guardActivationClause link =>
        have hCheck :
            link.check (cert.dag.nodeAt index hIndex).parents
              payload.atomMap initial = true := by
          simpa [PropInitialJustification.check, hJustification, hInitialGet]
            using hJustificationCheck
        unfold PropGuardActivationLink.check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with
          ⟨hCheckPrefix, hLiteralChecks⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hCheckPrefix, hGuardChecks⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hCheckPrefix, hInitialEqBool⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hParentInBool, hObjectEqBool⟩
        have hInitialEq : initial.clause = link.encodedClause :=
          PropResolution.clauseEq_eq.mp hInitialEqBool
        have hObjectEq : link.parent.clause = link.objectClause :=
          Clause.eq_sound link.parent.clause link.objectClause hObjectEqBool
        have hDagActivation :
            cert.dag.propGuardActivationInitialLinkOk (cert.dag.nodeAt index hIndex).parents link = true := by
          simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
        have hParentMem :
            link.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
          ParentClause.mem_toList_of_idIn hParentInBool
        let hParentSize := Nat.lt_trans (cert.contract.parents_before index hIndex link.parent.id hParentMem) hIndex
        have hParentNodeSome :
            cert.dag.node? link.parent.id =
              some (cert.dag.nodeAt link.parent.id hParentSize) :=
          cert.dag.node?_eq_some_nodeAt hParentSize
        unfold DAG.propGuardActivationInitialLinkOk at hDagActivation
        rw [hParentNodeSome] at hDagActivation
        rcases Bool.and_eq_true_iff.mp hDagActivation with
          ⟨hDagPrefix, hGuardFields⟩
        rcases Bool.and_eq_true_iff.mp hDagPrefix with
          ⟨_hParentContains, hSnapshot⟩
        rcases Bool.and_eq_true_iff.mp hGuardFields with
          ⟨_hParentGuarded, hGuardEq⟩
        have hParentInvariant :
            Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt link.parent.id hParentSize) :=
          hParents link.parent.id hParentMem
        have hSnapshotClause :=
          cert.parentClause_eq_nodeAt_of_snapshot
            link.parent hParentSize hSnapshot
        have hObjectOfGuards : (∀ lit, lit ∈ (Guards.canonical link.guards).toList →
              lit.Holds valuation) →
              Clause.Satisfies env link.objectClause := by
          intro hLinkGuards
          have hParentGuards :
              Node.GuardsHold valuation (cert.dag.nodeAt link.parent.id hParentSize).guards :=
            Node.GuardsHold.of_guardSetEq hGuardEq hLinkGuards
          have hParentSat :=
            hParentInvariant env hBound hParentGuards
          have hObjectConclusion :
              link.objectClause = (cert.dag.nodeAt link.parent.id hParentSize).conclusion :=
            hObjectEq.symm.trans hSnapshotClause
          simpa only [hObjectConclusion] using hParentSat
        have hEncodedSat :=
          PropGuardActivationLink.encodedClause_satisfies (base := valuation) (atomMap := payload.atomMap)
            hGuardChecks hLiteralChecks hObjectOfGuards
        simpa only [hInitialEq] using hEncodedSat
    | propLearnedClause link =>
        have hCheck :
            link.check (cert.dag.nodeAt index hIndex).parents
              payload.atomMap initial = true := by
          simpa [PropInitialJustification.check, hJustification, hInitialGet]
            using hJustificationCheck
        unfold PropLearnedClauseLink.check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with
          ⟨hCheckPrefix, hInitialEqBool⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hParentContains, hOutside⟩
        have hInitialEq : initial.clause = link.clause :=
          PropResolution.clauseEq_eq.mp hInitialEqBool
        have hDagLearned :
            cert.dag.propLearnedInitialLinkOk (cert.dag.nodeAt index hIndex).parents link = true := by
          simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
        have hParentMem :
            link.parent ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
          have hArray :
              link.parent ∈ (cert.dag.nodeAt index hIndex).parents := by
            simpa using hParentContains
          exact Array.mem_def.mp hArray
        let hParentSize := Nat.lt_trans (cert.contract.parents_before index hIndex link.parent hParentMem) hIndex
        have hParentNodeSome :
            cert.dag.node? link.parent =
              some (cert.dag.nodeAt link.parent hParentSize) :=
          cert.dag.node?_eq_some_nodeAt hParentSize
        unfold DAG.propLearnedInitialLinkOk at hDagLearned
        rw [hParentNodeSome] at hDagLearned
        rcases Bool.and_eq_true_iff.mp hDagLearned with
          ⟨_hParentContainsDag, hLearnedMatch⟩
        cases hParentPayload : (cert.dag.nodeAt link.parent hParentSize).payload with
        | propositionalLearnedClause learnedPayload =>
            simp [hParentPayload] at hLearnedMatch
            have hLinkLearnedEq : link.clause = learnedPayload.learned :=
              PropResolution.clauseEq_eq.mp (by simpa using hLearnedMatch)
            have hParentPayloadCheck := (cert.contract.node_contract link.parent hParentSize).payload_checked
            simp [hParentPayload] at hParentPayloadCheck
            have hLearnedPayloadCheck :
                learnedPayload.check (cert.dag.nodeAt link.parent hParentSize).parents (cert.dag.nodeAt link.parent hParentSize).conclusion = true := by
              simpa [Payload.check] using hParentPayloadCheck
            unfold PropositionalLearnedClausePayload.check at hLearnedPayloadCheck
            rcases Bool.and_eq_true_iff.mp hLearnedPayloadCheck with
              ⟨_hConflictParent, hParentConclusionEmpty⟩
            have hParentGuardCheck := (cert.contract.node_contract link.parent hParentSize).guards_checked
            unfold DAG.localNodeGuardsOk at hParentGuardCheck
            simp [hParentPayload] at hParentGuardCheck
            rcases hParentGuardCheck with
              ⟨_hParentEmptyFromGuards, hConflictMatch⟩
            cases hConflictNode? : cert.dag.node? learnedPayload.conflict with
            | none =>
                simp [hConflictNode?] at hConflictMatch
            | some conflictNode =>
                have hConflictMatch' :
                    conflictNode.theoryConflict &&
                      Guards.eq (cert.dag.nodeAt link.parent hParentSize).guards
                        conflictNode.guards && (match conflictNode.payload with
                        | Payload.theoryConflict _ =>
                            PropResolution.clauseEq learnedPayload.learned (Guards.learnedClause conflictNode.guards)
                        | _ => false) = true := by
                  simpa [hConflictNode?] using hConflictMatch
                rcases Bool.and_eq_true_iff.mp hConflictMatch' with
                  ⟨hConflictPrefix, hLearnedEqBool⟩
                rcases Bool.and_eq_true_iff.mp hConflictPrefix with
                  ⟨_hConflictTheory, hGuardEq⟩
                cases hConflictPayload : conflictNode.payload with
                | theoryConflict _ =>
                    rw [hConflictPayload] at hLearnedEqBool
                    have hLearnedEqConflict :
                        learnedPayload.learned =
                          Guards.learnedClause conflictNode.guards :=
                      PropResolution.clauseEq_eq.mp (by simpa using hLearnedEqBool)
                    by_cases hParentGuards :
                        Node.GuardsHold valuation (cert.dag.nodeAt link.parent hParentSize).guards
                    · have hParentInvariant :
                          Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt link.parent hParentSize) :=
                        hParents link.parent hParentMem
                      have hParentSat :=
                        hParentInvariant env hBound hParentGuards
                      exact False.elim (Clause.not_satisfies_of_isEmpty
                          hParentConclusionEmpty hParentSat)
                    · have hNotConflictGuards :
                          ¬ Node.GuardsHold valuation conflictNode.guards := by
                        intro hConflictGuards
                        apply hParentGuards
                        intro lit hLit
                        have hCanonical :
                            Guards.canonical (cert.dag.nodeAt link.parent hParentSize).guards =
                              Guards.canonical conflictNode.guards :=
                          PropResolution.clauseEq_eq.mp (by simpa [Guards.eq] using hGuardEq)
                        exact hConflictGuards lit (by
                          simpa [hCanonical] using hLit)
                      have hClauseEq :
                          link.clause =
                            Guards.learnedClause conflictNode.guards :=
                        hLinkLearnedEq.trans hLearnedEqConflict
                      have hLearnedSat :=
                        PropLearnedClauseLink.satisfies_of_not_guards (base := valuation) (atomMap := payload.atomMap) (env := env) (link := link)
                          (guards := conflictNode.guards)
                          hClauseEq hOutside hNotConflictGuards
                      simpa only [hInitialEq] using hLearnedSat
                | source _ => simp [hConflictPayload] at hLearnedEqBool
                | avatarSplit _ => simp [hConflictPayload] at hLearnedEqBool
                | avatarComponent _ => simp [hConflictPayload] at hLearnedEqBool
                | localRule _ => simp [hConflictPayload] at hLearnedEqBool
                | propositionalLearnedClause _ =>
                    simp [hConflictPayload] at hLearnedEqBool
                | residualCdcl _ => simp [hConflictPayload] at hLearnedEqBool
        | source _ => simp [hParentPayload] at hLearnedMatch
        | avatarSplit _ => simp [hParentPayload] at hLearnedMatch
        | avatarComponent _ => simp [hParentPayload] at hLearnedMatch
        | localRule _ => simp [hParentPayload] at hLearnedMatch
        | theoryConflict _ => simp [hParentPayload] at hLearnedMatch
        | residualCdcl _ => simp [hParentPayload] at hLearnedMatch
    | avatarSkeleton link =>
        have hCheck :
            link.check (cert.dag.nodeAt index hIndex).parents
              payload.atomMap initial = true := by
          simpa [PropInitialJustification.check, hJustification, hInitialGet]
            using hJustificationCheck
        unfold PropAvatarSkeletonLink.check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with
          ⟨hCheckPrefix, hInitialEqBool⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hParentContains, hOutside⟩
        have hInitialEq : initial.clause = link.skeleton :=
          PropResolution.clauseEq_eq.mp hInitialEqBool
        have hDagSkeleton :
            cert.dag.propAvatarSkeletonInitialLinkOk (cert.dag.nodeAt index hIndex).parents link = true := by
          simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
        have hParentMem :
            link.parent ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
          have hArray :
              link.parent ∈ (cert.dag.nodeAt index hIndex).parents := by
            simpa using hParentContains
          exact Array.mem_def.mp hArray
        let hParentSize := Nat.lt_trans (cert.contract.parents_before index hIndex link.parent hParentMem) hIndex
        have hParentNodeSome :
            cert.dag.node? link.parent =
              some (cert.dag.nodeAt link.parent hParentSize) :=
          cert.dag.node?_eq_some_nodeAt hParentSize
        unfold DAG.propAvatarSkeletonInitialLinkOk at hDagSkeleton
        rw [hParentNodeSome] at hDagSkeleton
        rcases Bool.and_eq_true_iff.mp hDagSkeleton with
          ⟨_hParentContainsDag, hSplitFields⟩
        rcases Bool.and_eq_true_iff.mp hSplitFields with
          ⟨hParentUnguarded, hSkeletonMatch⟩
        cases hParentPayload : (cert.dag.nodeAt link.parent hParentSize).payload with
        | avatarSplit splitPayload =>
            rw [hParentPayload] at hSkeletonMatch
            have hSkeletonEq :
                link.skeleton =
                  PropResolution.canonicalClause splitPayload.selectors :=
              PropResolution.clauseEq_eq.mp (by simpa using hSkeletonMatch)
            have hParentInvariant :
                Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt link.parent hParentSize) :=
              hParents link.parent hParentMem
            have hParentGuards :
                Node.GuardsHold valuation (cert.dag.nodeAt link.parent hParentSize).guards :=
              Node.GuardsHold.of_isEmpty (by
                simpa [Node.unguarded] using hParentUnguarded)
            have hParentPayloadCheck := (cert.contract.node_contract link.parent hParentSize).payload_checked
            rw [hParentPayload] at hParentPayloadCheck
            have hSplitCheck :
                splitPayload.check (cert.dag.nodeAt link.parent hParentSize).parents (cert.dag.nodeAt link.parent hParentSize).conclusion = true := by
              simpa [Payload.check] using hParentPayloadCheck
            have hSourceConclusion := (AvatarSplitPayload.check_source hSplitCheck).2
            have hSourceValid :
                Clause.ValidOnBoundStack base splitPayload.source.clause := by
              intro sourceEnv hSourceBound
              have hParentSat :=
                hParentInvariant sourceEnv hSourceBound hParentGuards
              simpa only [hSourceConclusion] using hParentSat
            have hSkeletonBase :
                PropResolution.Clause.Satisfies valuation link.skeleton := by
              have hCanonical := (hSplitSemantics hParentNodeSome hParentPayload).mp hSourceValid
              simpa only [hSkeletonEq] using hCanonical
            rcases hSkeletonBase with ⟨literal, hLiteralMem, hLiteral⟩
            have hLiteralOutside :
                PropLiteralLink.outsideAtomMap payload.atomMap literal = true := by
              have hAll := Array.all_eq_true.mp hOutside
              have hArrayMem : literal ∈ link.skeleton :=
                Array.mem_def.mpr hLiteralMem
              rcases Array.mem_iff_getElem.mp hArrayMem with
                ⟨literalSlot, hLiteralSlot, hLiteralGet⟩
              have hAt := hAll literalSlot hLiteralSlot
              simpa [hLiteralGet] using hAt
            have hLiteralMixed :
                literal.Holds (PropLiteralLink.valuation valuation payload.atomMap env) := (PropLiteralLink.holds_valuation_iff_of_outsideAtomMap
                (base := valuation) (env := env) hLiteralOutside).2 hLiteral
            apply PropResolution.Clause.satisfies_of_mem (clause := initial.clause) (lit := literal)
            · simpa only [hInitialEq] using hLiteralMem
            · exact hLiteralMixed
        | source _ => simp [hParentPayload] at hSkeletonMatch
        | avatarComponent _ => simp [hParentPayload] at hSkeletonMatch
        | localRule _ => simp [hParentPayload] at hSkeletonMatch
        | theoryConflict _ => simp [hParentPayload] at hSkeletonMatch
        | propositionalLearnedClause _ =>
            simp [hParentPayload] at hSkeletonMatch
        | residualCdcl _ => simp [hParentPayload] at hSkeletonMatch
  exact False.elim (PropResolution.checkedUnsat_sound hInitialSatisfies hCheckedUnsat)
/--
AVATAR fixed-bound-stack 整图中的本地规则步骤。
父节点只在当前模型和同一 bound stack 上消费；substitution 与 standardize-apart 通过
语义环境搬运，不调用跨模型的旧 guarded 不变量。
-/
theorem localRuleBoundStackGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : LocalRulePayload σ) (hLocal :
      (cert.dag.nodeAt index hIndex).payload = .localRule payload) :
    Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hLocal] at hPayloadCheck
  have hLocalCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with
    ⟨hLocalPrefix, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLocalPrefix with
    ⟨_hParentsNonempty, hEvidenceCheck⟩
  have hNodeSnapshots :
      payload.evidence.parentClauses.all (fun parent => cert.dag.parentSnapshotChecked parent) = true := by
    have hAllNodes := Array.all_eq_true.mp cert.contract.parent_snapshots_checked
    have hNode : ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
          cert.dag.parentSnapshotChecked parent) = true := by
      simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
        hAllNodes index hIndex
    rw [hLocal] at hNode
    simpa [Payload.parentClauses, LocalRulePayload.parentClauses] using hNode
  have hSnapshotFor :
      ∀ (parent : ParentClause σ),
        parent ∈ payload.evidence.parentClauses.toList →
          cert.dag.parentSnapshotChecked parent = true := by
    intro parent hMem
    have hArrayMem : parent ∈ payload.evidence.parentClauses :=
      Array.mem_def.mpr hMem
    rcases Array.mem_iff_getElem.mp hArrayMem with
      ⟨slot, hSlot, hGet⟩
    have hAt := (Array.all_eq_true.mp hNodeSnapshots) slot hSlot
    simpa [hGet] using hAt
  have hParentSat :
      ∀ (parent : ParentClause σ),
        parent ∈ payload.evidence.parentClauses.toList →
          parent.idIn (cert.dag.nodeAt index hIndex).parents = true →
            ∀ env, Logic.FirstOrder.Env.SameBoundStack env base →
              Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
                Clause.Satisfies env parent.clause := by
    intro parent hPayloadMem hParentIn env hBound hGuards
    have hParentMem :
        parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
      ParentClause.mem_toList_of_idIn hParentIn
    let hParentSize := Nat.lt_trans (cert.contract.parents_before index hIndex parent.id hParentMem) hIndex
    have hSnapshot :=
      hSnapshotFor parent hPayloadMem
    have hParentClause :=
      cert.parentClause_eq_nodeAt_of_snapshot parent hParentSize hSnapshot
    have hParentInvariant :
        Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt parent.id hParentSize) :=
      hParents parent.id hParentMem
    have hParentGuards :
        Node.GuardsHold valuation (cert.dag.nodeAt parent.id hParentSize).guards :=
      cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
        parent.id hParentMem hParentSize hGuards
    simpa only [hParentClause] using
      hParentInvariant env hBound hParentGuards
  have hSubstitutedParentSat :
      ∀ (parent : ParentClause σ),
        parent ∈ payload.evidence.parentClauses.toList →
          parent.idIn (cert.dag.nodeAt index hIndex).parents = true →
            ∀ (subst : TermSubstitution σ),
              TermSubstitution.BoundClosed subst ∧
                TermSubstitution.WellSorted subst →
                ∀ env, Logic.FirstOrder.Env.SameBoundStack env base →
                  Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
                    Clause.Satisfies env (Clause.applySubstitution subst parent.clause) := by
    intro parent hPayloadMem hParentIn subst hAdmissible env hBound hGuards
    let targetEnv := TermSubstitution.semanticEnv subst env hAdmissible.2
    have hEnvMatches :=
      TermSubstitution.semanticEnv_matches (subst := subst) (env := env) (hAdmissible := hAdmissible.2)
    have hTargetBound :
        Logic.FirstOrder.Env.SameBoundStack targetEnv base := by
      intro sort position
      exact (hEnvMatches.1 sort position).trans (hBound sort position)
    have hSatTarget :=
      hParentSat parent hPayloadMem hParentIn targetEnv hTargetBound hGuards
    exact (Clause.satisfies_applySubstitution_iff_of_envMatches (subst := subst) (env := env) (targetEnv := targetEnv)
      hAdmissible.1 hEnvMatches parent.clause).mpr hSatTarget
  have hStandardizedParentSat :
      ∀ (parent : ParentClause σ),
        parent ∈ payload.evidence.parentClauses.toList →
          parent.idIn (cert.dag.nodeAt index hIndex).parents = true →
            ∀ (offset : Nat) (subst : TermSubstitution σ),
              TermSubstitution.BoundClosed subst ∧
                TermSubstitution.WellSorted subst →
                ∀ env, Logic.FirstOrder.Env.SameBoundStack env base →
                  Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
                    Clause.Satisfies env (Clause.applySubstitution subst (Clause.renameFreeVars offset parent.clause)) := by
    intro parent hPayloadMem hParentIn offset subst hAdmissible env hBound hGuards
    let substitutionEnv := TermSubstitution.semanticEnv subst env hAdmissible.2
    have hSubstitutionEnv :=
      TermSubstitution.semanticEnv_matches (subst := subst) (env := env) (hAdmissible := hAdmissible.2)
    let renamedEnv := FreeVarRenaming.semanticEnv offset substitutionEnv
    have hRenamedEnv :=
      FreeVarRenaming.semanticEnv_matches (offset := offset) (sourceEnv := substitutionEnv)
    have hRenamedBound :
        Logic.FirstOrder.Env.SameBoundStack renamedEnv base := by
      intro sort position
      exact (hRenamedEnv.1 sort position).trans ((hSubstitutionEnv.1 sort position).trans (hBound sort position))
    have hSatOriginal :=
      hParentSat parent hPayloadMem hParentIn renamedEnv hRenamedBound hGuards
    have hSatRenamed : Clause.Satisfies substitutionEnv (Clause.renameFreeVars offset parent.clause) := (Clause.satisfies_renameFreeVars_iff_of_envMatches
        (offset := offset) (sourceEnv := substitutionEnv) (targetEnv := renamedEnv) hRenamedEnv parent.clause).mpr hSatOriginal
    exact (Clause.satisfies_applySubstitution_iff_of_envMatches (subst := subst) (env := env) (targetEnv := substitutionEnv)
      hAdmissible.1 hSubstitutionEnv (Clause.renameFreeVars offset parent.clause)).mpr hSatRenamed
  intro env hBound hGuards
  exact LocalRuleEvidence.satisfies_of_check (M := M) (fun currentEnv =>
      Logic.FirstOrder.Env.SameBoundStack currentEnv base ∧
        Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards)
    hEvidenceCheck (fun parent hPayloadMem hParentIn currentEnv hContext =>
      hParentSat parent hPayloadMem hParentIn currentEnv
        hContext.1 hContext.2) (fun parent hPayloadMem hParentIn subst hAdmissible currentEnv hContext =>
      hSubstitutedParentSat parent hPayloadMem hParentIn subst hAdmissible
        currentEnv hContext.1 hContext.2) (fun parent hPayloadMem hParentIn offset subst hAdmissible currentEnv hContext =>
      hStandardizedParentSat parent hPayloadMem hParentIn offset subst hAdmissible
        currentEnv hContext.1 hContext.2)
    env ⟨hBound, hGuards⟩
theorem avatarBoundStackGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (hProblem : cert.dag.problem.Valid base)
    (hComponentSemantics :
      AvatarComponentSelectorSemantics cert.dag base valuation) (hSplitSemantics :
      AvatarSplitSelectorSemantics cert.dag base valuation) (hSupported : cert.dag.avatarSoundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size) (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) :
    Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt index hIndex) := by
  have hNodeSupported :=
    DAG.avatarSoundnessSupported_of_eq_true hSupported index hIndex
  cases hPayload : (cert.dag.nodeAt index hIndex).payload with
  | source initialIndex =>
      exact cert.sourceBoundStackGuardedTopologicalStep
        base valuation hProblem index hIndex hParents initialIndex hPayload
  | avatarSplit payload =>
      exact cert.avatarSplitBoundStackGuardedTopologicalStep
        base valuation index hIndex hParents payload hPayload
  | avatarComponent payload =>
      exact cert.avatarComponentBoundStackGuardedTopologicalStepOfRegistry
        base valuation hComponentSemantics index hIndex hParents payload hPayload
  | localRule payload =>
      exact cert.localRuleBoundStackGuardedTopologicalStep
        base valuation index hIndex hParents payload hPayload
  | theoryConflict payload =>
      exact cert.theoryConflictBoundStackGuardedTopologicalStep
        base valuation index hIndex hParents payload hPayload
  | propositionalLearnedClause payload =>
      exact cert.propositionalLearnedClauseBoundStackGuardedTopologicalStep
        base valuation index hIndex hParents payload hPayload
  | residualCdcl payload =>
      have hPayloadSupported :
          payload.avatarSoundnessSupported = true := by
        simpa [hPayload, Payload.avatarSoundnessSupported] using hNodeSupported
      exact cert.residualCdclAvatarBoundStackGuardedTopologicalStep
        base valuation hSplitSemantics index hIndex hParents payload hPayload
        hPayloadSupported
theorem boundStackGuardedInvariant_of_avatarSoundnessSupported
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (hProblem : cert.dag.problem.Valid base)
    (hComponentSemantics :
      AvatarComponentSelectorSemantics cert.dag base valuation) (hSplitSemantics :
      AvatarSplitSelectorSemantics cert.dag base valuation) (hSupported : cert.dag.avatarSoundnessSupported = true) :
    cert.dag.BoundStackGuardedInvariant base valuation :=
  cert.topologicalInduction (P := fun _ _ node =>
      Node.BoundStackGuardedInvariant base valuation node) (fun index hIndex hParents =>
      cert.avatarBoundStackGuardedTopologicalStep
        base valuation hProblem hComponentSemantics hSplitSemantics
        hSupported index hIndex hParents)
theorem rootBoundStackGuardedInvariant_of_avatarSoundnessSupported
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (hProblem : cert.dag.problem.Valid base)
    (hComponentSemantics :
      AvatarComponentSelectorSemantics cert.dag base valuation) (hSplitSemantics :
      AvatarSplitSelectorSemantics cert.dag base valuation) (hSupported : cert.dag.avatarSoundnessSupported = true) :
    Node.BoundStackGuardedInvariant base valuation (cert.dag.nodeAt cert.dag.root cert.contract.root_exists) :=
  cert.rootByTopologicalInduction (P := fun _ _ node =>
      Node.BoundStackGuardedInvariant base valuation node) (fun index hIndex hParents =>
      cert.avatarBoundStackGuardedTopologicalStep
        base valuation hProblem hComponentSemantics hSplitSemantics
        hSupported index hIndex hParents)
/--
AVATAR residual CDCL 专用 root contradiction。
root checker 保证无 guard 且结论为空；整图 fixed-bound-stack soundness 因而直接否定
当前模型中的 ClauseProblem.Valid。
-/
theorem rootEmptyContradiction_of_avatarSoundnessSupported
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) (valuation : PropResolution.Valuation) (hProblem : cert.dag.problem.Valid base)
    (hComponentSemantics :
      AvatarComponentSelectorSemantics cert.dag base valuation) (hSplitSemantics :
      AvatarSplitSelectorSemantics cert.dag base valuation) (hSupported : cert.dag.avatarSoundnessSupported = true) : False := by
  have hRootInvariant :=
    cert.rootBoundStackGuardedInvariant_of_avatarSoundnessSupported
      base valuation hProblem hComponentSemantics hSplitSemantics hSupported
  have hRootGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt cert.dag.root cert.contract.root_exists).guards :=
    Node.GuardsHold.of_isEmpty (by
      simpa [Node.unguarded] using cert.contract.root_unguarded)
  have hRootSat :=
    hRootInvariant base (Logic.FirstOrder.Env.SameBoundStack.refl base) hRootGuards
  exact Clause.not_satisfies_of_isEmpty cert.contract.root_conclusion_empty hRootSat
end CheckedDAG
end DAGCertificate
end Automation
end YesMetaZFC
