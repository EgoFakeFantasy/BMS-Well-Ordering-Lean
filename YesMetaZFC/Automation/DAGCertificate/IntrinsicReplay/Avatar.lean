import YesMetaZFC.Automation.DAGCertificate.AvatarRegistry
import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Semantics

/-!
# AVATAR 的内在回放接口

本模块只消费已检查 DAG 与统一 free registry 下的内在字句。selector 的语义合同
直接指向 `CompiledClause.TrueIn`，因此不再引入 raw 字句满足关系、外部 bound stack
或良构性桥接。后续 registry 语义闭合只需要实现这里的两个合同。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace IntrinsicReplay

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

universe x

variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]

theorem avatarSplitNodeOk_fields
    {dag : DAG σ} {node : Node σ}
    {payload : AvatarSplitPayload σ}
    (hOk : dag.avatarSplitNodeOk node payload = true) :
    node.unguarded = true ∧
      dag.parentSnapshotChecked payload.source = true ∧
        ∃ sourceNode initialIndex,
          dag.node? payload.source.id = some sourceNode ∧
            sourceNode.unguarded = true ∧
              sourceNode.payload = .source initialIndex := by
  unfold DAG.avatarSplitNodeOk at hOk
  split at hOk <;> simp_all
  split at hOk <;> simp_all

theorem avatarComponentNodeOk_fields
    {dag : DAG σ} {node : Node σ}
    {payload : AvatarComponentPayload σ}
    (hOk : dag.avatarComponentNodeOk node payload = true) :
    ∃ splitNode splitPayload indices selector,
      dag.node? payload.split = some splitNode ∧
        splitNode.payload = .avatarSplit splitPayload ∧
          splitPayload.partitions[payload.componentIndex]? = some indices ∧
            AvatarSplit.selectorAt? splitPayload.selectors
                payload.componentIndex = some selector ∧
              splitNode.unguarded = true ∧
                node.conclusion =
                    Clause.atIndices splitNode.conclusion indices ∧
                  Guards.eq node.guards #[selector] = true := by
  unfold DAG.avatarComponentNodeOk at hOk
  split at hOk <;> simp_all
  split at hOk <;> simp_all
  split at hOk <;> simp_all
  exact Clause.eq_sound _ _ hOk.2.1

/-- 当前统一 registry 中，一个 raw 字句拥有的内在全称真实性见证。 -/
def AvatarClauseTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {dag : DAG σ} (compiled : Compile.CheckedDAGClauses dag)
    (raw : Clause σ) : Prop :=
  ∃ clause : Compile.CompiledClause compiled.compilation.registry,
    clause.raw = raw ∧ clause.TrueIn M

/-!
selector 合同使用 split 节点当前已经检查过的 conclusion，而不是重新携带 source
良构证明。这样 component 回放只依赖一个 raw equality 和一个已编译字句见证。
-/
def AvatarComponentSemantics
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {dag : DAG σ} (compiled : Compile.CheckedDAGClauses dag)
    (valuation : PropResolution.Valuation) : Prop :=
  ∀ {splitId splitNode splitPayload componentIndex indices selector},
    dag.node? splitId = some splitNode →
      splitNode.payload = .avatarSplit splitPayload →
        splitPayload.partitions[componentIndex]? = some indices →
          AvatarSplit.selectorAt? splitPayload.selectors componentIndex =
            some selector →
            (selector.Holds valuation ↔
              AvatarClauseTrueIn M compiled
                (Clause.atIndices splitNode.conclusion indices))

def AvatarSplitSemantics
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {dag : DAG σ} (compiled : Compile.CheckedDAGClauses dag)
    (valuation : PropResolution.Valuation) : Prop :=
  ∀ {splitId splitNode splitPayload},
    dag.node? splitId = some splitNode →
      splitNode.payload = .avatarSplit splitPayload →
        (AvatarClauseTrueIn M compiled splitNode.conclusion ↔
          PropResolution.Clause.Satisfies valuation
            (PropResolution.canonicalClause splitPayload.selectors))

def avatarSelectorValuation
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {dag : DAG σ} (compiled : Compile.CheckedDAGClauses dag)
    (entries : List (AvatarSelectorComponent σ)) :
    PropResolution.Valuation :=
  fun varId =>
    ∃ entry, entry ∈ entries ∧ entry.selector.var = varId ∧
      AvatarClauseTrueIn M compiled entry.component

omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem avatarSelector_holds_iff_trueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {dag : DAG σ} (compiled : Compile.CheckedDAGClauses dag)
    (entries : List (AvatarSelectorComponent σ))
    (hPositive : ∀ entry, entry ∈ entries → entry.selector.positive = true)
    (hCompatible : AvatarSelectorComponent.Compatible entries)
    {entry : AvatarSelectorComponent σ} (hEntry : entry ∈ entries) :
    entry.selector.Holds (avatarSelectorValuation M compiled entries) ↔
      AvatarClauseTrueIn M compiled entry.component := by
  constructor
  · intro hSelector
    have hValue :
        avatarSelectorValuation M compiled entries entry.selector.var := by
      simpa [PropResolution.Lit.Holds, hPositive entry hEntry] using hSelector
    rcases hValue with ⟨other, hOther, hVariable, hTrue⟩
    have hComponent : other.component = entry.component :=
      hCompatible other hOther entry hEntry hVariable
    simpa [hComponent] using hTrue
  · intro hTrue
    have hValue :
        avatarSelectorValuation M compiled entries entry.selector.var :=
      ⟨entry, hEntry, rfl, hTrue⟩
    simpa [PropResolution.Lit.Holds, hPositive entry hEntry] using hValue

omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem avatarComponentSemantics_of_registry
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {dag : DAG σ} (compiled : Compile.CheckedDAGClauses dag)
    (entries : List (AvatarSelectorComponent σ))
    (hPositive : ∀ entry, entry ∈ entries → entry.selector.positive = true)
    (hCompatible : AvatarSelectorComponent.Compatible entries)
    (hSourceEq : ∀ {splitId splitNode splitPayload},
      dag.node? splitId = some splitNode →
        splitNode.payload = .avatarSplit splitPayload →
          splitNode.conclusion = splitPayload.source.clause)
    (hEntry : ∀ {splitId splitNode splitPayload componentIndex indices selector},
      dag.node? splitId = some splitNode →
        splitNode.payload = .avatarSplit splitPayload →
          splitPayload.partitions[componentIndex]? = some indices →
            AvatarSplit.selectorAt? splitPayload.selectors componentIndex =
              some selector →
                ⟨selector,
                  Clause.atIndices splitPayload.source.clause indices⟩ ∈ entries) :
    AvatarComponentSemantics M compiled
      (avatarSelectorValuation M compiled entries) := by
  intro splitId splitNode splitPayload componentIndex indices selector
    hNode hPayload hIndices hSelector
  let entry : AvatarSelectorComponent σ :=
    ⟨selector, Clause.atIndices splitNode.conclusion indices⟩
  have hEntrySource :
      (⟨selector, Clause.atIndices splitPayload.source.clause indices⟩ :
        AvatarSelectorComponent σ) ∈ entries :=
    hEntry hNode hPayload hIndices hSelector
  have hSource := hSourceEq hNode hPayload
  have hEntry' : entry ∈ entries := by
    simpa [entry, hSource] using hEntrySource
  exact avatarSelector_holds_iff_trueIn M compiled entries
    hPositive hCompatible hEntry'

theorem avatarComponent_guardedNodeTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : AvatarComponentPayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload =
      .avatarComponent payload)
    (hSemantics : AvatarComponentSemantics M compiled valuation) :
    GuardedNodeTrueIn M valuation compiled index hIndex := by
  intro hCurrent
  have hGuardCheck :=
    (cert.contract.node_contract index hIndex).guards_checked
  have hLocalCheck :
      cert.dag.avatarComponentNodeOk
        (cert.dag.nodeAt index hIndex) payload = true := by
    simpa [DAG.localNodeGuardsOk, hPayload] using hGuardCheck
  rcases avatarComponentNodeOk_fields hLocalCheck with
    ⟨splitNode, splitPayload, indices, selector, hSplitNode,
      hSplitPayload, hIndices, hSelector, hSplitUnguarded,
      hConclusion, hGuardEq⟩
  have hSelectorHoldSet : GuardsHold valuation #[selector] :=
    GuardsHold.of_eq hGuardEq hCurrent
  have hSelectorMem :
      selector ∈ (Guards.canonical #[selector]).toList := by
    apply PropResolution.mem_canonicalClause_of_mem
    simp
  have hSelectorHolds : selector.Holds valuation :=
    hSelectorHoldSet selector hSelectorMem
  have hComponentValid :
      AvatarClauseTrueIn M compiled
        (Clause.atIndices splitNode.conclusion indices) :=
    (hSemantics hSplitNode hSplitPayload hIndices hSelector).mp
      hSelectorHolds
  rcases hComponentValid with ⟨component, hComponentRaw, hComponentTrue⟩
  have hNodeRaw :
      (compiled.nodeAt index hIndex).raw = component.raw := by
    calc
      (compiled.nodeAt index hIndex).raw =
          (cert.dag.nodeAt index hIndex).conclusion :=
        compiled.nodeAt_raw index hIndex
      _ = Clause.atIndices splitNode.conclusion indices := hConclusion
      _ = component.raw := hComponentRaw.symm
  exact Compile.CompiledClause.trueIn_iff_of_raw_eq M hNodeRaw |>.mpr
    hComponentTrue

theorem avatarSkeleton_initial_satisfies
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (assignment : Assignment M compiled.compilation.registry.context)
    (atomMap : Array (Formula σ))
    (link : PropAvatarSkeletonLink)
    (initial : PropResolution.InitialClause)
    (hCheck : link.check (cert.dag.nodeAt index hIndex).parents
      atomMap initial = true)
    (hDag : cert.dag.propAvatarSkeletonInitialLinkOk
      (cert.dag.nodeAt index hIndex).parents link = true)
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex))
    (hSplitSemantics : AvatarSplitSemantics M compiled valuation) :
    PropResolution.Clause.Satisfies
      (overlayValuation M assignment valuation atomMap) initial.clause := by
  have hCheckParts := Bool.and_eq_true_iff.mp hCheck
  have hCheckPrefix := Bool.and_eq_true_iff.mp hCheckParts.1
  have hParentMem :
      link.parent ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
    have hParentArray :
        link.parent ∈ (cert.dag.nodeAt index hIndex).parents := by
      simpa using hCheckPrefix.1
    exact Array.mem_def.mp hParentArray
  have hInitialEq : initial.clause = link.skeleton :=
    PropResolution.clauseEq_eq.mp hCheckParts.2
  let hParentIndex :=
    Nat.lt_trans
      (cert.contract.parents_before index hIndex link.parent hParentMem)
      hIndex
  have hParentNodeSome :
      cert.dag.node? link.parent =
        some (cert.dag.nodeAt link.parent hParentIndex) :=
    cert.dag.node?_eq_some_nodeAt hParentIndex
  unfold DAG.propAvatarSkeletonInitialLinkOk at hDag
  rw [hParentNodeSome] at hDag
  have hDagParts := Bool.and_eq_true_iff.mp hDag
  have hSplitFields := Bool.and_eq_true_iff.mp hDagParts.2
  have hParentGuards :
      GuardsHold valuation
        (cert.dag.nodeAt link.parent hParentIndex).guards :=
    guardsHold_of_unguarded hSplitFields.1
  have hParentTrue :
      NodeTrueIn M compiled link.parent hParentIndex := by
    exact hParents link.parent hParentMem hParentGuards
  cases hParentPayload :
      (cert.dag.nodeAt link.parent hParentIndex).payload with
  | avatarSplit splitPayload =>
      rw [hParentPayload] at hSplitFields
      have hSkeletonEq :
          link.skeleton =
            PropResolution.canonicalClause splitPayload.selectors :=
        PropResolution.clauseEq_eq.mp (by simpa using hSplitFields.2)
      have hParentAvatar :
          AvatarClauseTrueIn M compiled
            (cert.dag.nodeAt link.parent hParentIndex).conclusion :=
        ⟨compiled.nodeAt link.parent hParentIndex,
          compiled.nodeAt_raw link.parent hParentIndex, hParentTrue⟩
      have hSkeletonTrue :
          PropResolution.Clause.Satisfies valuation
            (PropResolution.canonicalClause splitPayload.selectors) :=
        (hSplitSemantics hParentNodeSome hParentPayload).mp hParentAvatar
      rcases hSkeletonTrue with ⟨literal, hLiteralMem, hLiteral⟩
      have hLiteralLinkMem : literal ∈ link.skeleton.toList := by
        rw [hSkeletonEq]
        exact hLiteralMem
      have hLiteralOutside :
          PropLiteralLink.outsideAtomMap atomMap literal = true := by
        have hOutside := hCheckPrefix.2
        have hAll := Array.all_eq_true.mp hOutside
        have hArrayMem : literal ∈ link.skeleton :=
          Array.mem_def.mpr hLiteralLinkMem
        rcases Array.mem_iff_getElem.mp hArrayMem with
          ⟨literalIndex, hLiteralIndex, hLiteralGet⟩
        simpa [hLiteralGet] using hAll literalIndex hLiteralIndex
      have hLiteralOverlay :
          literal.Holds (overlayValuation M assignment valuation atomMap) :=
        (holds_of_outside_overlay M assignment valuation atomMap literal
          hLiteralOutside).mpr hLiteral
      exact PropResolution.Clause.satisfies_of_mem
        (by simpa [hInitialEq] using hLiteralLinkMem) hLiteralOverlay
  | source _ =>
      simp [hParentPayload] at hSplitFields
  | avatarComponent _ =>
      simp [hParentPayload] at hSplitFields
  | localRule _ =>
      simp [hParentPayload] at hSplitFields
  | theoryConflict _ =>
      simp [hParentPayload] at hSplitFields
  | propositionalLearnedClause _ =>
      simp [hParentPayload] at hSplitFields
  | residualCdcl _ =>
      simp [hParentPayload] at hSplitFields

theorem avatarInitialJustification_satisfies
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (assignment : Assignment M compiled.compilation.registry.context)
    (atomMap : Array (Formula σ))
    (justification : PropInitialJustification σ)
    (initial : PropResolution.InitialClause)
    (hCheck : justification.check (cert.dag.nodeAt index hIndex).parents
      atomMap initial = true)
    (hDag : cert.dag.propInitialJustificationDagOk
      (cert.dag.nodeAt index hIndex).parents justification = true)
    (hSupported : justification.avatarSoundnessSupported = true)
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex))
    (hSplitSemantics : AvatarSplitSemantics M compiled valuation) :
    PropResolution.Clause.Satisfies
      (overlayValuation M assignment valuation atomMap) initial.clause := by
  cases justification with
  | parentClause link =>
      exact initialJustification_satisfies M valuation cert compiled index hIndex
        assignment atomMap (.parentClause link) initial hCheck hDag (by rfl)
        hParents
  | guardActivationClause link =>
      exact initialJustification_satisfies M valuation cert compiled index hIndex
        assignment atomMap (.guardActivationClause link) initial hCheck hDag
        (by rfl) hParents
  | propLearnedClause link =>
      exact initialJustification_satisfies M valuation cert compiled index hIndex
        assignment atomMap (.propLearnedClause link) initial hCheck hDag (by rfl)
        hParents
  | avatarSkeleton link =>
      exact avatarSkeleton_initial_satisfies M valuation cert compiled index hIndex
        assignment atomMap link initial hCheck hDag hParents hSplitSemantics

theorem avatarInitialSatisfies_of_justificationsListCheck
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (assignment : Assignment M compiled.compilation.registry.context)
    (atomMap : Array (Formula σ))
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex))
    (hSplitSemantics : AvatarSplitSemantics M compiled valuation) :
    ∀ {initials : List PropResolution.InitialClause}
      {justifications : List (PropInitialJustification σ)},
      PropositionalClosurePayload.justificationsListCheck
        (cert.dag.nodeAt index hIndex).parents atomMap
        initials justifications = true →
      (∀ justification, justification ∈ justifications →
        cert.dag.propInitialJustificationDagOk
          (cert.dag.nodeAt index hIndex).parents justification = true) →
      (∀ justification, justification ∈ justifications →
        justification.avatarSoundnessSupported = true) →
      ∀ initial, initial ∈ initials →
        PropResolution.Clause.Satisfies
          (overlayValuation M assignment valuation atomMap) initial.clause := by
  intro initials
  induction initials with
  | nil =>
      intro justifications hCheck hDag hSupported target hTarget
      simp at hTarget
  | cons initial initials ih =>
      intro justifications
      cases justifications with
      | nil =>
          intro hCheck hDag hSupported target hTarget
          simp [PropositionalClosurePayload.justificationsListCheck] at hCheck
      | cons justification justifications =>
          intro hCheck hDag hSupported target hTarget
          have hCheckParts := Bool.and_eq_true_iff.mp hCheck
          have hHeadCheck := hCheckParts.1
          have hTailCheck := hCheckParts.2
          have hHeadDag := hDag justification (by simp)
          have hHeadSupported := hSupported justification (by simp)
          have hHeadSat := avatarInitialJustification_satisfies M valuation cert
            compiled index hIndex assignment atomMap justification initial
            hHeadCheck hHeadDag hHeadSupported hParents hSplitSemantics
          have hTailDag : ∀ item, item ∈ justifications →
              cert.dag.propInitialJustificationDagOk
                (cert.dag.nodeAt index hIndex).parents item = true := by
            intro item hItem
            exact hDag item (by simp [hItem])
          have hTailSupported : ∀ item, item ∈ justifications →
              item.avatarSoundnessSupported = true := by
            intro item hItem
            exact hSupported item (by simp [hItem])
          rcases List.mem_cons.mp hTarget with rfl | hTarget
          · exact hHeadSat
          · exact ih hTailCheck hTailDag hTailSupported target hTarget

theorem residualCdcl_avatar_guardedNodeTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (assignment : Assignment M compiled.compilation.registry.context)
    (payload : PropositionalClosurePayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload =
      .residualCdcl payload)
    (hPayloadSupported : payload.avatarSoundnessSupported = true)
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex))
    (hSplitSemantics : AvatarSplitSemantics M compiled valuation) :
    GuardedNodeTrueIn M valuation compiled index hIndex := by
  intro _hCurrent
  have hCheck := payloadCheck_of_payload_eq cert index hIndex hPayload
  have hResidualCheck :
      (!((cert.dag.nodeAt index hIndex).parents.isEmpty) &&
        (cert.dag.nodeAt index hIndex).conclusion.isEmpty &&
          payload.check (cert.dag.nodeAt index hIndex).parents) = true := by
    simpa [Payload.check, hPayload] using hCheck
  have hPayloadCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents = true :=
    (Bool.and_eq_true_iff.mp hResidualCheck).2
  have hCheck₁ := Bool.and_eq_true_iff.mp hPayloadCheck
  have hCheck₂ := Bool.and_eq_true_iff.mp hCheck₁.1
  have hCheck₃ := Bool.and_eq_true_iff.mp hCheck₂.1
  have hCheck₄ := Bool.and_eq_true_iff.mp hCheck₃.1
  have hCheck₅ := Bool.and_eq_true_iff.mp hCheck₄.1
  have hCheck₆ := Bool.and_eq_true_iff.mp hCheck₅.1
  have hUnsat :
      PropResolution.checkedUnsat payload.initialClauses payload.proof = true :=
    hCheck₆.1
  have hJustifications :
      payload.justificationsCheck (cert.dag.nodeAt index hIndex).parents = true :=
    hCheck₆.2
  have hJustificationsList :=
    PropositionalClosurePayload.justificationsListCheck_eq_true_of_check
      hJustifications
  have hDagLinksAll :
      payload.initialJustifications.all (fun justification =>
        cert.dag.propInitialJustificationDagOk
          (cert.dag.nodeAt index hIndex).parents justification) = true := by
    have hLinks :=
      (cert.contract.node_contract index hIndex).prop_initial_links_checked
    simpa [DAG.propInitialLinksOk, hPayload] using hLinks
  have hDagLinks : ∀ justification,
      justification ∈ payload.initialJustifications.toList →
        cert.dag.propInitialJustificationDagOk
          (cert.dag.nodeAt index hIndex).parents justification = true := by
    intro justification hMem
    exact array_check_of_mem hDagLinksAll hMem
  have hSupportedAll :
      payload.initialJustifications.all
        PropInitialJustification.avatarSoundnessSupported = true := by
    simpa [PropositionalClosurePayload.avatarSoundnessSupported] using
      hPayloadSupported
  have hSupported : ∀ justification,
      justification ∈ payload.initialJustifications.toList →
        justification.avatarSoundnessSupported = true := by
    intro justification hMem
    exact array_check_of_mem hSupportedAll hMem
  have hInitial : ∀ initial,
      initial ∈ payload.initialClauses.toList →
        PropResolution.Clause.Satisfies
          (overlayValuation M assignment valuation payload.atomMap) initial.clause := by
    exact avatarInitialSatisfies_of_justificationsListCheck M valuation cert
      compiled index hIndex assignment payload.atomMap hParents hSplitSemantics
      hJustificationsList hDagLinks hSupported
  exact False.elim <|
    PropResolution.checkedUnsat_sound
      (valuation := overlayValuation M assignment valuation payload.atomMap)
      hInitial hUnsat

theorem avatarSplit_guardedNodeTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (hInitial : ∀ target ∈ compiled.compilation.initialClauses.toList,
      target.TrueIn M)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : AvatarSplitPayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload =
      .avatarSplit payload) :
    GuardedNodeTrueIn M valuation compiled index hIndex := by
  intro _hCurrent
  have hPayloadCheck :=
    payloadCheck_of_payload_eq cert index hIndex hPayload
  have hSplitCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold AvatarSplitPayload.check at hSplitCheck
  have hSplitParts := Bool.and_eq_true_iff.mp hSplitCheck
  have hSourceParts := Bool.and_eq_true_iff.mp hSplitParts.1
  have hSourceMem :
      payload.source.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hSourceParts.2
  have hConclusion :
      (cert.dag.nodeAt index hIndex).conclusion = payload.source.clause :=
    (Clause.eq_sound payload.source.clause
      (cert.dag.nodeAt index hIndex).conclusion hSplitParts.2).symm
  let hSourceIndex :=
    Nat.lt_trans
      (cert.contract.parents_before index hIndex payload.source.id hSourceMem)
      hIndex
  have hSourceParentMem :
      payload.source ∈
        (Payload.avatarSplit payload).parentClauses.toList := by
    simp [Payload.parentClauses, AvatarSplitPayload.parentClauses]
  have hSnapshot : cert.dag.parentSnapshotChecked payload.source = true :=
    parentSnapshotChecked_of_payload_mem cert index hIndex hPayload
      hSourceParentMem
  rcases DAG.parentSnapshotChecked_sound hSnapshot with
    ⟨snapshotNode, hSnapshotNode, hSnapshotClause⟩
  have hSnapshotNodeEq :
      snapshotNode = cert.dag.nodeAt payload.source.id hSourceIndex := by
    exact Option.some.inj
      (hSnapshotNode.symm.trans
        (cert.dag.node?_eq_some_nodeAt hSourceIndex))
  have hSnapshotClause' :
      (cert.dag.nodeAt payload.source.id hSourceIndex).conclusion =
        payload.source.clause := by
    rw [← hSnapshotNodeEq]
    exact hSnapshotClause
  have hNodeOk :
      cert.dag.avatarSplitNodeOk
        (cert.dag.nodeAt index hIndex) payload = true := by
    have hGuardCheck :=
      (cert.contract.node_contract index hIndex).guards_checked
    simpa [DAG.localNodeGuardsOk, hPayload] using hGuardCheck
  rcases avatarSplitNodeOk_fields hNodeOk with
    ⟨_hNodeUnguarded, _hSnapshotChecked, sourceNode, initialIndex,
      hSourceSome, _hSourceUnguarded, hSourcePayload⟩
  have hSourceNodeEq :
      sourceNode = cert.dag.nodeAt payload.source.id hSourceIndex := by
    exact Option.some.inj
      (hSourceSome.symm.trans
        (cert.dag.node?_eq_some_nodeAt hSourceIndex))
  have hSourcePayloadAt :
      (cert.dag.nodeAt payload.source.id hSourceIndex).payload =
        .source initialIndex := by
    simpa [← hSourceNodeEq] using hSourcePayload
  have hSourcePayloadCheck :=
    (cert.contract.node_contract payload.source.id hSourceIndex).payload_checked
  rw [hSourcePayloadAt] at hSourcePayloadCheck
  have hSourceCheck :
      Payload.check cert.dag.problem
        (cert.dag.nodeAt payload.source.id hSourceIndex).parents
        (cert.dag.nodeAt payload.source.id hSourceIndex).conclusion
        (.source initialIndex) = true := by
    simpa [Payload.check] using hSourcePayloadCheck
  have hSourceTrue :
      NodeTrueIn M compiled payload.source.id hSourceIndex :=
    source_trueIn M cert compiled hInitial payload.source.id hSourceIndex
      initialIndex hSourceCheck
  have hSourceRaw :
      (compiled.nodeAt payload.source.id hSourceIndex).raw =
        payload.source.clause := by
    exact (compiled.nodeAt_raw payload.source.id hSourceIndex).trans
      hSnapshotClause'
  have hNodeRaw :
      (compiled.nodeAt index hIndex).raw =
        (compiled.nodeAt payload.source.id hSourceIndex).raw := by
    exact (compiled.nodeAt_raw index hIndex).trans
      (hConclusion.trans hSourceRaw.symm)
  exact (Compile.CompiledClause.trueIn_iff_of_raw_eq M hNodeRaw).mpr
    hSourceTrue

omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem DAG.avatarSoundnessSupported_of_eq_true
    {dag : DAG σ} (hSupported : dag.avatarSoundnessSupported = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      (dag.nodeAt index hIndex).payload.avatarSoundnessSupported = true := by
  intro index hIndex
  have hNode := Array.all_eq_true.mp hSupported index hIndex
  simpa [DAG.avatarSoundnessSupported, DAG.nodeAt,
    DAG.nodeAvatarSoundnessSupported] using! hNode

theorem avatarGuardedNodeTrueIn_of_supported
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (hInitial : ∀ target ∈ compiled.compilation.initialClauses.toList,
      target.TrueIn M)
    (hComponentSemantics :
      AvatarComponentSemantics M compiled valuation)
    (hSplitSemantics : AvatarSplitSemantics M compiled valuation)
    (hSupported : cert.dag.avatarSoundnessSupported = true) :
    ∀ index (hIndex : index < cert.dag.nodes.size),
      GuardedNodeTrueIn M valuation compiled index hIndex := by
  refine cert.dag.topologicalInduction cert.contract.parents_before
    (P := fun index hIndex _ =>
      GuardedNodeTrueIn M valuation compiled index hIndex) ?_
  intro index hIndex hParents
  have hNodeSupported :=
    DAG.avatarSoundnessSupported_of_eq_true hSupported index hIndex
  cases hPayload : (cert.dag.nodeAt index hIndex).payload with
  | source initialIndex =>
      exact source_guardedNodeTrueIn M valuation cert compiled index hIndex
        initialIndex hPayload hInitial
  | avatarSplit payload =>
      exact avatarSplit_guardedNodeTrueIn M valuation cert compiled hInitial
        index hIndex payload hPayload
  | avatarComponent payload =>
      exact avatarComponent_guardedNodeTrueIn M valuation cert compiled index
        hIndex payload hPayload hComponentSemantics
  | localRule payload =>
      exact localRule_guardedNodeTrueIn M valuation cert compiled index hIndex
        payload hPayload hParents
  | theoryConflict payload =>
      exact theoryConflict_guardedNodeTrueIn M valuation cert compiled index
        hIndex payload hPayload hParents
  | propositionalLearnedClause payload =>
      exact propositionalLearned_guardedNodeTrueIn M valuation cert compiled
        index hIndex payload hPayload hParents
  | residualCdcl payload =>
      have hPayloadSupported : payload.avatarSoundnessSupported = true := by
        simpa [hPayload, Payload.avatarSoundnessSupported] using hNodeSupported
      rcases assignmentNonempty M compiled.compilation.registry.context with
        ⟨assignment⟩
      exact residualCdcl_avatar_guardedNodeTrueIn M valuation cert compiled
        index hIndex assignment payload hPayload hPayloadSupported hParents
        hSplitSemantics

theorem rootNodeTrueIn_of_avatar_supported
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (hInitial : ∀ target ∈ compiled.compilation.initialClauses.toList,
      target.TrueIn M)
    (hComponentSemantics :
      AvatarComponentSemantics M compiled valuation)
    (hSplitSemantics : AvatarSplitSemantics M compiled valuation)
    (hSupported : cert.dag.avatarSoundnessSupported = true) :
    NodeTrueIn M compiled cert.dag.root cert.contract.root_exists := by
  have hAll := avatarGuardedNodeTrueIn_of_supported M valuation cert compiled
    hInitial hComponentSemantics hSplitSemantics hSupported
    cert.dag.root cert.contract.root_exists
  have hRootUnguarded :
      (cert.dag.nodeAt cert.dag.root cert.contract.root_exists).guards.isEmpty = true := by
    simpa [Node.unguarded] using cert.contract.root_unguarded
  exact hAll (guardsHold_of_unguarded hRootUnguarded)

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
