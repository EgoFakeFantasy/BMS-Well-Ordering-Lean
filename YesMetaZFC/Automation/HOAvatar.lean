import YesMetaZFC.Automation.HOSearch
import YesMetaZFC.Automation.Guards
import YesMetaZFC.Automation.PropCdcl
import YesMetaZFC.Automation.Resolution.CertificateSlice
import YesMetaZFC.Automation.Superposition
/-!
# 原生高阶 saturation / CDCL 双核协调器
本模块直接以 HO-AVATAR split/component DAG 为搜索种子。saturation clause id 与
HO-DAG node id 通过显式表对齐；每轮 given-clause 新增的 proof step 会立即写回同一个
persistent DAG arena。CDCL UNSAT 后再自动追加 theory conflict、learned clause 与
residual root。
-/
namespace YesMetaZFC
namespace Automation
namespace HOAvatar
open HOSearchMaterialization
abbrev SearchClause := CoreSyntax.Search.Clause
abbrev DAG := HOSearchMaterialization.DAG
abbrev Node := HOSearchMaterialization.Node
abbrev CheckedAvatarDAG :=
  HODAGCertificate.CheckedAvatarDAG (σ := HOSearchMaterialization.SearchSignature)
abbrev Diagnostic := Certificate.Diagnostic
def diagnostic (phase : Certificate.Phase) (message : String) : Diagnostic :=
  Certificate.Diagnostic.ofMessage .superposition phase message
structure Config where
  higherOrder : HOSearch.Config := {}
  saturation : Redundancy.Config := {}
  cdcl : PropCdcl.Incremental.Config := {}
  theoryFuelPerModel : Nat := 256
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
def saturationEligible : HODAGCertificate.Payload
    HOSearchMaterialization.SearchSignature → Bool
  | .avatarComponent _ => true
  | .betaEta _ => true
  | .substitution _ => true
  | .standardizeApart _ => true
  | .resolution _ => true
  | .factoring _ => true
  | .equalityResolution _ => true
  | .booleanExtensionality _ => true
  | .rewrite _ _ => true
  | .argumentCongruence _ => true
  | .functionExtensionality _ => true
  | .source _ => false
  | .avatarSplit _ => false
  | .theoryConflict _ => false
  | .propositionalLearnedClause _ => false
  | .residualCdcl _ => false
private def extensionalSeedParentOk (dag : DAG) (parentId : Nat) : Bool :=
  match dag.node? parentId with
  | some parent => HOSearch.avatarExtensionalParentEligible parent
  | none => false
/--
HO-AVATAR saturation seed 的来源纪律。
component 必须携带 selector guard；β/η 是唯一允许无 guard 进入 arena 的全局公理；
其余普通推理节点必须继承非空 component guard。外延一元节点还要追溯直接父来源。
-/
def saturationSeedNodeOk (dag : DAG) (node : Node) : Bool :=
  node.check dag.problem &&
    dag.localNodeGuardsOk node &&
      match node.payload with
      | .avatarComponent _ => !node.unguarded
      | .betaEta _ => node.unguarded
      | .substitution _ => !node.unguarded
      | .standardizeApart _ => !node.unguarded
      | .resolution _ => !node.unguarded
      | .factoring _ => !node.unguarded
      | .equalityResolution _ => !node.unguarded
      | .booleanExtensionality evidence =>
          !node.unguarded && extensionalSeedParentOk dag evidence.parent.id
      | .rewrite _ _ => !node.unguarded
      | .argumentCongruence evidence =>
          !node.unguarded && extensionalSeedParentOk dag evidence.parent.id
      | .functionExtensionality evidence =>
          !node.unguarded && extensionalSeedParentOk dag evidence.parent.id
      | _ => false
/--
HO-AVATAR DAG 到双核搜索的稳定 seed。
`guardedClauses`、`dagNodeIds` 同槽；`splitNodeIds`、`propInitialClauses` 同槽。
-/
structure ArenaSeed where
  dag : DAG
  guardedClauses : Array Superposition.GuardedClause
  dagNodeIds : Array Nat
  splitNodeIds : Array Nat
  propInitialClauses : Array PropResolution.InitialClause
namespace ArenaSeed
private def guardedSlotOk (seed : ArenaSeed) (slot : Nat) (guarded : Superposition.GuardedClause) : Bool :=
  match seed.dagNodeIds[slot]? with
  | none => false
  | some nodeId =>
      match seed.dag.node? nodeId with
      | none => false
      | some node =>
          saturationSeedNodeOk seed.dag node &&
            Guards.eq node.guards guarded.guards &&
              match node.conclusion? seed.dag.problem with
              | none => false
              | some conclusion =>
                  match HOSearch.searchClause? conclusion with
                  | none => false
                  | some projected =>
                      CoreSyntax.Search.clauseEq projected guarded.clause
private def splitSlotOk (seed : ArenaSeed) (slot : Nat) (initial : PropResolution.InitialClause) : Bool :=
  match seed.splitNodeIds[slot]? with
  | none => false
  | some nodeId =>
      match seed.dag.node? nodeId with
      | none => false
      | some node =>
          match node.payload with
          | .avatarSplit payload =>
              PropResolution.clauseEq initial.clause (PropResolution.canonicalClause payload.selectors) &&
                match initial.origin with
                | .residual index => index == node.id
                | _ => false
          | _ => false
def check (seed : ArenaSeed) : Bool :=
  seed.guardedClauses.size == seed.dagNodeIds.size &&
    seed.splitNodeIds.size == seed.propInitialClauses.size && (seed.guardedClauses.mapIdx seed.guardedSlotOk).all id &&
        (seed.propInitialClauses.mapIdx seed.splitSlotOk).all id
def ofSearch? (search : HOSearch.Result) : Option ArenaSeed := do
  let mut guardedClauses : Array Superposition.GuardedClause := #[]
  let mut dagNodeIds : Array Nat := #[]
  let mut splitNodeIds : Array Nat := #[]
  let mut propInitialClauses : Array PropResolution.InitialClause := #[]
  for node in search.dag.nodes do
    match node.payload with
    | .avatarSplit payload =>
        splitNodeIds := splitNodeIds.push node.id
        propInitialClauses := propInitialClauses.push {
          clause := PropResolution.canonicalClause payload.selectors
          origin := .residual node.id
        }
    | _ =>
        pure ()
    if saturationEligible node.payload then
      let conclusion ← node.conclusion? search.dag.problem
      let clause ← HOSearch.searchClause? conclusion
      guardedClauses := guardedClauses.push {
        guards := node.guards
        clause := clause
      }
      dagNodeIds := dagNodeIds.push node.id
  let seed : ArenaSeed := {
    dag := search.dag
    guardedClauses := guardedClauses
    dagNodeIds := dagNodeIds
    splitNodeIds := splitNodeIds
    propInitialClauses := propInitialClauses
  }
  if seed.check && !seed.splitNodeIds.isEmpty then some seed else none
end ArenaSeed
/--
常驻 saturation arena 与同一 HO-DAG 的稳定映射。
`clauseNodeIds[id]` 是 saturation clause `id` 当前对应的最终规则 DAG 节点。
-/
structure PersistentArena where
  saturation : Superposition.State
  dag : DAG
  clauseNodeIds : Array Nat
  seedSize : Nat
namespace PersistentArena
def dagNodeId? (arena : PersistentArena) (clauseId : Nat) : Option Nat :=
  arena.clauseNodeIds[clauseId]?
private def syncStep (arena : PersistentArena) (saturation : Superposition.State) (stepIndex : Nat) :
    Except String PersistentArena := do
  let step ←
    match saturation.steps[stepIndex]? with
    | some step => pure step
    | none => throw s!"missing saturation proof step {stepIndex}"
  let arenaId := arena.seedSize + stepIndex
  let arenaClause ←
    match saturation.clauses[arenaId]? with
    | some clause => pure clause
    | none => throw s!"missing saturation clause {arenaId}"
  let guards ←
    match saturation.guardsAt? arenaId with
    | some guards => pure guards
    | none => throw s!"missing saturation guards {arenaId}"
  if !CoreSyntax.Search.clauseEq arenaClause step.clause then
    throw s!"saturation step {stepIndex} changed its retained clause"
  let resource ←
    match step.resource? with
    | some resource => pure resource
    | none => throw s!"saturation step {stepIndex} has no local proof witness"
  let resource ←
    match resource.remapParentsWith? arena.dagNodeId? with
    | some resource => pure resource
    | none => throw s!"saturation step {stepIndex} has an unmapped parent"
  let next ←
    match pushHigherOrderResource? arena.dag (.local resource) with
    | some next => pure next
    | none => throw s!"saturation step {stepIndex} failed HO-DAG materialization"
  if next.nodes.size ≤ arena.dag.nodes.size then
    throw s!"saturation step {stepIndex} did not append a conclusion node"
  let finalId := next.nodes.size - 1
  let finalNode ←
    match next.node? finalId with
    | some node => pure node
    | none => throw s!"saturation step {stepIndex} lost its final DAG node"
  let conclusion ←
    match finalNode.conclusion? next.problem with
    | some clause => pure clause
    | none => throw s!"saturation step {stepIndex} has no final conclusion"
  let projected ←
    match HOSearch.searchClause? conclusion with
    | some clause => pure clause
    | none => throw s!"saturation step {stepIndex} is not search-projectable"
  if !CoreSyntax.Search.clauseEq projected arenaClause ||
      !Guards.eq finalNode.guards guards then
    throw s!"saturation step {stepIndex} changed its clause or guard support"
  pure {
    arena with
    saturation := saturation
    dag := next
    clauseNodeIds := arena.clauseNodeIds.push finalId
  }
def syncProofSteps (arena : PersistentArena) (saturation : Superposition.State) : Except String PersistentArena := do
  if saturation.clauses.size != arena.seedSize + saturation.steps.size ||
      saturation.guards.size != saturation.clauses.size ||
      saturation.enabled.size != saturation.clauses.size then
    throw "persistent HO saturation clause/proof arena is not aligned"
  if arena.clauseNodeIds.size < arena.seedSize then
    throw "persistent HO DAG mapping is shorter than its seed"
  let synced := arena.clauseNodeIds.size - arena.seedSize
  if synced > saturation.steps.size then
    throw "persistent HO DAG mapping is ahead of the saturation journal"
  let mut current := { arena with saturation := saturation }
  for stepIndex in [synced:saturation.steps.size] do
    current ← current.syncStep saturation stepIndex
  pure current
end PersistentArena
structure TheoryConflict where
  clauseId : Superposition.ClauseId
  guards : Superposition.GuardSet
  learned : PropResolution.Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure TheoryState where
  arena : PersistentArena
  lastAssignment : Array (Option Bool) := #[]
def literalTrue (assignment : Array (Option Bool)) (literal : PropResolution.Lit) : Bool :=
  match assignment.getD literal.var none with
  | some value => if literal.positive then value else !value
  | none => false
def supportActive (assignment : Array (Option Bool)) (guards : Superposition.GuardSet) : Bool :=
  guards.all (literalTrue assignment)
def firstActiveConflictFrom? (state : Superposition.State)
    (assignment : Array (Option Bool))
    (cursor : Data.ClauseMetadataTable.RetainedEmptyCursor) :
    Data.ClauseMetadataTable.RetainedEmptyCursor × Option TheoryConflict :=
  state.clauseMetadata.foldRetainedEmptyFromUntil cursor none fun _ id =>
    if state.enabledAt id then
      match state.clauses[id]?, state.guardsAt? id with
      | some clause, some guards =>
          if clause.isEmpty && supportActive assignment guards then
            .done <| some {
              clauseId := id
              guards := guards
              learned :=
                PropResolution.canonicalClause (guards.map PropResolution.Lit.neg)
            }
          else
            .next none
      | _, _ => .next none
    else
      .next none
def firstActiveConflict? (state : Superposition.State)
    (assignment : Array (Option Bool)) : Option TheoryConflict :=
  (firstActiveConflictFrom? state assignment {}).2
def TheoryConflict.check (state : Superposition.State) (assignment : Array (Option Bool)) (conflict : TheoryConflict) : Bool :=
  state.enabledAt conflict.clauseId && state.retained conflict.clauseId &&
    match state.clauses[conflict.clauseId]?,
        state.guardsAt? conflict.clauseId with
    | some clause, some guards =>
        clause.isEmpty &&
          Guards.eq guards conflict.guards &&
            supportActive assignment conflict.guards &&
              PropResolution.clauseEq conflict.learned (PropResolution.canonicalClause (conflict.guards.map PropResolution.Lit.neg))
    | _, _ => false
/--
在一个 selector assignment 下运行 given-clause，并逐步同步 persistent HO-DAG。
-/
def saturateModel (config : Config) (assignment : Array (Option Bool)) :
    Nat → Redundancy.WorkBudget → PersistentArena →
      Data.ClauseMetadataTable.RetainedEmptyCursor →
      Except String (PersistentArena ×
        Data.ClauseMetadataTable.RetainedEmptyCursor × Option TheoryConflict × Bool)
  | 0, _, arena, cursor =>
      let (cursor, conflict?) :=
        firstActiveConflictFrom? arena.saturation assignment cursor
      pure (arena, cursor, conflict?, false)
  | fuel + 1, budget, arena, cursor =>
      let (cursor, conflict?) :=
        firstActiveConflictFrom? arena.saturation assignment cursor
      match conflict? with
      | some conflict =>
          pure (arena, cursor, some conflict, true)
      | none =>
          match
              Superposition.State.selectGiven?
                config.saturation arena.saturation with
          | some (given, givenWorkspace) => do
              let saturation := {
                arena.saturation with
                givenWorkspace := givenWorkspace
                selectionClock := arena.saturation.selectionClock + 1
                processed := arena.saturation.processed + 1
              }
              let step :=
                Superposition.State.processGiven
                  config.saturation saturation given budget
              let arena ← arena.syncProofSteps step.state
              if step.complete then
                saturateModel config assignment fuel step.budget arena cursor
              else
                pure (arena, cursor, none, false)
          | none =>
              pure (arena, cursor, none, true)
structure TheoryRoundResult where
  state : TheoryState
  conflict? : Option TheoryConflict
  complete : Bool
  error? : Option String := none
def runTheoryRound (config : Config) (arena : PersistentArena)
    (assignment : Array (Option Bool)) (changedVars : Array Nat) : TheoryRoundResult :=
  let saturation :=
    arena.saturation.reseed changedVars (supportActive assignment)
  let arena := { arena with saturation := saturation }
  match saturateModel config assignment config.theoryFuelPerModel
      (Redundancy.WorkBudget.ofConfig config.saturation saturation.lifecycle.work)
      arena {} with
  | .ok (arena, _, conflict?, complete) =>
      {
        state := { arena := arena, lastAssignment := assignment }
        conflict? := conflict?
        complete := complete
      }
  | .error message =>
      {
        state := { arena := arena, lastAssignment := assignment }
        conflict? := none
        complete := false
        error? := some message
      }
namespace TheoryRoundResult
def toTheoryResponse (round : TheoryRoundResult) (assignment : Array (Option Bool)) :
    PropCdcl.Incremental.TheoryResponse TheoryState TheoryConflict :=
  match round.error? with
  | some message =>
      .unknown round.state message
  | none =>
      match round.conflict? with
      | some conflict =>
          if conflict.check round.state.arena.saturation assignment then
            .conflict round.state conflict.learned conflict
          else
            .unknown round.state
              "HO-AVATAR theory conflict failed its guard protocol checker"
      | none =>
          if round.complete then
            .model round.state
          else
            .unknown round.state
              "HO-AVATAR theory saturation exhausted its per-model fuel"
end TheoryRoundResult
def theoryStep (config : Config) (state : TheoryState)
    (delta : PropCdcl.Incremental.AssignmentDelta) :
    PropCdcl.Incremental.TheoryResponse TheoryState TheoryConflict :=
  match state with
  | { arena, lastAssignment } =>
      let assignment := delta.apply lastAssignment
      (runTheoryRound config arena assignment delta.changedVars).toTheoryResponse assignment
structure RunResult where
  initialClauses : Array SearchClause
  higherOrderSearch : HOSearch.Result
  seed : ArenaSeed
  search :
    PropCdcl.Incremental.RunResult TheoryState TheoryConflict
def run (config : Config) (initialClauses : Array SearchClause) :
    Except Diagnostic RunResult := do
  let sourceDag ←
    match avatarSourceDAG? initialClauses with
    | some dag => pure dag
    | none =>
        throw (diagnostic .sourceMaterialization
          "native HO clauses failed HO-AVATAR split/component materialization")
  let higherOrderSearch := HOSearch.runAvatar sourceDag config.higherOrder
  let seed ←
    match ArenaSeed.ofSearch? higherOrderSearch with
    | some seed => pure seed
    | none =>
        throw (diagnostic .sourceMaterialization
          "HO-AVATAR DAG failed persistent saturation/CDCL seed extraction")
  let arena : PersistentArena := {
    saturation :=
      Superposition.State.dormant
        config.saturation seed.guardedClauses
    dag := seed.dag
    clauseNodeIds := seed.dagNodeIds
    seedSize := seed.guardedClauses.size
  }
  let initialState : TheoryState := { arena := arena }
  let search :=
    PropCdcl.Incremental.run config.cdcl 0 (seed.propInitialClauses.map (fun initial => initial.clause))
      initialState (theoryStep config)
  pure {
    initialClauses := initialClauses
    higherOrderSearch := higherOrderSearch
    seed := seed
    search := search
  }
namespace RunResult
def finalInitialClauses (result : RunResult) :
    Array PropResolution.InitialClause :=
  result.seed.propInitialClauses ++
    result.search.theoryClauses.mapIdx fun index clause => {
      clause := clause
      origin := .residual (result.seed.splitNodeIds.size + index)
    }
def unsatProof? (config : Config) (result : RunResult) :
    Option PropResolution.CdclProof :=
  match result.search.outcome with
  | .unsat =>
      PropCdcl.unsatProof? config.cdcl.cdcl 0 result.finalInitialClauses
  | _ =>
      none
def checkedUnsat? (config : Config) (result : RunResult) :
    Option PropResolution.CheckedUnsatCertificate := do
  let proof ← result.unsatProof? config
  PropResolution.CheckedUnsatCertificate.mk?
    result.finalInitialClauses proof
def stats (result : RunResult) : Certificate.Stats :=
  let saturation := result.search.state.arena.saturation
  {
    steps := saturation.steps.size
    clauses := saturation.clauses.size
    generated := saturation.lifecycle.generatedCandidates
    retained := saturation.lifecycle.retainedCandidates
    verified := saturation.lifecycle.checkedCandidates
    residuals := result.search.theoryClauses.size
    fuel := saturation.processed
  }
private def conflictNode? (result : RunResult) (index : Nat) :
    Option Nat := do
  let evidence ← result.search.theoryEvidence[index]?
  let learned ← result.search.theoryClauses[index]?
  if !PropResolution.clauseEq learned evidence.learned then
    none
  let nodeId ←
    result.search.state.arena.dagNodeId? evidence.clauseId
  let node ← result.search.state.arena.dag.node? nodeId
  let conclusion ← node.conclusion? result.search.state.arena.dag.problem
  if conclusion.isEmpty &&
      Guards.eq node.guards evidence.guards &&
        PropResolution.clauseEq learned (Guards.learnedClause node.guards) then
    some nodeId
  else
    none
structure CertificateMaterialization where
  checked : CheckedAvatarDAG
  theoryConflictNodeIds : Array Nat
  learnedClauseNodeIds : Array Nat
  root : Nat
/--
自动把 theory conflict、propositional learned clause 与最终 CDCL root 写入同一
persistent HO-DAG arena，并运行 DAG/selector-registry 双 checker。
-/
def materializeCertificate? (config : Config) (result : RunResult) :
    Except Diagnostic CertificateMaterialization := do
  let proof ←
    match result.unsatProof? config with
    | some proof => pure proof
    | none =>
        throw (diagnostic .residualSplit
          "HO-AVATAR dual-core search did not produce a CDCL UNSAT proof")
  if result.search.theoryClauses.size !=
      result.search.theoryEvidence.size then
    throw (diagnostic .sourceMaterialization
      "HO-AVATAR theory clauses and evidence are not slot-aligned")
  let slice ←
    match PropResolution.CertificateSlice.compactRaw?
        result.finalInitialClauses proof with
    | some slice => pure slice
    | none =>
        throw (diagnostic .residualSplit
          "HO-AVATAR certificate slicing failed")
  let certificate := slice.certificate
  let splitCount := result.seed.splitNodeIds.size
  let mut splitIndices : Array Nat :=
    Array.emptyWithCapacity slice.initialIndices.size
  let mut theoryIndices : Array Nat :=
    Array.emptyWithCapacity slice.initialIndices.size
  for index in slice.initialIndices do
    if index < splitCount then
      splitIndices := splitIndices.push index
    else
      theoryIndices := theoryIndices.push (index - splitCount)
  let mut dag := result.search.state.arena.dag
  let mut theoryConflictNodeIds : Array Nat := #[]
  let mut learnedClauseNodeIds : Array Nat := #[]
  for index in theoryIndices do
    let proofNodeId ←
      match result.conflictNode? index with
      | some id => pure id
      | none =>
          throw (diagnostic .sourceMaterialization
            s!"HO-AVATAR theory conflict {index} lost its persistent DAG origin")
    let (nextDag, conflictId) ←
      match pushTheoryConflict? dag proofNodeId with
      | some result => pure result
      | none =>
          throw (diagnostic .residualSplit
            s!"failed to materialize HO theory conflict {index}")
    dag := nextDag
    let (nextDag, learnedId) ←
      match pushPropositionalLearnedClause? dag conflictId with
      | some result => pure result
      | none =>
          throw (diagnostic .residualSplit
            s!"failed to materialize HO learned clause {index}")
    dag := nextDag
    theoryConflictNodeIds := theoryConflictNodeIds.push conflictId
    learnedClauseNodeIds := learnedClauseNodeIds.push learnedId
  let mut sourceIds : Array Nat :=
    Array.emptyWithCapacity certificate.initialClauses.size
  for index in splitIndices do
    let splitId ←
      match result.seed.splitNodeIds[index]? with
      | some splitId => pure splitId
      | none =>
          throw (diagnostic .sourceMaterialization
            s!"HO-AVATAR split node {index} is missing")
    sourceIds := sourceIds.push splitId
  for learnedId in learnedClauseNodeIds do
    sourceIds := sourceIds.push learnedId
  let checked ←
    match checkedResidualCdclFromSources? dag sourceIds certificate with
    | some checked => pure checked
    | none =>
        throw (diagnostic .dagCheck
          "HO-AVATAR residual root failed the linear HO-DAG checker")
  let avatarChecked ←
    match HODAGCertificate.CheckedAvatarDAG.mk? checked with
    | some checked => pure checked
    | none =>
        throw (diagnostic .dagCheck
          "HO-AVATAR residual graph failed the selector registry checker")
  pure {
    checked := avatarChecked
    theoryConflictNodeIds := theoryConflictNodeIds
    learnedClauseNodeIds := learnedClauseNodeIds
    root := avatarChecked.checked.dag.root
  }
end RunResult
end HOAvatar
end Automation
end YesMetaZFC
