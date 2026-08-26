import YesMetaZFC.Automation.PropCdcl
import YesMetaZFC.Automation.Resolution.CertificateSlice
import YesMetaZFC.Automation.Guards
import YesMetaZFC.Automation.SearchMaterialization
import YesMetaZFC.Automation.Superposition
import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.Data.CanonicalSeedWorkspace
import YesMetaZFC.Automation.LazyDefinitionRegistry
import YesMetaZFC.Automation.Data.CertificateWorkspace
import YesMetaZFC.Automation.Data.Intern
/-!
# AVATAR 一阶饱和 / CDCL 双核协调器
本模块实现搜索期的正统 AVATAR 数据流：
1. 每个输入字句按变量连通性拆成 components；
2. 跨 source 复用结构相同的 component selector；
3. SAT 层持有 source 的 component 析取 skeleton；
4. 一阶层只在当前 assignment 激活的 support 上运行 given-clause；
5. guarded empty `Γ ⟹ ⊥` 立即学习为命题字句 `¬Γ`；
6. 同一个 CDCL machine 与同一个一阶 clause/proof arena 跨轮保留。
component splitting 已通过独立 split descriptor/component payload 接入 SearchDAG 与
最终 DAG checker；它绝不把 component 伪装成 canonical source。对象模型诱导 selector
valuation 的整图 soundness 仍由后续专用 AVATAR 归纳负责。
-/
namespace YesMetaZFC
namespace Automation
namespace Avatar
abbrev Clause := CoreSyntax.Search.Clause
abbrev GuardSet := Superposition.GuardSet
abbrev ComponentId := Nat
structure ComponentOrigin where
  sourceIndex : Nat
  literalIndices : Array Nat
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure Component where
  id : ComponentId
  guard : PropResolution.Lit
  clause : Clause
  origins : Array ComponentOrigin := #[]
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure SourceSplit where
  sourceIndex : Nat
  original : Clause
  partitions : Array (Array Nat)
  components : Array ComponentId
  selectors : PropResolution.Clause
  skeleton : PropResolution.Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure LazySource where
  sourceIndex : Nat
  clause : Clause
  components : Array ComponentId
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure Problem where
  initialClauses : Array Clause
  objectAtomCount : Nat
  components : Array Component
  sourceSplits : Array SourceSplit
  lazySources : Array LazySource := #[]
  sourceArenaSlots : Array (Array Superposition.ClauseId) := #[]
  seedSlots : Array Nat := #[]
  lazyDefinitions? : Option LazyDefinitionRegistry.Payload := none
  propClauses : Array PropResolution.Clause
  numVars : Nat
  deriving Repr, Inhabited, Lean.ToExpr
private def pushNatUnique (values : Array Nat) (value : Nat) : Array Nat :=
  if values.contains value then values else values.push value
abbrev termVars := AvatarSplit.termVars
abbrev literalVars := AvatarSplit.literalVars
abbrev varsOverlap := AvatarSplit.varsOverlap
abbrev clauseAtIndices := AvatarSplit.clauseAtIndices
abbrev splitClause := AvatarSplit.splitClause
private inductive ObjectAtomTag
private inductive ComponentClauseTag
def objectAtomCount (clauses : Array Clause) : Nat :=
  runST fun σ => do
    let atoms ←
      Data.InternTable.Builder.empty (σ := σ) (tag := ObjectAtomTag)
        (α := SearchMaterialization.PropAtom) 64
    for clause in clauses do
      for literal in clause do
        let _ ← atoms.intern (SearchMaterialization.PropAtom.ofLiteral literal)
    atoms.size
private def addOrigin (component : Component) (origin : ComponentOrigin) : Component :=
  if component.origins.contains origin then
    component
  else
    { component with origins := component.origins.push origin }
private def Problem.buildWithSlots (initialClauses : Array Clause) (seedSlots : Array Nat)
    (lazyDefinitions? : Option LazyDefinitionRegistry.Payload) : Problem :=
  runST fun σ => do
    let initialClauses := initialClauses.map Redundancy.normalizeClause
    let guardBase := Avatar.objectAtomCount initialClauses
    let componentClauses ←
      Data.InternTable.Builder.empty (σ := σ) (tag := ComponentClauseTag)
        (α := Clause) (Nat.max 16 initialClauses.size)
    let mut components : Array Component := #[]
    let mut sourceSplits : Array SourceSplit := #[]
    let mut propClauses : Array PropResolution.Clause := #[]
    let mut sourceArenaSlots := (List.replicate initialClauses.size #[]).toArray
    for h : sourceIndex in [:initialClauses.size] do
      let original := initialClauses[sourceIndex]
      let mut componentIds := #[]
      let mut partitions := #[]
      for split in splitClause original do
        let origin : ComponentOrigin := {
          sourceIndex := sourceIndex
          literalIndices := split.1
        }
        let clauseId ← componentClauses.intern split.2
        let id := clauseId.raw - 1
        if id < components.size then
          let component := components[id]!
          components := components.set! id (addOrigin component origin)
        else
          components := components.push {
            id := id
            guard := { var := guardBase + id, positive := true }
            clause := split.2
            origins := #[origin]
          }
        partitions := partitions.push split.1
        componentIds := pushNatUnique componentIds id
      let selectors :=
        componentIds.filterMap fun id =>
          components[id]?.map (fun component => component.guard)
      let skeleton := PropResolution.canonicalClause selectors
      sourceSplits := sourceSplits.push {
        sourceIndex := sourceIndex
        original := original
        partitions := partitions
        components := componentIds
        selectors := selectors
        skeleton := skeleton
      }
      sourceArenaSlots := sourceArenaSlots.set! sourceIndex componentIds
      propClauses := propClauses.push skeleton
    let lazySlots :=
      match lazyDefinitions? with
      | some registry => registry.lazySlots
      | none => #[]
    let mut lazySources : Array LazySource := #[]
    for h : sourceIndex in [:initialClauses.size] do
      if lazySlots.contains sourceIndex then
        lazySources := lazySources.push {
          sourceIndex := sourceIndex
          clause := initialClauses[sourceIndex]
          components := sourceArenaSlots.getD sourceIndex #[]
        }
    return {
      initialClauses := initialClauses
      objectAtomCount := guardBase
      components := components
      sourceSplits := sourceSplits
      lazySources := lazySources
      sourceArenaSlots := sourceArenaSlots
      seedSlots := seedSlots
      lazyDefinitions? := lazyDefinitions?
      propClauses := propClauses
      numVars := guardBase + components.size
    }
def Problem.build (initialClauses : Array Clause) : Problem :=
  Problem.buildWithSlots initialClauses (List.range initialClauses.size).toArray none
def Problem.buildWithLazyDefinitions (registry : LazyDefinitionRegistry.Checked) : Problem :=
  Problem.buildWithSlots registry.payload.initialClauses
    registry.payload.seedSlots (some registry.payload)
namespace Problem
def guardedComponents (problem : Problem) : Array Superposition.GuardedClause :=
  problem.components.map fun component => {
    guards := #[component.guard]
    clause := component.clause
  }
def guardedArenaInputs (problem : Problem) : Array Superposition.GuardedClause :=
  problem.guardedComponents
/--
固定输入前缀的初始开放掩码。
只要一个 interned component 至少有一个 seed source origin，它就从第一轮开始开放。
-/
def initialEnabled (problem : Problem) : Array Bool :=
  problem.components.map fun component =>
    component.origins.any fun origin =>
      problem.seedSlots.contains origin.sourceIndex
def arenaInputSize (problem : Problem) : Nat :=
  problem.components.size
def lazyArenaIdsForClause (problem : Problem) (clause : Clause) :
    Array Superposition.ClauseId :=
  match problem.lazyDefinitions? with
  | none => #[]
  | some registry =>
      clause.foldl (fun ids literal =>
          (registry.slotsForLiteral literal).foldl (fun ids slot =>
              match problem.sourceArenaSlots[slot]? with
              | some sourceIds => sourceIds.foldl pushNatUnique ids
              | none => ids)
            ids)
        #[]
def enableLazySourcesForGiven (problem : Problem) (supportIsActive : GuardSet → Bool) (state : Superposition.State)
    (given : Superposition.PassiveEntry) : Superposition.State :=
  match state.clauses[given.clauseId]? with
  | some clause =>
      state.enableClausesSupported (problem.lazyArenaIdsForClause clause)
        supportIsActive
  | none => state
def propInitialClauses (problem : Problem) :
    Array PropResolution.InitialClause :=
  problem.sourceSplits.map fun split => {
    clause := split.skeleton
    origin := .residual split.sourceIndex
  }
structure SearchSeed where
  dag : SearchMaterialization.SearchDAG
  sourceNodes : Array SearchMaterialization.ClauseInfo
  splitNodes : Array SearchMaterialization.ClauseInfo
  componentNodes : Array SearchMaterialization.ClauseInfo
/--
把 AVATAR problem 的 canonical source table 自动物化为轻量 SearchDAG。
同一个 interned component 只建立一个节点；它可以被多个 source skeleton 复用，但其
split 来源固定为首次出现的 source descriptor。
-/
def searchSeed? (problem : Problem) : Option SearchSeed := do
  let mut dag := SearchMaterialization.SearchDAG.ofInitialClauses problem.initialClauses
  let mut workspace :=
    Data.CanonicalSeedWorkspace.emptyWithCapacity
      problem.sourceSplits.size problem.sourceSplits.size problem.components.size
  for h : splitIndex in [:problem.sourceSplits.size] do
    let split := problem.sourceSplits[splitIndex]
    if workspace.sourceIsUsed split.sourceIndex || workspace.splitIsUsed splitIndex then
      none
    else
      let (nextDag, source) ←
        dag.addSourceKnownUnused? #[] split.sourceIndex
      dag := nextDag
      let nextWorkspace ← workspace.registerSource? split.sourceIndex source.id
      workspace := nextWorkspace
      let (nextDag, splitNode) ←
        dag.addAvatarSplitKnownUnused? source split.partitions split.selectors
      dag := nextDag
      let nextWorkspace ← workspace.registerSplit? splitIndex splitNode.id
      workspace := nextWorkspace
      if split.components.size != split.partitions.size then
        none
      else
        for h : localIndex in [:split.components.size] do
          let componentId := split.components[localIndex]
          match workspace.componentNode? componentId with
          | some _ => pure ()
          | none =>
              let (nextDag, componentNode) ←
                dag.addAvatarComponentKnownUnused? splitNode localIndex
              let component ← problem.components[componentId]?
              if CoreSyntax.Search.clauseEq componentNode.clause component.clause then
                let nextWorkspace ←
                  workspace.registerComponent? componentId componentNode.id
                dag := nextDag
                workspace := nextWorkspace
              else
                none
  let mut sourceNodes : Array SearchMaterialization.ClauseInfo := #[]
  for split in problem.sourceSplits do
    let sourceId ← workspace.sourceNode? split.sourceIndex
    let source ← dag.get? sourceId
    sourceNodes := sourceNodes.push source
  let mut splitNodes : Array SearchMaterialization.ClauseInfo := #[]
  for h : splitIndex in [:problem.sourceSplits.size] do
    let splitId ← workspace.splitNode? splitIndex
    let splitNode ← dag.get? splitId
    splitNodes := splitNodes.push splitNode
  let mut componentNodes : Array SearchMaterialization.ClauseInfo := #[]
  for h : componentId in [:problem.components.size] do
    let componentNodeId ← workspace.componentNode? componentId
    let componentNode ← dag.get? componentNodeId
    componentNodes := componentNodes.push componentNode
  pure {
    dag := dag
    sourceNodes := sourceNodes
    splitNodes := splitNodes
    componentNodes := componentNodes
  }
end Problem
def literalTrue (assignment : Array (Option Bool)) (literal : PropResolution.Lit) : Bool :=
  match assignment.getD literal.var none with
  | some value => if literal.positive then value else !value
  | none => false
def supportActive (assignment : Array (Option Bool)) (guards : GuardSet) : Bool :=
  guards.all (literalTrue assignment)
structure TheoryConflict where
  clauseId : Superposition.ClauseId
  guards : GuardSet
  learned : PropResolution.Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure TheoryState where
  saturation : Superposition.State
  lastAssignment : Array (Option Bool) := #[]
  deriving Repr, Lean.ToExpr
structure Config where
  saturation : Redundancy.Config := {}
  cdcl : PropCdcl.Incremental.Config := {}
  theoryFuelPerModel : Nat := 256
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
def firstActiveConflictFrom? (state : Superposition.State) (assignment : Array (Option Bool)) (cursor : Data.ClauseMetadataTable.RetainedEmptyCursor) :
    Data.ClauseMetadataTable.RetainedEmptyCursor × Option TheoryConflict :=
  state.clauseMetadata.foldRetainedEmptyFromUntil cursor none fun _ id =>
    if state.enabledAt id then
      match state.clauses[id]?, state.guardsAt? id with
      | some clause, some guards =>
          if clause.isEmpty && supportActive assignment guards then
            .done <| some {
              clauseId := id
              guards := guards
              learned := PropResolution.canonicalClause (guards.map PropResolution.Lit.neg)
            }
          else
            .next none
      | _, _ => .next none
    else
      .next none
def firstActiveConflict? (state : Superposition.State) (assignment : Array (Option Bool)) : Option TheoryConflict :=
  (firstActiveConflictFrom? state assignment {}).2
def TheoryConflict.check (state : Superposition.State) (assignment : Array (Option Bool)) (conflict : TheoryConflict) : Bool :=
  state.enabledAt conflict.clauseId && state.retained conflict.clauseId &&
    match state.clauses[conflict.clauseId]?, state.guardsAt? conflict.clauseId with
    | some clause, some guards =>
        clause.isEmpty &&
          Guards.eq guards conflict.guards &&
            supportActive assignment conflict.guards &&
              PropResolution.clauseEq conflict.learned (PropResolution.canonicalClause (conflict.guards.map PropResolution.Lit.neg))
    | _, _ => false
def saturateModel (config : Config) (problem : Problem) (assignment : Array (Option Bool)) :
    Nat → Redundancy.WorkBudget → Superposition.State →
      Data.ClauseMetadataTable.RetainedEmptyCursor →
      Superposition.State × Data.ClauseMetadataTable.RetainedEmptyCursor ×
        Option TheoryConflict × Bool
  | 0, _, state, cursor =>
      let (cursor, conflict?) := firstActiveConflictFrom? state assignment cursor
      (state, cursor, conflict?, false)
  | fuel + 1, budget, state, cursor =>
      let (cursor, conflict?) := firstActiveConflictFrom? state assignment cursor
      match conflict? with
      | some conflict => (state, cursor, some conflict, true)
      | none =>
          match Superposition.State.selectGiven? config.saturation state with
          | some (given, givenWorkspace) =>
              let state := {
                state with
                givenWorkspace := givenWorkspace
                selectionClock := state.selectionClock + 1
                processed := state.processed + 1
              }
              let step :=
                Superposition.State.processGivenWith config.saturation state given budget (problem.enableLazySourcesForGiven (supportActive assignment))
              if step.complete then
                saturateModel config problem assignment fuel step.budget step.state cursor
              else
                (step.state, cursor, none, false)
          | none => (state, cursor, none, true)
structure TheoryRoundResult where
  state : TheoryState
  conflict? : Option TheoryConflict
  complete : Bool
  deriving Repr, Lean.ToExpr
def runTheoryRound (config : Config) (problem : Problem)
    (saturation : Superposition.State)
    (assignment : Array (Option Bool)) (changedVars : Array Nat) : TheoryRoundResult :=
  let seeded :=
    saturation.reseed changedVars (supportActive assignment)
  let (saturation, _, conflict?, complete) :=
    saturateModel config problem assignment config.theoryFuelPerModel (Redundancy.WorkBudget.ofConfig config.saturation seeded.lifecycle.work) seeded {}
  {
    state := { saturation := saturation, lastAssignment := assignment }
    conflict? := conflict?
    complete := complete
  }
namespace TheoryRoundResult
def toTheoryResponse (round : TheoryRoundResult) (assignment : Array (Option Bool)) :
    PropCdcl.Incremental.TheoryResponse TheoryState TheoryConflict :=
  match round.conflict? with
  | some conflict =>
      if conflict.check round.state.saturation assignment then
        .conflict round.state conflict.learned conflict
      else
        .unknown round.state
          "AVATAR theory conflict failed the selector/guard protocol checker"
  | none =>
      if round.complete then
        .model round.state
      else
        .unknown round.state "AVATAR theory saturation exhausted its per-model fuel"
end TheoryRoundResult
def theoryStep (config : Config) (problem : Problem) (state : TheoryState)
    (delta : PropCdcl.Incremental.AssignmentDelta) :
    PropCdcl.Incremental.TheoryResponse TheoryState TheoryConflict :=
  match state with
  | { saturation, lastAssignment } =>
      let assignment := delta.apply lastAssignment
      (runTheoryRound config problem saturation assignment delta.changedVars).toTheoryResponse assignment
structure RunResult where
  problem : Problem
  search :
    PropCdcl.Incremental.RunResult TheoryState TheoryConflict
structure Metrics where
  sourceClauses : Nat
  components : Nat
  saturationProcessed : Nat
  generatedCandidates : Nat
  checkedCandidates : Nat
  retainedCandidates : Nat
  ruleRejectedCandidates : Nat
  retentionRejectedCandidates : Nat
  indexedBatches : Nat
  indexedBatchHits : Nat
  indexedCandidates : Nat
  workConsumed : Nat
  workExhaustions : Nat
  indexOccurrences : Nat
  indexMaintenanceSteps : Nat
  termPositions : Nat
  inferenceAttempts : Nat
  unificationAttempts : Nat
  localChecks : Nat
  retentionChecks : Nat
  subsumptionNodes : Nat
  backwardDeletionChecks : Nat
  forwardSimplificationSteps : Nat
  activatedClauses : Nat
  deletedClauses : Nat
  arenaInitial : Nat
  arenaFinal : Nat
  arenaGrowth : Nat
  theoryRounds : Nat
  theoryClauses : Nat
  cdclDecisions : Nat
  cdclConflicts : Nat
  cdclPropagations : Nat
  cdclBacktracks : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace Metrics
def indexedBatchHitPermille (metrics : Metrics) : Nat :=
  if metrics.indexedBatches == 0 then
    0
  else
    metrics.indexedBatchHits * 1000 / metrics.indexedBatches
end Metrics
private def runProblem (config : Config) (problem : Problem) : RunResult :=
  let theoryState : TheoryState := {
    saturation :=
      Superposition.State.dormantWithEnabled config.saturation
        problem.guardedArenaInputs problem.initialEnabled
  }
  {
    problem := problem
    search :=
      PropCdcl.Incremental.run config.cdcl problem.numVars problem.propClauses
        theoryState (theoryStep config problem)
  }
def run (config : Config) (initialClauses : Array Clause) : RunResult :=
  runProblem config (Problem.build initialClauses)
def runWithLazyDefinitions (config : Config) (registry : LazyDefinitionRegistry.Checked) : RunResult :=
  runProblem config (Problem.buildWithLazyDefinitions registry)
namespace RunResult
def metrics (result : RunResult) : Metrics :=
  let saturation := result.search.state.saturation
  let lifecycle := saturation.lifecycle
  {
    sourceClauses := result.problem.initialClauses.size
    components := result.problem.components.size
    saturationProcessed := saturation.processed
    generatedCandidates := lifecycle.generatedCandidates
    checkedCandidates := lifecycle.checkedCandidates
    retainedCandidates := lifecycle.retainedCandidates
    ruleRejectedCandidates := lifecycle.ruleRejectedCandidates
    retentionRejectedCandidates := lifecycle.retentionRejectedCandidates
    indexedBatches := lifecycle.indexedBatches
    indexedBatchHits := lifecycle.indexedBatchHits
    indexedCandidates := lifecycle.indexedCandidates
    workConsumed := lifecycle.work.consumed
    workExhaustions := lifecycle.workExhaustions
    indexOccurrences := lifecycle.work.indexOccurrences
    indexMaintenanceSteps := lifecycle.work.indexMaintenanceSteps
    termPositions := lifecycle.work.termPositions
    inferenceAttempts := lifecycle.work.inferenceAttempts
    unificationAttempts := lifecycle.work.unificationAttempts
    localChecks := lifecycle.work.localChecks
    retentionChecks := lifecycle.work.retentionChecks
    subsumptionNodes := lifecycle.work.subsumptionNodes
    backwardDeletionChecks := lifecycle.work.backwardDeletionChecks
    forwardSimplificationSteps := lifecycle.work.forwardSimplificationSteps
    activatedClauses := lifecycle.activatedClauses
    deletedClauses := lifecycle.deletedClauses
    arenaInitial := result.problem.arenaInputSize
    arenaFinal := saturation.clauses.size
    arenaGrowth := saturation.steps.size
    theoryRounds := result.search.theoryRounds
    theoryClauses := result.search.theoryClauses.size
    cdclDecisions := result.search.stats.decisions
    cdclConflicts := result.search.stats.conflicts
    cdclPropagations := result.search.stats.propagations
    cdclBacktracks := result.search.stats.backtracks
  }
def searchSeed? (result : RunResult) : Option Problem.SearchSeed :=
  result.problem.searchSeed?
structure ProofMaterialization where
  dag : SearchMaterialization.SearchDAG
  arenaToSearch : Array (Option SearchMaterialization.NodeId)
  splitNodes : Array SearchMaterialization.ClauseInfo
  conflictProofNodes : Array SearchMaterialization.ClauseInfo
  deriving Repr
structure CertificateMaterialization where
  dag : SearchMaterialization.SearchDAG
  arenaToSearch : Array (Option SearchMaterialization.NodeId)
  splitNodes : Array SearchMaterialization.ClauseInfo
  conflictProofNodes : Array SearchMaterialization.ClauseInfo
  theoryConflictNodes : Array SearchMaterialization.ClauseInfo
  learnedClauseNodes : Array SearchMaterialization.ClauseInfo
  root : SearchMaterialization.ClauseInfo
  deriving Repr
private def arenaShapeAligned (result : RunResult) : Bool := Id.run do
  let state := result.search.state.saturation
  let inputSize := result.problem.arenaInputSize
  if state.clauses.size != inputSize + state.steps.size ||
      state.guards.size != state.clauses.size ||
      state.enabled.size != state.clauses.size ||
      !state.clauseMetadata.alignedWith state.clauses.size then
    return false
  for h : id in [:result.problem.components.size] do
    match result.problem.components[id]?, state.clauses[id]?, state.guardsAt? id with
    | some component, some clause, some guards =>
        if !CoreSyntax.Search.clauseEq component.clause clause ||
            !Guards.eq guards #[component.guard] then
          return false
    | _, _, _ => return false
  for h : index in [:state.steps.size] do
    let id := inputSize + index
    let step := state.steps[index]
    if !state.enabledAt id || !step.rule.parents.all (fun parent => parent < id) then
      return false
    match state.clauses[id]?, state.guardsAt? id, state.ruleGuards? step.rule with
    | some clause, some guards, some expectedGuards =>
        if !CoreSyntax.Search.clauseEq clause step.clause ||
            !Guards.eq guards expectedGuards then
          return false
    | _, _, _ => return false
  return true
private def remapResourceRef? (arenaToSearch : Array (Option SearchMaterialization.NodeId))
    (ref : ResourceTrace.ClauseRef) : Option ResourceTrace.ClauseRef := do
  let target? ← arenaToSearch[ref.id]?
  let target ← target?
  pure { ref with id := target }
private def remapLocalWitness? (arenaToSearch : Array (Option SearchMaterialization.NodeId)) :
    ResourceTrace.LocalStepWitness → Option ResourceTrace.LocalStepWitness
  | .unary resource => do
      let parent ← remapResourceRef? arenaToSearch resource.parent
      pure (.unary { resource with parent := parent })
  | .resolution resource => do
      let left ← remapResourceRef? arenaToSearch resource.left
      let right ← remapResourceRef? arenaToSearch resource.right
      pure (.resolution { resource with left := left, right := right })
  | .rewrite resource => do
      let equality ← remapResourceRef? arenaToSearch resource.equality
      let target ← remapResourceRef? arenaToSearch resource.target
      pure (.rewrite { resource with equality := equality, target := target })
private def neededProofSteps (inputSize : Nat) (steps : Array Superposition.ProofStep) (roots : Array Superposition.ClauseId) : Array Bool :=
  roots.foldl (fun needed root =>
      Superposition.markProofAncestor inputSize steps (steps.size + 1) root needed) (List.replicate steps.size false).toArray
private def initialArenaMap (arenaSize : Nat) (componentNodes : Array SearchMaterialization.ClauseInfo) :
    Array (Option SearchMaterialization.NodeId) := Id.run do
  let mut mapping := (List.replicate arenaSize none).toArray
  for h : id in [:componentNodes.size] do
    mapping := mapping.set! id (some componentNodes[id].id)
  return mapping
private def mappedInfo? (dag : SearchMaterialization.SearchDAG) (arenaToSearch : Array (Option SearchMaterialization.NodeId))
    (arenaId : Superposition.ClauseId) :
    Option SearchMaterialization.ClauseInfo := do
  let searchId? ← arenaToSearch[arenaId]?
  let searchId ← searchId?
  dag.get? searchId
private def conflictMatches (result : RunResult) (index : Nat) (info : SearchMaterialization.ClauseInfo) : Bool :=
  match result.search.theoryEvidence[index]?, result.search.theoryClauses[index]? with
  | some evidence, some learned =>
      info.clause.isEmpty &&
        Guards.eq info.guards evidence.guards &&
          PropResolution.clauseEq learned evidence.learned &&
            PropResolution.clauseEq evidence.learned (Guards.learnedClause info.guards)
  | _, _ => false
/--
把 persistent saturation arena 中实际参与 theory conflicts 的 proof-step 祖先闭包
自动映射进 canonical SearchDAG。
映射表按原始 arena clause id 索引；未进入冲突祖先闭包的派生槽保持 `none`。输入
component 固定绑定到 split/component 节点，派生槽只能引用已经完成映射的父节点。
-/
private def materializeProofStepsFor?
    (config : Config) (result : RunResult) (theoryIndices : Array Nat) :
    SearchMaterialization.Result ProofMaterialization := do
  if result.search.theoryClauses.size != result.search.theoryEvidence.size then
    throw (SearchMaterialization.diagnostic .sourceMaterialization
      "AVATAR theory clauses and theory evidence have different sizes")
  if !result.arenaShapeAligned then
    throw (SearchMaterialization.diagnostic .sourceMaterialization
      "persistent saturation clause/proof arena is not aligned")
  let seed ← SearchMaterialization.requireSome .sourceMaterialization
    "failed to rebuild canonical AVATAR SearchDAG seed" result.searchSeed?
  let state := result.search.state.saturation
  let inputSize := result.problem.arenaInputSize
  if seed.componentNodes.size != result.problem.components.size ||
      seed.splitNodes.size != result.problem.sourceSplits.size then
    throw (SearchMaterialization.diagnostic .sourceMaterialization
      "canonical AVATAR SearchDAG seed does not cover the persistent input arena")
  let mut roots : Array Superposition.ClauseId :=
    Array.emptyWithCapacity theoryIndices.size
  for index in theoryIndices do
    let evidence ← SearchMaterialization.requireSome .sourceMaterialization
      s!"persistent saturation theory evidence {index} is missing" <|
        result.search.theoryEvidence[index]?
    roots := roots.push evidence.clauseId
  let needed := neededProofSteps inputSize state.steps roots
  let mut dag := seed.dag
  let mut arenaToSearch := initialArenaMap state.clauses.size seed.componentNodes
  for h : index in [:state.steps.size] do
    if needed[index]? == some true then
      let step := state.steps[index]
      let arenaId := inputSize + index
      if !Superposition.validProofStep config.saturation state.clauses step then
        throw (SearchMaterialization.diagnostic .sourceMaterialization
          s!"persistent saturation proof step {arenaId} failed its local checker")
      let resource ← SearchMaterialization.requireSome .sourceMaterialization
        s!"persistent saturation proof step {arenaId} has no resource witness" step.resource?
      let resource ← SearchMaterialization.requireSome .sourceMaterialization
        s!"persistent saturation proof step {arenaId} references an unmapped parent" <|
          remapLocalWitness? arenaToSearch resource
      let (nextDag, info) ← SearchMaterialization.requireSome .sourceMaterialization
        s!"failed to add persistent saturation proof step {arenaId} to SearchDAG" <|
          dag.addResourceTraceLocalWitness? resource
      if !CoreSyntax.Search.clauseEq info.clause step.clause then
        throw (SearchMaterialization.diagnostic .sourceMaterialization
          s!"persistent saturation proof step {arenaId} changed its result clause")
      dag := nextDag
      arenaToSearch := arenaToSearch.set! arenaId (some info.id)
  let mut conflictNodes : Array SearchMaterialization.ClauseInfo :=
    Array.emptyWithCapacity theoryIndices.size
  for index in theoryIndices do
    let evidence ← SearchMaterialization.requireSome .sourceMaterialization
      s!"persistent saturation theory evidence {index} is missing" <|
        result.search.theoryEvidence[index]?
    let conflict ← SearchMaterialization.requireSome .sourceMaterialization
      s!"persistent saturation conflict root {evidence.clauseId} was not materialized" <|
        mappedInfo? dag arenaToSearch evidence.clauseId
    if !result.conflictMatches index conflict then
      throw (SearchMaterialization.diagnostic .sourceMaterialization
        s!"persistent saturation conflict {index} does not match its SearchDAG root")
    conflictNodes := conflictNodes.push conflict
  if dag.check then
    pure {
      dag := dag
      arenaToSearch := arenaToSearch
      splitNodes := seed.splitNodes
      conflictProofNodes := conflictNodes
    }
  else
    throw (SearchMaterialization.diagnostic .dagCheck
      "SearchDAG checker rejected persistent saturation proof materialization")

def materializeProofSteps? (config : Config) (result : RunResult) :
    SearchMaterialization.Result ProofMaterialization :=
  result.materializeProofStepsFor? config
    (List.range result.search.theoryEvidence.size).toArray
def finalInitialClauses (result : RunResult) :
    Array PropResolution.InitialClause :=
  result.problem.propInitialClauses ++
    result.search.theoryClauses.mapIdx fun index clause => {
      clause := clause
      origin := .residual (result.problem.sourceSplits.size + index)
    }
/--
若常驻搜索得到 UNSAT，统一重建一次原始命题 proof。
材料化热路径先清洗 proof，再只检查最终紧凑证书。
-/
def unsatProof? (config : Config) (result : RunResult) :
    Option PropResolution.CdclProof :=
  match result.search.outcome with
  | .unsat =>
      PropCdcl.unsatProof? config.cdcl.cdcl result.problem.numVars
        result.finalInitialClauses
  | _ => none
def checkedUnsat? (config : Config) (result : RunResult) :
    Option PropResolution.CheckedUnsatCertificate := do
  let proof ← result.unsatProof? config
  PropResolution.CheckedUnsatCertificate.mk?
    result.finalInitialClauses proof
/--
自动材料化 theory conflicts、对应的 propositional learned clauses，以及最终
residual-CDCL 空 root。
CDCL initial 顺序固定为 source skeleton 前缀加 learned-clause 后缀；root 只引用显式
learned 节点，不再把 guarded-empty 对象推导节点直接当作命题 initial。
-/
def materializeCertificate? (config : Config) (result : RunResult) :
    SearchMaterialization.Result CertificateMaterialization := do
  let proof ← SearchMaterialization.requireSome .residualSplit
    "persistent AVATAR search did not produce an UNSAT proof" <|
      result.unsatProof? config
  let slice ← SearchMaterialization.requireSome .residualSplit
    "persistent AVATAR certificate slicing failed" <|
      PropResolution.CertificateSlice.compactRaw?
        result.finalInitialClauses proof
  let certificate := slice.certificate
  let splitCount := result.problem.sourceSplits.size
  let mut splitIndices : Array Nat :=
    Array.emptyWithCapacity slice.initialIndices.size
  let mut theoryIndices : Array Nat :=
    Array.emptyWithCapacity slice.initialIndices.size
  for index in slice.initialIndices do
    if index < splitCount then
      splitIndices := splitIndices.push index
    else
      theoryIndices := theoryIndices.push (index - splitCount)
  let proof ← result.materializeProofStepsFor? config theoryIndices
  let mut selectedSplitNodes : Array SearchMaterialization.ClauseInfo :=
    Array.emptyWithCapacity splitIndices.size
  for index in splitIndices do
    let split ← SearchMaterialization.requireSome .sourceMaterialization
      s!"persistent AVATAR split node {index} is missing" <|
        proof.splitNodes[index]?
    selectedSplitNodes := selectedSplitNodes.push split
  let mut workspace :
      Data.CertificateMaterializationWorkspace
        PropResolution.CheckedUnsatCertificate SearchMaterialization.SearchDAG (Array (Option SearchMaterialization.NodeId))
          SearchMaterialization.ClauseInfo := {
    certificate := certificate
    dag := proof.dag
    arenaToSearch := proof.arenaToSearch
    splitNodes := selectedSplitNodes
    conflictProofNodes := proof.conflictProofNodes
  }
  for conflictProof in workspace.conflictProofNodes do
    let (nextDag, theoryConflict) ← SearchMaterialization.requireSome .residualSplit
      s!"failed to materialize theory conflict from proof node {conflictProof.id}" <|
        workspace.dag.addTheoryConflict? conflictProof
    workspace := workspace.setDag nextDag |>.pushTheoryConflict theoryConflict
    let (nextDag, learned) ← SearchMaterialization.requireSome .residualSplit
      s!"failed to materialize learned clause from theory conflict {theoryConflict.id}" <|
        workspace.dag.addPropositionalLearnedClause? theoryConflict
    workspace := workspace.setDag nextDag |>.pushLearnedClause learned
  let sources := workspace.sources
  let (finalDag, root) ←
    workspace.dag.addResidualCdclFromSources sources workspace.certificate
    "persistent AVATAR saturation/CDCL"
  if workspace.theoryConflictNodes.size != theoryIndices.size ||
      workspace.learnedClauseNodes.size != theoryIndices.size ||
      !root.globallyEmpty then
    throw (SearchMaterialization.diagnostic .dagCheck
      "persistent AVATAR certificate artifacts are not aligned")
  pure {
    dag := finalDag
    arenaToSearch := workspace.arenaToSearch
    splitNodes := workspace.splitNodes
    conflictProofNodes := workspace.conflictProofNodes
    theoryConflictNodes := workspace.theoryConflictNodes
    learnedClauseNodes := workspace.learnedClauseNodes
    root := root
  }
def searchDAG? (config : Config) (result : RunResult) :
    SearchMaterialization.Result (SearchMaterialization.SearchDAG × SearchMaterialization.ClauseInfo) := do
  let materialized ← result.materializeCertificate? config
  pure (materialized.dag, materialized.root)
end RunResult
end Avatar
end Automation
end YesMetaZFC
