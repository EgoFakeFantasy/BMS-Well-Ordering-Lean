import Lean
import YesMetaZFC.Automation.Request.GoalAttempt
import YesMetaZFC.Automation.HostNormalization.CoreRules
import YesMetaZFC.Automation.LogicSoundness
/-!
# 新 `prove_auto` 请求层
这一层只负责宿主上下文收集、provider 调度与内在闭句证书消费。预处理、原始搜索
语法及其检查编译均由各后端负责，不再从请求层反向依赖 completeness 或 source
bridge。
当前入口：
* `prove_auto CERT cert`
* `prove_auto VALID cert`
* `prove_auto BACKEND success`
搜索器应产出上述 checked certificate 对象或 proof-carrying `BackendSuccess` 对象。
-/
namespace YesMetaZFC
open Lean Elab Tactic Meta
namespace Automation
namespace ProveAutoRequest
universe x
private def closeByProof (name : Name) (proof : Expr) : TacticM Unit := do
  closeMainGoal name (← instantiateMVars proof)
private unsafe def proveProposition? (target : Expr) : TacticM (Option Expr) :=
  withoutModifyingState do
    let proof ← mkFreshExprMVar (some target)
    setGoals [proof.mvarId!]
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| first | rfl | decide +kernel))
      unless (← getGoals).isEmpty do
        return none
      let result ← instantiateMVars proof
      unless (← getMVarsNoDelayed result).isEmpty do
        return none
      return some result
    catch _ =>
      return none
private def proofFitsMainGoal (proof : Expr) : TacticM Bool :=
  withoutModifyingState do
    let goal ← getMainTarget
    let proofType ← inferType proof
    withTransparency .reducible <| isDefEq proofType goal
/--
`prove_auto` 的 Lean 元层资源作用域。
继承调用点的心跳预算，使搜索、预处理与 CDCL 除了各自的 fuel 和 arena 预算外，
也始终受 Lean 的全局 `maxHeartbeats` 约束。Lean 没有无穷递归深度哨兵，因此只把
递归深度上限提升到实际不可达的范围。
-/
def withProveAutoResources (action : TacticM α) : TacticM α :=
  withTheReader Core.Context (fun context =>
      let recursionLimit := Nat.max 1_000_000 context.maxRecDepth
      let options := Lean.maxRecDepth.set context.options recursionLimit
      { context with
        options
        maxRecDepth := recursionLimit })
    action
/-! ## 上下文相关性与 provider 扩展 -/
/--
给高层公式定义指定一个伪类型式的 unfold key。
key 使用层级名字，例如 `setTheory.ordinal.comparison`。上下文收集器只把 key 相等，
或处于同一祖先/后代链上的局部引理视为强相关。
-/
initialize proveAutoUnfoldAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `prove_auto_unfold
    descr := "hierarchical unfold key used by prove_auto context relevance"
    getParam := fun _ stx => do
      let identifier ← Attribute.Builtin.getIdent stx
      pure identifier.getId.eraseMacroScopes
  }
def unfoldKey? (env : Environment) (declaration : Name) : Option Name :=
  proveAutoUnfoldAttr.getParam? env declaration
register_option prove_auto.context.maxFacts : Nat := {
  defValue := 16
  descr := "maximum number of strongly relevant local facts collected by prove_auto"
}
register_option prove_auto.host.maxFacts : Nat := {
  defValue := 12
  descr := "maximum number of relevant Lean host facts sent to one AVATAR provider"
}
initialize registerTraceClass `YesMetaZFC.proveAuto.context
initialize registerTraceClass `YesMetaZFC.proveAuto.proof
namespace ContextRelevance
structure Profile where
  heads : Array Name := #[]
  propositionFVars : Array FVarId := #[]
  objectFVars : Array FVarId := #[]
  keys : Array Name := #[]
private def pushNameUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name
private def pushFVarUnique (variables : Array FVarId) (fvar : FVarId) : Array FVarId :=
  if variables.contains fvar then variables else variables.push fvar
def Profile.merge (left right : Profile) : Profile := {
  heads := right.heads.foldl pushNameUnique left.heads
  propositionFVars :=
    right.propositionFVars.foldl pushFVarUnique left.propositionFVars
  objectFVars :=
    right.objectFVars.foldl pushFVarUnique left.objectFVars
  keys := right.keys.foldl pushNameUnique left.keys
}
private def ignoredHead (name : Name) : Bool :=
  name == ``False || name == ``True || name == ``Not ||
    name == ``And || name == ``Or || name == ``Iff ||
    name == ``Eq || name == ``Exists
private partial def collectAux (env : Environment) (expression : Expr) (fuel : Nat) (forceFVar : Bool) (visited : Array Name) (profile : Profile) :
    MetaM (Array Name × Profile) := do
  if fuel == 0 then
    return (visited, profile)
  let expression := expression.consumeMData
  let mut visited := visited
  let mut profile := profile
  match expression.getAppFn with
  | .const declaration _ =>
      if !ignoredHead declaration then
        profile := {
          profile with
          heads := pushNameUnique profile.heads declaration
        }
      if let some key := unfoldKey? env declaration then
        profile := {
          profile with
          keys := pushNameUnique profile.keys key
        }
        if !visited.contains declaration then
          visited := visited.push declaration
          if let some unfolded ← unfoldDefinition? expression true then
            (visited, profile) ←
              collectAux env unfolded (fuel - 1) forceFVar visited profile
  | .fvar fvar =>
      if expression.isApp then
        profile := {
          profile with
          propositionFVars :=
            pushFVarUnique profile.propositionFVars fvar
        }
  | _ =>
      pure ()
  match expression with
  | .fvar fvar =>
      if ← isProp expression then
        profile := {
          profile with
          propositionFVars :=
            pushFVarUnique profile.propositionFVars fvar
        }
      else if forceFVar then
        profile := {
          profile with
          objectFVars :=
            pushFVarUnique profile.objectFVars fvar
        }
      else
        profile := {
          profile with
          objectFVars :=
            pushFVarUnique profile.objectFVars fvar
        }
      return (visited, profile)
  | .forallE _ domain body _ =>
      (visited, profile) ←
        collectAux env domain (fuel - 1) false visited profile
      collectAux env body (fuel - 1) false visited profile
  | .lam _ domain body _ =>
      (visited, profile) ←
        collectAux env domain (fuel - 1) false visited profile
      collectAux env body (fuel - 1) false visited profile
  | .letE _ type value body _ =>
      (visited, profile) ←
        collectAux env type (fuel - 1) false visited profile
      (visited, profile) ←
        collectAux env value (fuel - 1) false visited profile
      collectAux env body (fuel - 1) false visited profile
  | .proj _ _ body =>
      collectAux env body (fuel - 1) forceFVar visited profile
  | _ =>
      let equalitySides :=
        expression.getAppFn.constName? == some ``Eq
      expression.getAppArgs.foldlM (init := (visited, profile)) fun state argument =>
          collectAux env argument (fuel - 1) equalitySides
            state.1 state.2
def collect (expression : Expr) : MetaM Profile := do
  let expression ← instantiateMVars expression
  let env ← getEnv
  return (← collectAux env expression 64 false #[] {}).2
def collectUnfoldKeys (expression : Expr) : MetaM (Array Name) := do
  return (← collect expression).keys
private def keyScore (target candidate : Name) : Nat :=
  if target == candidate then
    3
  else if target.isPrefixOf candidate then
    2
  else if candidate.isPrefixOf target then
    1
  else
    0
def unfoldScore (targetKeys candidateKeys : Array Name) : Nat :=
  targetKeys.foldl (fun best target =>
      candidateKeys.foldl (fun best candidate => Nat.max best (keyScore target candidate))
        best)
    0
private def sharedNameCount (left right : Array Name) : Nat :=
  left.foldl (fun count name => if right.contains name then count + 1 else count)
    0
private def sharedFVarCount (left right : Array FVarId) : Nat :=
  left.foldl (fun count fvar =>
      if right.contains fvar then count + 1 else count)
    0
private def sharedObjectFVarCount
    (left right ignored : Array FVarId) : Nat :=
  left.foldl (fun count fvar =>
      if !ignored.contains fvar && right.contains fvar then count + 1 else count)
    0
/--
收集局部上下文中的环境索引变量。

若一个非命题变量出现在另一个非命题声明的类型中，它通常描述模型、解释或依赖索引，
而不是搜索目标里的数学对象。此类变量仍保留在 profile 中供完整前沿传播使用，但不贡献
对象重合分，避免同处一个模型中的任意事实互相吸引。
-/
def infrastructureObjectFVars : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
        localDecl.isLet then
      continue
    let type ← instantiateMVars localDecl.type
    if ← isProp type then
      continue
    let (_, freeVariables) ← type.collectFVars.run {}
    for freeVariable in freeVariables.fvarIds do
      if freeVariable != localDecl.fvarId && !result.contains freeVariable then
        result := result.push freeVariable
  return result
/--
相关性分数优先层级 unfold key，其次命题自由变量，最后公式/项头。
逻辑连接词和等词本身不作为头；等式两侧的真实函数、谓词和局部函数变量会进入锚点。
-/
def score
    (target candidate : Profile)
    (ignoredObjectFVars : Array FVarId := #[]) : Nat :=
  unfoldScore target.keys candidate.keys * 100 +
    sharedFVarCount target.propositionFVars candidate.propositionFVars * 20 +
    sharedObjectFVarCount target.objectFVars candidate.objectFVars
        ignoredObjectFVars * 10 +
    sharedNameCount target.heads candidate.heads * 5
/--
结构 proposition 的类型参数通常覆盖许多无关命题变量，不能借此挤占叶字段。
只有层级 key 或结构头本身被目标/已选规则引用时，结构 proof 才获得高相关性。
-/
def structureScore
    (target candidate : Profile)
    (ignoredObjectFVars : Array FVarId := #[]) : Nat :=
  unfoldScore target.keys candidate.keys * 100 +
    sharedObjectFVarCount target.objectFVars candidate.objectFVars
        ignoredObjectFVars * 20 +
    sharedNameCount target.heads candidate.heads * 5

/--
提取候选定理的逻辑结论。

对象量词和命题前提都从触发表面剥离；候选一旦被选中，完整 profile 仍会并入前沿，
所以后续轮次可以继续追踪其前提。这里不展开普通定义，避免把稳定的宿主谓词头抹掉。
-/
private partial def ruleConclusion (proposition : Expr) (fuel : Nat := 32) :
    MetaM Expr := do
  if fuel == 0 then
    return proposition
  let proposition := proposition.consumeMData
  match proposition with
  | .forallE _ _ body _ =>
      ruleConclusion body (fuel - 1)
  | .letE _ _ value body _ =>
      ruleConclusion (body.instantiate1 value) (fuel - 1)
  | _ =>
      return proposition

/--
完整 profile 用于选中后的前沿扩张，trigger profile 只描述候选最终能够推出的结论。
这使 `A → B` 在需求为 `B` 时可见，而在需求仅为 `A` 时不会反向吸入。
-/
def collectCandidateProfiles (proposition : Expr) :
    MetaM (Profile × Profile) := do
  let full ← collect proposition
  let conclusion ← ruleConclusion proposition
  let trigger ←
    if conclusion == proposition then
      pure full
    else
      collect conclusion
  return (full, trigger)
end ContextRelevance
/--
一个上下文闭合入口消费的原始请求。
`useFacts` 只保存用户或结构 proof 节点显式给出的 proof term。局部候选扫描、相关性
选择和最终 checked facts 都在统一准备阶段完成，避免每个 provider 重复展开同一事实面。
-/
structure ContextRequest where
  goal : Expr
  useFacts : Array Expr := #[]
inductive ContextPreparation where
  | relevantFacts
  | providerManaged
deriving BEq, Repr
inductive ContextProviderRequirement where
  | any
  | hostObjectSyntax
deriving BEq, Repr
structure ContextCandidate where
  label : Name
  origin : FVarId
  isRootResource : Bool
  proposition : Expr
  proof : Expr
  profile : ContextRelevance.Profile
  triggerProfile : ContextRelevance.Profile
  isStructure : Bool
structure ContextPreparationStats where
  explicitRaw : Nat := 0
  explicitExpanded : Nat := 0
  localCandidates : Nat := 0
  contextSelected : Nat := 0
  contextRejected : Nat := 0
  totalFacts : Nat := 0
  terminalPropositions : Nat := 0
deriving Repr
structure ContextTerminalSnapshot where
  factPropositions : Array Expr := #[]
  hasHostObjectSyntax : Bool := false
  hasHostRules : Bool := false
structure ContextResourceSummary where
  present : Bool := false
  providerManaged : Bool := false
  explicitRaw : Nat := 0
  explicitExpanded : Nat := 0
  selected : Array Name := #[]
  rejected : Nat := 0
def ContextResourceSummary.render (summary : ContextResourceSummary) : String :=
  if summary.providerManaged then
    s!"provider-managed; explicitRaw={summary.explicitRaw}"
  else
    s!"explicit={summary.explicitExpanded}; explicitRaw={summary.explicitRaw}; " ++
      s!"auto={summary.selected.size}; selected={summary.selected}; " ++
      s!"rejected={summary.rejected}"
/--
同一叶子上供所有通用 provider 共享的准备结果。
`facts` 是 provider 实际送入 checked source 的唯一事实面；`candidates` 保留 AVATAR
HR 前端所需的 proof-carrying 候选及其相关性 profile。任何局部事实或注册规则都必须
进入统一 AVATAR 搜索与证书回放，准备层不保存直接闭合目标的 proof term。
-/
structure PreparedContextRequest where
  goal : Expr
  useFacts : Array Expr := #[]
  facts : Array Expr := #[]
  candidates : Array ContextCandidate := #[]
  goalProfile : ContextRelevance.Profile := {}
  terminal : ContextTerminalSnapshot := {}
  resourceSummary : ContextResourceSummary := {}
  stats : ContextPreparationStats := {}
inductive ContextProviderAdmission where
  | notApplicable (reason : String)
  | accepted (build : MetaM Expr)
/--
一个可插拔的上下文请求构造器。
`.relevantFacts` provider 共享同一 `PreparedContextRequest`；`.providerManaged` provider
只接收原始目标和显式资源，自行构造专用上下文。两类 provider 都只能返回
proof-carrying `GoalAttempt`，不能直接生成当前目标的证明项。
-/
structure ContextProvider where
  priority : Nat := 0
  preparation : ContextPreparation := .relevantFacts
  requirement : ContextProviderRequirement := .any
  admit : PreparedContextRequest → MetaM ContextProviderAdmission
private def pushNameUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name
initialize contextProviderExtension :
    PersistentEnvExtension Name Name (Array Name) ←
  registerPersistentEnvExtension {
    name := `YesMetaZFC.Automation.ProveAutoRequest.contextProviderExtension
    mkInitial := pure #[]
    addImportedFn := fun imported =>
      pure <| imported.foldl (fun providers entries =>
          entries.foldl pushNameUnique providers) #[]
    addEntryFn := pushNameUnique
    exportEntriesFn := id
    statsFn := fun providers =>
      s!"prove_auto context providers: {providers.size}"
  }
syntax (name := registerProveAutoContextProvider)
  "register_prove_auto_context_provider " ident : command
elab_rules : command
  | `(register_prove_auto_context_provider $provider:ident) => do
      let providerName ← resolveGlobalConstNoOverload provider
      let providerType ← Lean.Elab.Command.liftTermElabM <|
        inferType (mkConst providerName)
      let expectedType := mkConst ``ContextProvider
      unless ← Lean.Elab.Command.liftTermElabM <|
          isDefEq providerType expectedType do
        throwErrorAt provider
          "context provider `{providerName}` has type{indentExpr providerType}, \
          expected `{expectedType}`"
      modifyEnv fun env =>
        contextProviderExtension.addEntry env providerName
private structure ProofExpansionState where
  propositions : Array Expr := #[]
  proofs : Array Expr := #[]
private abbrev ProofExpansionM := StateRefT ProofExpansionState MetaM
private def registerProofResource (proof : Expr) :
    ProofExpansionM Bool := do
  let proposition ← instantiateMVars (← inferType proof)
  unless ← isProp proposition do
    throwError
      "prove_auto expected a proof resource, but got{indentExpr proposition}"
  let state ← get
  if state.propositions.any fun seen => seen == proposition then
    return false
  set (show ProofExpansionState from {
    propositions := state.propositions.push proposition
    proofs := state.proofs.push proof
  })
  return true
private partial def expandProofResource (proof : Expr) :
    ProofExpansionM Unit := do
  unless ← registerProofResource proof do
    return
  let proposition ← instantiateMVars (← inferType proof)
  let reduced ← whnf proposition
  let .const structureName _ := reduced.getAppFn
    | return
  let some structureInfo := getStructureInfo? (← getEnv) structureName
    | return
  for fieldName in structureInfo.fieldNames do
    let projection ← mkProjection proof fieldName
    let projectionType ← instantiateMVars (← inferType projection)
    if ← isProp projectionType then
      expandProofResource projection
/--
递归展开 proof-valued 结构字段，并按命题去重。
显式 `USE` 与自动局部上下文必须共用这个入口，避免两种资源看到不同的结构表面。
-/
def expandProofResources (proofs : Array Expr) : MetaM (Array Expr) := do
  let (_, state) ← (proofs.forM expandProofResource).run {}
  return state.proofs
private def propositionIsStructure (proposition : Expr) : MetaM Bool := do
  let reduced ← whnf proposition
  let .const structureName _ := reduced.getAppFn
    | return false
  return (getStructureInfo? (← getEnv) structureName).isSome
private def proofResourceLabel (origin : Name) (proof : Expr) : MetaM Name := do
  match proof.consumeMData with
  | .proj structureName fieldIndex _ =>
      let some structureInfo := getStructureInfo? (← getEnv) structureName
        | return origin
      return structureInfo.fieldNames[fieldIndex]?.getD origin
  | _ =>
      return proof.getAppFn.constName?.getD origin
private def localProofCandidates : MetaM (Array ContextCandidate) := do
  let mut candidates := #[]
  for localDecl in (← getLCtx) do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
        localDecl.isLet then
      continue
    let proposition ← instantiateMVars localDecl.type
    unless ← isProp proposition do
      continue
    let resources ← expandProofResources #[localDecl.toExpr]
    for proof in resources do
      let proposition ← instantiateMVars (← inferType proof)
      unless candidates.any fun candidate =>
          candidate.proposition == proposition do
        let (profile, triggerProfile) ←
          ContextRelevance.collectCandidateProfiles proposition
        candidates := candidates.push {
          label := ← proofResourceLabel localDecl.userName proof
          origin := localDecl.fvarId
          isRootResource := proof == localDecl.toExpr
          proposition := proposition
          proof := proof
          profile
          triggerProfile
          isStructure := ← propositionIsStructure proposition
        }
  return candidates
/--
保守识别通用 provider 是否会看到宿主对象语法。
`false` 只覆盖纯命题连接词、命题蕴涵和零参数命题 atom；未知应用、对象量词、存在式
与等式都返回 `true`，因此该门只会少做优化，不会把潜在 FO/HO 请求误送走。
-/
private partial def expressionHasHostObjectSyntaxAux (expression : Expr) : MetaM Bool := do
  let expression ← whnf (← instantiateMVars expression)
  if expression.isConstOf ``False || expression.isConstOf ``True then
    return false
  if expression.isAppOfArity ``Not 1 then
    return ← expressionHasHostObjectSyntaxAux expression.getAppArgs[0]!
  if expression.isAppOfArity ``And 2 ||
      expression.isAppOfArity ``Or 2 ||
      expression.isAppOfArity ``Iff 2 then
    for argument in expression.getAppArgs do
      if ← expressionHasHostObjectSyntaxAux argument then
        return true
    return false
  if expression.isAppOfArity ``Eq 3 ||
      expression.isAppOfArity ``Exists 2 then
    return true
  match expression with
  | .forallE _ domain body _ =>
      if !(← isProp domain) then
        return true
      return (← expressionHasHostObjectSyntaxAux domain) || (← expressionHasHostObjectSyntaxAux body)
  | .letE _ _ value body _ =>
      expressionHasHostObjectSyntaxAux (body.instantiate1 value)
  | .app _ _ =>
      return true
  | _ =>
      return false
private def expressionHasHostObjectSyntax (expression : Expr) : MetaM Bool := do
  try
    expressionHasHostObjectSyntaxAux expression
  catch _ =>
    return true
private def makeContextTerminalSnapshot (goal : Expr) (factPropositions : Array Expr) :
    MetaM ContextTerminalSnapshot := do
  let mut hasHostObjectSyntax ← expressionHasHostObjectSyntax goal
  if !hasHostObjectSyntax then
    for proposition in factPropositions do
      if ← expressionHasHostObjectSyntax proposition then
        hasHostObjectSyntax := true
        break
  return {
    factPropositions
    hasHostObjectSyntax
  }
def prepareContextRequest (request : ContextRequest) : MetaM PreparedContextRequest := do
  let explicitResources ← expandProofResources request.useFacts
  let explicitPropositions ← explicitResources.mapM fun proof => do
    instantiateMVars (← inferType proof)
  let goalProfile ← ContextRelevance.collect request.goal
  let mut frontier := goalProfile
  for proposition in explicitPropositions do
    frontier := frontier.merge (← ContextRelevance.collect proposition)
  let allCandidates ← localProofCandidates
  let ignoredObjectFVars ← ContextRelevance.infrastructureObjectFVars
  let mut remaining :=
    allCandidates.filter fun candidate =>
      !explicitPropositions.any fun proposition =>
        proposition == candidate.proposition
  let candidatePoolSize := remaining.size
  let options ← getOptions
  let maxFacts : Nat :=
    Nat.min
      (options.get `prove_auto.context.maxFacts 16)
      (options.get `prove_auto.host.maxFacts 12)
  let mut selected : Array ContextCandidate := #[]
  let mut selectedTrace : Array (Name × Nat) := #[]
  while selected.size < maxFacts do
    let mut bestIndex? : Option Nat := none
    let mut bestScore := 0
    let mut bestIsStructure := true
    let mut bestExactTarget := false
    for index in [0 : remaining.size] do
      let some candidate := remaining[index]?
        | continue
      let exactTarget := candidate.proposition == request.goal
      let score :=
        if exactTarget then
          10_000
        else if candidate.isStructure then
          ContextRelevance.structureScore frontier candidate.triggerProfile
            ignoredObjectFVars
        else
          ContextRelevance.score frontier candidate.triggerProfile
            ignoredObjectFVars
      if !exactTarget && score < 10 then
        continue
      if score > bestScore || (score == bestScore && bestIndex?.isSome &&
            bestIsStructure && !candidate.isStructure) then
        bestScore := score
        bestIsStructure := candidate.isStructure
        bestExactTarget := exactTarget
        bestIndex? := some index
    let some bestIndex := bestIndex?
      | break
    let some candidate := remaining[bestIndex]?
      | break
    selected := selected.push candidate
    selectedTrace := selectedTrace.push (candidate.label, bestScore)
    if bestExactTarget then
      break
    frontier := frontier.merge candidate.profile
    if candidate.isRootResource then
      remaining := remaining.filter fun remainingCandidate =>
        remainingCandidate.origin != candidate.origin
    else
      remaining := remaining.eraseIdx! bestIndex
  let selectedNames := selected.map ContextCandidate.label
  let facts := explicitResources ++ selected.map ContextCandidate.proof
  let factPropositions :=
    explicitPropositions ++ selected.map ContextCandidate.proposition
  let terminal ←
    makeContextTerminalSnapshot request.goal factPropositions
  let stats : ContextPreparationStats := {
    explicitRaw := request.useFacts.size
    explicitExpanded := explicitResources.size
    localCandidates := allCandidates.size
    contextSelected := selected.size
    contextRejected := candidatePoolSize - selected.size
    totalFacts := facts.size
    terminalPropositions := factPropositions.size
  }
  let summary : ContextResourceSummary := {
    present := true
    explicitRaw := request.useFacts.size
    explicitExpanded := explicitResources.size
    selected := selectedNames
    rejected := candidatePoolSize - selected.size
  }
  trace[YesMetaZFC.proveAuto.context]
    "prepared once; {summary.render}; localCandidates={allCandidates.size}; \
    total={facts.size}; ranked={selectedTrace}; \
    keys={frontier.keys}; heads={frontier.heads}"
  return {
    goal := request.goal
    useFacts := request.useFacts
    facts := facts
    candidates := allCandidates
    goalProfile := goalProfile
    terminal := terminal
    resourceSummary := summary
    stats := stats
  }
/--
checked 宿主事务后的资源边界。

这里不重新扫描局部上下文；事务返回的每个根资源仍会展开 proof-valued 字段，供
正规化后的 HR rule 需求匹配。实际 `facts` 保持根资源去重，只有 `candidates`
持有投影视图，因此第二阶段不会把根定义、投影字段与正规化副本同时送入
clausification。
-/
def prepareCheckedContextRequest
    (request : ContextRequest) : MetaM PreparedContextRequest := do
  let mut facts := #[]
  let mut candidates := #[]
  let mut propositions := #[]
  for proof in request.useFacts do
    let proof ← instantiateMVars proof
    let proposition ← instantiateMVars (← inferType proof)
    unless propositions.any fun existing => existing == proposition do
      propositions := propositions.push proposition
      facts := facts.push proof
    let resources ← expandProofResources #[proof]
    for resource in resources do
      let resourceProposition ←
        instantiateMVars (← inferType resource)
      if candidates.any fun candidate =>
          candidate.proposition == resourceProposition then
        continue
      let (profile, triggerProfile) ←
        ContextRelevance.collectCandidateProfiles resourceProposition
      candidates := candidates.push {
        label := ← proofResourceLabel `explicit resource
        origin := proof.fvarId?.getD ⟨`explicit⟩
        isRootResource := resource == proof
        proposition := resourceProposition
        proof := resource
        profile
        triggerProfile
        isStructure := ← propositionIsStructure resourceProposition
      }
  let goalProfile ← ContextRelevance.collect request.goal
  let terminal ←
    makeContextTerminalSnapshot request.goal propositions
  let summary : ContextResourceSummary := {
    present := true
    explicitRaw := request.useFacts.size
    explicitExpanded := facts.size
  }
  trace[YesMetaZFC.proveAuto.context]
    "prepared exact checked resources; {summary.render}; facts={facts.size}; \
    candidates={candidates.size}"
  return {
    goal := request.goal
    useFacts := request.useFacts
    facts
    candidates
    goalProfile
    terminal
    resourceSummary := summary
    stats := {
      explicitRaw := request.useFacts.size
      explicitExpanded := facts.size
      localCandidates := candidates.size
      totalFacts := facts.size
      terminalPropositions := propositions.size
    }
  }
def ContextRequest.prepareProviderManaged (request : ContextRequest) : PreparedContextRequest := {
  goal := request.goal
  useFacts := request.useFacts
  resourceSummary := {
    present := true
    providerManaged := true
    explicitRaw := request.useFacts.size
  }
  stats := {
    explicitRaw := request.useFacts.size
  }
}
namespace GoalAttempt
theorem backendSoundOfClosedAt
    {σ : LogicSoundness.SetLevel.Signature}
    (problem : LogicSoundness.SetLevel.DeepProblem σ)
    (attempt : LogicSoundness.SetLevel.BackendAttemptAt.{x} problem)
    (hClosed : LogicSoundness.SetLevel.BackendAttemptAt.closed attempt = true) :
    LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
      problem.theory problem.target := by
  cases hAttempt : attempt with
  | success success =>
      exact success.sound
  | failure diagnostic =>
      simp [LogicSoundness.SetLevel.BackendAttemptAt.closed, hAttempt] at hClosed
theorem backendSoundOfClosed
    {σ : LogicSoundness.SetLevel.Signature}
    (problem : LogicSoundness.SetLevel.DeepProblem σ)
    (attempt : LogicSoundness.SetLevel.BackendAttempt problem)
    (hClosed : attempt.closed = true) :
    LogicSoundness.SetLevel.SemanticallyEntails
      problem.theory problem.target :=
  backendSoundOfClosedAt problem attempt hClosed
end GoalAttempt
private structure ContextDispatchResult where
  attempt? : Option Expr := none
  resourceSummary : ContextResourceSummary := {}
private structure ScheduledContextProvider where
  name : Name
  provider : ContextProvider
private abbrev ContextProviderSchedule :=
  Array ScheduledContextProvider
private unsafe def prepareContextProviderSchedule :
    TacticM ContextProviderSchedule := do
  let env ← getEnv
  let mut providers : Array (Nat × Name × ContextProvider) := #[]
  for providerName in contextProviderExtension.getState env do
    let provider ←
      evalExpr ContextProvider (mkConst ``ContextProvider) (mkConst providerName)
    providers := providers.push (provider.priority, providerName, provider)
  return (providers.qsort fun left right =>
    decide (left.1 > right.1)).map fun provider => {
      name := provider.2.1
      provider := provider.2.2
    }
private structure ContextDispatchObserver where
  providerVisited : Name → TacticM Unit := fun _ => pure ()
  providerBuilt :
    Name → ContextPreparation → TacticM Unit := fun _ _ => pure ()
  providerSkipped : Name → TacticM Unit := fun _ => pure ()
  prepared : PreparedContextRequest → TacticM Unit := fun _ => pure ()
  summaryEvaluated : TacticM Unit := pure ()
private unsafe def contextualAttempt? (request : ContextRequest) (preparedSeed? : Option PreparedContextRequest := none)
    (schedule? : Option ContextProviderSchedule := none) (observer : ContextDispatchObserver := {}) :
    TacticM ContextDispatchResult := do
  let schedule ←
    match schedule? with
    | some schedule => pure schedule
    | none => prepareContextProviderSchedule
  let mut prepared? := preparedSeed?
  let mut resourceSummary :=
    preparedSeed?.map (·.resourceSummary) |>.getD {}
  for scheduled in schedule do
    let providerName := scheduled.name
    let provider := scheduled.provider
    let prepared ←
      match provider.preparation with
      | .providerManaged =>
          pure request.prepareProviderManaged
      | .relevantFacts =>
          match prepared? with
          | some prepared =>
              trace[YesMetaZFC.proveAuto.context]
                "reuse prepared context for provider `{providerName}`"
              pure prepared
          | none =>
              let prepared ← prepareContextRequest request
              observer.prepared prepared
              prepared? := some prepared
              resourceSummary := prepared.resourceSummary
              pure prepared
    trace[YesMetaZFC.proveAuto.context]
      "provider `{providerName}` preparation={repr provider.preparation}; \
      facts={prepared.facts.size}; candidates={prepared.candidates.size}"
    observer.providerVisited providerName
    if provider.requirement == .hostObjectSyntax &&
        !prepared.terminal.hasHostObjectSyntax then
      observer.providerSkipped providerName
      trace[YesMetaZFC.proveAuto.context]
        "provider `{providerName}` skipped: no host object syntax"
      continue
    match ← provider.admit prepared with
    | .notApplicable reason =>
      observer.providerSkipped providerName
      trace[YesMetaZFC.proveAuto.context]
        "provider `{providerName}` not applicable: {reason}"
      continue
    | .accepted build =>
      observer.providerBuilt providerName provider.preparation
      let attempt ← build
      let expectedType := mkApp (mkConst ``GoalAttempt) request.goal
      let actualType ← inferType attempt
      unless ← isDefEq actualType expectedType do
        throwError
          "prove_auto context provider `{providerName}` returned{indentExpr actualType}, \
          expected{indentExpr expectedType}"
      return {
        attempt? := some attempt
        resourceSummary := prepared.resourceSummary
      }
  return {
    resourceSummary := resourceSummary
  }
class GoalRequest (goal : Prop) where
  run : GoalAttempt goal
namespace GoalRequest
@[reducible] def ofAttemptAt
    {σ : LogicSoundness.SetLevel.Signature}
    (problem : LogicSoundness.SetLevel.DeepProblem σ)
    (attempt : LogicSoundness.SetLevel.BackendAttemptAt.{x} problem) :
    GoalRequest (LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
        problem.theory problem.target) where
  run := {
    closed := LogicSoundness.SetLevel.BackendAttemptAt.closed attempt
    summary := LogicSoundness.SetLevel.BackendAttemptAt.summary attempt
    sound := GoalAttempt.backendSoundOfClosedAt problem attempt
  }
@[reducible] def ofAttempt
    {σ : LogicSoundness.SetLevel.Signature}
    (problem : LogicSoundness.SetLevel.DeepProblem σ)
    (attempt : LogicSoundness.SetLevel.BackendAttempt problem) :
    GoalRequest (LogicSoundness.SetLevel.SemanticallyEntails
        problem.theory problem.target) :=
  ofAttemptAt problem attempt
end GoalRequest
syntax (name := proveAutoCheckedCertificate)
  "prove_auto " "CERT " term : tactic
@[tactic proveAutoCheckedCertificate] unsafe def evalProveAutoCheckedCertificate : Tactic :=
  fun stx => do
    withProveAutoResources do
      withMainContext do
        let cert ← elabTerm stx[2] none
        let proof ← mkAppM ``LogicSoundness.SetLevel.CheckedCertificate.sound #[cert]
        closeByProof `prove_auto_cert proof
syntax (name := proveAutoBackendSuccess)
  "prove_auto " "BACKEND " term : tactic
@[tactic proveAutoBackendSuccess] unsafe def evalProveAutoBackendSuccess : Tactic :=
  fun stx => do
    withProveAutoResources do
      withMainContext do
        let success ← elabTerm stx[2] none
        let semanticProof ←
          mkAppM ``LogicSoundness.SetLevel.BackendSuccess.sound #[success]
        if ← proofFitsMainGoal semanticProof then
          closeByProof `prove_auto_backend semanticProof
        else
          throwError
            "prove_auto BACKEND certificate does not match the current intrinsic semantic target"
syntax (name := proveAutoCheckedValidCertificate)
  "prove_auto " "VALID " term : tactic
@[tactic proveAutoCheckedValidCertificate]
unsafe def evalProveAutoCheckedValidCertificate : Tactic :=
  fun stx => do
    withProveAutoResources do
      withMainContext do
        let cert ← elabTerm stx[2] none
        let proof ← mkAppM ``LogicSoundness.SetLevel.CheckedValidCertificate.sound #[cert]
        closeByProof `prove_auto_valid proof
/--
在当前局部上下文中证明一个计算 Bool 为真。
调用方必须先把 closed 投影规约到 proof-free 计算表达式；这里只检查结果，
不对完整证书做全递归正规化。
-/
private unsafe def proveBoolTrue? (expression : Expr) : TacticM (Option Expr) := do
  let expression ← instantiateMVars expression
  if expression.hasMVar then
    throwError "internal kernel replay check retained metavariables{indentExpr expression}"
  if expression.hasFVar then
    throwError "internal kernel replay check retained free variables{indentExpr expression}"
  let trueExpr := mkConst ``Bool.true
  let proofType ← mkEq expression trueExpr
  if ← withoutModifyingState <|
      withTransparency .all <| isDefEq expression trueExpr then
    return some (← mkEqRefl trueExpr)
  proveProposition? proofType
private unsafe def closeGoalAttempt (routed : Expr) (resourceSummary : ContextResourceSummary := {}) (onSummary : TacticM Unit := pure ()) : TacticM Unit := do
  let goal ← getMainTarget
  trace[YesMetaZFC.proveAuto.request]
    "start closed projection"
  let closedRaw := mkApp2 (mkConst ``GoalAttempt.closed) goal routed
  let closed ← withTransparency .all <| whnf closedRaw
  trace[YesMetaZFC.proveAuto.request]
    "finished closed projection"
  let (_, closedFreeVariables) ← closed.collectFVars.run {}
  let localContext ← getLCtx
  for freeVariable in closedFreeVariables.fvarIds do
    unless localContext.contains freeVariable do
      throwError
        "internal prove_auto closed replay leaked free variable `{freeVariable.name}`"
    let localDecl := localContext.get! freeVariable
    if localDecl.isImplementationDetail then
      throwError
        "internal prove_auto closed replay retained implementation-detail free variable \
        `{freeVariable.name}` of type{indentExpr localDecl.type}"
  if let some closedProof ← proveBoolTrue? closed then
    trace[YesMetaZFC.proveAuto.request]
      "closed proof established"
    let proof ← instantiateMVars <|
      mkApp3 (mkConst ``GoalAttempt.soundOfClosed) goal routed closedProof
    trace[YesMetaZFC.proveAuto.request]
      "sound proof assembled"
    let (_, freeVariables) ← proof.collectFVars.run {}
    for freeVariable in freeVariables.fvarIds do
      unless localContext.contains freeVariable do
        throwError
          "internal prove_auto proof leaked free variable `{freeVariable.name}`"
      let localDecl := localContext.get! freeVariable
      if localDecl.isImplementationDetail then
        throwError
          "internal prove_auto proof retained implementation-detail free variable \
          `{freeVariable.name}` of type{indentExpr localDecl.type}"
    closeByProof `prove_auto_routed proof
  else
    onSummary
    let summaryRaw := mkApp2 (mkConst ``GoalAttempt.summary) goal routed
    let summaryExpr ← withTransparency .all <| whnf summaryRaw
    let label ← evalExpr String (mkConst ``String) summaryExpr
    if !resourceSummary.present then
      throwError "prove_auto routed backend failed: {label}"
    else
      throwError
        "prove_auto routed backend failed: {label}\n\
        context resources: {resourceSummary.render}"
syntax (name := proveAutoRouted) "prove_auto" : tactic
private unsafe def runContextRequestCore (request : ContextRequest) (prepared? : Option PreparedContextRequest := none)
    (schedule? : Option ContextProviderSchedule := none) (observer : ContextDispatchObserver := {}) :
    TacticM Unit := do
  let dispatch ←
    contextualAttempt? request prepared? schedule? observer
  if let some contextual := dispatch.attempt? then
    closeGoalAttempt contextual dispatch.resourceSummary
      observer.summaryEvaluated
  else
    let requestType := mkApp (mkConst ``GoalRequest) request.goal
    let routed ←
      try
        let goalRequest ← synthInstance requestType
        pure <| mkApp2 (mkConst ``GoalRequest.run) request.goal goalRequest
      catch _ =>
        throwError
          "prove_auto could not synthesize a proof-carrying `GoalRequest` for the current \
          target and no context provider accepted the request; provide a local instance via \
          `GoalRequest.ofSource`, add supported `USE` facts, or use \
          `prove_auto CERT/BACKEND/VALID`."
    closeGoalAttempt routed dispatch.resourceSummary
      observer.summaryEvaluated
/--
运行一次已经完成宿主正规化的 provider 请求。
新 dispatch 只通过此入口进入 checked provider；调度细节不暴露为公共协议。
-/
unsafe def runContextRequest (request : ContextRequest)
    (prepared? : Option PreparedContextRequest := none) :
    TacticM Unit :=
  runContextRequestCore request prepared?
end ProveAutoRequest
end Automation
end YesMetaZFC
