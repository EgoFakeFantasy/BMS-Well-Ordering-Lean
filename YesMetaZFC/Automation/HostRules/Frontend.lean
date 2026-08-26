import Lean.Meta.Tactic.Simp.Main
import YesMetaZFC.Automation.HostRules.Registry
import YesMetaZFC.Automation.HostProp
import YesMetaZFC.Automation.Request
/-!
# HR 前端

HR 前端统一负责：
* 把 Lean 宿主命题重化为 `HostProp.Formula`；
* 按结论需求实例化已注册推理规则的对象参数；
* 把规则及其已知支持保存为 proof-carrying source facts；
* 构造供唯一 AVATAR 主线消费的 source/deep problem 快照。

前端不应用规则关闭目标。即使局部事实与目标完全一致，也仍作为 source 进入
AVATAR，由后端回放实际搜索证书。
-/
namespace YesMetaZFC
namespace Automation
namespace HostRules
namespace Frontend

open Lean Meta
open ProveAutoRequest
open HostProp

initialize registerTraceClass `YesMetaZFC.proveAuto.hostRules.frontend

register_option prove_auto.hr.maxRules : Nat := {
  defValue := 8
  descr := "maximum number of proof-carrying HR rules compiled per host request"
}

private structure ReifyState where
  atoms : Array Expr := #[]

private abbrev ReifyM := StateRefT ReifyState MetaM

private def internAtom (expression : Expr) : ReifyM Atom := do
  let state ← get
  if let some index :=
      state.atoms.findIdx? fun atom => atom == expression then
    return { id := index }
  for index in [0 : state.atoms.size] do
    let equivalent ← liftM <|
      withTransparency .reducible <|
        isDefEq state.atoms[index]! expression
    if equivalent then
      return { id := index }
  let id := state.atoms.size
  set (show ReifyState from {
    atoms := state.atoms.push expression
  })
  return { id }

private partial def reifyFormula (expression : Expr) : ReifyM Formula := do
  let expression ← instantiateMVars expression
  let expression ← liftM <| whnf expression.consumeMData
  if expression.isConstOf ``False then
    return .falsum
  if expression.isConstOf ``True then
    return .truth
  if expression.isAppOfArity ``Not 1 then
    return .neg (← reifyFormula expression.getAppArgs[0]!)
  if expression.isAppOfArity ``And 2 then
    return .conj
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Or 2 then
    return .disj
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Iff 2 then
    return .iff
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  match expression with
  | .forallE _ domain body _ =>
      if !body.hasLooseBVar 0 && (← isProp domain) then
        return .imp
          (← reifyFormula domain)
          (← reifyFormula body)
      return .atom (← internAtom expression)
  | _ =>
      return .atom (← internAtom expression)

private def atomFunctionExpr (atoms : Array Expr) : MetaM Expr := do
  withLocalDeclD `atomId (mkConst ``Nat) fun atomId => do
    let mut body := mkConst ``False
    for index in [0 : atoms.size] do
      let condition ← mkEq atomId (mkNatLit index)
      let decidable ←
        synthInstance (mkApp (mkConst ``Decidable) condition)
      body :=
        mkApp5 (mkConst ``ite [Level.succ Level.zero])
          (mkSort Level.zero) condition decidable atoms[index]! body
    mkLambdaFVars #[atomId] body

/--
HR 前端交给后端的完整重化快照。Lean 命题与 proof-carrying facts 只出现在 `input`
的语义对齐字段中；后端搜索只消费两个纯语法问题。
-/
structure ReifiedRequest where
  input : Expr
  sourceProblemValue : SourcePreprocessing.Problem
  sourceProblem : Expr
  problem : Expr
  hSource : Expr
  hProblem : Expr
  admissible : Expr

private structure SimplifiedFact where
  proposition : Expr
  proof : Expr

private def simplifyFact (context : Simp.Context)
    (proposition proof : Expr) : MetaM SimplifiedFact := do
  let (result, _) ← simp proposition context
  let proof ←
    match result.proof? with
    | some equality =>
        pure <| mkApp4 (mkConst ``Eq.mp [Level.zero])
          proposition result.expr equality proof
    | none =>
        mkExpectedTypeHint proof result.expr
  return {
    proposition := result.expr
    proof
  }

/-- 把准备后的宿主请求重化为公共 AVATAR 可消费的问题快照。 -/
def reify (request : PreparedContextRequest) : MetaM ReifiedRequest := do
  for factType in request.terminal.factPropositions do
    unless ← isProp factType do
      throwError
        "prove_auto HR fact is not a proposition:{indentExpr factType}"
  let simpContext ← Simp.Context.mkDefault
  let mut factTypes := #[]
  let mut proofs := #[]
  for index in [0 : request.facts.size] do
    let simplified ←
      simplifyFact simpContext
        request.terminal.factPropositions[index]!
        request.facts[index]!
    factTypes := factTypes.push simplified.proposition
    proofs := proofs.push simplified.proof
  let (targetResult, _) ← simp request.goal simpContext
  let ((premises, target), state) ← (do
      let premises ←
        factTypes.toList.mapM reifyFormula
      let target ← reifyFormula targetResult.expr
      pure (premises, target)).run {}
  let atoms ← atomFunctionExpr state.atoms
  let facts ←
    HostProp.proofFactsExprWithTypes proofs factTypes
  let premiseList ←
    mkListLit (mkConst ``Formula) (premises.map toExpr)
  let targetFormula := toExpr target
  let evalFunction := mkApp (mkConst ``Formula.eval) atoms
  let premiseEvals ← mkAppM ``List.map #[evalFunction, premiseList]
  let factPropositions ←
    mkAppM ``Facts.propositions #[facts]
  let targetEval :=
    mkApp2 (mkConst ``Formula.eval) atoms targetFormula
  let hPremises ← mkEqRefl premiseEvals
  unless ← isDefEq
      (← inferType hPremises)
      (← mkEq premiseEvals factPropositions) do
    throwError "internal HR premise alignment is not definitional"
  let hTarget ← mkEqRefl targetEval
  let hTarget ←
    match targetResult.proof? with
    | some equality => mkEqSymm equality
    | none => pure hTarget
  unless ← isDefEq (← inferType hTarget)
      (← mkEq targetEval request.goal) do
    throwError "internal HR target alignment is not definitional"
  let input :=
    mkAppN (mkConst ``CheckedInput.mk)
      #[request.goal, atoms, facts, premiseList, targetFormula,
        hPremises, hTarget]
  let sourceProblem ←
    mkAppM ``CheckedInput.sourceProblemOfSyntax
      #[premiseList, targetFormula]
  let problem ←
    mkAppM ``CheckedInput.deepProblemOfSyntax
      #[premiseList, targetFormula]
  let expectedSource ←
    mkAppM ``CheckedInput.sourceProblem #[input]
  let expectedProblem ←
    mkAppM ``CheckedInput.deepProblem #[input]
  unless ← isDefEq sourceProblem expectedSource do
    throwError "internal HR source snapshot lost syntax alignment"
  unless ← isDefEq problem expectedProblem do
    throwError "internal HR deep snapshot lost syntax alignment"
  let hSource ← mkEqRefl sourceProblem
  let hProblem ← mkEqRefl problem
  let admissible ←
    mkAppM ``CheckedInput.deepProblemOfSyntax_admissible
      #[premiseList, targetFormula]
  trace[YesMetaZFC.proveAuto.hostRules.frontend]
    "reified atoms={state.atoms.size}; premises={premises.length}; \
    resources={request.resourceSummary.render}"
  for index in [0 : state.atoms.size] do
    trace[YesMetaZFC.proveAuto.hostRules.frontend]
      "HR atom[{index}]={state.atoms[index]!}"
  return {
    input
    sourceProblemValue :=
      CheckedInput.sourceProblemOfSyntax premises target
    sourceProblem
    problem
    hSource
    hProblem
    admissible
  }

private partial def goalHasLogicalStructure (goal : Expr) :
    MetaM Bool := do
  let goal ← whnf (← instantiateMVars goal)
  if goal.isAppOfArity ``Not 1 ||
      goal.isAppOfArity ``And 2 ||
      goal.isAppOfArity ``Or 2 ||
      goal.isAppOfArity ``Iff 2 then
    return true
  match goal with
  | .forallE _ domain body _ =>
      return !body.hasLooseBVar 0 && (← isProp domain)
  | .letE _ _ value body _ =>
      goalHasLogicalStructure (body.instantiate1 value)
  | _ =>
      return false

/-- 判断请求是否需要 HR 命题骨架后端。 -/
def applicable (request : PreparedContextRequest) : MetaM Bool := do
  unless ← isProp request.goal do
    return false
  return !request.facts.isEmpty ||
    (← goalHasLogicalStructure request.goal)

private structure Candidate where
  label : Name
  proposition : Expr
  proof : Expr
  conclusionHead? : Option Name := none
deriving Inhabited

private structure CompiledRule where
  declaration : Name
  proposition : Expr
  proof : Expr
  premises : Array Expr := #[]
  supports : Array Candidate := #[]

private def pushNameUnique (names : Array Name) (name : Name) :
    Array Name :=
  if names.contains name then names else names.push name

private def pushCandidateUnique (candidates : Array Candidate)
    (candidate : Candidate) : Array Candidate :=
  if candidates.any fun existing =>
      existing.proposition == candidate.proposition then
    candidates
  else
    candidates.push candidate

private def allCandidatesOfPrepared
    (prepared : PreparedContextRequest) :
    MetaM (Array Candidate) := do
  let mut candidates := #[]
  for candidate in prepared.candidates do
    candidates := pushCandidateUnique candidates {
      label := candidate.label
      proposition := candidate.proposition
      proof := candidate.proof
      conclusionHead? :=
        ← Registry.propositionConclusionHead? candidate.proposition
    }
  for index in [0 : prepared.facts.size] do
    let proof := prepared.facts[index]!
    let proposition := prepared.terminal.factPropositions[index]!
    candidates := pushCandidateUnique candidates {
      label := proof.getAppFn.constName?.getD `explicit
      proposition
      proof
      conclusionHead? :=
        ← Registry.propositionConclusionHead? proposition
    }
  return candidates

private def tryUnify (left right : Expr) : MetaM Bool := do
  let savedState ← saveState
  if ← withTransparency .reducible <| isDefEq left right then
    return true
  savedState.restore
  return false

private def tryUnifyAlias (left right : Expr) : MetaM Bool := do
  let savedState ← saveState
  if ← withTransparency .default <| isDefEq left right then
    return true
  savedState.restore
  return false

private partial def collectDemandPropositions
    (proposition : Expr) (fuel : Nat := 32)
    (demands : Array Expr := #[]) :
    MetaM (Array Expr) := do
  if fuel == 0 then
    return demands
  let proposition ← instantiateMVars proposition
  let proposition := proposition.consumeMData
  let demands :=
    if demands.any fun existing => existing == proposition then
      demands
    else
      demands.push proposition
  match proposition with
  | _ =>
      let reduced ← whnf proposition
      if reduced != proposition then
        return ←
          collectDemandPropositions reduced (fuel - 1) demands
      if reduced.isAppOfArity ``And 2 ||
          reduced.isAppOfArity ``Or 2 ||
          reduced.isAppOfArity ``Iff 2 then
        let arguments := reduced.getAppArgs
        let demands ←
          collectDemandPropositions
            arguments[0]! (fuel - 1) demands
        collectDemandPropositions
          arguments[1]! (fuel - 1) demands
      else
        return demands

private def demandHead? (proposition : Expr) :
    MetaM (Option Name) :=
  Registry.propositionConclusionHead? proposition

private def matchingDemand? (conclusion : Expr)
    (demands : Array Expr) : MetaM Bool := do
  let conclusionHead? ← demandHead? conclusion
  let mut index := demands.size
  while index > 0 do
    index := index - 1
    let demand := demands[index]!
    if conclusionHead?.isSome &&
        (← demandHead? demand) != conclusionHead? then
      continue
    if ← tryUnify conclusion demand then
      return true
  return false

private def matchingCandidate? (pattern : Expr)
    (candidates : Array Candidate) : MetaM (Option Candidate) := do
  let patternHead? ←
    Registry.propositionConclusionHead? pattern
  /- 先走稳定头索引快路径。 -/
  let mut index := candidates.size
  while index > 0 do
    index := index - 1
    let candidate := candidates[index]!
    if candidate.conclusionHead? != patternHead? then
      continue
    if ← tryUnify pattern candidate.proposition then
      return some candidate
  /-
  定义别名可能拥有不同表面头，例如 `IsRegularCardinal` 可约为
  `IsCofinality κ κ`。只对快路径未命中的剩余候选做一次线性回退。
  -/
  index := candidates.size
  while index > 0 do
    index := index - 1
    let candidate := candidates[index]!
    if candidate.conclusionHead? == patternHead? then
      continue
    if ← tryUnifyAlias pattern candidate.proposition then
      return some candidate
  return none

private def demandedCandidates
    (demands : Array Expr) (candidates : Array Candidate) :
    MetaM (Array Candidate) := do
  let mut selected := #[]
  for demand in demands do
    if let some candidate ←
        matchingCandidate? demand candidates then
      selected := pushCandidateUnique selected candidate
  return selected

private def validateLocalExpression (label : String)
    (expression : Expr) : MetaM Unit := do
  let (_, freeVariables) ← expression.collectFVars.run {}
  let localContext ← getLCtx
  for freeVariable in freeVariables.fvarIds do
    unless localContext.contains freeVariable do
      throwError
        "internal HR {label} leaked a temporary free variable: \
        {freeVariable.name}"

private partial def withSpecializedRuleBinders {α : Type}
    (type proof : Expr) (premiseArguments objectArguments : Array Expr := #[])
    (action :
      Array Expr → Array Expr → Expr → Expr → MetaM α) : MetaM α := do
  let type ← whnf type
  match type with
  | .forallE binderName domain body binderInfo =>
      let domain ← instantiateMVars domain
      if ← isProp domain then
        unless binderInfo.isExplicit do
          throwError "HR rule has an implicit proposition premise"
        withLocalDecl binderName binderInfo domain fun argument =>
          withSpecializedRuleBinders
            (body.instantiate1 argument) (mkApp proof argument)
            (premiseArguments.push argument) objectArguments action
      else
        if binderInfo.isInstImplicit then
          throwError "HR rule has a typeclass binder"
        let argument ← mkFreshExprMVar domain
        withSpecializedRuleBinders
          (body.instantiate1 argument) (mkApp proof argument)
          premiseArguments (objectArguments.push argument) action
  | _ =>
      action premiseArguments objectArguments proof type

private def compileRule (entry : Registry.Entry)
    (demands : Array Expr) (candidates : Array Candidate) :
    MetaM (Option CompiledRule) := do
  let savedState ← saveState
  let result? ←
    try
      let sourceTheorem ←
        mkConstWithFreshMVarLevels entry.declaration
      let theoremType ←
        instantiateMVars (← inferType sourceTheorem)
      withSpecializedRuleBinders theoremType sourceTheorem #[] #[]
          fun premiseArguments objectArguments bodyProof conclusion => do
        let mut supports := #[]
        unless ← matchingDemand? conclusion demands do
          throwError "HR rule conclusion is not demanded"
        let mut premises := #[]
        for argument in premiseArguments do
          let premise ←
            instantiateMVars (← inferType argument)
          premises := premises.push premise
          if let some support ←
              matchingCandidate? premise candidates then
            supports := pushCandidateUnique supports support
        let conclusion ← instantiateMVars conclusion
        let mut hasProgress := premises.isEmpty
        for premise in premises do
          unless ← tryUnify premise conclusion do
            hasProgress := true
            break
        unless hasProgress do
          throwError "HR rule is a circular identity"
        let objectArguments ←
          objectArguments.mapM instantiateMVars
        if objectArguments.any fun argument => argument.hasMVar then
          throwError
            "HR rule object parameters are not uniquely determined"
        let bodyProof ← instantiateMVars bodyProof
        let proof ←
          instantiateMVars (← mkLambdaFVars premiseArguments bodyProof)
        let proposition ←
          instantiateMVars (← inferType proof)
        let instantiatedPremises ←
          premises.mapM instantiateMVars
        if proof.hasMVar || proposition.hasMVar ||
            instantiatedPremises.any (·.hasMVar) then
          throwError "HR rule retained metavariables"
        unless ← isProp proposition do
          throwError "HR rule compilation lost proposition type"
        pure <| some {
          declaration := entry.declaration
          proposition
          proof
          premises := instantiatedPremises
          supports
        }
    catch error =>
      trace[YesMetaZFC.proveAuto.hostRules.frontend]
        "HR rule `{entry.declaration}` skipped: {error.toMessageData}"
      pure none
  savedState.restore
  if let some result := result? then
    validateLocalExpression "rule proof" result.proof
    validateLocalExpression "rule proposition" result.proposition
    for premise in result.premises do
      validateLocalExpression "rule premise" premise
    for support in result.supports do
      validateLocalExpression "rule support" support.proof
  return result?

private def demandHeads (demands : Array Expr) :
    MetaM (Array Name) := do
  let mut heads := #[]
  for demand in demands do
    if let some head ← demandHead? demand then
      heads := pushNameUnique heads head
  return heads

private def appendFact (proof proposition : Expr)
    (facts propositions : Array Expr) :
    Array Expr × Array Expr :=
  if propositions.any fun existing =>
      existing == proposition then
    (facts, propositions)
  else
    (facts.push proof, propositions.push proposition)

/--
按需求闭包编译宿主推理规则。规则的命题前提不要求已经拥有局部证明；它们保留在
完整 proposition 中，由 AVATAR saturation 统一搜索。已有支持只作为额外 source
加入，不在 Meta 层执行 `apply` 或 `exact`。
-/
def augmentRules (prepared : PreparedContextRequest) :
    MetaM PreparedContextRequest := do
  let candidates ← allCandidatesOfPrepared prepared
  let maxRules :=
    (← getOptions).get `prove_auto.hr.maxRules 8
  if maxRules == 0 then
    return prepared
  let rootDemands ←
    collectDemandPropositions prepared.goal
  let mut demands := rootDemands
  let mut compiled := #[]
  let mut visited := #[]
  while compiled.size < maxRules do
    let heads ← demandHeads demands
    let entries ← Registry.rulesForHeads heads
    let mut progressed := false
    for entry in entries do
      if compiled.size >= maxRules then
        break
      if visited.contains entry.declaration then
        continue
      visited := visited.push entry.declaration
      if let some source ←
          compileRule entry demands candidates then
        compiled := compiled.push source
        progressed := true
        for premise in source.premises do
          demands ← collectDemandPropositions premise 16 demands
    unless progressed do
      break
  let directSupports ←
    demandedCandidates rootDemands candidates
  if compiled.isEmpty && directSupports.isEmpty then
    return prepared
  let mut facts := prepared.facts
  let mut propositions := prepared.terminal.factPropositions
  let mut selectedNames := prepared.resourceSummary.selected
  for source in compiled do
    (facts, propositions) :=
      appendFact source.proof source.proposition facts propositions
    selectedNames := pushNameUnique selectedNames source.declaration
    for support in source.supports do
      (facts, propositions) :=
        appendFact support.proof support.proposition facts propositions
      selectedNames := pushNameUnique selectedNames support.label
  for support in directSupports do
    (facts, propositions) :=
      appendFact support.proof support.proposition facts propositions
    selectedNames := pushNameUnique selectedNames support.label
  for source in compiled do
    trace[YesMetaZFC.proveAuto.hostRules.frontend]
      "HR rule `{source.declaration}` proposition={source.proposition}; \
      premises={source.premises}"
  trace[YesMetaZFC.proveAuto.hostRules.frontend]
    "compiled HR rules={compiled.map (·.declaration)}; \
    directSupports={directSupports.size}; demands={demands.size}; \
    facts={prepared.facts.size}->{facts.size}"
  return {
    prepared with
    facts
    terminal := {
      factPropositions := propositions
      hasHostObjectSyntax := prepared.terminal.hasHostObjectSyntax
      hasHostRules := true
    }
    resourceSummary := {
      prepared.resourceSummary with
      selected := selectedNames
    }
    stats := {
      prepared.stats with
      totalFacts := facts.size
      terminalPropositions := propositions.size
    }
  }
end Frontend
end HostRules
end Automation
end YesMetaZFC
