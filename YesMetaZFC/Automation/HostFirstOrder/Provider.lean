import Lean
import YesMetaZFC.Automation.HostFirstOrder.Semantics
import YesMetaZFC.Automation.HostProp
import YesMetaZFC.Automation.Request

/-!
# 宿主一阶 provider

元层只负责把 Lean 表达式重化为索引语法。内部 raw 节点不会离开本文件；提交给内核的
对象始终是 `Formula 0`，量词体在构造时携带 `Formula (depth + 1)`，因此不再生成
作用域、良构或 admissibility 证明。
-/

namespace YesMetaZFC
namespace Automation
namespace HostFirstOrder
namespace Provider

universe u

open Lean Meta
open ProveAutoRequest

structure ReifiedRequest where
  input : Expr
  sourceProblemValue : SourcePreprocessing.Problem
  sourceProblem : Expr
  searchProblem : Expr
  compiled : Expr

private structure FunctionEntry where
  head : Expr
  arity : Nat

private structure PredicateEntry where
  head : Expr
  arity : Nat

private inductive RawTerm where
  | bvar (id : FVarId)
  | app (symbol : Nat) (arguments : List RawTerm)

private inductive RawFormula where
  | atom (symbol : Nat) (arguments : List RawTerm)
  | equal (left right : RawTerm)
  | falsum
  | truth
  | neg (body : RawFormula)
  | conj (left right : RawFormula)
  | disj (left right : RawFormula)
  | imp (left right : RawFormula)
  | iff (left right : RawFormula)
  | forallE (binder : FVarId) (body : RawFormula)
  | existsE (binder : FVarId) (body : RawFormula)

mutual
  private def rawTermToTyped (depth : Nat) (bound : List FVarId) :
      RawTerm → Option (Term depth)
    | .bvar id =>
        match bound.findIdx? (fun entry => entry == id) with
        | none => none
        | some index =>
            if h : index < depth then
              some (.bvar ⟨index, h⟩)
            else
              none
    | .app symbol arguments =>
        match rawTermsToTyped depth bound arguments with
        | some arguments => some (.app symbol arguments)
        | none => none

  private def rawTermsToTyped (depth : Nat) (bound : List FVarId) :
      List RawTerm → Option (List (Term depth))
    | [] => some []
    | head :: tail => do
        let head ← rawTermToTyped depth bound head
        let tail ← rawTermsToTyped depth bound tail
        pure (head :: tail)

  private def rawFormulaToTyped (depth : Nat) (bound : List FVarId) :
      RawFormula → Option (Formula depth)
    | .atom symbol arguments =>
        match rawTermsToTyped depth bound arguments with
        | some arguments => some (.atom symbol arguments)
        | none => none
    | .equal left right => do
        let left ← rawTermToTyped depth bound left
        let right ← rawTermToTyped depth bound right
        pure (.equal left right)
    | .falsum => some .falsum
    | .truth => some .truth
    | .neg body => do
        let body ← rawFormulaToTyped depth bound body
        pure (.neg body)
    | .conj left right => do
        let left ← rawFormulaToTyped depth bound left
        let right ← rawFormulaToTyped depth bound right
        pure (.conj left right)
    | .disj left right => do
        let left ← rawFormulaToTyped depth bound left
        let right ← rawFormulaToTyped depth bound right
        pure (.disj left right)
    | .imp left right => do
        let left ← rawFormulaToTyped depth bound left
        let right ← rawFormulaToTyped depth bound right
        pure (.imp left right)
    | .iff left right => do
        let left ← rawFormulaToTyped depth bound left
        let right ← rawFormulaToTyped depth bound right
        pure (.iff left right)
    | .forallE binder body => do
        let body ← rawFormulaToTyped (Nat.succ depth) (binder :: bound) body
        pure (.forallE body)
    | .existsE binder body => do
        let body ← rawFormulaToTyped (Nat.succ depth) (binder :: bound) body
        pure (.existsE body)
end

private def closeRawFormula (formula : RawFormula) : Option ClosedFormula :=
  rawFormulaToTyped 0 [] formula

private def closeRawFormulas : List RawFormula → Option (List ClosedFormula)
  | [] => some []
  | head :: tail => do
      let head ← closeRawFormula head
      let tail ← closeRawFormulas tail
      pure (head :: tail)

private structure NativeReifyState where
  domain : Expr
  functions : Array FunctionEntry := #[]
  predicates : Array PredicateEntry := #[]
  bound : Array FVarId := #[]

private abbrev NativeReifyM := StateRefT NativeReifyState MetaM

private def withObjectBinder {β : Type} (binderName : Name)
    (domain : Expr) (action : Expr → NativeReifyM β) :
    NativeReifyM (FVarId × β) := do
  let state ← get
  let (result, nextState) ←
    withLocalDeclD binderName domain fun binder =>
      ((do
          let result ← action binder
          pure (binder.fvarId!, result)).run {
            state with bound := state.bound.push binder.fvarId!
          })
  set { nextState with bound := state.bound }
  return result

private def rememberDomain (candidate : Expr) :
    StateRefT (Option Expr) MetaM Unit := do
  if ← isProp candidate then
    throwError "proposition binders are not first-order object domains"
  match ← get with
  | none =>
      set (some candidate)
  | some domain =>
      unless ← withTransparency .reducible <| isDefEq domain candidate do
        throwError
          "native host first-order reification found heterogeneous domains \
          {domain} and {candidate}"

private partial def discoverDomain (expression : Expr) :
    StateRefT (Option Expr) MetaM Unit := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  if expression.isAppOfArity ``Not 1 then
    return ← discoverDomain expression.getAppArgs[0]!
  if expression.isAppOfArity ``And 2 ||
      expression.isAppOfArity ``Or 2 ||
      expression.isAppOfArity ``Iff 2 then
    for argument in expression.getAppArgs do
      discoverDomain argument
    return
  if expression.isAppOfArity ``Eq 3 then
    rememberDomain expression.getAppArgs[0]!
    return
  if expression.isAppOfArity ``Exists 2 then
    let domain := expression.getAppArgs[0]!
    rememberDomain domain
    let predicate ← whnf expression.getAppArgs[1]!
    match predicate with
    | .lam _ binderDomain body _ =>
        rememberDomain binderDomain
        discoverDomain body
    | _ =>
        return
    return
  match expression with
  | .forallE _ domain body _ =>
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          throwError "dependent proposition binders are not supported"
        discoverDomain domain
        discoverDomain body
      else
        rememberDomain domain
        discoverDomain body
  | .letE _ _ value body _ =>
      discoverDomain (body.instantiate1 value)
  | _ =>
      return

private def discoverSharedDomain? (expressions : Array Expr) :
    MetaM (Option Expr) := do
  let (_, domain?) ← (expressions.forM discoverDomain).run none
  return domain?

private def objectSuffix (domain expression : Expr) :
    MetaM (Expr × Array Expr) := do
  let arguments := expression.getAppArgs
  let mut split := arguments.size
  while split > 0 do
    let argumentType ← instantiateMVars (← inferType arguments[split - 1]!)
    if ← withTransparency .reducible <| isDefEq argumentType domain then
      split := split - 1
    else
      break
  let mut head := expression.getAppFn
  for index in [0 : split] do
    head := mkApp head arguments[index]!
  if head.hasLooseBVars then
    throwError
      "native host first-order symbols cannot capture object bound variables"
  return (head, arguments.extract split arguments.size)

private def capturesObjectBound (expression : Expr) : NativeReifyM Bool := do
  let state ← get
  let (_, freeVariables) ← expression.collectFVars.run {}
  return state.bound.any fun bound =>
    freeVariables.fvarIds.contains bound

private def internFunction (head : Expr) (arity : Nat) : NativeReifyM Nat := do
  let state ← get
  if let some index := state.functions.findIdx? fun entry =>
      entry.arity == arity && entry.head == head then
    return index
  let id := state.functions.size
  set { state with functions := state.functions.push { head, arity } }
  return id

private def internPredicate (head : Expr) (arity : Nat) : NativeReifyM Nat := do
  let state ← get
  if let some index := state.predicates.findIdx? fun entry =>
      entry.arity == arity && entry.head == head then
    return index
  let id := state.predicates.size
  set { state with predicates := state.predicates.push { head, arity } }
  return id

private partial def reifyTerm (expression : Expr) : NativeReifyM RawTerm := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  match expression with
  | .bvar _ =>
      throwError "unexpected loose object binder during native reification"
  | .fvar id =>
      let state ← get
      if state.bound.contains id then
        return .bvar id
      let domain := state.domain
      let expressionType ← instantiateMVars (← inferType expression)
      unless ← withTransparency .reducible <| isDefEq expressionType domain do
        throwError
          "native host first-order term has type {expressionType}, expected {domain}"
      let functionId ← internFunction expression 0
      return .app functionId []
  | .letE _ _ value body _ =>
      reifyTerm (body.instantiate1 value)
  | _ =>
      let domain := (← get).domain
      let expressionType ← instantiateMVars (← inferType expression)
      unless ← withTransparency .reducible <| isDefEq expressionType domain do
        throwError
          "native host first-order term has type {expressionType}, expected {domain}"
      let (head, arguments) ← objectSuffix domain expression
      if ← capturesObjectBound head then
        throwError
          "native host first-order function symbol captures an object binder"
      let id ← internFunction head arguments.size
      let arguments ← arguments.toList.mapM reifyTerm
      return .app id arguments

private partial def reifyFormula (expression : Expr) : NativeReifyM RawFormula := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  if expression.isConstOf ``False then
    return .falsum
  if expression.isConstOf ``True then
    return .truth
  if expression.isAppOfArity ``Not 1 then
    return .neg (← reifyFormula expression.getAppArgs[0]!)
  if expression.isAppOfArity ``And 2 then
    return .conj (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Or 2 then
    return .disj (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Iff 2 then
    return .iff (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Eq 3 then
    let domain := (← get).domain
    let equalityDomain := expression.getAppArgs[0]!
    unless ← withTransparency .reducible <| isDefEq equalityDomain domain do
      throwError "native host first-order equality is outside the object domain"
    return .equal (← reifyTerm expression.getAppArgs[1]!)
      (← reifyTerm expression.getAppArgs[2]!)
  if expression.isAppOfArity ``Exists 2 then
    let domain := (← get).domain
    let existentialDomain := expression.getAppArgs[0]!
    unless ← withTransparency .reducible <| isDefEq existentialDomain domain do
      throwError "native host first-order existential is outside the object domain"
    let predicate := expression.getAppArgs[1]!
    let reduced ← whnf predicate
    let (binder, body) ←
      match reduced with
      | .lam _ binderDomain body _ => do
          unless ← withTransparency .reducible <| isDefEq binderDomain domain do
            throwError "native host first-order existential binder changed domain"
          withObjectBinder `witness binderDomain fun binder =>
            reifyFormula (body.instantiate1 binder)
      | _ =>
          withObjectBinder `witness domain fun binder =>
            reifyFormula (mkApp predicate binder)
    return .existsE binder body
  match expression with
  | .forallE _ domain body _ =>
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          throwError "dependent proposition binders are not supported"
        return .imp (← reifyFormula domain) (← reifyFormula body)
      let objectDomain := (← get).domain
      unless ← withTransparency .reducible <| isDefEq domain objectDomain do
        throwError "native host first-order universal changed object domain"
      let (binder, body) ←
        withObjectBinder `object domain fun binder =>
          reifyFormula (body.instantiate1 binder)
      return .forallE binder body
  | .letE _ _ value body _ =>
      reifyFormula (body.instantiate1 value)
  | _ =>
      unless ← isProp expression do
        throwError "native host first-order formula expected a proposition"
      let domain := (← get).domain
      let (head, arguments) ← objectSuffix domain expression
      if ← capturesObjectBound head then
        throwError
          "native host first-order predicate symbol captures an object binder"
      let id ← internPredicate head arguments.size
      let arguments ← arguments.toList.mapM reifyTerm
      return .atom id arguments

private def domainLevel (domain : Expr) : MetaM Level := do
  match ← whnf (← inferType domain) with
  | .sort (.succ level) =>
      return level
  | type =>
      throwError "native host first-order domain is not a type: {type}"

private def objectDefault? (domain : Expr) : MetaM (Option Expr) := do
  for localDecl in (← getLCtx) do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
        localDecl.isLet then
      continue
    let localType ← instantiateMVars localDecl.type
    if ← withTransparency .reducible <| isDefEq localType domain then
      return some localDecl.toExpr
  return none

private partial def applyFromList (domain resultType fallback head : Expr)
    (remaining : Nat) (arguments : Expr)
    (values : Array Expr := #[]) : MetaM Expr := do
  if remaining = 0 then
    let result := mkAppN head values
    let actualType ← instantiateMVars (← inferType result)
    unless ← withTransparency .reducible <| isDefEq actualType resultType do
      throwError
        "native host symbol {head} does not return {resultType}"
    return result
  let domainUniverse ← domainLevel domain
  let .sort resultUniverse ← whnf (← inferType resultType)
    | throwError "native host symbol result is not a type"
  let listDomain := mkApp (mkConst ``List [domainUniverse]) domain
  let motive ←
    withLocalDeclD `items listDomain fun items =>
      mkLambdaFVars #[items] resultType
  let consBranch ←
    withLocalDeclD `head domain fun value =>
      withLocalDeclD `tail listDomain fun tail => do
        let body ← applyFromList domain resultType fallback head
          (remaining - 1) tail (values.push value)
        mkLambdaFVars #[value, tail] body
  return mkAppN (mkConst ``List.casesOn [resultUniverse, domainUniverse])
    #[domain, motive, arguments, fallback, consBranch]

private def functionTableExpr (domain default : Expr)
    (entries : Array FunctionEntry) : MetaM Expr := do
  let level ← domainLevel domain
  let listDomain := mkApp (mkConst ``List [level]) domain
  withLocalDeclD `symbol (mkConst ``Nat) fun symbol =>
    withLocalDeclD `arguments listDomain fun arguments => do
      let mut body := default
      let mut index := entries.size
      while index > 0 do
        index := index - 1
        let some entry := entries[index]?
          | throwError "internal native function table index escaped bounds"
        let branch ←
          applyFromList domain domain default entry.head entry.arity arguments
        let condition ← mkEq symbol (mkNatLit index)
        let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
        body := mkApp5 (mkConst ``ite [Level.succ level])
          domain condition decidable branch body
      mkLambdaFVars #[symbol, arguments] body

private def predicateTableExpr (domain : Expr)
    (entries : Array PredicateEntry) : MetaM Expr := do
  let level ← domainLevel domain
  let listDomain := mkApp (mkConst ``List [level]) domain
  withLocalDeclD `symbol (mkConst ``Nat) fun symbol =>
    withLocalDeclD `arguments listDomain fun arguments => do
      let mut body := mkConst ``False
      let mut index := entries.size
      while index > 0 do
        index := index - 1
        let some entry := entries[index]?
          | throwError "internal native predicate table index escaped bounds"
        let branch ←
          applyFromList domain (mkSort Level.zero) (mkConst ``False)
            entry.head entry.arity arguments
        let condition ← mkEq symbol (mkNatLit index)
        let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
        body := mkApp5 (mkConst ``ite [Level.succ Level.zero]) (mkSort Level.zero)
          condition decidable branch body
      mkLambdaFVars #[symbol, arguments] body

private def checkedInput? (request : PreparedContextRequest)
    (domain default : Expr) (rawPremises : List RawFormula)
    (rawTarget : RawFormula) (state : NativeReifyState) :
    MetaM (Option ReifiedRequest) := do
  let some premises := closeRawFormulas rawPremises
    | return none
  let some target := closeRawFormula rawTarget
    | return none
  let functionTable ← functionTableExpr domain default state.functions
  let predicateTable ← predicateTableExpr domain state.predicates
  let level ← domainLevel domain
  let interpretation :=
    mkAppN (mkConst ``Interpretation.mk [level])
      #[domain, default, functionTable, predicateTable]
  let facts ←
    HostProp.proofFactsExprWithTypes request.facts
      request.terminal.factPropositions
  let formulaType := mkApp (mkConst ``Formula) (mkNatLit 0)
  let premiseList ←
    mkListLit formulaType (premises.map (fun formula => toExpr formula))
  let targetFormula := toExpr target
  let evalFunction ←
    mkAppM ``Semantics.closedEval #[interpretation]
  let premiseEvals ← mkAppM ``List.map #[evalFunction, premiseList]
  let factPropositions ←
    mkAppM ``HostProp.Facts.propositions #[facts]
  let targetEval ←
    mkAppM ``Semantics.closedEval #[interpretation, targetFormula]
  let hPremises ← mkEqRefl premiseEvals
  unless ← withTransparency .all <|
      isDefEq (← inferType hPremises)
        (← mkEq premiseEvals factPropositions) do
    throwError "internal indexed HostFirstOrder premise alignment is not definitional"
  let hTarget ← mkEqRefl targetEval
  unless ← withTransparency .all <|
      isDefEq (← inferType hTarget) (← mkEq targetEval request.goal) do
    throwError
      "internal indexed HostFirstOrder target alignment is not definitional:\n\
      eval={indentExpr targetEval}\ngoal={indentExpr request.goal}"
  let input :=
    mkAppN (mkConst ``Semantics.CheckedInput.mk [level])
      #[request.goal, interpretation, facts, premiseList, targetFormula,
        hPremises, hTarget]
  let sourceProblem ←
    mkAppM ``Semantics.CheckedInput.sourceProblem #[input]
  let searchProblem ←
    mkAppM ``Semantics.CheckedInput.searchProblem #[input]
  let compiled ←
    mkAppM ``Semantics.CheckedInput.checkedProblem #[input]
  return some {
    input
    sourceProblemValue := sourceProblemOfSyntax premises target
    sourceProblem
    searchProblem
    compiled
  }

def reify (request : PreparedContextRequest) :
    MetaM (Option ReifiedRequest) := do
  let expressions := request.terminal.factPropositions.push request.goal
  let some domain ←
      try discoverSharedDomain? expressions
      catch _ => pure none
    | return none
  let some default ← objectDefault? domain
    | return none
  try
    let ((rawPremises, rawTarget), state) ←
      (do
        let rawPremises ←
          request.terminal.factPropositions.toList.mapM reifyFormula
        let rawTarget ← reifyFormula request.goal
        pure (rawPremises, rawTarget)).run {
          domain
        }
    checkedInput? request domain default rawPremises rawTarget state
  catch error =>
    trace[YesMetaZFC.proveAuto.hostFirstOrder]
      "indexed native reification rejected request: {error.toMessageData}"
    pure none

end Provider
end HostFirstOrder
end Automation
end YesMetaZFC
