import Lean
import YesMetaZFC.Automation.FirstOrderDerives
import YesMetaZFC.Logic.FirstOrder.Admissibility
/-!
# `Derives` 有限全称闭包入口
本模块把非空理论下反复出现的“理论句子保证 + 空上下文新鲜性 + 逐层全域化”
整理为 `derive_close`。搜索层只选择已经注册的理论闭公式证明；每一层闭包仍直接
重放 `FirstOrder.Derives.forall_intro`，最终证明项由 Lean 内核核对。
-/
namespace YesMetaZFC
namespace Automation
namespace DerivesClosure
open Lean Elab Tactic Meta
open Logic FirstOrder
universe u v w
theorem theory_fresh_of_sentence
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} (hSentence : ∀ formula, T formula → Formula.Sentence formula) (sort : σ.SortSymbol) (eigen : FreeVarId) :
    ∀ formula, T formula → (sort, eigen) ∉ Formula.freeSupport formula := by
  intro formula hFormula
  have hClosed := (hSentence formula hFormula).2
  rw [hClosed]
  simp
theorem empty_context_fresh
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (eigen : FreeVarId) :
    ∀ formula, formula ∈ ([] : Context σ) → (sort, eigen) ∉ Formula.freeSupport formula := by
  intro formula hFormula
  cases hFormula
theorem forall_intro_of_sentence
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ}
    {body : Formula σ} (hBody : Derives T [] body) (sort : σ.SortSymbol) (eigen : FreeVarId) (hSentence : ∀ formula, T formula → Formula.Sentence formula) :
    Derives T [] (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 body)) :=
  Derives.forall_intro (theory_fresh_of_sentence hSentence sort eigen) (empty_context_fresh sort eigen)
    hBody
theorem forall_intro_empty
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {body : Formula σ} (hBody : Derives (Theory.empty : Theory σ) [] body) (sort : σ.SortSymbol) (eigen : FreeVarId) :
    Derives (Theory.empty : Theory σ) [] (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 body)) := by
  apply Derives.forall_intro
  · intro formula hFormula
    cases hFormula
  · exact empty_context_fresh sort eigen
  · exact hBody
private def push_name_unique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name
initialize derive_close_sentence_extension :
    PersistentEnvExtension Name Name (Array Name) ←
  registerPersistentEnvExtension {
    name := `YesMetaZFC.Automation.DerivesClosure.derive_close_sentence_extension
    mkInitial := pure #[]
    addImportedFn := fun imported =>
      pure <| imported.foldl (fun names entries =>
          entries.foldl push_name_unique names) #[]
    addEntryFn := push_name_unique
    exportEntriesFn := id
    statsFn := fun names =>
      s!"derive_close sentence providers: {names.size}"
  }
/--
把形如 `∀ {formula}, T formula → Formula.Sentence formula` 的定理注册给
`derive_close`。注册项只提供理论新鲜性证明，不参与搜索开放公式。
-/
initialize
  registerBuiltinAttribute {
    name := `derive_close_sentence
    descr := "register a closed-theory proof for derive_close"
    applicationTime := .afterCompilation
    add := fun declaration stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal `derive_close_sentence kind
      let environment ← getEnv
      unless (environment.getModuleIdxFor? declaration).isNone do
        throwAttrDeclInImportedModule
          `derive_close_sentence declaration
      modifyEnv fun environment =>
        derive_close_sentence_extension.addEntry
          environment declaration
  }
private structure DerivesView where
  signature : Expr
  decidableEq : Expr
  theory : Expr
  context : Expr
  formula : Expr
private def derives_view_from_arguments (arguments : Array Expr) :
    MetaM (Option DerivesView) := do
  if arguments.size < 5 then
    return none
  return some {
    signature := arguments[0]!
    decidableEq := arguments[1]!
    theory := arguments[2]!
    context := arguments[3]!
    formula := arguments[4]!
  }
private def derives_view? (target : Expr) : MetaM (Option DerivesView) := do
  let target ← instantiateMVars target
  if target.isAppOfArity ``Logic.FirstOrder.Derives 5 then
    return ← derives_view_from_arguments target.getAppArgs
  let target ← whnf target
  unless target.isAppOfArity ``Nonempty 1 do
    return none
  let payloadType ← whnf target.getAppArgs[0]!
  unless payloadType.isAppOfArity ``Logic.FirstOrder.ND_Checked 5 do
    return none
  derives_view_from_arguments payloadType.getAppArgs
private def same_expression (left right : Expr) : MetaM Bool := do
  if Expr.equal left right then
    return true
  withoutModifyingState do
    withTransparency .reducible <| isDefEq left right
private def signature_universe_levels (signature : Expr) : MetaM (List Level) := do
  let signatureType ← whnf (← inferType signature)
  match signatureType.getAppFn with
  | .const _ levels =>
      return levels
  | _ =>
      throwError
        "derive_close found an unexpected signature type{indentExpr signatureType}"
private def empty_theory (signature : Expr) (levels : List Level) : Expr :=
  mkApp (mkConst ``Logic.FirstOrder.Theory.empty levels)
    signature
private def empty_context (signature : Expr) (levels : List Level) : MetaM Expr :=
  mkListLit (mkApp (mkConst ``Logic.FirstOrder.Formula levels)
      signature)
    []
private def collect_outer_sorts (formula : Expr) (count : Nat) : MetaM (Array Expr) := do
  let mut current := formula
  let mut sorts := #[]
  for _ in [:count] do
    current ← whnf current
    unless current.isAppOfArity ``Logic.FirstOrder.Formula.forallE 3 do
      throwError
        "derive_close expected {count} outer universal binders, \
        but found only {sorts.size}{indentExpr current}"
    let arguments := current.getAppArgs
    sorts := sorts.push arguments[1]!
    current := arguments[2]!
  return sorts
private def close_empty (sorts ids : Array Expr) (proof : Expr) : MetaM Expr := do
  let mut result := proof
  for offset in [:sorts.size] do
    let index := sorts.size - offset - 1
    result ←
      mkAppM ``forall_intro_empty
        #[result, sorts[index]!, ids[index]!]
  return result
private def close_with_sentence (provider : Name) (sorts ids : Array Expr) (proof : Expr) : MetaM Expr := do
  let sentenceProof ← mkConstWithFreshMVarLevels provider
  let mut result := proof
  for offset in [:sorts.size] do
    let index := sorts.size - offset - 1
    result ←
      mkAppM ``forall_intro_of_sentence
        #[result, sorts[index]!, ids[index]!, sentenceProof]
  return result
private def finalize_proof (goal : MVarId) (target proof : Expr) : MetaM Bool := do
  let proof ← instantiateMVars proof
  let proofType ← inferType proof
  unless ← withTransparency .all <| isDefEq proofType target do
    return false
  let proof ← instantiateMVars proof
  unless (← getMVarsNoDelayed proof).isEmpty do
    return false
  goal.assign proof
  return true
private unsafe def run_derive_close (idSyntaxes : Array (TSyntax `term)) (proofSyntax : TSyntax `term) : TacticM Unit := do
  let savedState ← saveState
  let goal ← getMainGoal
  let target ← withMainContext <| instantiateMVars (← getMainTarget)
  try
    let some targetView ← withMainContext <| derives_view? target
      | throwError
          "derive_close expects a Derives goal{indentExpr target}"
    let ids ← withMainContext do
      idSyntaxes.mapM fun idSyntax => do
        let id ← instantiateMVars (← elabTerm idSyntax (some (mkConst ``Nat)))
        unless (← getMVarsNoDelayed id).isEmpty do
          throwErrorAt idSyntax
            "derive_close variable id contains unresolved metavariables"
        return id
    let sorts ← withMainContext <|
      collect_outer_sorts targetView.formula ids.size
    let openProof ← withMainContext do
      instantiateMVars (← elabTermForApply proofSyntax (mayPostpone := false))
    let openType ← withMainContext <| inferType openProof
    let some openView ← withMainContext <| derives_view? openType
      | throwErrorAt proofSyntax
          "derive_close source must prove a Derives judgment, but has type\
          {indentExpr openType}"
    let levels ← withMainContext <|
      signature_universe_levels targetView.signature
    let emptyTheory := empty_theory targetView.signature levels
    let emptyContext ← withMainContext <|
      empty_context targetView.signature levels
    let sourceSignatureMatches ← withMainContext <|
      same_expression openView.signature targetView.signature
    let sourceTheoryIsEmpty ← withMainContext <|
      same_expression openView.theory emptyTheory
    let sourceContextIsEmpty ← withMainContext <|
      same_expression openView.context emptyContext
    let sourceIsPure :=
      sourceSignatureMatches &&
        sourceTheoryIsEmpty && sourceContextIsEmpty
    if sourceIsPure then
      let closed ← withMainContext <|
        close_empty sorts ids openProof
      let weakened :=
        mkAppN (mkConst ``Logic.FirstOrder.Derives.of_empty levels)
          #[targetView.signature, targetView.decidableEq,
            targetView.theory, targetView.context,
            targetView.formula, closed]
      if ← withMainContext <| finalize_proof goal target weakened then
        replaceMainGoal []
        return
      throwError
        "derive_close closed the pure theorem, but the result does not match \
        the requested target{indentExpr target}"
    let sourceTheoryMatches ← withMainContext <|
      same_expression openView.theory targetView.theory
    let sourceContextMatches ← withMainContext <|
      same_expression openView.context targetView.context
    let targetContextIsEmpty ← withMainContext <|
      same_expression targetView.context emptyContext
    let sourceMatchesTarget :=
      sourceSignatureMatches && sourceTheoryMatches &&
        sourceContextMatches && targetContextIsEmpty
    unless sourceMatchesTarget do
      throwErrorAt proofSyntax
        "derive_close requires either a pure theorem or the target theory \
        with an empty local context"
    let providers :=
      derive_close_sentence_extension.getState (← getEnv)
    for provider in providers do
      let providerState ← saveState
      try
        let closed ← withMainContext <|
          close_with_sentence provider sorts ids openProof
        if ← withMainContext <| finalize_proof goal target closed then
          replaceMainGoal []
          return
        providerState.restore
      catch _ =>
        providerState.restore
    throwError
      "derive_close found no registered sentence proof for the target theory; \
      mark a theorem with @[derive_close_sentence]"
  catch error =>
    savedState.restore
    throw error
/--
按目标最外层全称量词的 sort，使用给定 free variable 编号关闭一个开放推导。
示例：`derive_close (source, candidate) using hOpen`。
-/
syntax (name := deriveClose)
  "derive_close" " (" term,+ ")" " using " term : tactic
@[tactic deriveClose] unsafe def eval_derive_close : Tactic :=
  fun stx => do
    match stx with
    | `(tactic| derive_close ($ids:term,*) using $proof:term) =>
        run_derive_close ids.getElems proof
    | _ =>
        throwUnsupportedSyntax
end DerivesClosure
end Automation
end YesMetaZFC
