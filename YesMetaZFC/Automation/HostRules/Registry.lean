import Lean
/-!
# HR 推理规则注册表

注册项只保存 theorem 声明及其 proof-free 触发索引。实际调用时由 `Frontend`
按目标需求实例化对象参数，并保留完整命题前提；规则本身作为普通 source premise
送入 checked AVATAR 主路，注册层不执行 `exact` 或 `apply`。
-/
namespace YesMetaZFC
namespace Automation
namespace HostRules
namespace Registry

open Lean Meta

structure Entry where
  declaration : Name
  priority : Nat
  conclusionHead : Name
  premiseHeads : Array Name := #[]
  triggerHeads : Array Name := #[]
deriving Repr

private def pushNameUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

private def surfaceConstHead? (expression : Expr) : Option Name :=
  expression.consumeMData.getAppFn.constName?

/-- 提取一条 proposition 在全部 binder 后的稳定结论头。 -/
def propositionConclusionHead? (proposition : Expr) :
    MetaM (Option Name) := do
  let savedState ← saveState
  try
    let (_, _, conclusion) ← forallMetaTelescope proposition
    let conclusion ← instantiateMVars conclusion
    let result :=
      surfaceConstHead? conclusion
    let result ←
      match result with
      | some declaration => pure (some declaration)
      | none => surfaceConstHead? <$> whnf conclusion
    savedState.restore
    return result
  catch error =>
    savedState.restore
    throw error

private structure Shape where
  conclusionHead? : Option Name := none
  premiseHeads : Array Name := #[]
  hasInstanceBinder : Bool := false
  hasImplicitPropositionPremise : Bool := false

private def analyzeShape (proposition : Expr) : MetaM Shape := do
  let savedState ← saveState
  try
    let (arguments, binderInfos, conclusion) ←
      forallMetaTelescope proposition
    let mut premiseHeads := #[]
    let mut hasInstanceBinder := false
    let mut hasImplicitPropositionPremise := false
    for index in [0 : arguments.size] do
      let binderInfo := binderInfos[index]!
      hasInstanceBinder := hasInstanceBinder || binderInfo.isInstImplicit
      let domain ← instantiateMVars (← inferType arguments[index]!)
      if ← isProp domain then
        unless binderInfo.isExplicit do
          hasImplicitPropositionPremise := true
        if let some head ← propositionConclusionHead? domain then
          premiseHeads := pushNameUnique premiseHeads head
    let conclusion ← instantiateMVars conclusion
    let conclusionHead? ←
      match surfaceConstHead? conclusion with
      | some declaration => pure (some declaration)
      | none => surfaceConstHead? <$> whnf conclusion
    savedState.restore
    return {
      conclusionHead?
      premiseHeads
      hasInstanceBinder
      hasImplicitPropositionPremise
    }
  catch error =>
    savedState.restore
    throw error

private def entryOfDeclaration (declaration : Name)
    (priority : Nat) : MetaM Entry := do
  let some declarationInfo := (← getEnv).find? declaration
    | throwError "unknown declaration `{declaration}`"
  unless declarationInfo.isTheorem do
    throwError
      "prove_auto HR rule `{declaration}` must be a theorem declaration"
  let proof ← mkConstWithFreshMVarLevels declaration
  let proposition ← instantiateMVars (← inferType proof)
  unless ← isProp proposition do
    throwError
      "prove_auto HR rule `{declaration}` must have a proposition type"
  let shape ← analyzeShape proposition
  if shape.hasInstanceBinder then
    throwError
      "prove_auto HR rule `{declaration}` has a typeclass binder; \
      register a theorem with explicit implemented parameters"
  if shape.hasImplicitPropositionPremise then
    throwError
      "prove_auto HR rule `{declaration}` has an implicit proposition premise"
  let some conclusionHead := shape.conclusionHead?
    | throwError
        "prove_auto HR rule `{declaration}` needs a stable conclusion head"
  let triggerHeads :=
    #[conclusionHead]
  return {
    declaration
    priority
    conclusionHead
    premiseHeads := shape.premiseHeads
    triggerHeads
  }

private abbrev Index := NameMap (Array Entry)

private def insertBucket (index : Index) (head : Name)
    (entry : Entry) : Index :=
  let bucket := index.find? head |>.getD #[]
  if bucket.any fun existing =>
      existing.declaration == entry.declaration then
    index
  else
    index.insert head (bucket.push entry)

private def insertEntry (index : Index) (entry : Entry) : Index :=
  entry.triggerHeads.foldl
    (fun index head => insertBucket index head entry) index

private def flattenEntries (index : Index) : Array Entry :=
  index.foldl (fun entries _ bucket =>
      bucket.foldl (fun entries entry =>
          if entries.any fun existing =>
              existing.declaration == entry.declaration then
            entries
          else
            entries.push entry)
        entries)
    #[]

initialize extension :
    PersistentEnvExtension Entry Entry Index ←
  registerPersistentEnvExtension {
    name := `YesMetaZFC.Automation.HostRules.Registry.extension
    mkInitial := pure {}
    addImportedFn := fun imported =>
      pure <| imported.foldl (fun index entries =>
          entries.foldl insertEntry index) {}
    addEntryFn := insertEntry
    exportEntriesFn := flattenEntries
    statsFn := fun index =>
      s!"prove_auto HR-rule trigger buckets: {index.size}"
  }

private def ordered (entries : Array Entry) : Array Entry :=
  (entries.mapIdx fun position entry => (position, entry))
    |>.qsort (fun left right =>
      if left.2.priority == right.2.priority then
        left.1 < right.1
      else
        left.2.priority > right.2.priority)
    |>.map (·.2)

/-- 按需求 head 的持久索引读取去重后的 HR rules。 -/
def rulesForHeads (heads : Array Name) : CoreM (Array Entry) := do
  let index := extension.getState (← getEnv)
  let mut entries := #[]
  for head in heads do
    for entry in index.find? head |>.getD #[] do
      unless entries.any fun existing =>
          existing.declaration == entry.declaration do
        entries := entries.push entry
  return ordered entries

syntax (name := registerProveAutoHrRule)
  "register_prove_auto_hr_rule " ident : command
syntax (name := registerProveAutoHrRulePriority)
  "register_prove_auto_hr_rule " ident " PRIORITY " num : command

private def registerCommand (identifier : Ident) (priority : Nat) :
    Lean.Elab.Command.CommandElabM Unit := do
  let declaration ← resolveGlobalConstNoOverload identifier
  let entry ← Lean.Elab.Command.liftTermElabM <|
    entryOfDeclaration declaration priority
  let duplicate :=
    flattenEntries (extension.getState (← getEnv))
      |>.any fun existing =>
        existing.declaration == declaration
  if duplicate then
    throwErrorAt identifier
      "prove_auto HR rule `{declaration}` is already registered"
  modifyEnv fun env =>
    extension.addEntry env entry

elab_rules : command
  | `(register_prove_auto_hr_rule $rule:ident) =>
      registerCommand rule 100
  | `(register_prove_auto_hr_rule $rule:ident PRIORITY $priority:num) =>
      registerCommand rule priority.getNat

end Registry
end HostRules
end Automation
end YesMetaZFC
