import BMSTools
import Lean.Util.CollectAxioms

/-!
# 工具子库依赖审计

逐个检查本入口传递导入的桥接声明，而非只抽查若干出口。
不把无额外 Lean 公理解释为对象理论强度已经校准。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[`BMSConstructibleBridge, `BMSConstructibleBridge.FinalAssembly] do
    if env.header.moduleNames.contains name then
      throwError "Tools must not import the full proof entry: {name}"
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!
      if (`BMSConstructibleBridge).isPrefixOf moduleName ||
          (`BMSTools).isPrefixOf moduleName then
        let axioms ← collectAxioms name
        let unexpected := axioms.filter (!allowed.contains ·)
        unless unexpected.isEmpty do
          throwError "Unexpected axioms in {name}: {unexpected}"
        checked := checked + 1
  if checked == 0 then
    throwError "No tools declarations were audited"
  logInfo m!"Audited {checked} tool dependency declarations; only propext, Classical.choice, Quot.sound allowed."
