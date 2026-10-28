import BMSConstructibleBridge.SecondOrderHereditaryBMSWellOrder
import BMSConstructibleBridge.FinalAssembly
import Lean.Util.CollectAxioms

/-!
# 桥接核心闭包的集中机器公理守卫

导入原 ZFC 终局与原 Z₂ 固定高度终局，逐个检查两者传递导入的全部
`BMSConstructibleBridge` 模块声明，而非只检查若干出口；任一声明依赖
`propext`、`Classical.choice`、`Quot.sound` 以外的公理（含 `sorryAx`）时本模块构建失败。
它取代各中间模块末尾只打印、不会失败的 `#print axioms`；两个终局的精确
`#guard_msgs` 守卫仍保留在 `AxiomAudit.lean` 与 `SecondOrderHereditaryBMSAxiomAudit.lean`。
无额外 Lean 公理不等于对象理论强度已经校准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCoreAxiomAudit

open Lean Elab Command

/-- 检查已加载桥接模块中的声明；`only` 非空时只检查其中列出的声明。
返回实际检查的声明数与涉及的模块数，越界依赖立即报错。 -/
def audit (allowed : Array Name) (only : Array Name := #[]) : CommandElabM (Nat × Nat) := do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut modules : NameSet := {}
  for (name, _) in env.constants.toList do
    unless only.isEmpty || only.contains name do continue
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!
      if (`BMSConstructibleBridge).isPrefixOf moduleName then
        let axioms ← liftCoreM (collectAxioms name)
        let unexpected := axioms.filter (!allowed.contains ·)
        unless unexpected.isEmpty do
          throwError "Unexpected axioms in {name}: {unexpected}"
        checked := checked + 1
        modules := modules.insert moduleName
  return (checked, modules.size)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCoreAxiomAudit

/- 有效性自检：去掉 `Classical.choice` 后，已知使用选择的终局声明必须被拒绝。
若守卫失效而放行，这里的预期错误不出现，`#guard_msgs` 使本模块构建失败。 -/
open YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCoreAxiomAudit in
/--
error: Unexpected axioms in YesMetaZFC.BMS.ConstructibleBridge.bm4_strictWellOrder_l: [Classical.choice]
-/
#guard_msgs in
run_cmd do
  discard <| audit #[``propext, ``Quot.sound]
    (only := #[``YesMetaZFC.BMS.ConstructibleBridge.bm4_strictWellOrder_l])

open Lean YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCoreAxiomAudit in
run_cmd do
  let (checked, modules) ← audit #[``propext, ``Classical.choice, ``Quot.sound]
  if checked == 0 then
    throwError "No bridge declarations were audited"
  logInfo m!"Audited {checked} declarations in {modules} bridge modules; only propext, Classical.choice, Quot.sound allowed."
