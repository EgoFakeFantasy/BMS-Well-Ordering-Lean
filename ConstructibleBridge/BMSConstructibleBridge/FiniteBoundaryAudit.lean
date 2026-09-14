import BMSConstructibleBridge.FiniteStableBoundary
import BMSConstructibleBridge.EffectiveStabilityComplexity
import Lean.Util.CollectAxioms

/-!
# 有限层边界路线的独立审计

本文件必须单独检查，不能导入包含旧全反射路线的总入口。导入图守卫确保
局部化路线没有重新借用全公式反射；公理守卫覆盖本轮各模块的全部声明。
这只检查宿主层证明依赖，不把条件前提 `pairs_l` 当作已证明的弱理论定理。
-/

open Lean in
run_cmd do
  let E ← getEnv
  for M in #[`BMSConstructibleBridge.ExternalFullReflection,
      `BMSConstructibleBridge.NativeStageReflection,
      `BMSConstructibleBridge.NativeStableBoundary,
      `BMSConstructibleBridge.SeedConstruction,
      `BMSConstructibleBridge.FinalAssembly] do
    if E.header.moduleNames.contains M then
      throwError "有限层路线导入了全层背景模块：{M}"
  let A := #[``propext, ``Classical.choice, ``Quot.sound]
  let S := #[`YesMetaZFC.BMS.LocalDescent,
    `BMSConstructibleBridge.FiniteStageReflection,
    `BMSConstructibleBridge.FiniteStableBoundary,
    `BMSConstructibleBridge.EffectiveStabilityComplexity]
  let mut n : Nat := 0
  for (c, _) in E.constants.toList do
    if let some i := E.getModuleIdxFor? c then
      if S.contains E.header.moduleNames[i.toNat]! then
        let B ← collectAxioms c
        unless (B.filter (!A.contains ·)).isEmpty do
          throwError "{c} 存在非标准公理依赖：{B}"
        n := n + 1
  if n == 0 then
    throwError "没有检查任何有限层路线声明"
  for c in #[``YesMetaZFC.BMS.ConstructibleBridge.FiniteStability.wf_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.FiniteStability.wellOrder_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.FiniteStability.no_descent_l,
      ``YesMetaZFC.BMS.ConstructibleBridge.EffectiveStability.named_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.EffectiveStability.ambient_m,
      ``YesMetaZFC.BMS.ConstructibleBridge.EffectiveStability.close_m] do
    unless E.contains c do
      throwError "缺少有限层终局定理：{c}"
  logInfo m!"有限层路线审计通过：{n} 个声明；无全层反射导入；仅三项标准公理。"

#print axioms YesMetaZFC.BMS.ConstructibleBridge.FiniteStability.wellOrder_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.FiniteStability.no_descent_l
#print axioms YesMetaZFC.BMS.ConstructibleBridge.EffectiveStability.level_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.EffectiveStability.named_m
#print axioms YesMetaZFC.BMS.ConstructibleBridge.EffectiveStability.ambient_m
