import YesMetaZFC.Automation.Data.StableIdLiveness
/-!
# AVATAR 模型轮增量前沿
该工作区只保存 selector 到稳定 clause id 的追加式依赖 journal，以及当前模型下的
可见位。模型变化时直接消费 CDCL 提供的 selector delta，只枚举发生变化的 selector
所影响的字句；
Active/Passive 的语义迁移由上层饱和状态消费这里产生的 affected id。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
@[inline]
private def byteAt (values : ByteArray) (index : Nat) : UInt8 :=
  values[index]?.getD 0
/--
跨模型轮持久保留的 guard 依赖与可见状态。
`dependencyHeads[var]` 与 `dependencyNext` 使用 1-based journal slot；`0` 表示链尾。
dependency journal 永不删除，永久删除由上层 tombstone 过滤。`registered` 防止稳定 clause
id 重复登记，`affectedStamps` 只负责一次 assignment delta 内的去重。
-/
structure ModelRoundWorkspace where
  dependencyHeads : Array Nat := #[]
  dependencyClauseIds : Array Nat := #[]
  dependencyNext : Array Nat := #[]
  registered : ByteArray := ByteArray.empty
  registeredClauseIds : Array Nat := #[]
  visible : ByteArray := ByteArray.empty
  affectedStamps : Array Nat := #[]
  affectedGeneration : Nat := 1
  initialized : Bool := false
  deriving Repr, Inhabited, BEq, Lean.ToExpr
namespace ModelRoundWorkspace
@[inline]
def contains (workspace : ModelRoundWorkspace) (clauseId : Nat) : Bool :=
  byteAt workspace.registered clauseId != 0
@[inline]
def isVisible (workspace : ModelRoundWorkspace) (clauseId : Nat) : Bool :=
  byteAt workspace.visible clauseId != 0
def registerClause (workspace : ModelRoundWorkspace) (clauseId : Nat) (selectorVars : Array Nat) : ModelRoundWorkspace :=
  if workspace.contains clauseId then
    workspace
  else
    Id.run do
      let mut dependencyHeads := workspace.dependencyHeads
      let mut dependencyClauseIds := workspace.dependencyClauseIds
      let mut dependencyNext := workspace.dependencyNext
      for var in selectorVars do
        dependencyHeads := ensureArraySize dependencyHeads (var + 1) 0
        let previousHead := dependencyHeads.getD var 0
        let rawSlot := dependencyClauseIds.size + 1
        dependencyClauseIds := dependencyClauseIds.push clauseId
        dependencyNext := dependencyNext.push previousHead
        dependencyHeads := dependencyHeads.set! var rawSlot
      return {
        workspace with
        dependencyHeads := dependencyHeads
        dependencyClauseIds := dependencyClauseIds
        dependencyNext := dependencyNext
        registered :=
          setByteArrayD workspace.registered clauseId 1 0
        registeredClauseIds := workspace.registeredClauseIds.push clauseId
        visible := ensureByteArraySize workspace.visible (clauseId + 1) 0
        affectedStamps :=
          ensureArraySize workspace.affectedStamps (clauseId + 1) 0
      }
@[inline]
def setVisible (workspace : ModelRoundWorkspace) (clauseId : Nat) (value : Bool) :
    ModelRoundWorkspace :=
  {
    workspace with
    visible :=
      setByteArrayD workspace.visible clauseId (if value then 1 else 0) 0
  }
def deleteMany (workspace : ModelRoundWorkspace) (clauseIds : Array Nat) :
    ModelRoundWorkspace :=
  Id.run do
    let mut workspace := workspace
    for clauseId in clauseIds do
      workspace := workspace.setVisible clauseId false
    return workspace
/--
进入新 assignment，并返回所有可能改变 support 的稳定 clause id。
首轮需要初始化全部已登记字句；后续只遍历 changed selector 的依赖链。affected journal
按稳定登记顺序的链内顺序产生，上层不依赖该顺序决定 given 调度。
-/
def beginAssignment (workspace : ModelRoundWorkspace) (changedVars : Array Nat) :
    ModelRoundWorkspace × Array Nat := Id.run do
  if !workspace.initialized then
    return ({
      workspace with
      initialized := true
    }, workspace.registeredClauseIds)
  let generation := workspace.affectedGeneration + 1
  let mut affectedStamps := workspace.affectedStamps
  let mut affected := #[]
  for var in changedVars do
    let mut rawSlot := workspace.dependencyHeads.getD var 0
    while rawSlot != 0 do
      let slot := rawSlot - 1
      let clauseId := workspace.dependencyClauseIds.getD slot 0
      affectedStamps := ensureArraySize affectedStamps (clauseId + 1) 0
      if affectedStamps.getD clauseId 0 != generation then
        affectedStamps := affectedStamps.set! clauseId generation
        affected := affected.push clauseId
      rawSlot := workspace.dependencyNext.getD slot 0
  return ({
    workspace with
    affectedStamps := affectedStamps
    affectedGeneration := generation
  }, affected)
end ModelRoundWorkspace
end Data
end Automation
end YesMetaZFC
