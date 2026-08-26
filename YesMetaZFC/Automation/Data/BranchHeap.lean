import YesMetaZFC.Automation.Data.Util
/-!
# CDCL 分支优先队列
该模块维护 SAT/CDCL 搜索使用的可变变量堆。优先级首先比较 activity，再以单调 rank
打破平局；回跳释放的变量获得新的 rank，因此同 activity 下会先探索尚未决策的变量，
避免线性游标反复回卷。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
structure BranchStats where
  decisions : Nat := 0
  redecisions : Nat := 0
  conflicts : Nat := 0
  deriving Repr, Inhabited, BEq, DecidableEq
structure BranchHeap (σ : Type) where
  heap : MutArray σ Nat
  positions : MutArray σ Nat
  activities : MutArray σ Nat
  phases : MutByteArray σ
  ranks : MutArray σ Nat
  everDecided : MutByteArray σ
  initialized : ST.Ref σ Bool
  nextRank : ST.Ref σ Nat
  decisions : ST.Ref σ Nat
  redecisions : ST.Ref σ Nat
  conflicts : ST.Ref σ Nat
  releaseBuffer : MutArray σ Nat
  numVars : Nat
namespace BranchHeap
private def phaseCode (value : Bool) : UInt8 :=
  if value then 1 else 0
private def decodePhase (value : UInt8) : Bool :=
  value != 0
private def higherPriority {σ} (state : BranchHeap σ) (left right : Nat) : ST σ Bool := do
  let leftActivity ← state.activities.getD left 0
  let rightActivity ← state.activities.getD right 0
  if leftActivity != rightActivity then
    return leftActivity > rightActivity
  let leftRank ← state.ranks.getD left left
  let rightRank ← state.ranks.getD right right
  return leftRank < rightRank
private def swap {σ} (state : BranchHeap σ) (left right : Nat) : ST σ Unit := do
  if left != right then
    let leftVar ← state.heap.get! left
    let rightVar ← state.heap.get! right
    state.heap.set! left rightVar
    state.heap.set! right leftVar
    state.positions.set! leftVar (right + 1)
    state.positions.set! rightVar (left + 1)
private partial def siftUp {σ} (state : BranchHeap σ) (index : Nat) : ST σ Unit := do
  if index == 0 then
    return
  let parent := (index - 1) / 2
  let childVar ← state.heap.get! index
  let parentVar ← state.heap.get! parent
  if ← state.higherPriority childVar parentVar then
    state.swap index parent
    state.siftUp parent
private partial def siftDown {σ} (state : BranchHeap σ) (index : Nat) : ST σ Unit := do
  let size ← state.heap.size
  let left := 2 * index + 1
  if left >= size then
    return
  let right := left + 1
  let mut best := left
  if right < size then
    let leftVar ← state.heap.get! left
    let rightVar ← state.heap.get! right
    if ← state.higherPriority rightVar leftVar then
      best := right
  let currentVar ← state.heap.get! index
  let bestVar ← state.heap.get! best
  if ← state.higherPriority bestVar currentVar then
    state.swap index best
    state.siftDown best
/--
用 root hole 单向下移恢复堆序。
每层只把优先级更高的子节点写入父 hole，最后一次放置末元素；与通用 `siftDown`
逐层 swap 相比，heap/position 各减少一次反向写入。
-/
private def fillRootHole {σ} (state : BranchHeap σ) (lastVar size : Nat) :
    ST σ Unit := do
  let mut index := 0
  let mut placed := false
  while !placed do
    let left := 2 * index + 1
    if left >= size then
      state.heap.set! index lastVar
      state.positions.set! lastVar (index + 1)
      placed := true
    else
      let right := left + 1
      let mut best := left
      if right < size then
        let leftVar ← state.heap.get! left
        let rightVar ← state.heap.get! right
        if ← state.higherPriority rightVar leftVar then
          best := right
      let bestVar ← state.heap.get! best
      if ← state.higherPriority bestVar lastVar then
        state.heap.set! index bestVar
        state.positions.set! bestVar (index + 1)
        index := best
      else
        state.heap.set! index lastVar
        state.positions.set! lastVar (index + 1)
        placed := true
private def insertExisting {σ} (state : BranchHeap σ) (var : Nat) : ST σ Unit := do
  if var >= state.numVars || (← state.positions.getD var 0) != 0 then
    return
  let index ← state.heap.pushGetIndex var
  state.positions.set! var (index + 1)
  state.siftUp index
private def initialHigherPriority (activities : Array Nat) (left right : Nat) : Bool :=
  let leftActivity := activities.getD left 0
  let rightActivity := activities.getD right 0
  leftActivity > rightActivity || (leftActivity == rightActivity && left < right)
private def initialHeap (numVars : Nat) (activities : Array Nat) : Array Nat := Id.run do
  let mut heap := Array.ofFn fun index : Fin numVars => index.val
  let parentCount := numVars / 2
  for offset in [:parentCount] do
    let mut index := parentCount - 1 - offset
    let mut running := true
    while running do
      let left := 2 * index + 1
      if left >= numVars then
        running := false
      else
        let right := left + 1
        let mut best := left
        if right < numVars &&
            initialHigherPriority activities heap[right]! heap[left]! then
          best := right
        if initialHigherPriority activities heap[best]! heap[index]! then
          let current := heap[index]!
          heap := heap.set! index heap[best]!
          heap := heap.set! best current
          index := best
        else
          running := false
  return heap
private def positionsForHeap (numVars : Nat) (heap : Array Nat) : Array Nat := Id.run do
  let mut positions := filledArray numVars 0
  for h : index in [:heap.size] do
    positions := positions.set! heap[index] (index + 1)
  return positions
private def ensureInitialized {σ} (state : BranchHeap σ) : ST σ Unit := do
  if ← state.initialized.get then
    return
  let heapValues := initialHeap state.numVars (← state.activities.freeze)
  state.heap.set heapValues
  state.positions.set (positionsForHeap state.numVars heapValues)
  state.initialized.set true
def create {σ} (numVars : Nat) : ST σ (BranchHeap σ) := do
  let activityValues := filledArray numVars 0
  let heap ← MutArray.mk (σ := σ) (#[] : Array Nat)
  let positions ← MutArray.mk (σ := σ) (filledArray numVars 0)
  let activities ← MutArray.mk (σ := σ) activityValues
  let phases ← MutByteArray.mk (σ := σ) (filledByteArray numVars 0)
  let ranks ← MutArray.mk (σ := σ) (Array.ofFn fun index : Fin numVars => index.val)
  let everDecided ← MutByteArray.mk (σ := σ) (filledByteArray numVars 0)
  let state : BranchHeap σ := {
    heap := heap
    positions := positions
    activities := activities
    phases := phases
    ranks := ranks
    everDecided := everDecided
    initialized := ← ST.mkRef (σ := σ) false
    nextRank := ← ST.mkRef (σ := σ) numVars
    decisions := ← ST.mkRef (σ := σ) 0
    redecisions := ← ST.mkRef (σ := σ) 0
    conflicts := ← ST.mkRef (σ := σ) 0
    releaseBuffer := ← MutArray.mk (σ := σ) (#[] : Array Nat)
    numVars := numVars
  }
  return state
def loadProfile {σ} (state : BranchHeap σ) (activity : Array Nat) (phase : ByteArray) : ST σ Unit := do
  if ← state.initialized.get then
    return
  state.activities.set <| Array.ofFn fun index : Fin state.numVars =>
    activity.getD index 0
  state.phases.set <| Id.run do
    let mut out := filledByteArray state.numVars 0
    for index in [:state.numVars] do
      if index < phase.size then
        out := out.set! index (phase.get! index)
    return out
def remove {σ} (state : BranchHeap σ) (var : Nat) : ST σ Unit := do
  if var >= state.numVars then
    return
  let positionRaw ← state.positions.getD var 0
  if positionRaw == 0 then
    return
  let index := positionRaw - 1
  let some lastVar ← state.heap.pop? | return
  state.positions.set! var 0
  if index < (← state.heap.size) then
    state.heap.set! index lastVar
    state.positions.set! lastVar (index + 1)
    if index > 0 then
      let parent := (index - 1) / 2
      let parentVar ← state.heap.get! parent
      if ← state.higherPriority lastVar parentVar then
        state.siftUp index
      else
        state.siftDown index
    else
      state.siftDown index
@[inline]
def savePhase {σ} (state : BranchHeap σ) (var : Nat) (value : Bool) : ST σ Unit := do
  if var < state.numVars then
    state.phases.set! var (phaseCode value)
def release {σ} (state : BranchHeap σ) (var : Nat) : ST σ Unit := do
  state.ensureInitialized
  if var >= state.numVars || (← state.positions.getD var 0) != 0 then
    return
  let rank ← state.nextRank.get
  state.nextRank.set (rank + 1)
  state.ranks.set! var rank
  state.insertExisting var
def beginReleaseBatch {σ} (state : BranchHeap σ) : ST σ Unit :=
  state.releaseBuffer.truncate 0
def queueRelease {σ} (state : BranchHeap σ) (var : Nat) : ST σ Unit :=
  state.releaseBuffer.push var
def pop? {σ} (state : BranchHeap σ) : ST σ (Option (Nat × Bool)) := do
  state.ensureInitialized
  let size ← state.heap.size
  if size == 0 then
    return none
  let var ← state.heap.get! 0
  let some lastVar ← state.heap.pop? | return none
  state.positions.set! var 0
  let remaining ← state.heap.size
  if remaining != 0 then
    state.fillRootHole lastVar remaining
  return some (var, decodePhase (← state.phases.getD var 0))
def noteDecision {σ} (state : BranchHeap σ) (var : Nat) : ST σ Unit := do
  state.decisions.modify (· + 1)
  if (← state.everDecided.getD var 0) != 0 then
    state.redecisions.modify (· + 1)
  else
    state.everDecided.set! var 1
def bump {σ} (state : BranchHeap σ) (var : Nat) (amount : Nat := 1024) : ST σ Unit := do
  if var >= state.numVars then
    return
  state.activities.modifyD var 0 (· + amount)
  let positionRaw ← state.positions.getD var 0
  if positionRaw != 0 then
    state.siftUp (positionRaw - 1)
private partial def rebuildFrom {σ} (state : BranchHeap σ) : Nat → ST σ Unit
  | 0 => pure ()
  | index + 1 => do
      state.siftDown index
      state.rebuildFrom index
private def appendReleased {σ} (state : BranchHeap σ) (var : Nat) :
    ST σ Bool := do
  if var >= state.numVars || (← state.positions.getD var 0) != 0 then
    return false
  let rank ← state.nextRank.get
  state.nextRank.set (rank + 1)
  state.ranks.set! var rank
  let index ← state.heap.pushGetIndex var
  state.positions.set! var (index + 1)
  return true
def releaseMany {σ} (state : BranchHeap σ) : ST σ Unit := do
  state.ensureInitialized
  let count ← state.releaseBuffer.size
  let mut inserted := false
  for index in [:count] do
    let var ← state.releaseBuffer.getD index 0
    if ← state.appendReleased var then
      inserted := true
  state.releaseBuffer.truncate 0
  if inserted then
    state.rebuildFrom ((← state.heap.size) / 2)
private def decay {σ} (state : BranchHeap σ) : ST σ Unit := do
  for var in [:state.numVars] do
    state.activities.modifyD var 0 (· / 2)
  if ← state.initialized.get then
    state.rebuildFrom ((← state.heap.size) / 2)
def finishConflict {σ} (state : BranchHeap σ) : ST σ Unit := do
  let count ← state.conflicts.get
  let next := count + 1
  state.conflicts.set next
  if next % 256 == 0 then
    state.decay
def stats {σ} (state : BranchHeap σ) : ST σ BranchStats := do
  return {
    decisions := ← state.decisions.get
    redecisions := ← state.redecisions.get
    conflicts := ← state.conflicts.get
  }
end BranchHeap
end Data
end Automation
end YesMetaZFC
