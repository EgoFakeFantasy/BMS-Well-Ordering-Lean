import Lean
import YesMetaZFC.Automation.Data.Util
/-!
# 稳定编号存活位图
追加式 arena 通过紧凑 `ByteArray` 永久记录稳定编号是否已经删除。`tombstones` 只统计
上次物理索引清理后新增的删除项；索引重建后保留删除位，但清零待清理计数。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
deriving instance Repr, Lean.ToExpr for ByteArray
structure StableIdLiveness where
  states : ByteArray := ByteArray.empty
  tombstones : Nat := 0
  deriving Repr, Inhabited, BEq, Lean.ToExpr
namespace StableIdLiveness
@[inline]
def isLive (liveness : StableIdLiveness) (id : Nat) : Bool :=
  match liveness.states[id]? with
  | some state => state != 1
  | none => true
@[inline]
def hasTombstones (liveness : StableIdLiveness) : Bool :=
  liveness.tombstones != 0
@[inline]
def isLive! (liveness : StableIdLiveness) (id : Nat) : Bool :=
  id >= liveness.states.size || liveness.states.get! id != 1
@[inline]
def delete (liveness : StableIdLiveness) (id : Nat) : StableIdLiveness :=
  if liveness.isLive id then
    { states := setByteArrayD liveness.states id 1 0
      tombstones := liveness.tombstones + 1 }
  else
    liveness
def deleteMany (liveness : StableIdLiveness) (ids : Array Nat) : StableIdLiveness :=
  Id.run do
    let mut liveness := liveness
    for id in ids do
      liveness := liveness.delete id
    return liveness
@[inline]
def markCompacted (liveness : StableIdLiveness) : StableIdLiveness :=
  { liveness with tombstones := 0 }
end StableIdLiveness
end Data
end Automation
end YesMetaZFC
