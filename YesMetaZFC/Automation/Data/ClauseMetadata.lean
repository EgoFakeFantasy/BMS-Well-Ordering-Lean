import YesMetaZFC.Automation.Data.Util
import YesMetaZFC.Automation.Data.Signature
/-!
# 搜索字句元数据表
搜索热路径只通过稳定字句编号访问权重和存活状态。把这些大型数组统一封装在 Data 层，
可以避免上层反复物化 retained id 数组，也为后续 signature 与增量索引元数据预留统一
所有权边界。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
structure ClauseSubsumptionKey where
  literalCount : Nat := 0
  signature : Signature256 := {}
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace ClauseSubsumptionKey
@[inline]
def maySubsume (pattern target : ClauseSubsumptionKey) : Bool :=
  pattern.literalCount <= target.literalCount &&
    pattern.signature.maySubsume target.signature
end ClauseSubsumptionKey
structure ClauseMetadata where
  weight : Nat := 0
  subsumption : ClauseSubsumptionKey := {}
  deleted : Bool := false
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
/--
搜索生命周期内与稳定字句编号对齐的元数据表。
`subsumptionHeads/subsumptionNext` 是按文字数分桶的单链索引。`emptyClauseIds` 是只追加
的空字句稳定编号 journal。它们都只保存稳定编号，删除通过 `entries.deleted` 留
tombstone，避免在热路径维护嵌套数组及其额外 RC。
-/
structure ClauseMetadataTable where
  entries : Array ClauseMetadata := #[]
  subsumptionHeads : Array (Option Nat) := #[]
  subsumptionNext : Array (Option Nat) := #[]
  emptyClauseIds : Array Nat := #[]
  deriving Repr, Inhabited, BEq, Lean.ToExpr
namespace ClauseMetadataTable
structure RetainedEmptyCursor where
  nextIndex : Nat := 0
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
@[inline]
def size (table : ClauseMetadataTable) : Nat :=
  table.entries.size
@[inline]
def alignedWith (table : ClauseMetadataTable) (size : Nat) : Bool :=
  table.size == size &&
    table.subsumptionNext.size == size &&
      table.emptyClauseIds.all (· < size)
@[inline]
def get? (table : ClauseMetadataTable) (id : Nat) : Option ClauseMetadata :=
  table.entries[id]?
@[inline]
def weight? (table : ClauseMetadataTable) (id : Nat) : Option Nat :=
  table.get? id |>.map (·.weight)
@[inline]
def subsumptionKey? (table : ClauseMetadataTable) (id : Nat) :
    Option ClauseSubsumptionKey :=
  table.get? id |>.map (·.subsumption)
@[inline]
def retained (table : ClauseMetadataTable) (id : Nat) : Bool :=
  match table.get? id with
  | some metadata => !metadata.deleted
  | none => false
def push (table : ClauseMetadataTable) (metadata : ClauseMetadata) : ClauseMetadataTable :=
  Id.run do
    let id := table.entries.size
    let literalCount := metadata.subsumption.literalCount
    let mut heads := table.subsumptionHeads
    for _ in [heads.size:literalCount + 1] do
      heads := heads.push none
    let previous := heads[literalCount]!
    heads := heads.set! literalCount (some id)
    return {
      entries := table.entries.push { metadata with deleted := false }
      subsumptionHeads := heads
      subsumptionNext := table.subsumptionNext.push previous
      emptyClauseIds :=
        if literalCount == 0 then table.emptyClauseIds.push id else table.emptyClauseIds
    }
def ofLiveEntries (entries : Array ClauseMetadata) : ClauseMetadataTable :=
  entries.foldl (fun table metadata => table.push metadata) {}
@[inline]
def delete (table : ClauseMetadataTable) (id : Nat) : ClauseMetadataTable :=
  match table.get? id with
  | some metadata =>
      if metadata.deleted then
        table
      else
        { table with entries := table.entries.set! id { metadata with deleted := true } }
  | none => table
def deleteMany (table : ClauseMetadataTable) (ids : Array Nat) : ClauseMetadataTable :=
  Id.run do
    let mut table := table
    for id in ids do
      table := table.delete id
    return table
def foldRetained {α : Type} (table : ClauseMetadataTable) (initial : α) (visit : α → Nat → α) : α :=
  Id.run do
    let mut state := initial
    for h : id in [:table.entries.size] do
      if !table.entries[id].deleted then
        state := visit state id
    return state
private inductive BucketResult (α : Type) where
  | exhausted (state : α)
  | done (result : α)
@[inline]
private def bucketHead? (table : ClauseMetadataTable) (literalCount : Nat) :
    Option Nat :=
  match table.subsumptionHeads[literalCount]? with
  | some head => head
  | none => none
@[inline]
private def bucketNext? (table : ClauseMetadataTable) (id : Nat) : Option Nat :=
  match table.subsumptionNext[id]? with
  | some next => next
  | none => none
private def foldBucketUntil {α : Type} (table : ClauseMetadataTable) (fuel : Nat) (cursor : Option Nat) (initial : α)
    (visit : α → Nat → ClauseMetadata → FoldStep α) : BucketResult α :=
  match fuel, cursor with
  | 0, _ => .exhausted initial
  | _ + 1, none => .exhausted initial
  | fuel + 1, some id =>
      let next := table.bucketNext? id
      match table.get? id with
      | some metadata =>
          if metadata.deleted then
            foldBucketUntil table fuel next initial visit
          else
            match visit initial id metadata with
            | .next state => foldBucketUntil table fuel next state visit
            | .done result => .done result
      | none => foldBucketUntil table fuel next initial visit
/--
按文字数索引遍历所有可能 duplicate 或 forward-subsumer。
visitor 的布尔参数说明该节点是否还满足 duplicate 的必要条件。subsumption 关闭时只访问
duplicate 候选；开启时仍由最终 `clauseSubsumes` 完整复核。
-/
def foldForwardCandidatesUntil {α : Type} (table : ClauseMetadataTable) (target : ClauseSubsumptionKey) (includeSubsumption : Bool) (initial : α)
    (visit : α → Nat → Bool → FoldStep α) : α :=
  Id.run do
    let mut state := initial
    let upper := Nat.min (target.literalCount + 1) table.subsumptionHeads.size
    for literalCount in [:upper] do
      let result :=
        foldBucketUntil table table.entries.size (table.bucketHead? literalCount) state
          fun state id metadata =>
            let duplicatePossible := metadata.subsumption == target
            let subsumptionPossible :=
              includeSubsumption && metadata.subsumption.maySubsume target
            if duplicatePossible || subsumptionPossible then
              visit state id duplicatePossible
            else
              .next state
      match result with
      | .exhausted next => state := next
      | .done result => return result
    return state
def foldBackwardCandidatesUntil {α : Type} (table : ClauseMetadataTable) (pattern : ClauseSubsumptionKey) (initial : α) (visit : α → Nat → FoldStep α) : α :=
  Id.run do
    let mut state := initial
    for literalCount in [pattern.literalCount:table.subsumptionHeads.size] do
      let result :=
        foldBucketUntil table table.entries.size (table.bucketHead? literalCount) state
          fun state id metadata =>
            if pattern.maySubsume metadata.subsumption then
              visit state id
            else
              .next state
      match result with
      | .exhausted next => state := next
      | .done result => return result
    return state
def foldBackwardCandidates {α : Type} (table : ClauseMetadataTable) (pattern : ClauseSubsumptionKey) (initial : α) (visit : α → Nat → α) : α :=
  table.foldBackwardCandidatesUntil pattern initial fun state id =>
    .next (visit state id)
def foldRetainedUntil {α : Type} (table : ClauseMetadataTable) (initial : α) (visit : α → Nat → FoldStep α) : α :=
  Id.run do
    let mut state := initial
    for h : id in [:table.entries.size] do
      if !table.entries[id].deleted then
        match visit state id with
        | .next next => state := next
        | .done result => return result
    return state
/--
从固定 assignment 的增量游标开始扫描 retained empty 节点。
游标始终推进到已经检查过的 journal 后缀；同一 assignment 内旧节点的 support 真值不会
变化，因此后续只需检查新追加的 empty。删除节点通过 metadata tombstone 跳过。
-/
def foldRetainedEmptyFromUntil {α : Type} (table : ClauseMetadataTable) (cursor : RetainedEmptyCursor) (initial : α)
    (visit : α → Nat → FoldStep α) : RetainedEmptyCursor × α :=
  Id.run do
    let mut state := initial
    let mut nextIndex := Nat.min cursor.nextIndex table.emptyClauseIds.size
    for h : index in [nextIndex:table.emptyClauseIds.size] do
      let id := table.emptyClauseIds[index]
      nextIndex := index + 1
      if table.retained id then
        match visit state id with
        | .next next => state := next
        | .done result => return ({ nextIndex := nextIndex }, result)
    return ({ nextIndex := nextIndex }, state)
def firstRetained? (table : ClauseMetadataTable) (predicate : Nat → Bool) : Option Nat :=
  table.foldRetainedUntil none fun _ id =>
    if predicate id then .done (some id) else .next none
def retainedIds (table : ClauseMetadataTable) : Array Nat :=
  table.foldRetained #[] fun ids id => ids.push id
end ClauseMetadataTable
end Data
end Automation
end YesMetaZFC
