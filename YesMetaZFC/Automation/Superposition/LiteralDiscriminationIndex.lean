import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.Data.OpenAddress
import YesMetaZFC.Automation.Data.StableIdLiveness
import YesMetaZFC.Automation.Data.Util
/-!
# 互补文字判别索引

索引采用扁平 arena 和 1-based 链接：

* partition 哈希表按 polarity/predicate 定位；
* bucket 哈希表按完整 root discrimination key 定位；
* occurrence 只追加到全局 entry arena，bucket 保存 FIFO 首尾链接。

热插入不再重建 partition/bucket 数组，也不在 bucket 内复制历史 occurrence。
-/
namespace YesMetaZFC
namespace Automation
namespace Superposition
inductive TermIndexKey where
  | varKey
  | bvarKey (sort : CoreSyntax.CoreSort) (index : Nat)
  | applyKey
  | lamKey (domain codomain : CoreSyntax.CoreSort)
  | symbol (kind : CoreSyntax.Search.SymbolKind) (id arity : Nat)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
namespace TermIndexKey
def unifiable (left right : TermIndexKey) : Bool :=
  match left, right with
  | varKey, _ => true
  | _, varKey => true
  | bvarKey sort index, bvarKey sort' index' => sort == sort' && index == index'
  | applyKey, applyKey => true
  | lamKey domain codomain, lamKey domain' codomain' =>
      domain == domain' && codomain == codomain'
  | symbol kind id arity, symbol kind' id' arity' =>
      kind == kind' && id == id' && arity == arity'
  | _, _ => false
def canMatch (pattern target : TermIndexKey) : Bool :=
  match pattern, target with
  | varKey, _ => true
  | bvarKey sort index, bvarKey sort' index' => sort == sort' && index == index'
  | applyKey, applyKey => true
  | lamKey domain codomain, lamKey domain' codomain' =>
      domain == domain' && codomain == codomain'
  | symbol kind id arity, symbol kind' id' arity' =>
      kind == kind' && id == id' && arity == arity'
  | _, _ => false
end TermIndexKey
def termRootKey : CoreSyntax.Search.Term → TermIndexKey
  | CoreSyntax.Search.Term.var _ => .varKey
  | CoreSyntax.Search.Term.bvar sort index => .bvarKey sort index
  | CoreSyntax.Search.Term.fvar .. => .varKey
  | CoreSyntax.Search.Term.app symbol _ =>
      .symbol symbol.kind symbol.id symbol.arity
  | CoreSyntax.Search.Term.apply .. => .applyKey
  | CoreSyntax.Search.Term.lam domain codomain _ => .lamKey domain codomain
structure LiteralIndexKey where
  positive : Bool
  predicate : CoreSyntax.Search.PredicateKind
  left : TermIndexKey
  right : TermIndexKey
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
namespace LiteralIndexKey
def complementary (query candidate : LiteralIndexKey) : Bool :=
  query.positive != candidate.positive &&
    query.predicate == candidate.predicate &&
      ((TermIndexKey.unifiable query.left candidate.left &&
          TermIndexKey.unifiable query.right candidate.right) ||
        (query.predicate == CoreSyntax.Search.PredicateKind.equal &&
          TermIndexKey.unifiable query.left candidate.right &&
          TermIndexKey.unifiable query.right candidate.left))
end LiteralIndexKey
structure LiteralDiscriminationKey where
  positive : Bool
  predicate : CoreSyntax.Search.PredicateKind
  left : TermIndexKey
  right : TermIndexKey
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
namespace LiteralDiscriminationKey
def ofLiteral (literal : CoreSyntax.Search.Literal) : LiteralDiscriminationKey := {
  positive := literal.positive
  predicate := literal.predicate
  left := termRootKey literal.left
  right := termRootKey literal.right
}
def complementaryToLiteral (query : CoreSyntax.Search.Literal)
    (candidate : LiteralDiscriminationKey) : Bool :=
  LiteralIndexKey.complementary {
    positive := query.positive
    predicate := query.predicate
    left := termRootKey query.left
    right := termRootKey query.right
  } {
    positive := candidate.positive
    predicate := candidate.predicate
    left := candidate.left
    right := candidate.right
  }
end LiteralDiscriminationKey
structure LiteralOccurrence where
  clauseId : Nat
  literalIndex : Nat
  literal : CoreSyntax.Search.Literal
  deriving Repr, Lean.ToExpr
structure LiteralOccurrenceLink where
  occurrence : LiteralOccurrence
  next : Nat := 0
  deriving Repr, Lean.ToExpr
structure LiteralBucket where
  key : LiteralDiscriminationKey
  firstEntry : Nat := 0
  lastEntry : Nat := 0
  partitionNext : Nat := 0
  hashNext : Nat := 0
  deriving Repr, Lean.ToExpr
structure LiteralPartition where
  positive : Bool
  predicate : CoreSyntax.Search.PredicateKind
  firstBucket : Nat := 0
  lastBucket : Nat := 0
  hashNext : Nat := 0
  deriving Repr, Lean.ToExpr
structure LiteralDiscriminationIndex where
  partitions : Array LiteralPartition := #[]
  partitionHashSlots : Array Nat := #[]
  buckets : Array LiteralBucket := #[]
  bucketHashSlots : Array Nat := #[]
  entries : Array LiteralOccurrenceLink := #[]
  deriving Repr, Lean.ToExpr
namespace LiteralDiscriminationIndex
def empty : LiteralDiscriminationIndex := {}
@[inline]
private def partitionHash (positive : Bool)
    (predicate : CoreSyntax.Search.PredicateKind) : UInt64 :=
  mixHash (Hashable.hash positive) (Hashable.hash predicate)
@[inline]
private def partitionSlot (width : Nat) (positive : Bool)
    (predicate : CoreSyntax.Search.PredicateKind) : Nat :=
  if width == 0 then 0 else (partitionHash positive predicate).toNat % width
@[inline]
private def bucketSlot (width : Nat) (key : LiteralDiscriminationKey) : Nat :=
  if width == 0 then 0 else (Hashable.hash key).toNat % width
private def rehashPartitions (index : LiteralDiscriminationIndex)
    (requestedWidth : Nat) : LiteralDiscriminationIndex := Id.run do
  let width := Data.hashTableWidth requestedWidth
  let mut slots := Data.filledArray width 0
  let mut partitions := index.partitions
  for h : i in [:index.partitions.size] do
    let partition := index.partitions[i]
    let slot := partitionSlot width partition.positive partition.predicate
    partitions := partitions.set! i {
      partition with hashNext := slots[slot]!
    }
    slots := slots.set! slot (i + 1)
  return { index with partitions := partitions, partitionHashSlots := slots }
private def rehashBuckets (index : LiteralDiscriminationIndex)
    (requestedWidth : Nat) : LiteralDiscriminationIndex := Id.run do
  let width := Data.hashTableWidth requestedWidth
  let mut slots := Data.filledArray width 0
  let mut buckets := index.buckets
  for h : i in [:index.buckets.size] do
    let bucket := index.buckets[i]
    let slot := bucketSlot width bucket.key
    buckets := buckets.set! i { bucket with hashNext := slots[slot]! }
    slots := slots.set! slot (i + 1)
  return { index with buckets := buckets, bucketHashSlots := slots }
@[inline]
private def ensurePartitionCapacity (index : LiteralDiscriminationIndex) :
    LiteralDiscriminationIndex :=
  if index.partitionHashSlots.isEmpty then
    index.rehashPartitions 16
  else if (index.partitions.size + 1) * 4 >=
      index.partitionHashSlots.size * 3 then
    index.rehashPartitions (index.partitionHashSlots.size * 2)
  else
    index
@[inline]
private def ensureBucketCapacity (index : LiteralDiscriminationIndex) :
    LiteralDiscriminationIndex :=
  if index.bucketHashSlots.isEmpty then
    index.rehashBuckets 16
  else if (index.buckets.size + 1) * 4 >= index.bucketHashSlots.size * 3 then
    index.rehashBuckets (index.bucketHashSlots.size * 2)
  else
    index
private def findPartitionId? (index : LiteralDiscriminationIndex)
    (positive : Bool) (predicate : CoreSyntax.Search.PredicateKind) :
    Option Nat := Id.run do
  if index.partitionHashSlots.isEmpty then
    return none
  let slot := partitionSlot index.partitionHashSlots.size positive predicate
  let mut link := index.partitionHashSlots[slot]!
  while link != 0 do
    match index.partitions[link - 1]? with
    | some partition =>
        if partition.positive == positive && partition.predicate == predicate then
          return some link
        link := partition.hashNext
    | none => return none
  return none
private def findBucketId? (index : LiteralDiscriminationIndex)
    (key : LiteralDiscriminationKey) : Option Nat := Id.run do
  if index.bucketHashSlots.isEmpty then
    return none
  let slot := bucketSlot index.bucketHashSlots.size key
  let mut link := index.bucketHashSlots[slot]!
  while link != 0 do
    match index.buckets[link - 1]? with
    | some bucket =>
        if bucket.key == key then
          return some link
        link := bucket.hashNext
    | none => return none
  return none
private def ensurePartition (index : LiteralDiscriminationIndex)
    (positive : Bool) (predicate : CoreSyntax.Search.PredicateKind) :
    Nat × LiteralDiscriminationIndex :=
  match index.findPartitionId? positive predicate with
  | some id => (id, index)
  | none =>
      let index := index.ensurePartitionCapacity
      let slot :=
        partitionSlot index.partitionHashSlots.size positive predicate
      let id := index.partitions.size + 1
      let partition : LiteralPartition := {
        positive := positive
        predicate := predicate
        hashNext := index.partitionHashSlots[slot]!
      }
      (id, {
        index with
        partitions := index.partitions.push partition
        partitionHashSlots := index.partitionHashSlots.set! slot id
      })
private def pushBucket (index : LiteralDiscriminationIndex)
    (partitionId : Nat) (key : LiteralDiscriminationKey) :
    Nat × LiteralDiscriminationIndex :=
  let index := index.ensureBucketCapacity
  match index.partitions[partitionId - 1]? with
  | none => (0, index)
  | some partition =>
      let slot := bucketSlot index.bucketHashSlots.size key
      let id := index.buckets.size + 1
      let bucket : LiteralBucket := {
        key := key
        hashNext := index.bucketHashSlots[slot]!
      }
      let buckets := index.buckets.push bucket
      let buckets :=
        if partition.lastBucket == 0 then
          buckets
        else
          match buckets[partition.lastBucket - 1]? with
          | some previous =>
              buckets.set! (partition.lastBucket - 1) {
                previous with partitionNext := id
              }
          | none => buckets
      let partition := {
        partition with
        firstBucket :=
          if partition.firstBucket == 0 then id else partition.firstBucket
        lastBucket := id
      }
      (id, {
        index with
        partitions := index.partitions.set! (partitionId - 1) partition
        buckets := buckets
        bucketHashSlots := index.bucketHashSlots.set! slot id
      })
private def pushOccurrence (index : LiteralDiscriminationIndex)
    (bucketId : Nat) (occurrence : LiteralOccurrence) :
    LiteralDiscriminationIndex :=
  match index.buckets[bucketId - 1]? with
  | none => index
  | some bucket =>
      let id := index.entries.size + 1
      let entries := index.entries.push { occurrence := occurrence }
      let entries :=
        if bucket.lastEntry == 0 then
          entries
        else
          match entries[bucket.lastEntry - 1]? with
          | some previous =>
              entries.set! (bucket.lastEntry - 1) { previous with next := id }
          | none => entries
      let bucket := {
        bucket with
        firstEntry := if bucket.firstEntry == 0 then id else bucket.firstEntry
        lastEntry := id
      }
      {
        index with
        buckets := index.buckets.set! (bucketId - 1) bucket
        entries := entries
      }
def insert (index : LiteralDiscriminationIndex)
    (entry : LiteralOccurrence) : LiteralDiscriminationIndex :=
  let key := LiteralDiscriminationKey.ofLiteral entry.literal
  let (partitionId, index) :=
    index.ensurePartition key.positive key.predicate
  match index.findBucketId? key with
  | some bucketId => index.pushOccurrence bucketId entry
  | none =>
      let (bucketId, index) := index.pushBucket partitionId key
      index.pushOccurrence bucketId entry
def compact (index : LiteralDiscriminationIndex)
    (liveness : Data.StableIdLiveness) : LiteralDiscriminationIndex :=
  index.entries.foldl (fun compacted link =>
      if liveness.isLive! link.occurrence.clauseId then
        compacted.insert link.occurrence
      else
        compacted)
    LiteralDiscriminationIndex.empty
def foldComplementaryUntil {β : Type} (index : LiteralDiscriminationIndex)
    (literal : CoreSyntax.Search.Literal) (initial : β)
    (visit : β → LiteralOccurrence → Data.FoldStep β) : β := Id.run do
  let some partitionId :=
      index.findPartitionId? (!literal.positive) literal.predicate
    | return initial
  let some partition := index.partitions[partitionId - 1]? | return initial
  let mut state := initial
  let mut bucketLink := partition.firstBucket
  while bucketLink != 0 do
    match index.buckets[bucketLink - 1]? with
    | some bucket =>
        if LiteralDiscriminationKey.complementaryToLiteral literal bucket.key then
          let mut entryLink := bucket.firstEntry
          while entryLink != 0 do
            match index.entries[entryLink - 1]? with
            | some entry =>
                match visit state entry.occurrence with
                | .next next => state := next
                | .done result => return result
                entryLink := entry.next
            | none => entryLink := 0
        bucketLink := bucket.partitionNext
    | none => bucketLink := 0
  return state
@[inline]
def isEmpty (index : LiteralDiscriminationIndex) : Bool :=
  index.entries.isEmpty
@[inline]
def size (index : LiteralDiscriminationIndex) : Nat :=
  index.entries.size
end LiteralDiscriminationIndex
end Superposition
end Automation
end YesMetaZFC
