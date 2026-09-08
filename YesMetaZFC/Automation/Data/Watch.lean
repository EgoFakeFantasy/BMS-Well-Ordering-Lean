import YesMetaZFC.Automation.Data.Packed
/-!
# Watched buckets
泛化 two-watched literals 的桶表。具体 SAT/CDCL 后端负责解释 watch position 和传播语义；
这里仅维护 `slot → item` 列表。item 自身的 watch 位置应与其固定头部放在同一处。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
structure WatchTable where
  buckets : Array (Array Nat) := #[]
  deriving Repr, BEq, Inhabited
namespace WatchTable
def empty (slotCount : Nat := 0) : WatchTable :=
  { buckets := filledArray slotCount #[] }
def ensureSlot (table : WatchTable) (slot : Nat) : WatchTable :=
  { table with buckets := ensureArraySize table.buckets (slot + 1) #[] }
def bucket (table : WatchTable) (slot : Nat) : Array Nat :=
  table.buckets.getD slot #[]
def setBucket (table : WatchTable) (slot : Nat) (items : Array Nat) : WatchTable :=
  let table := table.ensureSlot slot
  { table with buckets := table.buckets.set! slot items }
def pushBucket (table : WatchTable) (slot item : Nat) : WatchTable :=
  let table := table.ensureSlot slot
  { table with buckets := table.buckets.set! slot ((table.bucket slot).push item) }
def drainBucket (table : WatchTable) (slot : Nat) : Array Nat × WatchTable := (table.bucket slot, table.setBucket slot #[])
def compactBucket (table : WatchTable) (slot : Nat) (keep : Nat → Bool) : WatchTable :=
  let kept := (table.bucket slot).filter keep
  table.setBucket slot kept
def negLiteralBucket (table : WatchTable) (slot : Nat) : Array Nat :=
  table.bucket (negLiteralSlot slot)
end WatchTable
/-!
## ST builder
热传播循环通过 builder 更新 watch table。冻结的 `WatchTable` 只作为循环边界快照，
不要把 builder 内部数组写入 trace 或历史列表。
-/
structure WatchTable.Builder (σ : Type) where
  buckets : MutArray σ (Array Nat)
namespace WatchTable.Builder
def ofTable {σ : Type} (table : WatchTable) : ST σ (WatchTable.Builder σ) := do
  let buckets ← MutArray.mk (σ := σ) table.buckets
  return { buckets := buckets }
def empty {σ : Type} (slotCount : Nat := 0) : ST σ (WatchTable.Builder σ) :=
  ofTable (WatchTable.empty slotCount)
def freeze {σ : Type} (builder : WatchTable.Builder σ) : ST σ WatchTable := do
  let buckets ← builder.buckets.freeze
  return { buckets := buckets }
def bucket {σ : Type} (builder : WatchTable.Builder σ) (slot : Nat) : ST σ (Array Nat) :=
  builder.buckets.getD slot #[]
def setBucket {σ : Type} (builder : WatchTable.Builder σ) (slot : Nat) (items : Array Nat) : ST σ Unit :=
  builder.buckets.setD slot items #[]
@[inline]
def pushBucket {σ : Type} (builder : WatchTable.Builder σ) (slot item : Nat) : ST σ Unit :=
  builder.buckets.modifyNestedD slot #[] (fun items => items.push item)
def drainBucket {σ : Type} (builder : WatchTable.Builder σ) (slot : Nat) :
    ST σ (Array Nat) :=
  builder.buckets.takeD slot #[]
def compactBucket {σ : Type} (builder : WatchTable.Builder σ) (slot : Nat) (keep : Nat → Bool) : ST σ Unit := do
  let items ← builder.drainBucket slot
  builder.setBucket slot (items.filter keep)
def negLiteralBucket {σ : Type} (builder : WatchTable.Builder σ) (slot : Nat) :
    ST σ (Array Nat) :=
  builder.bucket (negLiteralSlot slot)
end WatchTable.Builder
end Data
end Automation
end YesMetaZFC
