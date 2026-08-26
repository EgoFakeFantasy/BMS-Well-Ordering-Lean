import YesMetaZFC.Automation.Resolution
/-!
# 自动化公共 Guard 内核
本模块统一 AVATAR、搜索材料化、超消元与一阶/高阶 DAG 使用的 guard 表示。
guard 集按合取解释，并统一采用命题字句的稳定排序与去重作为规范形式。
-/
namespace YesMetaZFC
namespace Automation
namespace Guards
universe u v
abbrev Lit := PropResolution.Lit
abbrev Set := PropResolution.Clause
def canonical (guards : Set) : Set :=
  PropResolution.canonicalClause guards
def merge (left right : Set) : Set :=
  canonical (left ++ right)
def eq (left right : Set) : Bool :=
  PropResolution.clauseEq (canonical left) (canonical right)
def subset (left right : Set) : Bool :=
  let right := canonical right
  (canonical left).all fun guard => right.contains guard
def learnedClause (guards : Set) : PropResolution.Clause :=
  canonical (guards.map PropResolution.Lit.neg)
theorem mem_of_mem_canonical {guards : Set} {lit : Lit} (hMem : lit ∈ (canonical guards).toList) :
    lit ∈ guards.toList := by
  simpa [canonical, PropResolution.canonicalClause] using
    PropResolution.mem_of_mem_canonicalClauseList hMem
theorem mem_canonical_merge_left {left right : Set} {lit : Lit} (hMem : lit ∈ (canonical left).toList) :
    lit ∈ (canonical (merge left right)).toList := by
  have hRaw : lit ∈ left.toList := mem_of_mem_canonical hMem
  have hAppend : lit ∈ (left ++ right).toList := by simp [hRaw]
  have hMerged : lit ∈ (merge left right).toList := by
    simpa [merge, canonical] using
      PropResolution.mem_canonicalClause_of_mem hAppend
  exact PropResolution.mem_canonicalClause_of_mem hMerged
theorem mem_canonical_merge_right {left right : Set} {lit : Lit} (hMem : lit ∈ (canonical right).toList) :
    lit ∈ (canonical (merge left right)).toList := by
  have hRaw : lit ∈ right.toList := mem_of_mem_canonical hMem
  have hAppend : lit ∈ (left ++ right).toList := by simp [hRaw]
  have hMerged : lit ∈ (merge left right).toList := by
    simpa [merge, canonical] using
      PropResolution.mem_canonicalClause_of_mem hAppend
  exact PropResolution.mem_canonicalClause_of_mem hMerged
def mergeList? {ι : Type v} (lookup : ι → Option Set) : List ι → Option Set
  | [] => some #[]
  | key :: rest => do
      let head ← lookup key
      let tail ← mergeList? lookup rest
      some (merge head tail)
theorem mem_canonical_mergeList_of_mem {ι : Type v}
    {lookup : ι → Option Set} {keys : List ι} {key : ι}
    {keyGuards guards : Set} {lit : Lit} (hMerge : mergeList? lookup keys = some guards) (hKey : key ∈ keys) (hLookup : lookup key = some keyGuards)
    (hLit : lit ∈ (canonical keyGuards).toList) :
    lit ∈ (canonical guards).toList := by
  induction keys generalizing guards with
  | nil => cases hKey
  | cons head rest ih =>
      simp [mergeList?] at hMerge
      cases hHead : lookup head with
      | none => simp [hHead] at hMerge
      | some headGuards =>
          cases hTail : mergeList? lookup rest with
          | none => simp [hHead, hTail] at hMerge
          | some tailGuards =>
              have hGuards : guards = merge headGuards tailGuards := by
                simpa [hHead, hTail] using hMerge.symm
              rcases List.mem_cons.mp hKey with hHeadKey | hRest
              · subst head
                rw [hLookup] at hHead
                cases hHead
                subst guards
                exact mem_canonical_merge_left hLit
              · subst guards
                exact mem_canonical_merge_right (ih hTail hRest)
structure GuardedClause (α : Type u) where
  guards : Set := #[]
  clause : α
  deriving Repr, Inhabited, BEq, Lean.ToExpr
namespace GuardedClause
def plain (clause : α) : GuardedClause α :=
  { clause := clause }
def unguarded (guarded : GuardedClause α) : Bool :=
  guarded.guards.isEmpty
def globallyEmpty (isEmpty : α → Bool) (guarded : GuardedClause α) : Bool :=
  guarded.unguarded && isEmpty guarded.clause
def theoryConflict (isEmpty : α → Bool) (guarded : GuardedClause α) : Bool :=
  !guarded.unguarded && isEmpty guarded.clause
def eq (clauseEq : α → α → Bool) (left right : GuardedClause α) : Bool :=
  Guards.eq left.guards right.guards && clauseEq left.clause right.clause
end GuardedClause
end Guards
end Automation
end YesMetaZFC
