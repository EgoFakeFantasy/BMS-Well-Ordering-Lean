import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ProjectRelationElimination

/-!
# Project 关系消去的代入搬运

本模块证明子集定义展开与 `openAt`、`closeFreeAt`、`substituteFree` 相容，并把
这些合同提升到任意中间公式。这里只处理纯句法操作；Hilbert 证明树搬运位于后续
证明模块。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProjectRelationElimination

open Nonlogical.BasicSetTheory

set_option autoImplicit false

private abbrev targetSort :=
  YesMetaZFC.SetTheory.SetSort.set

private theorem fresh_append
    {α : Type} {value : α} {left right : List α}
    (hLeft : value ∉ left) (hRight : value ∉ right) :
    value ∉ left ++ right := by
  intro hMember
  rcases List.mem_append.mp hMember with
    hMember | hMember
  · exact hLeft hMember
  · exact hRight hMember

/-- 子集展开与打开 bound 变量交换。 -/
theorem subset_openAt
    (depth : Nat) (replacement left right : PureTerm)
    (hReplacementClosed :
      Term.BoundClosed replacement)
    (hReplacementFresh :
      (targetSort, 0) ∉
        Term.freeSupport replacement) :
    Formula.openAt targetSort depth replacement
        (subset left right) =
      subset
        (Term.openAt targetSort depth
          replacement left)
        (Term.openAt targetSort depth
          replacement right) := by
  unfold subset
  change
    Formula.forallE targetSort
        (Formula.openAt targetSort (depth + 1)
          replacement
          (Formula.closeFreeAt targetSort 0 0
            (.imp (mem (free 0) left)
              (mem (free 0) right)))) =
      Formula.forallE targetSort
        (Formula.closeFreeAt targetSort 0 0
          (.imp
            (mem (free 0)
              (Term.openAt targetSort depth
                replacement left))
            (mem (free 0)
              (Term.openAt targetSort depth
                replacement right))))
  congr 1
  rw [formula_open_close 0 0 depth replacement
    _ (Nat.zero_le _) hReplacementClosed
    hReplacementFresh]
  simp [Formula.openAt, mem, free,
    Term.openAt]

/-- 子集展开与关闭另一个自由变量交换。 -/
theorem subset_closeFreeAt
    (id : FreeVarId) (depth : Nat)
    (left right : PureTerm)
    (hId : 0 ≠ id) :
    Formula.closeFreeAt targetSort id depth
        (subset left right) =
      subset
        (Term.closeFreeAt targetSort id depth left)
        (Term.closeFreeAt targetSort id depth right) := by
  unfold subset
  change
    Formula.forallE targetSort
        (Formula.closeFreeAt targetSort id (depth + 1)
          (Formula.closeFreeAt targetSort 0 0
            (.imp (mem (free 0) left)
              (mem (free 0) right)))) =
      Formula.forallE targetSort
        (Formula.closeFreeAt targetSort 0 0
          (.imp
            (mem (free 0)
              (Term.closeFreeAt targetSort id depth left))
            (mem (free 0)
              (Term.closeFreeAt targetSort id depth right))))
  congr 1
  rw [formula_close_close 0 id 0 depth _
    hId (Nat.zero_le _)]
  simp [Formula.closeFreeAt, mem, free,
    Term.closeFreeAt, hId]

/-- 子集展开与另一个自由变量替换交换。 -/
theorem subset_substituteFree
    (id : FreeVarId) (replacement left right : PureTerm)
    (hId : id ≠ 0)
    (hReplacementClosed :
      Term.BoundClosed replacement)
    (hReplacementFresh :
      (targetSort, 0) ∉
        Term.freeSupport replacement) :
    Formula.substituteFree targetSort id replacement
        (subset left right) =
      subset
        (Term.substituteFree targetSort id
          replacement left)
        (Term.substituteFree targetSort id
          replacement right) := by
  unfold subset
  change
    Formula.forallE targetSort
        (Formula.substituteFree targetSort id replacement
          (Formula.closeFreeAt targetSort 0 0
            (.imp (mem (free 0) left)
              (mem (free 0) right)))) =
      Formula.forallE targetSort
        (Formula.closeFreeAt targetSort 0 0
          (.imp
            (mem (free 0)
              (Term.substituteFree targetSort id
                replacement left))
            (mem (free 0)
              (Term.substituteFree targetSort id
                replacement right))))
  congr 1
  rw [← Formula.closeFreeAt_substituteFree_comm
    targetSort id 0 0 replacement _
    hId hReplacementClosed hReplacementFresh]
  simp [Formula.substituteFree, mem, free,
    Term.substituteFree, Ne.symm hId]

/-- 原子翻译与打开 bound 变量交换。 -/
theorem atom_openAt
    (depth : Nat) (replacement : SourceTerm)
    (relation : RelationSymbol)
    (arguments : List SourceTerm)
    (hReplacementClosed :
      Term.BoundClosed replacement) :
    atom relation
        (arguments.map
          (Term.openAt SetSort.set depth replacement)) =
      Formula.openAt targetSort depth
        (term replacement)
        (atom relation arguments) := by
  by_cases hMembership : relation = .membership
  · subst relation
    cases arguments with
    | nil =>
        rfl
    | cons left tail =>
        cases tail with
        | nil =>
            rfl
        | cons right rest =>
            cases rest with
            | nil =>
                simp [atom, mem, Formula.openAt,
                  term_openAt]
            | cons extra rest =>
                rfl
  · by_cases hSubset : relation = .subset
    · subst relation
      cases arguments with
      | nil =>
          simp [atom, hMembership,
            Formula.openAt]
      | cons left tail =>
          cases tail with
          | nil =>
              simp [atom, hMembership,
                Formula.openAt]
          | cons right rest =>
              cases rest with
              | nil =>
                  simpa [atom, hMembership,
                    term_openAt] using
                    (subset_openAt depth
                      (term replacement)
                      (term left) (term right)
                      (term_bound_closed
                        hReplacementClosed)
                      (term_reserved_fresh
                        replacement)).symm
              | cons extra rest =>
                  simp [atom, hMembership,
                    Formula.openAt]
    · simp [atom, hMembership, hSubset,
        Formula.openAt]

/-- 原子翻译与关闭源自由变量交换。 -/
theorem atom_closeFreeAt
    (id : FreeVarId) (depth : Nat)
    (relation : RelationSymbol)
    (arguments : List SourceTerm) :
    atom relation
        (arguments.map
          (Term.closeFreeAt SetSort.set id depth)) =
      Formula.closeFreeAt targetSort (id + 1) depth
        (atom relation arguments) := by
  by_cases hMembership : relation = .membership
  · subst relation
    cases arguments with
    | nil =>
        rfl
    | cons left tail =>
        cases tail with
        | nil =>
            rfl
        | cons right rest =>
            cases rest with
            | nil =>
                simp [atom, mem, Formula.closeFreeAt,
                  term_closeFreeAt]
            | cons extra rest =>
                rfl
  · by_cases hSubset : relation = .subset
    · subst relation
      cases arguments with
      | nil =>
          simp [atom, hMembership,
            Formula.closeFreeAt]
      | cons left tail =>
          cases tail with
          | nil =>
              simp [atom, hMembership,
                Formula.closeFreeAt]
          | cons right rest =>
              cases rest with
              | nil =>
                  simpa [atom, hMembership,
                    term_closeFreeAt] using
                    (subset_closeFreeAt (id + 1)
                      depth (term left) (term right)
                      (Nat.zero_ne_add_one id)).symm
              | cons extra rest =>
                  simp [atom, hMembership,
                    Formula.closeFreeAt]
    · simp [atom, hMembership, hSubset,
        Formula.closeFreeAt]

/-- 原子翻译与源自由变量替换交换。 -/
theorem atom_substituteFree
    (id : FreeVarId) (replacement : SourceTerm)
    (relation : RelationSymbol)
    (arguments : List SourceTerm)
    (hReplacementClosed :
      Term.BoundClosed replacement) :
    atom relation
        (arguments.map
          (Term.substituteFree SetSort.set id
            replacement)) =
      Formula.substituteFree targetSort (id + 1)
        (term replacement)
        (atom relation arguments) := by
  by_cases hMembership : relation = .membership
  · subst relation
    cases arguments with
    | nil =>
        rfl
    | cons left tail =>
        cases tail with
        | nil =>
            rfl
        | cons right rest =>
            cases rest with
            | nil =>
                simp [atom, mem,
                  Formula.substituteFree,
                  term_substituteFree]
            | cons extra rest =>
                rfl
  · by_cases hSubset : relation = .subset
    · subst relation
      cases arguments with
      | nil =>
          simp [atom, hMembership,
            Formula.substituteFree]
      | cons left tail =>
          cases tail with
          | nil =>
              simp [atom, hMembership,
                Formula.substituteFree]
          | cons right rest =>
              cases rest with
              | nil =>
                  simpa [atom, hMembership,
                    term_substituteFree] using
                    (subset_substituteFree (id + 1)
                      (term replacement)
                      (term left) (term right)
                      (Nat.add_one_ne_zero id)
                      (term_bound_closed
                        hReplacementClosed)
                      (term_reserved_fresh
                        replacement)).symm
              | cons extra rest =>
                  simp [atom, hMembership,
                    Formula.substituteFree]
    · simp [atom, hMembership, hSubset,
        Formula.substituteFree]

/-- 公式翻译与打开 bound 变量交换。 -/
theorem formula_openAt
    (depth : Nat) (replacement : SourceTerm)
    (source : SourceFormula)
    (hReplacementClosed :
      Term.BoundClosed replacement) :
    formula
        (Formula.openAt SetSort.set depth
          replacement source) =
      Formula.openAt targetSort depth
        (term replacement) (formula source) := by
  induction source generalizing depth with
  | falsum => rfl
  | truth => rfl
  | rel relation arguments =>
      simpa [Formula.openAt] using
        atom_openAt depth replacement relation
          arguments hReplacementClosed
  | equal left right =>
      simp [formula, Formula.openAt, term_openAt]
  | neg body ih =>
      simp [formula, Formula.openAt, ih]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [formula, Formula.openAt,
        ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih =>
      cases sort
      simp [formula, Formula.openAt,
        Formula.next_depth, ih]

/-- 公式翻译与关闭源自由变量交换。 -/
theorem formula_closeFreeAt
    (id : FreeVarId) (depth : Nat)
    (source : SourceFormula) :
    formula
        (Formula.closeFreeAt SetSort.set id
          depth source) =
      Formula.closeFreeAt targetSort (id + 1)
        depth (formula source) := by
  induction source generalizing depth with
  | falsum => rfl
  | truth => rfl
  | rel relation arguments =>
      simpa [Formula.closeFreeAt] using
        atom_closeFreeAt id depth relation arguments
  | equal left right =>
      simp [formula, Formula.closeFreeAt,
        term_closeFreeAt]
  | neg body ih =>
      simp [formula, Formula.closeFreeAt, ih]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [formula, Formula.closeFreeAt,
        ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih =>
      cases sort
      simp [formula, Formula.closeFreeAt,
        Formula.next_depth, ih]

/-- 公式翻译与源自由变量替换交换。 -/
theorem formula_substituteFree
    (id : FreeVarId) (replacement : SourceTerm)
    (source : SourceFormula)
    (hReplacementClosed :
      Term.BoundClosed replacement) :
    formula
        (Formula.substituteFree SetSort.set id
          replacement source) =
      Formula.substituteFree targetSort (id + 1)
        (term replacement) (formula source) := by
  induction source with
  | falsum => rfl
  | truth => rfl
  | rel relation arguments =>
      simpa [Formula.substituteFree] using
        atom_substituteFree id replacement relation
          arguments hReplacementClosed
  | equal left right =>
      simp [formula, Formula.substituteFree,
        term_substituteFree]
  | neg body ih =>
      simp [formula, Formula.substituteFree, ih]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [formula, Formula.substituteFree,
        ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih =>
      cases sort
      simp [formula, Formula.substituteFree, ih]

/-- 子集展开保持已平移自由变量的新鲜性。 -/
theorem subset_fresh
    (id : FreeVarId) (left right : PureTerm)
    (hLeft :
      (targetSort, id + 1) ∉ Term.freeSupport left)
    (hRight :
      (targetSort, id + 1) ∉ Term.freeSupport right) :
    (targetSort, id + 1) ∉
      Formula.freeSupport (subset left right) := by
  intro hMember
  have hBody :=
    Formula.freeSupport_closeFreeAt_subset
      (targetSort, id + 1) targetSort 0 0
      (.imp (mem (free 0) left)
        (mem (free 0) right)) hMember
  have hZero :
      (targetSort, id + 1) ∉
        Term.freeSupport (free 0) := by
    intro hZero
    have hEqual :=
      congrArg Prod.snd
        (List.mem_singleton.mp hZero)
    simp at hEqual
  have hBodyFresh :
      (targetSort, id + 1) ∉
        Formula.freeSupport
          (.imp (mem (free 0) left)
            (mem (free 0) right)) := by
    simp only [Formula.freeSupport, mem,
      Term.freeSupportList, List.append_nil]
    exact fresh_append
      (fresh_append hZero hLeft)
      (fresh_append hZero hRight)
  exact hBodyFresh hBody

/-- 原子翻译保持源自由变量的新鲜性。 -/
theorem atom_fresh
    (id : FreeVarId) (relation : RelationSymbol)
    (arguments : List SourceTerm)
    (hFresh :
      (SetSort.set, id) ∉
        Term.freeSupportList arguments) :
    (targetSort, id + 1) ∉
      Formula.freeSupport (atom relation arguments) := by
  by_cases hMembership : relation = .membership
  · subst relation
    cases arguments with
    | nil => exact List.not_mem_nil
    | cons left tail =>
        cases tail with
        | nil => exact List.not_mem_nil
        | cons right rest =>
            cases rest with
            | nil =>
                have hLeft :
                    (SetSort.set, id) ∉
                      Term.freeSupport left := by
                  intro hMember
                  apply hFresh
                  simp only [Term.freeSupportList,
                    List.append_nil]
                  exact List.mem_append.mpr
                    (Or.inl hMember)
                have hRight :
                    (SetSort.set, id) ∉
                      Term.freeSupport right := by
                  intro hMember
                  apply hFresh
                  simp only [Term.freeSupportList,
                    List.append_nil]
                  exact List.mem_append.mpr
                    (Or.inr hMember)
                rw [show atom .membership [left, right] =
                  mem (term left) (term right) by
                    simp [atom]]
                simp only [Formula.freeSupport, mem,
                  Term.freeSupportList, List.append_nil]
                exact fresh_append
                  (term_fresh id left hLeft)
                  (term_fresh id right hRight)
            | cons extra rest => exact List.not_mem_nil
  · by_cases hSubset : relation = .subset
    · subst relation
      cases arguments with
      | nil => exact List.not_mem_nil
      | cons left tail =>
          cases tail with
          | nil => exact List.not_mem_nil
          | cons right rest =>
              cases rest with
              | nil =>
                  apply subset_fresh id
                  · apply term_fresh
                    intro hMember
                    apply hFresh
                    simp only [Term.freeSupportList,
                      List.append_nil]
                    exact List.mem_append.mpr
                      (Or.inl hMember)
                  · apply term_fresh
                    intro hMember
                    apply hFresh
                    simp only [Term.freeSupportList,
                      List.append_nil]
                    exact List.mem_append.mpr
                      (Or.inr hMember)
              | cons extra rest => exact List.not_mem_nil
    · rw [show atom relation arguments =
        (Formula.falsum : PureFormula) by
          simp [atom, hMembership, hSubset]]
      exact List.not_mem_nil

/-- 公式翻译保持源自由变量的新鲜性。 -/
theorem formula_fresh
    (id : FreeVarId) (source : SourceFormula)
    (hFresh :
      (SetSort.set, id) ∉
        Formula.freeSupport source) :
    (targetSort, id + 1) ∉
      Formula.freeSupport (formula source) := by
  induction source with
  | falsum => exact List.not_mem_nil
  | truth => exact List.not_mem_nil
  | rel relation arguments =>
      exact atom_fresh id relation arguments <| by
        simpa [Formula.freeSupport] using hFresh
  | equal left right =>
      apply fresh_append
      · apply term_fresh
        intro hMember
        apply hFresh
        exact List.mem_append.mpr (Or.inl hMember)
      · apply term_fresh
        intro hMember
        apply hFresh
        exact List.mem_append.mpr (Or.inr hMember)
  | neg body ih =>
      exact ih hFresh
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      apply fresh_append
      · apply ihLeft
        intro hMember
        apply hFresh
        exact List.mem_append.mpr (Or.inl hMember)
      · apply ihRight
        intro hMember
        apply hFresh
        exact List.mem_append.mpr (Or.inr hMember)
  | forallE sort body ih
  | existsE sort body ih =>
      exact ih <| by
        simpa [Formula.freeSupport] using hFresh

end ProjectRelationElimination
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
