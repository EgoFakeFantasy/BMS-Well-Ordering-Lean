import YesMetaZFC.BMS.Array
import Lean.Elab.Tactic.Omega

/-!
# BM4 parent 与 ancestor 的规格层

这里证明 Stage 0 的下降搜索确实返回最大的合格候选，并建立 parent/ancestor 的索引
下降性质。后续复制块引理只依赖本文件的规格，不展开搜索程序。
-/

namespace YesMetaZFC
namespace BMS

theorem greatestBelow?_some_lt {bound : Nat} {predicate : Nat → Bool} {found : Nat}
    (hFound : greatestBelow? bound predicate = some found) :
    found < bound := by
  induction bound with
  | zero =>
      simp [greatestBelow?] at hFound
  | succ bound ih =>
      by_cases hTop : predicate bound = true
      · simp [greatestBelow?, hTop] at hFound
        omega
      · simp [greatestBelow?, hTop] at hFound
        exact Nat.lt_succ_of_lt (ih hFound)

theorem greatestBelow?_some_satisfies {bound : Nat} {predicate : Nat → Bool} {found : Nat}
    (hFound : greatestBelow? bound predicate = some found) :
    predicate found = true := by
  induction bound with
  | zero =>
      simp [greatestBelow?] at hFound
  | succ bound ih =>
      by_cases hTop : predicate bound = true
      · simp [greatestBelow?, hTop] at hFound
        simpa [hFound] using hTop
      · simp [greatestBelow?, hTop] at hFound
        exact ih hFound

theorem greatestBelow?_some_isGreatest {bound : Nat} {predicate : Nat → Bool} {found : Nat}
    (hFound : greatestBelow? bound predicate = some found) :
    ∀ candidate, candidate < bound → predicate candidate = true → candidate ≤ found := by
  induction bound with
  | zero =>
      simp [greatestBelow?] at hFound
  | succ bound ih =>
      by_cases hTop : predicate bound = true
      · simp [greatestBelow?, hTop] at hFound
        subst found
        intro candidate hCandidate _
        omega
      · simp [greatestBelow?, hTop] at hFound
        intro candidate hCandidate hEligible
        have hLe : candidate ≤ bound := Nat.le_of_lt_succ hCandidate
        rcases Nat.lt_or_eq_of_le hLe with hSmaller | hEqual
        · exact ih hFound candidate hSmaller hEligible
        · subst candidate
          exact (hTop hEligible).elim

theorem greatestBelow?_eq_none_iff {bound : Nat} {predicate : Nat → Bool} :
    greatestBelow? bound predicate = none ↔
      ∀ candidate, candidate < bound → predicate candidate = false := by
  induction bound with
  | zero =>
      simp [greatestBelow?]
  | succ bound ih =>
      constructor
      · intro hNone candidate hCandidate
        by_cases hTop : predicate bound = true
        · simp [greatestBelow?, hTop] at hNone
        · have hRecursive : greatestBelow? bound predicate = none := by
            simpa [greatestBelow?, hTop] using hNone
          have hLe : candidate ≤ bound := Nat.le_of_lt_succ hCandidate
          rcases Nat.lt_or_eq_of_le hLe with hSmaller | hEqual
          · exact (ih.mp hRecursive) candidate hSmaller
          · subst candidate
            cases hValue : predicate bound with
            | false => rfl
            | true => exact (hTop hValue).elim
      · intro hAll
        have hTopFalse : predicate bound = false :=
          hAll bound (Nat.lt_succ_self bound)
        have hRecursive : greatestBelow? bound predicate = none :=
          ih.mpr (fun candidate hCandidate =>
            hAll candidate (Nat.lt_trans hCandidate (Nat.lt_succ_self bound)))
        simp [greatestBelow?, hTopFalse, hRecursive]

theorem greatestBelow?_eq_some_iff {bound found : Nat} {predicate : Nat → Bool} :
    greatestBelow? bound predicate = some found ↔
      found < bound ∧ predicate found = true ∧
        ∀ candidate, candidate < bound → predicate candidate = true → candidate ≤ found := by
  constructor
  · intro hFound
    exact ⟨greatestBelow?_some_lt hFound, greatestBelow?_some_satisfies hFound,
      greatestBelow?_some_isGreatest hFound⟩
  · rintro ⟨hFoundLt, hFoundEligible, hMaximal⟩
    cases hSearch : greatestBelow? bound predicate with
    | none =>
        have hFalse := (greatestBelow?_eq_none_iff.mp hSearch)
          found hFoundLt
        simp [hFoundEligible] at hFalse
    | some result =>
        have hResultLe : result ≤ found := hMaximal result
          (greatestBelow?_some_lt hSearch)
          (greatestBelow?_some_satisfies hSearch)
        have hFoundLe : found ≤ result :=
          greatestBelow?_some_isGreatest hSearch found hFoundLt hFoundEligible
        have hEqual : result = found := Nat.le_antisymm hResultLe hFoundLe
        subst result
        rfl

/-- `row` 上不含 `candidate < target` 的 parent 候选条件。 -/
def parentEligible (row : Nat) (array : BMSArray) (target candidate : Nat) : Bool :=
  match row with
  | 0 =>
      match entry? array candidate 0, entry? array target 0 with
      | some left, some right => left < right
      | _, _ => false
  | lowerRow + 1 =>
      isAncestor array lowerRow candidate target &&
        match entry? array candidate (lowerRow + 1), entry? array target (lowerRow + 1) with
        | some left, some right => left < right
        | _, _ => false

/-- parent 候选条件中只依赖当前行数值的严格比较部分。 -/
def entryLess (array : BMSArray) (row candidate target : Nat) : Bool :=
  match entry? array candidate row, entry? array target row with
  | some left, some right => left < right
  | _, _ => false

@[simp]
theorem parentEligible_zero_eq_entryLess (array : BMSArray) (target candidate : Nat) :
    parentEligible 0 array target candidate = entryLess array 0 candidate target := rfl

@[simp]
theorem parentEligible_succ_eq_entryLess (row : Nat) (array : BMSArray)
    (target candidate : Nat) :
    parentEligible (row + 1) array target candidate =
      (isAncestor array row candidate target &&
        entryLess array (row + 1) candidate target) := rfl

theorem parentEligible_zero_congr_entryLess {left right : BMSArray}
    {leftTarget rightTarget leftCandidate rightCandidate : Nat}
    (hEntry : entryLess left 0 leftCandidate leftTarget =
      entryLess right 0 rightCandidate rightTarget) :
    parentEligible 0 left leftTarget leftCandidate =
      parentEligible 0 right rightTarget rightCandidate := by
  simpa using hEntry

theorem parentEligible_succ_congr_entryLess {row : Nat} {left right : BMSArray}
    {leftTarget rightTarget leftCandidate rightCandidate : Nat}
    (hAncestor : isAncestor left row leftCandidate leftTarget =
      isAncestor right row rightCandidate rightTarget)
    (hEntry : entryLess left (row + 1) leftCandidate leftTarget =
      entryLess right (row + 1) rightCandidate rightTarget) :
    parentEligible (row + 1) left leftTarget leftCandidate =
      parentEligible (row + 1) right rightTarget rightCandidate := by
  simp only [parentEligible_succ_eq_entryLess]
  rw [hAncestor, hEntry]

theorem parent_eq_greatestBelow? (row : Nat) (array : BMSArray) (target : Nat) :
    parent row array target =
      if target < array.length then
        greatestBelow? target (parentEligible row array target)
      else
        none := by
  cases row <;> rfl

theorem parent_some_target_valid {row : Nat} {array : BMSArray} {target found : Nat}
    (hParent : parent row array target = some found) :
    target < array.length := by
  rw [parent_eq_greatestBelow?] at hParent
  split at hParent
  next hTarget => exact hTarget
  next _ => simp at hParent

theorem parent_some_lt {row : Nat} {array : BMSArray} {target found : Nat}
    (hParent : parent row array target = some found) :
    found < target := by
  rw [parent_eq_greatestBelow?] at hParent
  split at hParent
  next _ => exact greatestBelow?_some_lt hParent
  next _ => simp at hParent

theorem parent_some_eligible {row : Nat} {array : BMSArray} {target found : Nat}
    (hParent : parent row array target = some found) :
    parentEligible row array target found = true := by
  rw [parent_eq_greatestBelow?] at hParent
  split at hParent
  next _ => exact greatestBelow?_some_satisfies hParent
  next _ => simp at hParent

theorem parent_some_isGreatest {row : Nat} {array : BMSArray} {target found : Nat}
    (hParent : parent row array target = some found) :
    ∀ candidate, candidate < target →
      parentEligible row array target candidate = true →
      candidate ≤ found := by
  rw [parent_eq_greatestBelow?] at hParent
  split at hParent
  next _ => exact greatestBelow?_some_isGreatest hParent
  next _ => simp at hParent

theorem parent_eq_some_iff {row : Nat} {array : BMSArray} {target found : Nat} :
    parent row array target = some found ↔
      target < array.length ∧ found < target ∧
        parentEligible row array target found = true ∧
        ∀ candidate, candidate < target →
          parentEligible row array target candidate = true → candidate ≤ found := by
  rw [parent_eq_greatestBelow?]
  by_cases hTarget : target < array.length
  · simp only [hTarget, ↓reduceIte, true_and]
    exact greatestBelow?_eq_some_iff
  · simp [hTarget]

/-- 第零行 parent 的结果满足论文中的坐标严格不等式。 -/
theorem parent_zero_some_spec {array : BMSArray} {target found : Nat}
    (hParent : parent 0 array target = some found) :
    found < target ∧
      ∃ left right,
        entry? array found 0 = some left ∧
        entry? array target 0 = some right ∧
        left < right := by
  refine ⟨parent_some_lt hParent, ?_⟩
  have hEligible := parent_some_eligible hParent
  cases hLeft : entry? array found 0 with
  | none => simp [parentEligible, hLeft] at hEligible
  | some left =>
      cases hRight : entry? array target 0 with
      | none => simp [parentEligible, hLeft, hRight] at hEligible
      | some right =>
          refine ⟨left, right, rfl, rfl, ?_⟩
          simpa [parentEligible, hLeft, hRight] using hEligible

/-- 高一行的 parent 同时满足低一行 ancestry 与本行坐标严格不等式。 -/
theorem parent_succ_some_spec {row : Nat} {array : BMSArray} {target found : Nat}
    (hParent : parent (row + 1) array target = some found) :
    found < target ∧
      isAncestor array row found target = true ∧
      ∃ left right,
        entry? array found (row + 1) = some left ∧
        entry? array target (row + 1) = some right ∧
        left < right := by
  have hEligible := parent_some_eligible hParent
  have hAncestor : isAncestor array row found target = true := by
    cases hValue : isAncestor array row found target with
    | false => simp [parentEligible, hValue] at hEligible
    | true => rfl
  refine ⟨parent_some_lt hParent, hAncestor, ?_⟩
  cases hLeft : entry? array found (row + 1) with
  | none => simp [parentEligible, hLeft] at hEligible
  | some left =>
      cases hRight : entry? array target (row + 1) with
      | none => simp [parentEligible, hLeft, hRight] at hEligible
      | some right =>
          refine ⟨left, right, rfl, rfl, ?_⟩
          simpa [parentEligible, hLeft, hRight, hAncestor] using hEligible

/-- 任意一行的 parent 边都使该行坐标严格增加。 -/
theorem parent_some_entry_lt {row : Nat} {array : BMSArray} {target found : Nat}
    (hParent : parent row array target = some found) :
    ∃ left right,
      entry? array found row = some left ∧
      entry? array target row = some right ∧
      left < right := by
  cases row with
  | zero =>
      exact (parent_zero_some_spec hParent).2
  | succ lowerRow =>
      simpa [Nat.succ_eq_add_one] using (parent_succ_some_spec hParent).2.2

/-- 同一行上的严格坐标比较具有传递性。 -/
theorem entryLess_trans {array : BMSArray} {row left middle right : Nat}
    (hLeftMiddle : entryLess array row left middle = true)
    (hMiddleRight : entryLess array row middle right = true) :
    entryLess array row left right = true := by
  cases hLeft : entry? array left row with
  | none => simp [entryLess, hLeft] at hLeftMiddle
  | some leftValue =>
      cases hMiddle : entry? array middle row with
      | none => simp [entryLess, hLeft, hMiddle] at hLeftMiddle
      | some middleValue =>
          cases hRight : entry? array right row with
          | none => simp [entryLess, hMiddle, hRight] at hMiddleRight
          | some rightValue =>
              simp [entryLess, hLeft, hMiddle, hRight] at hLeftMiddle hMiddleRight ⊢
              omega

theorem parent_eq_none_iff {row : Nat} {array : BMSArray} {target : Nat} :
    parent row array target = none ↔
      array.length ≤ target ∨
        ∀ candidate, candidate < target →
          parentEligible row array target candidate = false := by
  rw [parent_eq_greatestBelow?]
  by_cases hTarget : target < array.length
  · simp [hTarget, greatestBelow?_eq_none_iff]
    omega
  · simp [hTarget]
    omega

theorem exists_parent_of_eligible {row : Nat} {array : BMSArray}
    {target candidate : Nat}
    (hTarget : target < array.length)
    (hCandidate : candidate < target)
    (hEligible : parentEligible row array target candidate = true) :
    ∃ found, parent row array target = some found ∧ candidate ≤ found := by
  cases hParent : parent row array target with
  | some found =>
      exact ⟨found, rfl, parent_some_isGreatest hParent candidate
        hCandidate hEligible⟩
  | none =>
      rw [parent_eq_none_iff] at hParent
      rcases hParent with hOutOfBounds | hNoCandidate
      · omega
      · rw [hNoCandidate candidate hCandidate] at hEligible
        simp at hEligible

theorem parent_congr {row target : Nat} {left right : BMSArray}
    (hLength : left.length = right.length)
    (hEligible : ∀ candidate,
      parentEligible row left target candidate =
        parentEligible row right target candidate) :
    parent row left target = parent row right target := by
  rw [parent_eq_greatestBelow?, parent_eq_greatestBelow?, hLength]
  congr 2
  funext candidate
  exact hEligible candidate

/-- 两个数组长度可以不同；只要目标存在且目标以前的候选谓词相同，parent 就相同。 -/
theorem parent_congr_below_target {row target : Nat} {left right : BMSArray}
    (hLeftTarget : target < left.length)
    (hRightTarget : target < right.length)
    (hEligible : ∀ candidate, candidate < target →
      parentEligible row left target candidate =
        parentEligible row right target candidate) :
    parent row left target = parent row right target := by
  cases hLeftParent : parent row left target with
  | some found =>
      symm
      rw [parent_eq_some_iff]
      rw [parent_eq_some_iff] at hLeftParent
      refine ⟨hRightTarget, hLeftParent.2.1, ?_, ?_⟩
      · rw [← hEligible found hLeftParent.2.1]
        exact hLeftParent.2.2.1
      · intro candidate hCandidate hCandidateEligible
        apply hLeftParent.2.2.2 candidate hCandidate
        rw [hEligible candidate hCandidate]
        exact hCandidateEligible
  | none =>
      symm
      rw [parent_eq_none_iff]
      rw [parent_eq_none_iff] at hLeftParent
      right
      intro candidate hCandidate
      rw [← hEligible candidate hCandidate]
      rcases hLeftParent with hOutOfBounds | hNoCandidate
      · omega
      · exact hNoCandidate candidate hCandidate

theorem parentEligible_zero_congr {left right : BMSArray} {target candidate : Nat}
    (hCandidate : entry? left candidate 0 = entry? right candidate 0)
    (hTarget : entry? left target 0 = entry? right target 0) :
    parentEligible 0 left target candidate = parentEligible 0 right target candidate := by
  simp only [parentEligible]
  rw [hCandidate, hTarget]

theorem parentEligible_succ_congr {row : Nat} {left right : BMSArray}
    {target candidate : Nat}
    (hAncestor : isAncestor left row candidate target =
      isAncestor right row candidate target)
    (hCandidate : entry? left candidate (row + 1) =
      entry? right candidate (row + 1))
    (hTarget : entry? left target (row + 1) =
      entry? right target (row + 1)) :
    parentEligible (row + 1) left target candidate =
      parentEligible (row + 1) right target candidate := by
  simp only [parentEligible]
  rw [hAncestor, hCandidate, hTarget]

theorem ancestorChain_mem_lt
    {parentFunction : Nat → Option Nat}
    (hDecrease : ∀ {target found}, parentFunction target = some found → found < target)
    {current fuel ancestor : Nat}
    (hMember : ancestor ∈ ancestorChain parentFunction current fuel) :
    ancestor < current := by
  induction fuel generalizing current with
  | zero =>
      simp [ancestorChain] at hMember
  | succ fuel ih =>
      simp only [ancestorChain] at hMember
      split at hMember
      next => simp at hMember
      next parent hParent =>
        simp only [List.mem_cons] at hMember
        rcases hMember with hEqual | hTail
        · subst ancestor
          exact hDecrease hParent
        · exact Nat.lt_trans (ih hTail) (hDecrease hParent)

theorem isAncestor_lt {array : BMSArray} {row ancestor target : Nat}
    (hAncestor : isAncestor array row ancestor target = true) :
    ancestor < target := by
  apply ancestorChain_mem_lt (parentFunction := parent row array)
    (fun hParent => parent_some_lt hParent)
  simpa [isAncestor] using hAncestor

theorem direct_parent_isAncestor {array : BMSArray} {row ancestor target : Nat}
    (hParent : parent row array target = some ancestor) :
    isAncestor array row ancestor target = true := by
  have hPositive : 0 < target := Nat.zero_lt_of_lt (parent_some_lt hParent)
  cases target with
  | zero => omega
  | succ previous =>
      simp [isAncestor, ancestorChain, hParent]

theorem higher_parent_is_lower_ancestor {array : BMSArray}
    {row ancestor target : Nat}
    (hParent : parent (row + 1) array target = some ancestor) :
    isAncestor array row ancestor target = true := by
  have hEligible := parent_some_eligible hParent
  cases hAncestor : isAncestor array row ancestor target with
  | false => simp [parentEligible, hAncestor] at hEligible
  | true => rfl

theorem parentEligible_succ_isAncestor {array : BMSArray}
    {row candidate target : Nat}
    (hEligible : parentEligible (row + 1) array target candidate = true) :
    isAncestor array row candidate target = true := by
  cases hAncestor : isAncestor array row candidate target with
  | false => simp [parentEligible, hAncestor] at hEligible
  | true => rfl

end BMS
end YesMetaZFC
