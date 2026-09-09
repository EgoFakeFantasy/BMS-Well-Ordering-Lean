import YesMetaZFC.BMS.Parent

/-!
# BM4 ancestor 的无 fuel 规格

参考程序以列号作为 fuel。本文件用 `Relation.TransGen` 给出不含 fuel 的数学定义，
并证明两者等价；等价证明的关键正是 parent 严格减小列号。
-/

namespace YesMetaZFC
namespace BMS

/-- 从一列到其直接 `row`-parent 的有向边。 -/
def ParentEdge (row : Nat) (array : BMSArray) (larger smaller : Nat) : Prop :=
  parent row array larger = some smaller

/-- 不依赖计算 fuel 的严格 ancestor 关系。 -/
def StrictAncestor (row : Nat) (array : BMSArray) (larger smaller : Nat) : Prop :=
  Relation.TransGen (ParentEdge row array) larger smaller

theorem transGen_head
    {α : Type} {relation : α → α → Prop} {start finish : α}
    (path : Relation.TransGen relation start finish) :
    relation start finish ∨
      ∃ next, relation start next ∧ Relation.TransGen relation next finish := by
  induction path with
  | single edge => exact Or.inl edge
  | tail path edge ih =>
      rcases ih with direct | ⟨next, first, rest⟩
      · exact Or.inr ⟨_, direct, Relation.TransGen.single edge⟩
      · exact Or.inr ⟨_, first, Relation.TransGen.tail rest edge⟩

theorem parentTransGen_comparable
    {parentFunction : Nat → Option Nat}
    (hDecrease : ∀ {larger smaller},
      parentFunction larger = some smaller → smaller < larger)
    {target left right : Nat}
    (hLeft : Relation.TransGen
      (fun larger smaller => parentFunction larger = some smaller) target left)
    (hRight : Relation.TransGen
      (fun larger smaller => parentFunction larger = some smaller) target right) :
    left = right ∨
      Relation.TransGen
        (fun larger smaller => parentFunction larger = some smaller) left right ∨
      Relation.TransGen
        (fun larger smaller => parentFunction larger = some smaller) right left := by
  induction target using Nat.strongRecOn generalizing left right with
  | ind target ih =>
      rcases transGen_head hLeft with hLeftDirect | ⟨leftNext, hLeftNext, hLeftRest⟩
      · rcases transGen_head hRight with hRightDirect | ⟨rightNext, hRightNext, hRightRest⟩
        · have hEqual : left = right := by
            rw [hLeftDirect] at hRightDirect
            exact Option.some.inj hRightDirect
          exact Or.inl hEqual
        · have hEqual : left = rightNext := by
            rw [hLeftDirect] at hRightNext
            exact Option.some.inj hRightNext
          subst rightNext
          exact Or.inr (Or.inl hRightRest)
      · rcases transGen_head hRight with hRightDirect | ⟨rightNext, hRightNext, hRightRest⟩
        · have hEqual : right = leftNext := by
            rw [hRightDirect] at hLeftNext
            exact Option.some.inj hLeftNext
          subst leftNext
          exact Or.inr (Or.inr hLeftRest)
        · have hNextEqual : leftNext = rightNext := by
            rw [hLeftNext] at hRightNext
            exact Option.some.inj hRightNext
          subst rightNext
          exact ih leftNext (hDecrease hLeftNext) hLeftRest hRightRest

theorem ancestorChain_mem_strictAncestor
    {parentFunction : Nat → Option Nat}
    {current fuel ancestor : Nat}
    (hMember : ancestor ∈ ancestorChain parentFunction current fuel) :
    Relation.TransGen
      (fun larger smaller => parentFunction larger = some smaller)
      current ancestor := by
  induction fuel generalizing current with
  | zero => simp [ancestorChain] at hMember
  | succ fuel ih =>
      simp only [ancestorChain] at hMember
      split at hMember
      next => simp at hMember
      next next hNext =>
        simp only [List.mem_cons] at hMember
        rcases hMember with hDirect | hRest
        · subst ancestor
          exact Relation.TransGen.single (r := fun larger smaller =>
            parentFunction larger = some smaller) hNext
        · exact Relation.TransGen.trans
            (Relation.TransGen.single (r := fun larger smaller =>
              parentFunction larger = some smaller) hNext)
            (ih hRest)

theorem strictAncestor_mem_ancestorChain
    {parentFunction : Nat → Option Nat}
    (hDecrease : ∀ {larger smaller},
      parentFunction larger = some smaller → smaller < larger)
    {current fuel ancestor : Nat}
    (hFuel : current ≤ fuel)
    (hAncestor : Relation.TransGen
      (fun larger smaller => parentFunction larger = some smaller)
      current ancestor) :
    ancestor ∈ ancestorChain parentFunction current fuel := by
  induction fuel generalizing current with
  | zero =>
      have hCurrent : current = 0 := Nat.eq_zero_of_le_zero hFuel
      subst current
      rcases transGen_head hAncestor with hDirect | ⟨next, hNext, _⟩
      · have := hDecrease hDirect
        omega
      · have := hDecrease hNext
        omega
  | succ fuel ih =>
      rcases transGen_head hAncestor with hDirect | ⟨next, hNext, hRest⟩
      · simp [ancestorChain, hDirect]
      · have hNextLt : next < current := hDecrease hNext
        have hNextFuel : next ≤ fuel := by omega
        simp only [ancestorChain, hNext, List.mem_cons]
        exact Or.inr (ih hNextFuel hRest)

theorem isAncestor_iff_strictAncestor
    {array : BMSArray} {row ancestor target : Nat} :
    isAncestor array row ancestor target = true ↔
      StrictAncestor row array target ancestor := by
  constructor
  · intro hAncestor
    apply ancestorChain_mem_strictAncestor
    simpa [isAncestor] using hAncestor
  · intro hAncestor
    have hMember := strictAncestor_mem_ancestorChain
      (parentFunction := parent row array)
      (fun hParent => parent_some_lt hParent)
      (Nat.le_refl target)
      hAncestor
    simpa [isAncestor, StrictAncestor, ParentEdge] using hMember

theorem isAncestor_trans {array : BMSArray} {row earlier middle later : Nat}
    (hEarlier : isAncestor array row earlier middle = true)
    (hMiddle : isAncestor array row middle later = true) :
    isAncestor array row earlier later = true := by
  apply isAncestor_iff_strictAncestor.mpr
  exact Relation.TransGen.trans
    (isAncestor_iff_strictAncestor.mp hMiddle)
    (isAncestor_iff_strictAncestor.mp hEarlier)

/-- 同一 parent 函数下，具有相同直接 parent 的两个目标有相同严格 ancestors。 -/
theorem isAncestor_congr_of_parent_eq {array : BMSArray}
    {row leftTarget rightTarget : Nat}
    (hParent : parent row array leftTarget = parent row array rightTarget) :
    ∀ ancestor,
      isAncestor array row ancestor leftTarget =
        isAncestor array row ancestor rightTarget := by
  intro ancestor
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hAncestor
    have hPath := isAncestor_iff_strictAncestor.mp hAncestor
    rcases transGen_head hPath with hDirect | ⟨next, hNext, hRest⟩
    · apply isAncestor_iff_strictAncestor.mpr
      apply Relation.TransGen.single
      unfold ParentEdge at hDirect ⊢
      rwa [← hParent]
    · apply isAncestor_iff_strictAncestor.mpr
      exact Relation.TransGen.trans
        (Relation.TransGen.single (r := ParentEdge row array) (by
          unfold ParentEdge at hNext ⊢
          rwa [← hParent])) hRest
  · intro hAncestor
    have hPath := isAncestor_iff_strictAncestor.mp hAncestor
    rcases transGen_head hPath with hDirect | ⟨next, hNext, hRest⟩
    · apply isAncestor_iff_strictAncestor.mpr
      apply Relation.TransGen.single
      unfold ParentEdge at hDirect ⊢
      rwa [hParent]
    · apply isAncestor_iff_strictAncestor.mpr
      exact Relation.TransGen.trans
        (Relation.TransGen.single (r := ParentEdge row array) (by
          unfold ParentEdge at hNext ⊢
          rwa [hParent])) hRest

/-- 固定直接 parent 后，严格 ancestor 要么就是该 parent，要么是它的 ancestor。 -/
theorem isAncestor_iff_of_parent_some {array : BMSArray}
    {row ancestor target found : Nat}
    (hParent : parent row array target = some found) :
    isAncestor array row ancestor target = true ↔
      ancestor = found ∨ isAncestor array row ancestor found = true := by
  constructor
  · intro hAncestor
    have hPath := isAncestor_iff_strictAncestor.mp hAncestor
    rcases transGen_head hPath with hDirect | ⟨next, hNext, hRest⟩
    · unfold ParentEdge at hDirect
      rw [hParent] at hDirect
      exact Or.inl (Option.some.inj hDirect).symm
    · unfold ParentEdge at hNext
      rw [hParent] at hNext
      have hNextEq := Option.some.inj hNext
      subst next
      exact Or.inr (isAncestor_iff_strictAncestor.mpr hRest)
  · rintro (rfl | hAncestor)
    · exact direct_parent_isAncestor hParent
    · exact isAncestor_trans hAncestor (direct_parent_isAncestor hParent)

/-- 没有直接 parent 的目标没有严格 ancestors。 -/
theorem isAncestor_eq_false_of_parent_none {array : BMSArray}
    {row ancestor target : Nat}
    (hParent : parent row array target = none) :
    isAncestor array row ancestor target = false := by
  cases hValue : isAncestor array row ancestor target with
  | false => rfl
  | true =>
      have hPath := isAncestor_iff_strictAncestor.mp hValue
      rcases transGen_head hPath with hDirect | ⟨next, hNext, _⟩
      · unfold ParentEdge at hDirect
        rw [hParent] at hDirect
        simp at hDirect
      · unfold ParentEdge at hNext
        rw [hParent] at hNext
        simp at hNext

/-- 任意严格 ancestor 都不晚于目标的直接 parent。 -/
theorem ancestor_le_parent {array : BMSArray}
    {row ancestor target found : Nat}
    (hParent : parent row array target = some found)
    (hAncestor : isAncestor array row ancestor target = true) :
    ancestor ≤ found := by
  rcases (isAncestor_iff_of_parent_some hParent).mp hAncestor with
    rfl | hEarlier
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (isAncestor_lt hEarlier)

/-- 两个目标的 parent 都受同一上界约束且界内候选等价时，两个 parent 相同。 -/
theorem parent_eq_of_bounded_results {left right : BMSArray}
    {row leftTarget rightTarget bound : Nat}
    (hLeftTarget : leftTarget < left.length)
    (hRightTarget : rightTarget < right.length)
    (hBoundLeft : bound ≤ leftTarget)
    (hBoundRight : bound ≤ rightTarget)
    (hLeftResult : ∀ {found}, parent row left leftTarget = some found →
      found < bound)
    (hRightResult : ∀ {found}, parent row right rightTarget = some found →
      found < bound)
    (hEligible : ∀ candidate, candidate < bound →
      parentEligible row left leftTarget candidate =
        parentEligible row right rightTarget candidate) :
    parent row left leftTarget = parent row right rightTarget := by
  cases hLeftParent : parent row left leftTarget with
  | none =>
      cases hRightParent : parent row right rightTarget with
      | none => rfl
      | some rightFound =>
          have hRightBound := hRightResult hRightParent
          have hRightEligible := parent_some_eligible hRightParent
          have hLeftEligible : parentEligible row left leftTarget rightFound = true := by
            rw [hEligible rightFound hRightBound]
            exact hRightEligible
          rcases exists_parent_of_eligible hLeftTarget
              (Nat.lt_of_lt_of_le hRightBound hBoundLeft) hLeftEligible with
            ⟨leftFound, hLeftFound, _⟩
          rw [hLeftParent] at hLeftFound
          simp at hLeftFound
  | some leftFound =>
      cases hRightParent : parent row right rightTarget with
      | none =>
          have hLeftBound := hLeftResult hLeftParent
          have hLeftEligible := parent_some_eligible hLeftParent
          have hRightEligible : parentEligible row right rightTarget leftFound = true := by
            rw [← hEligible leftFound hLeftBound]
            exact hLeftEligible
          rcases exists_parent_of_eligible hRightTarget
              (Nat.lt_of_lt_of_le hLeftBound hBoundRight) hRightEligible with
            ⟨rightFound, hRightFound, _⟩
          rw [hRightParent] at hRightFound
          simp at hRightFound
      | some rightFound =>
          have hLeftBound := hLeftResult hLeftParent
          have hRightBound := hRightResult hRightParent
          have hLeftEligible := parent_some_eligible hLeftParent
          have hRightEligible := parent_some_eligible hRightParent
          have hLeftLeRight := parent_some_isGreatest hRightParent leftFound
            (Nat.lt_of_lt_of_le hLeftBound hBoundRight)
            (by rwa [← hEligible leftFound hLeftBound])
          have hRightLeLeft := parent_some_isGreatest hLeftParent rightFound
            (Nat.lt_of_lt_of_le hRightBound hBoundLeft)
            (by rwa [hEligible rightFound hRightBound])
          have hEqual : leftFound = rightFound := by omega
          subst rightFound
          rfl

/-- 高一行的严格 ancestor 必然也是低一行的严格 ancestor。 -/
theorem isAncestor_lower {array : BMSArray} {row ancestor target : Nat}
    (hAncestor : isAncestor array (row + 1) ancestor target = true) :
    isAncestor array row ancestor target = true := by
  have hStrict := isAncestor_iff_strictAncestor.mp hAncestor
  unfold StrictAncestor ParentEdge at hStrict
  induction hStrict with
  | single hParent =>
      exact (parent_succ_some_spec hParent).2.1
  | tail path hParent ih =>
      have hPath : isAncestor array (row + 1) _ _ = true :=
        isAncestor_iff_strictAncestor.mpr path
      exact isAncestor_trans (parent_succ_some_spec hParent).2.1 (ih hPath)

/-- 某行的 ancestor 在每个严格更低的行仍是 ancestor。 -/
theorem isAncestor_of_lt_row {array : BMSArray}
    {lowerRow row ancestor target : Nat} (hLower : lowerRow < row)
    (hAncestor : isAncestor array row ancestor target = true) :
    isAncestor array lowerRow ancestor target = true := by
  induction row generalizing lowerRow with
  | zero => omega
  | succ row ih =>
      have hAtRow : isAncestor array row ancestor target = true := by
        simpa [Nat.succ_eq_add_one] using isAncestor_lower hAncestor
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hLower) with hEqual | hStrict
      · subst lowerRow
        exact hAtRow
      · exact ih hStrict hAtRow

/-- 在目标以下逐点相同的下降 parent 函数产生相同的有限 ancestor 链。 -/
theorem ancestorChain_congr_below
    {leftParent rightParent : Nat → Option Nat} {target current fuel : Nat}
    (hLeftDecrease : ∀ {larger smaller},
      leftParent larger = some smaller → smaller < larger)
    (hParent : ∀ column, column ≤ target → leftParent column = rightParent column)
    (hCurrent : current ≤ target) :
    ancestorChain leftParent current fuel =
      ancestorChain rightParent current fuel := by
  induction fuel generalizing current with
  | zero => rfl
  | succ remaining ih =>
      simp only [ancestorChain]
      rw [← hParent current hCurrent]
      cases hNext : leftParent current with
      | none => rfl
      | some next =>
          simp only
          congr 1
          apply ih
          exact Nat.le_trans (Nat.le_of_lt (hLeftDecrease hNext)) hCurrent

/-- 目标以下逐点相同的 parent 函数给出相同的可计算 ancestor 判定。 -/
theorem isAncestor_congr_below {left right : BMSArray} {row ancestor target : Nat}
    (hParent : ∀ column, column ≤ target →
      parent row left column = parent row right column) :
    isAncestor left row ancestor target = isAncestor right row ancestor target := by
  unfold isAncestor
  rw [ancestorChain_congr_below
    (fun hEdge => parent_some_lt hEdge) hParent (Nat.le_refl target)]

/-- 若两个数组在目标列及其左侧逐项相同，则目标的每一层 parent 都相同。 -/
theorem parent_eq_of_entry?_eq_below {left right : BMSArray} {target : Nat}
    (hLeftTarget : target < left.length)
    (hRightTarget : target < right.length)
    (hEntry : ∀ column, column ≤ target → ∀ row,
      entry? left column row = entry? right column row) :
    ∀ row, parent row left target = parent row right target := by
  intro row
  induction row generalizing target with
  | zero =>
      apply parent_congr_below_target hLeftTarget hRightTarget
      intro candidate hCandidate
      exact parentEligible_zero_congr
        (hEntry candidate (Nat.le_of_lt hCandidate) 0)
        (hEntry target (Nat.le_refl target) 0)
  | succ lowerRow ih =>
      apply parent_congr_below_target hLeftTarget hRightTarget
      intro candidate hCandidate
      apply parentEligible_succ_congr
      · apply isAncestor_congr_below
        intro column hColumn
        apply ih
        · omega
        · omega
        · intro entryColumn hEntryColumn entryRow
          exact hEntry entryColumn
            (Nat.le_trans hEntryColumn hColumn) entryRow
      · exact hEntry candidate (Nat.le_of_lt hCandidate) (lowerRow + 1)
      · exact hEntry target (Nat.le_refl target) (lowerRow + 1)

/-- 前缀逐项相同时，该前缀内部的 ancestry 在所有行都不变。 -/
theorem isAncestor_eq_of_entry?_eq_below {left right : BMSArray}
    {ancestor target : Nat}
    (hLeftTarget : target < left.length)
    (hRightTarget : target < right.length)
    (hEntry : ∀ column, column ≤ target → ∀ row,
      entry? left column row = entry? right column row) :
    ∀ row, isAncestor left row ancestor target =
      isAncestor right row ancestor target := by
  intro row
  apply isAncestor_congr_below
  intro column hColumn
  exact parent_eq_of_entry?_eq_below (by omega) (by omega)
    (fun entryColumn hEntryColumn entryRow =>
      hEntry entryColumn (Nat.le_trans hEntryColumn hColumn) entryRow) row

/-- 严格 ancestor 在所考察行上的坐标严格小于目标列。 -/
theorem strictAncestor_entries_lt {array : BMSArray} {row target ancestor : Nat}
    (hAncestor : StrictAncestor row array target ancestor) :
    ∃ ancestorValue targetValue,
      entry? array ancestor row = some ancestorValue ∧
      entry? array target row = some targetValue ∧
      ancestorValue < targetValue := by
  unfold StrictAncestor ParentEdge at hAncestor
  induction hAncestor with
  | single hParent =>
      exact parent_some_entry_lt hParent
  | tail path hParent ih =>
      rcases ih with
        ⟨middleValue, targetValue, hMiddle, hTarget, hMiddleLt⟩
      rcases parent_some_entry_lt hParent with
        ⟨ancestorValue, middleValue', hAncestorValue, hMiddle', hAncestorLt⟩
      have hValueEqual : middleValue' = middleValue := by
        rw [hMiddle] at hMiddle'
        exact Option.some.inj hMiddle'.symm
      subst middleValue'
      exact ⟨ancestorValue, targetValue, hAncestorValue, hTarget,
        Nat.lt_trans hAncestorLt hMiddleLt⟩

/-- 可计算的 ancestor 判定同样给出本行坐标的严格不等式。 -/
theorem ancestor_entries_lt {array : BMSArray} {row target ancestor : Nat}
    (hAncestor : isAncestor array row ancestor target = true) :
    ∃ ancestorValue targetValue,
      entry? array ancestor row = some ancestorValue ∧
      entry? array target row = some targetValue ∧
      ancestorValue < targetValue :=
  strictAncestor_entries_lt (isAncestor_iff_strictAncestor.mp hAncestor)

theorem strictAncestor_comparable {array : BMSArray} {row target left right : Nat}
    (hLeft : StrictAncestor row array target left)
    (hRight : StrictAncestor row array target right) :
    left = right ∨ StrictAncestor row array left right ∨
      StrictAncestor row array right left := by
  exact parentTransGen_comparable
    (parentFunction := parent row array)
    (fun hParent => parent_some_lt hParent) hLeft hRight

theorem ancestors_comparable {array : BMSArray} {row target left right : Nat}
    (hLeft : isAncestor array row left target = true)
    (hRight : isAncestor array row right target = true) :
    left = right ∨ isAncestor array row right left = true ∨
      isAncestor array row left right = true := by
  have hComparable := strictAncestor_comparable
    (isAncestor_iff_strictAncestor.mp hLeft)
    (isAncestor_iff_strictAncestor.mp hRight)
  rcases hComparable with hEqual | hRightOfLeft | hLeftOfRight
  · exact Or.inl hEqual
  · exact Or.inr (Or.inl (isAncestor_iff_strictAncestor.mpr hRightOfLeft))
  · exact Or.inr (Or.inr (isAncestor_iff_strictAncestor.mpr hLeftOfRight))

theorem ancestor_of_common_target_of_le {array : BMSArray}
    {row target earlier later : Nat}
    (hEarlier : isAncestor array row earlier target = true)
    (hLater : isAncestor array row later target = true)
    (hOrder : earlier ≤ later) :
    earlier = later ∨ isAncestor array row earlier later = true := by
  rcases ancestors_comparable hEarlier hLater with hEqual | hLaterAncestor | hEarlierAncestor
  · exact Or.inl hEqual
  · have hLt := isAncestor_lt hLaterAncestor
    omega
  · exact Or.inr hEarlierAncestor

/-- 已知中间列是目标的 ancestor 时，更早列到目标等价于到该中间列。 -/
theorem isAncestor_iff_of_intermediate {array : BMSArray}
    {row earlier middle target : Nat}
    (hOrder : earlier < middle)
    (hMiddle : isAncestor array row middle target = true) :
    isAncestor array row earlier target = true ↔
      isAncestor array row earlier middle = true := by
  constructor
  · intro hEarlier
    rcases ancestor_of_common_target_of_le hEarlier hMiddle
        (Nat.le_of_lt hOrder) with hEqual | hAncestor
    · omega
    · exact hAncestor
  · intro hEarlier
    exact isAncestor_trans hEarlier hMiddle

/-- 同时是目标列所有较低行 ancestor 的列；对应 Hunter Lemma 2.5 证明中的集合 `I`。 -/
def AncestorBelow (array : BMSArray) (row candidate target : Nat) : Prop :=
  ∀ lowerRow, lowerRow < row → isAncestor array lowerRow candidate target = true

theorem ancestorBelow_of_isAncestor {array : BMSArray}
    {row candidate target : Nat}
    (hAncestor : isAncestor array row candidate target = true) :
    AncestorBelow array row candidate target := by
  intro lowerRow hLower
  exact isAncestor_of_lt_row hLower hAncestor

/-- 当前行的合格 parent 候选自动属于论文的集合 `I`。 -/
theorem ancestorBelow_of_parentEligible {array : BMSArray}
    {row candidate target : Nat}
    (hEligible : parentEligible row array target candidate = true) :
    AncestorBelow array row candidate target := by
  cases row with
  | zero =>
      intro lowerRow hLower
      omega
  | succ lowerRow =>
      have hAtLower := parentEligible_succ_isAncestor hEligible
      intro row hRow
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hRow) with hEqual | hStrict
      · subst row
        exact hAtLower
      · exact isAncestor_of_lt_row hStrict hAtLower

theorem parentEligible_of_ancestorBelow_of_entryLess {array : BMSArray}
    {row candidate target : Nat}
    (hBelow : AncestorBelow array row candidate target)
    (hEntryLess : entryLess array row candidate target = true) :
    parentEligible row array target candidate = true := by
  cases row with
  | zero =>
      simpa [parentEligible, entryLess] using hEntryLess
  | succ lowerRow =>
      have hAncestor := hBelow lowerRow (by omega)
      simpa [parentEligible, entryLess, hAncestor] using hEntryLess

theorem ancestorBelow_comparable {array : BMSArray}
    {row target left right lowerRow : Nat}
    (hLeft : AncestorBelow array row left target)
    (hRight : AncestorBelow array row right target)
    (hLower : lowerRow < row) :
    left = right ∨ isAncestor array lowerRow right left = true ∨
      isAncestor array lowerRow left right = true :=
  ancestors_comparable (hLeft lowerRow hLower) (hRight lowerRow hLower)

/-- 集合 `I` 中较早的列在每个低行都是较晚列的 ancestor。 -/
theorem ancestorBelow_of_common_target_of_lt {array : BMSArray}
    {row target earlier later : Nat}
    (hEarlier : AncestorBelow array row earlier target)
    (hLater : AncestorBelow array row later target)
    (hOrder : earlier < later) :
    AncestorBelow array row earlier later := by
  intro lowerRow hLower
  rcases ancestorBelow_comparable hEarlier hLater hLower with
    hEqual | hLaterAncestor | hEarlierAncestor
  · omega
  · have hReverse := isAncestor_lt hLaterAncestor
    omega
  · exact hEarlierAncestor

/-- 若一个固定候选在到达目标前始终合格，则 parent 链必定经过它。 -/
theorem isAncestor_of_persistent_parentEligible {array : BMSArray}
    {row earlier target : Nat}
    (hTarget : target < array.length)
    (hOrder : earlier < target)
    (hEligible : ∀ current, earlier < current → current ≤ target →
      parentEligible row array current earlier = true) :
    isAncestor array row earlier target = true := by
  induction target using Nat.strongRecOn with
  | ind target ih =>
      rcases exists_parent_of_eligible hTarget hOrder
          (hEligible target hOrder (Nat.le_refl target)) with
        ⟨found, hParent, hEarlierLe⟩
      have hFoundTarget := parent_some_lt hParent
      rcases Nat.eq_or_lt_of_le hEarlierLe with hEqual | hEarlierFound
      · subst found
        exact direct_parent_isAncestor hParent
      · have hFoundValid : found < array.length :=
          Nat.lt_trans hFoundTarget hTarget
        have hEarlierAncestorFound := ih found hFoundTarget hFoundValid
          hEarlierFound (fun current hEarlierCurrent hCurrentFound =>
            hEligible current hEarlierCurrent
              (Nat.le_trans hCurrentFound (Nat.le_of_lt hFoundTarget)))
        exact isAncestor_trans hEarlierAncestorFound
          (direct_parent_isAncestor hParent)

/-- 只需在目标的当前行 ancestor 段上保持候选合格，parent 链仍必经过该候选。 -/
theorem isAncestor_of_parentEligible_on_ancestor_segment {array : BMSArray}
    {row earlier target : Nat}
    (hTarget : target < array.length)
    (hOrder : earlier < target)
    (hEligible : ∀ current, earlier < current →
      (current = target ∨ isAncestor array row current target = true) →
      parentEligible row array current earlier = true) :
    isAncestor array row earlier target = true := by
  have hSegment : ∀ current, current < array.length → earlier < current →
      (current = target ∨ isAncestor array row current target = true) →
      isAncestor array row earlier current = true := by
    intro current
    induction current using Nat.strongRecOn with
    | ind current ih =>
        intro hCurrentValid hEarlierCurrent hCurrentSegment
        rcases exists_parent_of_eligible hCurrentValid hEarlierCurrent
            (hEligible current hEarlierCurrent hCurrentSegment) with
          ⟨found, hParent, hEarlierLe⟩
        have hFoundCurrent := parent_some_lt hParent
        rcases Nat.eq_or_lt_of_le hEarlierLe with hEqual | hEarlierFound
        · subst found
          exact direct_parent_isAncestor hParent
        · have hFoundSegment : found = target ∨
              isAncestor array row found target = true := by
            rcases hCurrentSegment with rfl | hCurrentAncestor
            · exact Or.inr (direct_parent_isAncestor hParent)
            · exact Or.inr (isAncestor_trans
                (direct_parent_isAncestor hParent) hCurrentAncestor)
          have hEarlierAncestorFound := ih found hFoundCurrent
            (Nat.lt_trans hFoundCurrent hCurrentValid) hEarlierFound hFoundSegment
          exact isAncestor_trans hEarlierAncestorFound
            (direct_parent_isAncestor hParent)
  exact hSegment target hTarget hOrder (Or.inl rfl)

/--
若 `earlier` 已在当前行 ancestor 链上，则集合 `I` 中位于它右侧的列在当前行
也具有严格更大的坐标。这是论文“首列坐标小于 `I` 中其后各列”的精确形式。
-/
theorem entry_lt_of_strictAncestor_of_ancestorBelow_between
    {array : BMSArray} {row target earlier candidate earlierValue candidateValue : Nat}
    (hAncestor : StrictAncestor row array target earlier)
    (hCandidateBelow : AncestorBelow array row candidate target)
    (hEarlierCandidate : earlier < candidate)
    (hCandidateTarget : candidate < target)
    (hEarlierEntry : entry? array earlier row = some earlierValue)
    (hCandidateEntry : entry? array candidate row = some candidateValue) :
    earlierValue < candidateValue := by
  unfold StrictAncestor ParentEdge at hAncestor
  induction hAncestor generalizing candidate earlierValue candidateValue with
  | single hParent =>
      rcases parent_some_entry_lt hParent with
        ⟨foundValue, targetValue, hFoundEntry, hTargetEntry, hFoundLt⟩
      have hFoundValue : foundValue = earlierValue := by
        rw [hEarlierEntry] at hFoundEntry
        exact Option.some.inj hFoundEntry.symm
      subst foundValue
      apply Nat.lt_of_not_ge
      intro hCandidateLe
      have hEntryLess : entryLess array row candidate target = true := by
        unfold entryLess
        rw [hCandidateEntry, hTargetEntry]
        simp
        omega
      have hEligible := parentEligible_of_ancestorBelow_of_entryLess
        hCandidateBelow hEntryLess
      have hCandidateLeEarlier := parent_some_isGreatest hParent candidate
        hCandidateTarget hEligible
      omega
  | tail path hParent ih =>
      rename_i middle finish
      rcases parent_some_entry_lt hParent with
        ⟨foundValue, middleValue, hFoundEntry, hMiddleEntry, hFoundLt⟩
      have hFoundValue : foundValue = earlierValue := by
        rw [hEarlierEntry] at hFoundEntry
        exact Option.some.inj hFoundEntry.symm
      subst foundValue
      have hMiddleAncestor : isAncestor array row middle target = true :=
        isAncestor_iff_strictAncestor.mpr path
      have hMiddleBelow := ancestorBelow_of_isAncestor hMiddleAncestor
      rcases Nat.lt_trichotomy candidate middle with
        hCandidateMiddle | hEqual | hMiddleCandidate
      · apply Nat.lt_of_not_ge
        intro hCandidateLe
        have hCandidateBelowMiddle := ancestorBelow_of_common_target_of_lt
          hCandidateBelow hMiddleBelow hCandidateMiddle
        have hEntryLess : entryLess array row candidate middle = true := by
          unfold entryLess
          rw [hCandidateEntry, hMiddleEntry]
          simp
          omega
        have hEligible := parentEligible_of_ancestorBelow_of_entryLess
          hCandidateBelowMiddle hEntryLess
        have hCandidateLeEarlier := parent_some_isGreatest hParent candidate
          hCandidateMiddle hEligible
        omega
      · subst candidate
        rw [hMiddleEntry] at hCandidateEntry
        have hValues : candidateValue = middleValue :=
          Option.some.inj hCandidateEntry.symm
        omega
      · exact Nat.lt_trans hFoundLt
          (ih hCandidateBelow hMiddleCandidate hCandidateTarget
            hMiddleEntry hCandidateEntry)

theorem entry_lt_of_ancestor_of_ancestorBelow_between
    {array : BMSArray} {row target earlier candidate earlierValue candidateValue : Nat}
    (hAncestor : isAncestor array row earlier target = true)
    (hCandidateBelow : AncestorBelow array row candidate target)
    (hEarlierCandidate : earlier < candidate)
    (hCandidateTarget : candidate < target)
    (hEarlierEntry : entry? array earlier row = some earlierValue)
    (hCandidateEntry : entry? array candidate row = some candidateValue) :
    earlierValue < candidateValue :=
  entry_lt_of_strictAncestor_of_ancestorBelow_between
    (isAncestor_iff_strictAncestor.mp hAncestor) hCandidateBelow
    hEarlierCandidate hCandidateTarget hEarlierEntry hCandidateEntry

/-- 当前行 ancestor 与集合 `I` 中位于其右侧的列之间不会出现 ancestry 缺口。 -/
theorem isAncestor_of_ancestorBelow_between {array : BMSArray}
    {row target earlier candidate : Nat}
    (hEarlierAncestor : isAncestor array row earlier target = true)
    (hCandidateBelow : AncestorBelow array row candidate target)
    (hEarlierCandidate : earlier < candidate)
    (hCandidateTarget : candidate < target)
    (hCandidateEntryExists : ∃ candidateValue,
      entry? array candidate row = some candidateValue) :
    isAncestor array row earlier candidate = true := by
  rcases ancestor_entries_lt hEarlierAncestor with
    ⟨earlierValue, targetValue, hEarlierEntry, hTargetEntry, hEarlierTargetValue⟩
  have hEarlierBelow := ancestorBelow_of_isAncestor hEarlierAncestor
  have hTargetValid : target < array.length := by
    unfold entry? at hTargetEntry
    cases hTargetColumn : array[target]? with
    | none => simp [hTargetColumn] at hTargetEntry
    | some targetColumn =>
        exact (List.getElem?_eq_some_iff.mp hTargetColumn).1
  have hCandidateValid : candidate < array.length :=
    Nat.lt_trans hCandidateTarget hTargetValid
  let candidateColumn := candidate
  apply isAncestor_of_parentEligible_on_ancestor_segment (target := candidateColumn)
    hCandidateValid hEarlierCandidate
  intro current hEarlierCurrent hCurrentSegment
  have hCurrentCandidate : current ≤ candidateColumn := by
    rcases hCurrentSegment with rfl | hCurrentAncestor
    · exact Nat.le_refl candidateColumn
    · exact Nat.le_of_lt (isAncestor_lt hCurrentAncestor)
  have hCurrentTarget : current < target :=
    Nat.lt_of_le_of_lt hCurrentCandidate hCandidateTarget
  have hCurrentBelowTarget : AncestorBelow array row current target := by
    rcases hCurrentSegment with rfl | hCurrentAncestor
    · exact hCandidateBelow
    · intro lowerRow hLower
      exact isAncestor_trans
        (isAncestor_of_lt_row hLower hCurrentAncestor)
        (hCandidateBelow lowerRow hLower)
  have hEarlierBelowCurrent := ancestorBelow_of_common_target_of_lt
    hEarlierBelow hCurrentBelowTarget hEarlierCurrent
  rcases hCurrentSegment with rfl | hCurrentAncestor
  · rcases hCandidateEntryExists with ⟨candidateValue, hCandidateEntry⟩
    have hValueLt := entry_lt_of_ancestor_of_ancestorBelow_between
      hEarlierAncestor hCandidateBelow hEarlierCandidate hCandidateTarget
      hEarlierEntry hCandidateEntry
    apply parentEligible_of_ancestorBelow_of_entryLess hEarlierBelowCurrent
    simp [entryLess, hEarlierEntry, hCandidateEntry, hValueLt]
  · rcases ancestor_entries_lt hCurrentAncestor with
      ⟨currentValue, candidateValue, hCurrentEntry, hCandidateEntry, hCurrentLt⟩
    have hValueLt := entry_lt_of_ancestor_of_ancestorBelow_between
      hEarlierAncestor hCurrentBelowTarget hEarlierCurrent hCurrentTarget
      hEarlierEntry hCurrentEntry
    apply parentEligible_of_ancestorBelow_of_entryLess hEarlierBelowCurrent
    simp [entryLess, hEarlierEntry, hCurrentEntry, hValueLt]

/--
在当前行坐标处处有定义时，ancestor 等价于：属于低行集合 `I`，并且其当前行坐标
是从自身到目标之间 `I` 上的严格记录最小值。
-/
theorem isAncestor_iff_ancestorBelow_and_recordMinimum
    {array : BMSArray} {row ancestor target : Nat}
    (hTarget : target < array.length)
    (hDefined : ∀ column, column < array.length →
      ∃ value, entry? array column row = some value) :
    isAncestor array row ancestor target = true ↔
      ancestor < target ∧ AncestorBelow array row ancestor target ∧
        entryLess array row ancestor target = true ∧
        ∀ middle, ancestor < middle → middle < target →
          AncestorBelow array row middle target →
          entryLess array row ancestor middle = true := by
  constructor
  · intro hAncestor
    have hOrder := isAncestor_lt hAncestor
    have hBelow := ancestorBelow_of_isAncestor hAncestor
    rcases ancestor_entries_lt hAncestor with
      ⟨ancestorValue, targetValue, hAncestorEntry, hTargetEntry, hValueLt⟩
    refine ⟨hOrder, hBelow, ?_, ?_⟩
    · simp [entryLess, hAncestorEntry, hTargetEntry, hValueLt]
    · intro middle hAncestorMiddle hMiddleTarget hMiddleBelow
      rcases hDefined middle (Nat.lt_trans hMiddleTarget hTarget) with
        ⟨middleValue, hMiddleEntry⟩
      have hAncestorMiddleValue :=
        entry_lt_of_ancestor_of_ancestorBelow_between hAncestor hMiddleBelow
          hAncestorMiddle hMiddleTarget hAncestorEntry hMiddleEntry
      simp [entryLess, hAncestorEntry, hMiddleEntry, hAncestorMiddleValue]
  · rintro ⟨hOrder, hBelow, hEntryLess, hRecord⟩
    apply isAncestor_of_parentEligible_on_ancestor_segment hTarget hOrder
    intro current hAncestorCurrent hSegment
    rcases hSegment with rfl | hCurrentAncestor
    · exact parentEligible_of_ancestorBelow_of_entryLess hBelow hEntryLess
    · have hCurrentTarget := isAncestor_lt hCurrentAncestor
      have hCurrentBelow := ancestorBelow_of_isAncestor hCurrentAncestor
      have hAncestorBelowCurrent := ancestorBelow_of_common_target_of_lt
        hBelow hCurrentBelow hAncestorCurrent
      exact parentEligible_of_ancestorBelow_of_entryLess
        hAncestorBelowCurrent
        (hRecord current hAncestorCurrent hCurrentTarget hCurrentBelow)

theorem ancestorBelow_comparable_of_pos {array : BMSArray}
    {row target left right : Nat} (hRow : 0 < row)
    (hLeft : AncestorBelow array row left target)
    (hRight : AncestorBelow array row right target) :
    left = right ∨ isAncestor array (row - 1) right left = true ∨
      isAncestor array (row - 1) left right = true := by
  exact ancestorBelow_comparable hLeft hRight (by omega)

end BMS
end YesMetaZFC
