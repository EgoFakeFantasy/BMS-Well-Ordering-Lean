import YesMetaZFC.BMS.Decomposition

/-!
# BM4 expansion 顺序的前缀基础

本文件开始形式化 Hunter Lemma 2.1–2.3。零号 expansion 是规范的
“删除末列”操作；因此连续零号 expansion 给出有限前缀路径。
-/

namespace YesMetaZFC
namespace BMS

namespace ValidArray

/-- 零号 expansion 的原数组是删末列后的规范化前缀。 -/
theorem raw_expand_zero (array : ValidArray) :
    (array.expand 0).raw =
      trimZeroRows (array.raw.take (array.raw.length - 1)) := by
  rw [ValidArray.raw_expand]
  exact ExpansionContext.expand_zero_eq_trimmed_take_pred array.raw

/-- 零号 expansion 恰好减少一列。 -/
theorem length_expand_zero (array : ValidArray) :
    (array.expand 0).raw.length = array.raw.length - 1 := by
  rw [array.raw_expand_zero, length_trimZeroRows, List.length_take]
  exact Nat.min_eq_left (Nat.sub_le _ _)

/-- 非空数组的零号 expansion 是一条严格 BM4 下降边。 -/
theorem step_expand_zero_of_pos (array : ValidArray)
    (hLength : 0 < array.raw.length) :
    Step (array.expand 0) array := by
  refine ⟨⟨0, rfl⟩, ?_⟩
  intro hEqual
  have hLengths := congrArg (fun value : ValidArray => value.raw.length) hEqual
  change (array.expand 0).raw.length = array.raw.length at hLengths
  rw [array.length_expand_zero] at hLengths
  omega

end ValidArray

/-- 连续执行 `count` 次零号 expansion。 -/
def zeroIterate : Nat → ValidArray → ValidArray
  | 0, array => array
  | count + 1, array => zeroIterate count (array.expand 0)

@[simp]
theorem zeroIterate_zero (array : ValidArray) : zeroIterate 0 array = array := rfl

@[simp]
theorem zeroIterate_succ (count : Nat) (array : ValidArray) :
    zeroIterate (count + 1) array = zeroIterate count (array.expand 0) := rfl

/-- 连续零号 expansion 后的列数是截断减法。 -/
theorem length_zeroIterate (count : Nat) (array : ValidArray) :
    (zeroIterate count array).raw.length = array.raw.length - count := by
  induction count generalizing array with
  | zero => simp
  | succ count ih =>
      rw [zeroIterate_succ, ih, array.length_expand_zero]
      omega

/-- 连续零号 expansion 的原数组，是一次性取相应列前缀后的规范形。 -/
theorem raw_zeroIterate (count : Nat) (array : ValidArray) :
    (zeroIterate count array).raw =
      trimZeroRows (array.raw.take (array.raw.length - count)) := by
  induction count generalizing array with
  | zero => simp [array.trimmed_eq]
  | succ count ih =>
      rw [zeroIterate_succ, ih, ValidArray.length_expand_zero,
        ValidArray.raw_expand_zero]
      rw [trimZeroRows_take_trimZeroRows]
      congr 1
      rw [List.take_take]
      congr 1
      omega

/-- 同一零号操作的有限迭代可以从外层取出最后一步。 -/
theorem zeroIterate_succ_eq_expand (count : Nat) (array : ValidArray) :
    zeroIterate (count + 1) array = (zeroIterate count array).expand 0 := by
  induction count generalizing array with
  | zero => rfl
  | succ count ih =>
      rw [zeroIterate_succ, ih]
      rfl

/-- 只要还有列可删，每一次零号迭代都是严格下降。 -/
theorem zeroIterate_step {count : Nat} {array : ValidArray}
    (hCount : count < array.raw.length) :
    Step (zeroIterate (count + 1) array) (zeroIterate count array) := by
  rw [show zeroIterate (count + 1) array =
      (zeroIterate count array).expand 0 from
    zeroIterate_succ_eq_expand count array]
  apply ValidArray.step_expand_zero_of_pos
  rw [length_zeroIterate]
  omega

/-- 任意正数次、且未越过空数组的零号迭代给出非空有限下降。 -/
theorem zeroIterate_strictDescent {count : Nat} {array : ValidArray}
    (hPositive : 0 < count) (hCount : count ≤ array.raw.length) :
    StrictDescent (zeroIterate count array) array := by
  induction count with
  | zero => omega
  | succ count ih =>
      cases count with
      | zero =>
          exact Relation.TransGen.single (zeroIterate_step (array := array) (by omega))
      | succ prior =>
          apply Relation.TransGen.tail
          · exact ih (by omega) (by omega)
          · exact zeroIterate_step (array := array) (by omega)

/-- BM4 生成顺序的非严格闭包。 -/
def GeneratedDescentOrEqual (smaller larger : ValidArray) : Prop :=
  smaller = larger ∨ StrictDescent smaller larger

/-- 合法次数的零号迭代总不超过起点。 -/
theorem zeroIterate_descentOrEqual {count : Nat} {array : ValidArray}
    (hCount : count ≤ array.raw.length) :
    GeneratedDescentOrEqual (zeroIterate count array) array := by
  cases count with
  | zero => exact Or.inl rfl
  | succ count =>
      exact Or.inr (zeroIterate_strictDescent (by omega) hCount)

/-- 合法数组的规范列前缀可由精确次数的零号 expansion 到达。 -/
theorem zeroIterate_length_sub_eq_of_raw_eq_take
    {smaller larger : ValidArray}
    (hLength : smaller.raw.length ≤ larger.raw.length)
    (hPrefix : smaller.raw = larger.raw.take smaller.raw.length) :
    zeroIterate (larger.raw.length - smaller.raw.length) larger = smaller := by
  apply ValidArray.ext
  rw [raw_zeroIterate]
  have hRemaining : larger.raw.length -
      (larger.raw.length - smaller.raw.length) = smaller.raw.length := by
    omega
  rw [hRemaining, ← hPrefix, smaller.trimmed_eq]

/-- 任意规范列前缀在 BM4 生成顺序中不大于原数组。 -/
theorem descentOrEqual_of_raw_eq_take {smaller larger : ValidArray}
    (hLength : smaller.raw.length ≤ larger.raw.length)
    (hPrefix : smaller.raw = larger.raw.take smaller.raw.length) :
    GeneratedDescentOrEqual smaller larger := by
  rw [← zeroIterate_length_sub_eq_of_raw_eq_take hLength hPrefix]
  apply zeroIterate_descentOrEqual
  omega

/-- `A[n+1]` 连续执行一个复制块长度的零号 expansion，恰好回到 `A[n]`。 -/
theorem ExpansionContext.zeroIterate_expand_succ {array : ValidArray}
    (context : ExpansionContext array) (index : Nat) :
    zeroIterate context.blockLength (array.expand (index + 1)) =
      array.expand index := by
  apply ValidArray.ext
  rw [raw_zeroIterate]
  have hRemaining : (array.expand (index + 1)).raw.length -
      context.blockLength = (array.expand index).raw.length := by
    rw [context.length_expand, context.length_expand]
    rw [show index + 1 + 1 = (index + 1) + 1 by omega, Nat.add_mul]
    omega
  rw [hRemaining, ValidArray.raw_expand array (index + 1)]
  change trimZeroRows
      ((trimZeroRows (expandRaw array.raw (index + 1))).take
        (array.expand index).raw.length) =
    (array.expand index).raw
  rw [trimZeroRows_take_trimZeroRows]
  have hTake :
      (expandRaw array.raw (index + 1)).take
          (array.expand index).raw.length =
        expandRaw array.raw index := by
    rw [context.length_expand index, ← context.length_expandRaw index]
    exact (context.expandRaw_eq_take_succ index).symm
  rw [hTake]
  rfl

/-- 相邻 expansion 在 BM4 生成顺序中可比。 -/
theorem ExpansionContext.expand_succ_descentOrEqual {array : ValidArray}
    (context : ExpansionContext array) (index : Nat) :
    GeneratedDescentOrEqual (array.expand index) (array.expand (index + 1)) := by
  rw [← context.zeroIterate_expand_succ index]
  apply zeroIterate_descentOrEqual
  rw [context.length_expand]
  rw [show index + 1 + 1 = (index + 1) + 1 by omega, Nat.add_mul]
  omega

/-- BM4 生成顺序的非严格版本具有传递性。 -/
theorem GeneratedDescentOrEqual.trans {first second third : ValidArray}
    (hFirstSecond : GeneratedDescentOrEqual first second)
    (hSecondThird : GeneratedDescentOrEqual second third) :
    GeneratedDescentOrEqual first third := by
  rcases hFirstSecond with hEqual | hDescent
  · subst first
    exact hSecondThird
  rcases hSecondThird with hEqual | hPrior
  · subst second
    exact Or.inr hDescent
  · exact Or.inr (Relation.TransGen.trans hPrior hDescent)

/-- 一条允许退化的 expansion 边总是相等或严格下降。 -/
theorem descentOrEqual_of_expansionEdge {larger smaller : ValidArray}
    (edge : ExpansionEdge larger smaller) :
    GeneratedDescentOrEqual smaller larger := by
  by_cases hEqual : smaller = larger
  · exact Or.inl hEqual
  · exact Or.inr (Relation.TransGen.single ⟨edge, hEqual⟩)

/-- 任意有限 expansion 路径的终点都不大于起点。 -/
theorem descentOrEqual_of_expansionPath {larger smaller : ValidArray}
    (path : ExpansionPath larger smaller) :
    GeneratedDescentOrEqual smaller larger := by
  induction path with
  | refl => exact Or.inl rfl
  | tail prior edge ih =>
      exact (descentOrEqual_of_expansionEdge edge).trans ih

/-- expansion 索引单调：较小索引的结果在生成顺序中不大于较大索引的结果。 -/
theorem ExpansionContext.expand_mono_descentOrEqual {array : ValidArray}
    (context : ExpansionContext array) {smallerIndex largerIndex : Nat}
    (hIndices : smallerIndex ≤ largerIndex) :
    GeneratedDescentOrEqual (array.expand smallerIndex)
      (array.expand largerIndex) := by
  obtain ⟨difference, rfl⟩ := Nat.exists_eq_add_of_le hIndices
  induction difference with
  | zero => simp [GeneratedDescentOrEqual]
  | succ difference ih =>
      have hPrior : GeneratedDescentOrEqual (array.expand smallerIndex)
          (array.expand (smallerIndex + difference)) := by
        simpa using ih (Nat.le_add_right smallerIndex difference)
      have hAdjacent :=
        context.expand_succ_descentOrEqual (smallerIndex + difference)
      exact hPrior.trans (by simpa [Nat.add_assoc] using hAdjacent)

/-- 不论是否存在 maximal parent，expansion 对索引都在生成顺序中单调。 -/
theorem expand_mono_descentOrEqual (array : ValidArray)
    {smallerIndex largerIndex : Nat} (hIndices : smallerIndex ≤ largerIndex) :
    GeneratedDescentOrEqual (array.expand smallerIndex)
      (array.expand largerIndex) := by
  cases hMaximal : maximalParentRow array.raw with
  | some maximalRow =>
      let context := Classical.choice
        (exists_expansionContext_of_maximalParentRow_eq_some hMaximal)
      exact context.expand_mono_descentOrEqual hIndices
  | none =>
      apply Or.inl
      apply ValidArray.ext
      simp [ValidArray.raw_expand, BMS.expand, expandRaw, hMaximal]

/-- 同一数组的任意两个直接 expansion 在生成顺序中可比。 -/
theorem expand_comparable (array : ValidArray) (firstIndex secondIndex : Nat) :
    array.expand firstIndex = array.expand secondIndex ∨
      StrictDescent (array.expand firstIndex) (array.expand secondIndex) ∨
      StrictDescent (array.expand secondIndex) (array.expand firstIndex) := by
  rcases Nat.lt_trichotomy firstIndex secondIndex with hLess | hEqual | hGreater
  · rcases expand_mono_descentOrEqual array (Nat.le_of_lt hLess) with
      hSame | hDescent
    · exact Or.inl hSame
    · exact Or.inr (Or.inl hDescent)
  · exact Or.inl (congrArg array.expand hEqual)
  · rcases expand_mono_descentOrEqual array (Nat.le_of_lt hGreater) with
      hSame | hDescent
    · exact Or.inl hSame.symm
    · exact Or.inr (Or.inr hDescent)

/-- seed 的右列在每个有效行上都以左列为 parent。 -/
theorem parent_seed_one_of_lt {row height : Nat} (hRow : row < height) :
    parent row (seed height) 1 = some 0 := by
  induction row generalizing height with
  | zero =>
      simp [parent, seed, greatestBelow?, entry?, hRow]
  | succ row ih =>
      have hPrior : row < height := by omega
      have hParent := ih hPrior
      have hParentRaw :
          parent row [List.replicate height 0, List.replicate height 1] 1 =
            some 0 := by
        simpa [seed] using hParent
      simp [parent, seed, greatestBelow?, ancestorChain, entry?, hRow,
        hParentRaw]

/-- seed 最后一列存在 parent 的最大行是最后一行。 -/
theorem maximalParentRow_seed_succ (height : Nat) :
    maximalParentRow (seed (height + 1)) = some height := by
  have hParent := parent_seed_one_of_lt
    (row := height) (height := height + 1) (by omega)
  have hParentRaw :
      parent height
          [List.replicate (height + 1) 0, List.replicate (height + 1) 1] 1 =
        some 0 := by
    simpa [seed] using hParent
  simp [maximalParentRow, seed, greatestBelow?, hParentRaw]

/-- 高一行的 seed 在索引 `1` 处 expansion 后恰好是前一个 seed。 -/
theorem validSeed_succ_expand_one (height : Nat) :
    (validSeed (height + 1)).expand 1 = validSeed height := by
  apply ValidArray.ext
  rw [ValidArray.raw_expand]
  have hMaximal := maximalParentRow_seed_succ height
  have hParent := parent_seed_one_of_lt
    (row := height) (height := height + 1) (by omega)
  have hMaximalRaw : maximalParentRow
      [List.replicate (height + 1) 0, List.replicate (height + 1) 1] =
        some height := by
    simpa [seed] using hMaximal
  have hParentRaw : parent height
      [List.replicate (height + 1) 0, List.replicate (height + 1) 1] 1 =
        some 0 := by
    simpa [seed] using hParent
  let zeroColumn := List.replicate (height + 1) 0
  let oneColumn := List.replicate (height + 1) 1
  let source : BMSArray := [zeroColumn, oneColumn]
  let liftedColumn := List.mapIdx
    (fun row value => if row < height then
      match zeroColumn[row]?, oneColumn[row]? with
      | some firstValue, some lastValue =>
          value + (lastValue - firstValue)
      | _, _ => value
    else value) zeroColumn
  have hLifted : liftedColumn = List.replicate height 1 ++ [0] := by
    apply List.ext_getElem?
    intro row
    simp only [liftedColumn, List.getElem?_mapIdx, zeroColumn, oneColumn,
      List.getElem?_replicate]
    by_cases hBefore : row < height
    · have hWithin : row < height + 1 := by omega
      simp [hBefore, hWithin]
    · by_cases hLast : row = height
      · subst row
        simp
      · have hOutside : ¬ row < height + 1 := by omega
        simp [hBefore, hOutside]
  have hExpanded : expandRaw source 1 = [zeroColumn, liftedColumn] := by
    simp [expandRaw, source, zeroColumn, oneColumn, hMaximalRaw, hParentRaw,
      slice, copyBlock, ascending, isAncestor, liftedColumn, List.range_succ]
    constructor
    · apply List.ext_getElem?
      intro row
      rw [List.getElem?_mapIdx]
      cases hZero : (List.replicate (height + 1) 0)[row]? <;>
        cases hOne : (List.replicate (height + 1) 1)[row]? <;>
          simp
    · rfl
  change trimZeroRows (expandRaw source 1) = seed height
  rw [hExpanded, hLifted]
  simp [trimZeroRows, trimHeight, seed, zeroColumn,
    supportHeight_append_zero, supportHeight_replicate_zero,
    supportHeight_replicate_one]

/-- 相邻 seed 之间存在一条严格的索引 `1` 下降边。 -/
theorem step_validSeed_succ (height : Nat) :
    Step (validSeed height) (validSeed (height + 1)) := by
  refine ⟨⟨1, (validSeed_succ_expand_one height).symm⟩, ?_⟩
  intro hEqual
  have hHeights := congrArg (fun array : ValidArray => trimHeight array.raw) hEqual
  simp [raw_validSeed, seed, trimHeight, supportHeight_replicate_zero,
    supportHeight_replicate_one] at hHeights

/-- 高度严格增大时，seed 在 BM4 生成顺序中严格增大。 -/
theorem validSeed_strictDescent {smallerHeight largerHeight : Nat}
    (hHeights : smallerHeight < largerHeight) :
    StrictDescent (validSeed smallerHeight) (validSeed largerHeight) := by
  obtain ⟨difference, hDifference⟩ :=
    Nat.exists_eq_add_of_le (Nat.le_of_lt hHeights)
  subst largerHeight
  have hPositive : 0 < difference := by omega
  induction difference with
  | zero => omega
  | succ difference ih =>
      cases difference with
      | zero =>
          exact Relation.TransGen.single (step_validSeed_succ smallerHeight)
      | succ prior =>
          have hPrior : StrictDescent (validSeed smallerHeight)
              (validSeed (smallerHeight + (prior + 1))) :=
            ih (by omega) (by omega)
          have hAdjacent : StrictDescent
              (validSeed (smallerHeight + (prior + 1)))
              (validSeed (smallerHeight + (prior + 1 + 1))) := by
            exact Relation.TransGen.single (by
              simpa [Nat.add_assoc] using
                step_validSeed_succ (smallerHeight + (prior + 1)))
          exact Relation.TransGen.trans hAdjacent hPrior

/-- 所有 seed 按高度构成一条链。 -/
theorem validSeed_comparable (firstHeight secondHeight : Nat) :
    validSeed firstHeight = validSeed secondHeight ∨
      StrictDescent (validSeed firstHeight) (validSeed secondHeight) ∨
      StrictDescent (validSeed secondHeight) (validSeed firstHeight) := by
  rcases Nat.lt_trichotomy firstHeight secondHeight with hLess | hEqual | hGreater
  · exact Or.inr (Or.inl (validSeed_strictDescent hLess))
  · exact Or.inl (congrArg validSeed hEqual)
  · exact Or.inr (Or.inr (validSeed_strictDescent hGreater))

/-! ## 有限生成闭包的全局链性 -/

/-- 严格下降链忘掉非退化证明后给出 expansion 路径。 -/
theorem expansionPath_of_strictDescent {smaller larger : ValidArray}
    (descent : StrictDescent smaller larger) :
    ExpansionPath larger smaller := by
  induction descent with
  | single step => exact ExpansionPath.single step.1
  | tail prior step ih => exact .tail ih step.1

/--
有限 expansion 路径若没有回到起点，则可以删去开头的退化边，
暴露第一条严格 `Step`。
-/
theorem ExpansionPath.eq_or_exists_first_step
    {larger smaller : ValidArray} (path : ExpansionPath larger smaller) :
    smaller = larger ∨
      ∃ first, Step first larger ∧ ExpansionPath first smaller := by
  induction path with
  | refl => exact Or.inl rfl
  | @tail middle smaller prior edge ih =>
      rcases ih with hMiddle | ⟨first, hFirst, hRest⟩
      · subst middle
        by_cases hEqual : smaller = larger
        · exact Or.inl hEqual
        · exact Or.inr ⟨smaller, ⟨edge, hEqual⟩, .refl smaller⟩
      · exact Or.inr ⟨first, hFirst, .tail hRest edge⟩

/--
若起点对 `Step` 可达，则从它出发的任意两条有限 expansion 路径的
终点可比。归纳下降发生在两条路径的第一条严格边上。
-/
theorem expansionPath_endpoints_comparable_of_accessible
    {larger : ValidArray} (hAccessible : Acc Step larger) :
    ∀ {first second : ValidArray},
      ExpansionPath larger first → ExpansionPath larger second →
        first = second ∨ StrictDescent first second ∨
          StrictDescent second first := by
  induction hAccessible with
  | intro larger hPredecessor ih =>
      intro first second hFirstPath hSecondPath
      rcases hFirstPath.eq_or_exists_first_step with
        hFirst | ⟨firstRoot, hFirstStep, hFirstRest⟩
      · subst first
        rcases descentOrEqual_of_expansionPath hSecondPath with
          hSecond | hSecondDescent
        · exact Or.inl hSecond.symm
        · exact Or.inr (Or.inr hSecondDescent)
      rcases hSecondPath.eq_or_exists_first_step with
        hSecond | ⟨secondRoot, hSecondStep, hSecondRest⟩
      · subst second
        rcases descentOrEqual_of_expansionPath hFirstPath with
          hFirst | hFirstDescent
        · exact Or.inl hFirst
        · exact Or.inr (Or.inl hFirstDescent)
      rcases hFirstStep.1 with ⟨firstIndex, hFirstRoot⟩
      rcases hSecondStep.1 with ⟨secondIndex, hSecondRoot⟩
      subst firstRoot
      subst secondRoot
      rcases expand_comparable larger firstIndex secondIndex with
        hSame | hOrdered
      · rw [← hSame] at hSecondRest
        exact ih (larger.expand firstIndex) hFirstStep
          hFirstRest hSecondRest
      · rcases hOrdered with hFirstSecond | hSecondFirst
        · have hPathToFirst : ExpansionPath
              (larger.expand secondIndex) (larger.expand firstIndex) :=
            expansionPath_of_strictDescent hFirstSecond
          exact ih (larger.expand secondIndex) hSecondStep
            (hPathToFirst.trans hFirstRest) hSecondRest
        · have hPathToSecond : ExpansionPath
              (larger.expand firstIndex) (larger.expand secondIndex) :=
            expansionPath_of_strictDescent hSecondFirst
          exact ih (larger.expand firstIndex) hFirstStep
            hFirstRest (hPathToSecond.trans hSecondRest)

end BMS
end YesMetaZFC
