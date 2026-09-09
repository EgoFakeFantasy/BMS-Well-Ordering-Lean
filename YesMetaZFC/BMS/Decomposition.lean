import YesMetaZFC.BMS.Generation

/-!
# Lemma 2.5 的复制块坐标

Hunter Lemma 2.5 的五个 ancestry 结论都依赖同一个索引事实：每个 `Bᵢ` 是等长的连续
区间。本文件把“存在最大 parent 行”的非退化 expansion 封装成上下文，并证明这些区间
在参考实现中的准确位置。这里尚不证明五个 ancestry 结论。
-/

namespace YesMetaZFC
namespace BMS

/-- 一次具有非空复制块 `B₀` 的 expansion 所需的全部见证。 -/
structure ExpansionContext (array : ValidArray) where
  lastIndex : Nat
  maximalRow : Nat
  parentColumn : Nat
  array_length : array.raw.length = lastIndex + 1
  maximal_row_eq : maximalParentRow array.raw = some maximalRow
  parent_eq : parent maximalRow array.raw lastIndex = some parentColumn

/-- `maximalParentRow` 成功时，其搜索结果规范地产生 expansion 上下文。 -/
theorem exists_expansionContext_of_maximalParentRow_eq_some
    {array : ValidArray} {maximalRow : Nat}
    (hMaximal : maximalParentRow array.raw = some maximalRow) :
    Nonempty (ExpansionContext array) := by
  unfold maximalParentRow at hMaximal
  split at hMaximal
  next hLength => simp at hMaximal
  next lastIndex hLength =>
    have hParentSome := greatestBelow?_some_satisfies hMaximal
    cases hParent : parent maximalRow array.raw lastIndex with
    | none => simp [hParent] at hParentSome
    | some parentColumn =>
        exact ⟨{
          lastIndex := lastIndex
          maximalRow := maximalRow
          parentColumn := parentColumn
          array_length := hLength
          maximal_row_eq := by simpa [maximalParentRow, hLength] using hMaximal
          parent_eq := hParent }⟩

/-- 删除末尾列并裁剪全零行，不改变保留前缀内部的真 ancestry。 -/
theorem isAncestor_original_of_trimZeroRows_take
    {array : BMSArray} {count row ancestor target : Nat}
    (hCount : count ≤ array.length) (hTarget : target < count)
    (hAncestor : isAncestor (trimZeroRows (array.take count)) row
      ancestor target = true) :
    isAncestor array row ancestor target = true := by
  rcases ancestor_entries_lt hAncestor with
    ⟨_ancestorValue, targetValue, _hAncestorEntry, hTargetEntry, hValueLt⟩
  have hTargetNonzero : targetValue ≠ 0 := by omega
  have hRowTrimmed : row < trimHeight (trimZeroRows (array.take count)) :=
    row_lt_trimHeight_of_entry?_eq_some_of_ne_zero hTargetEntry hTargetNonzero
  have hRow : row < trimHeight (array.take count) := by
    simpa [trimHeight_trimZeroRows] using hRowTrimmed
  have hTakeAncestor : isAncestor (array.take count) row ancestor target = true := by
    rw [← isAncestor_trimZeroRows_of_lt (array.take count) hRow]
    exact hAncestor
  have hTakeLength : (array.take count).length = count := by
    simp [List.length_take, Nat.min_eq_left hCount]
  have hPrefixEq : isAncestor (array.take count) row ancestor target =
      isAncestor array row ancestor target := by
    apply isAncestor_eq_of_entry?_eq_below
    · simpa [hTakeLength] using hTarget
    · exact Nat.lt_of_lt_of_le hTarget hCount
    · intro column hColumn entryRow
      unfold entry?
      rw [List.getElem?_take_of_lt (Nat.lt_of_le_of_lt hColumn hTarget)]
  rwa [hPrefixEq] at hTakeAncestor

namespace ExpansionContext

def goodPart {array : ValidArray} (context : ExpansionContext array) : BMSArray :=
  array.raw.take context.parentColumn

def badPart {array : ValidArray} (context : ExpansionContext array) : BMSArray :=
  slice array.raw context.parentColumn (context.lastIndex - context.parentColumn)

def blockLength {array : ValidArray} (context : ExpansionContext array) : Nat :=
  context.lastIndex - context.parentColumn

def copyStart {array : ValidArray} (context : ExpansionContext array)
    (copyNumber : Nat) : Nat :=
  context.parentColumn + copyNumber * context.blockLength

def copyPosition {array : ValidArray} (context : ExpansionContext array)
    (copyNumber localColumn : Nat) : Nat :=
  context.copyStart copyNumber + localColumn

/-- 一个全局列号是否位于第 `copyNumber` 个复制块中。 -/
def InCopy {array : ValidArray} (context : ExpansionContext array)
    (copyNumber column : Nat) : Prop :=
  context.copyStart copyNumber ≤ column ∧
    column < context.copyStart (copyNumber + 1)

theorem parentColumn_lt_lastIndex {array : ValidArray}
    (context : ExpansionContext array) :
    context.parentColumn < context.lastIndex :=
  parent_some_lt context.parent_eq

theorem blockLength_pos {array : ValidArray} (context : ExpansionContext array) :
    0 < context.blockLength := by
  simp only [blockLength]
  have hParent := context.parentColumn_lt_lastIndex
  omega

@[simp]
theorem length_goodPart {array : ValidArray} (context : ExpansionContext array) :
    context.goodPart.length = context.parentColumn := by
  simp only [goodPart, List.length_take]
  apply Nat.min_eq_left
  rw [context.array_length]
  have hParent := context.parentColumn_lt_lastIndex
  omega

@[simp]
theorem length_badPart {array : ValidArray} (context : ExpansionContext array) :
    context.badPart.length = context.blockLength := by
  simp [badPart, blockLength, slice, List.length_take, List.length_drop,
    context.array_length]
  omega

theorem getElem?_badPart {array : ValidArray} (context : ExpansionContext array)
    {localColumn : Nat} (hLocal : localColumn < context.blockLength) :
    context.badPart[localColumn]? =
      array.raw[context.parentColumn + localColumn]? := by
  unfold badPart slice
  change localColumn < context.lastIndex - context.parentColumn at hLocal
  rw [List.getElem?_take_of_lt hLocal, List.getElem?_drop]

/-- `badPart` 的局部坐标与原数组的全局坐标有相同条目。 -/
theorem entry?_badPart {array : ValidArray} (context : ExpansionContext array)
    {localColumn row : Nat} (hLocal : localColumn < context.blockLength) :
    entry? context.badPart localColumn row =
      entry? array.raw (context.parentColumn + localColumn) row := by
  unfold entry?
  rw [context.getElem?_badPart hLocal]

theorem exists_badPart_entry {array : ValidArray} (context : ExpansionContext array)
    {height localColumn row : Nat}
    (hUniform : UniformHeight height array.raw)
    (hLocal : localColumn < context.blockLength)
    (hRow : row < height) :
    ∃ column value,
      context.badPart[localColumn]? = some column ∧
        column[row]? = some value := by
  have hGlobal : context.parentColumn + localColumn < array.raw.length := by
    rw [context.array_length]
    have hParent := context.parentColumn_lt_lastIndex
    simp only [blockLength] at hLocal
    omega
  let column := array.raw[context.parentColumn + localColumn]
  have hColumn : array.raw[context.parentColumn + localColumn]? = some column :=
    List.getElem?_eq_some_iff.mpr ⟨hGlobal, rfl⟩
  have hBadColumn : context.badPart[localColumn]? = some column := by
    rw [context.getElem?_badPart hLocal, hColumn]
  have hColumnLength : column.length = height :=
    hUniform column (List.getElem_mem hGlobal)
  have hValueIndex : row < column.length := by omega
  let value := column[row]
  have hValue : column[row]? = some value :=
    List.getElem?_eq_some_iff.mpr ⟨hValueIndex, rfl⟩
  exact ⟨column, value, hBadColumn, hValue⟩

theorem expandRaw_eq_blocks {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) :
    expandRaw array.raw index =
      context.goodPart ++
        (List.range (index + 1)).flatMap (fun copyNumber =>
          copyBlock array.raw context.badPart context.maximalRow
            context.parentColumn copyNumber
            (array.raw[context.lastIndex]?.getD [])) := by
  unfold expandRaw
  rw [context.array_length]
  dsimp only
  rw [context.maximal_row_eq]
  dsimp only
  rw [context.parent_eq]
  rfl

@[simp]
theorem length_copyBlock (array block : BMSArray) (m₀ parentColumn copyNumber : Nat)
    (lastColumn : List Nat) :
    (copyBlock array block m₀ parentColumn copyNumber lastColumn).length = block.length := by
  simp [copyBlock]

theorem getElem?_copyBlock (array block : BMSArray)
    (m₀ parentColumn copyNumber localColumn : Nat) (lastColumn : List Nat) :
    (copyBlock array block m₀ parentColumn copyNumber lastColumn)[localColumn]? =
      block[localColumn]?.map (fun column =>
        column.mapIdx fun row value =>
          if ascending array m₀ parentColumn localColumn row then
            match (block.head?.getD [])[row]?, lastColumn[row]? with
            | some firstValue, some lastValue =>
                value + copyNumber * (lastValue - firstValue)
            | _, _ => value
          else
            value) := by
  unfold copyBlock
  dsimp only
  rw [List.getElem?_mapIdx]
  rfl

/-- 一个复制坐标在给定副本中的目标值。 -/
def copiedValue (array block : BMSArray) (m₀ parentColumn copyNumber localColumn row value : Nat)
    (lastColumn : List Nat) : Nat :=
  if ascending array m₀ parentColumn localColumn row then
    match (block.head?.getD [])[row]?, lastColumn[row]? with
    | some firstValue, some lastValue =>
        value + copyNumber * (lastValue - firstValue)
    | _, _ => value
  else
    value

@[simp]
theorem copiedValue_zero (array block : BMSArray)
    (m₀ parentColumn localColumn row value : Nat) (lastColumn : List Nat) :
    copiedValue array block m₀ parentColumn 0 localColumn row value lastColumn = value := by
  unfold copiedValue
  split
  · split <;> simp
  · rfl

theorem value_le_copiedValue (array block : BMSArray)
    (m₀ parentColumn copyNumber localColumn row value : Nat)
    (lastColumn : List Nat) :
    value ≤ copiedValue array block m₀ parentColumn copyNumber
      localColumn row value lastColumn := by
  unfold copiedValue
  split
  · split <;> omega
  · exact Nat.le_refl value

theorem copiedValue_lt_copiedValue_iff
    (array block : BMSArray) (m₀ parentColumn copyNumber : Nat)
    {leftLocal rightLocal row leftValue rightValue : Nat} (lastColumn : List Nat)
    (hAscending : ascending array m₀ parentColumn leftLocal row =
      ascending array m₀ parentColumn rightLocal row) :
    copiedValue array block m₀ parentColumn copyNumber leftLocal row leftValue lastColumn <
        copiedValue array block m₀ parentColumn copyNumber rightLocal row rightValue lastColumn ↔
      leftValue < rightValue := by
  unfold copiedValue
  rw [hAscending]
  by_cases hRightAscending : ascending array m₀ parentColumn rightLocal row = true
  · simp only [hRightAscending, ↓reduceIte]
    cases hFirst : (block.head?.getD [])[row]? <;>
      cases hLast : lastColumn[row]? <;> simp
  · have hFalse : ascending array m₀ parentColumn rightLocal row = false := by
      cases hValue : ascending array m₀ parentColumn rightLocal row
      · rfl
      · exact (hRightAscending hValue).elim
    simp [hFalse]

theorem ascending_of_ancestor_of_ascending
    (array : BMSArray) (m₀ parentColumn : Nat)
    {row candidateLocal targetLocal : Nat}
    (hAncestor : isAncestor array row
      (parentColumn + candidateLocal) (parentColumn + targetLocal) = true)
    (hTargetAscending : ascending array m₀ parentColumn targetLocal row = true) :
    ascending array m₀ parentColumn candidateLocal row = true := by
  have hCandidateLt : candidateLocal < targetLocal := by
    have hGlobalLt := isAncestor_lt hAncestor
    omega
  have hTargetData : row < m₀ ∧
      (targetLocal = 0 ∨
        isAncestor array row parentColumn (parentColumn + targetLocal) = true) := by
    simpa [ascending] using hTargetAscending
  rcases hTargetData with ⟨hRow, hTargetZero | hParentAncestor⟩
  · omega
  · have hParentLe : parentColumn ≤ parentColumn + candidateLocal := by omega
    rcases ancestor_of_common_target_of_le hParentAncestor hAncestor hParentLe with
      hEqual | hParentOfCandidate
    · have hCandidateZero : candidateLocal = 0 := by omega
      simp [ascending, hRow, hCandidateZero]
    · simp [ascending, hRow, hParentOfCandidate]

theorem ascending_eq_of_ancestor_of_ascending
    (array : BMSArray) (m₀ parentColumn : Nat)
    {row candidateLocal targetLocal : Nat}
    (hAncestor : isAncestor array row
      (parentColumn + candidateLocal) (parentColumn + targetLocal) = true)
    (hTargetAscending : ascending array m₀ parentColumn targetLocal row = true) :
    ascending array m₀ parentColumn candidateLocal row =
      ascending array m₀ parentColumn targetLocal row := by
  rw [hTargetAscending]
  exact ascending_of_ancestor_of_ascending array m₀ parentColumn
    hAncestor hTargetAscending

/-- 同层 ancestor 与目标的 ascending 状态总是一致。 -/
theorem ascending_eq_of_ancestor
    (array : BMSArray) (m₀ parentColumn : Nat)
    {row candidateLocal targetLocal : Nat}
    (hAncestor : isAncestor array row
      (parentColumn + candidateLocal) (parentColumn + targetLocal) = true) :
    ascending array m₀ parentColumn candidateLocal row =
      ascending array m₀ parentColumn targetLocal row := by
  cases hTargetAscending : ascending array m₀ parentColumn targetLocal row with
  | true =>
      have hEqual := ascending_eq_of_ancestor_of_ascending array m₀ parentColumn
        hAncestor hTargetAscending
      rw [hTargetAscending] at hEqual
      exact hEqual
  | false =>
      cases hCandidateAscending :
          ascending array m₀ parentColumn candidateLocal row with
      | false => rfl
      | true =>
          have hCandidateData : row < m₀ ∧
              (candidateLocal = 0 ∨
                isAncestor array row parentColumn
                  (parentColumn + candidateLocal) = true) := by
            simpa [ascending] using hCandidateAscending
          have hFirstAncestor : isAncestor array row parentColumn
              (parentColumn + targetLocal) = true := by
            rcases hCandidateData.2 with hZero | hFirst
            · subst candidateLocal
              simpa using hAncestor
            · exact isAncestor_trans hFirst hAncestor
          have hTargetTrue :
              ascending array m₀ parentColumn targetLocal row = true := by
            simp [ascending, hCandidateData.1, hFirstAncestor]
          rw [hTargetAscending] at hTargetTrue
          simp at hTargetTrue

/-- 集合 `I` 中位于 ascending 目标之前的块内列同样 ascending。 -/
theorem ascending_of_ancestorBelow_of_ascending
    (array : BMSArray) (m₀ parentColumn : Nat)
    {row candidateLocal targetLocal : Nat}
    (hLocalOrder : candidateLocal < targetLocal)
    (hCandidateBelow : AncestorBelow array row
      (parentColumn + candidateLocal) (parentColumn + targetLocal))
    (hCandidateEntry : ∃ candidateValue,
      entry? array (parentColumn + candidateLocal) row = some candidateValue)
    (hTargetAscending : ascending array m₀ parentColumn targetLocal row = true) :
    ascending array m₀ parentColumn candidateLocal row = true := by
  have hTargetData : row < m₀ ∧
      (targetLocal = 0 ∨
        isAncestor array row parentColumn
          (parentColumn + targetLocal) = true) := by
    simpa [ascending] using hTargetAscending
  rcases hTargetData with ⟨hRow, hTargetZero | hFirstAncestor⟩
  · omega
  · by_cases hCandidateZero : candidateLocal = 0
    · simp [ascending, hRow, hCandidateZero]
    · have hFirstCandidate : isAncestor array row parentColumn
          (parentColumn + candidateLocal) = true := by
        apply isAncestor_of_ancestorBelow_between hFirstAncestor hCandidateBelow
        · omega
        · omega
        · exact hCandidateEntry
      simp [ascending, hRow, hFirstCandidate]

theorem getElem?_copyBlock_eq_copiedValue (array block : BMSArray)
    (m₀ parentColumn copyNumber localColumn : Nat) (lastColumn : List Nat) :
    (copyBlock array block m₀ parentColumn copyNumber lastColumn)[localColumn]? =
      block[localColumn]?.map (fun column =>
        column.mapIdx (copiedValue array block m₀ parentColumn copyNumber localColumn · ·
          lastColumn)) := by
  simpa [copiedValue] using
    getElem?_copyBlock array block m₀ parentColumn copyNumber localColumn lastColumn

@[simp]
theorem copyBlock_zero (array block : BMSArray) (m₀ parentColumn : Nat)
    (lastColumn : List Nat) :
    copyBlock array block m₀ parentColumn 0 lastColumn = block := by
  apply List.ext_getElem?
  intro localColumn
  rw [getElem?_copyBlock_eq_copiedValue]
  cases hColumn : block[localColumn]? with
  | none => simp
  | some column =>
      simp only [Option.map_some]
      congr 1
      apply List.ext_getElem?
      intro row
      rw [List.getElem?_mapIdx]
      cases hValue : column[row]? <;> simp

/-- 未裁剪的零号 expansion 恰好删除原数组的最后一列。 -/
theorem expandRaw_zero_eq_take_pred (array : BMSArray) :
    expandRaw array 0 = array.take (array.length - 1) := by
  cases hLength : array.length with
  | zero =>
      have hEmpty : array = [] := List.eq_nil_of_length_eq_zero hLength
      simp [hEmpty, expandRaw]
  | succ lastIndex =>
      cases hMaximal : maximalParentRow array with
      | none => simp [expandRaw, hLength, hMaximal]
      | some maximalRow =>
          cases hParent : parent maximalRow array lastIndex with
          | none => simp [expandRaw, hLength, hMaximal, hParent]
          | some parentColumn =>
              have hParentLt : parentColumn < lastIndex := parent_some_lt hParent
              rw [expandRaw, hLength]
              simp only [hMaximal, hParent]
              change array.take parentColumn ++
                  (List.range 1).flatMap (fun copyNumber =>
                    copyBlock array
                      (slice array parentColumn (lastIndex - parentColumn))
                      maximalRow parentColumn copyNumber
                      (array[lastIndex]?.getD [])) =
                array.take (lastIndex + 1 - 1)
              simp only [List.range_one, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, copyBlock_zero]
              unfold slice
              rw [← List.take_add]
              have hSum : parentColumn + (lastIndex - parentColumn) =
                  lastIndex := Nat.add_sub_of_le (Nat.le_of_lt hParentLt)
              rw [hSum]
              simp

/-- 零号 expansion 是“删末列后再规范化”。 -/
theorem expand_zero_eq_trimmed_take_pred (array : BMSArray) :
    BMS.expand array 0 = trimZeroRows (array.take (array.length - 1)) := by
  simp [BMS.expand, expandRaw_zero_eq_take_pred]

theorem entry?_copyBlock (array block : BMSArray)
    (m₀ parentColumn copyNumber localColumn row value : Nat) (lastColumn column : List Nat)
    (hColumn : block[localColumn]? = some column)
    (hValue : column[row]? = some value) :
    entry? (copyBlock array block m₀ parentColumn copyNumber lastColumn) localColumn row =
      some (copiedValue array block m₀ parentColumn copyNumber localColumn row value
        lastColumn) := by
  unfold entry?
  rw [getElem?_copyBlock_eq_copiedValue, hColumn]
  simp [hValue]

theorem entry?_copyBlock_of_ascending (array block : BMSArray)
    (m₀ parentColumn copyNumber localColumn row value firstValue lastValue : Nat)
    (lastColumn column : List Nat)
    (hColumn : block[localColumn]? = some column)
    (hValue : column[row]? = some value)
    (hAscending : ascending array m₀ parentColumn localColumn row = true)
    (hFirst : (block.head?.getD [])[row]? = some firstValue)
    (hLast : lastColumn[row]? = some lastValue) :
    entry? (copyBlock array block m₀ parentColumn copyNumber lastColumn) localColumn row =
      some (value + copyNumber * (lastValue - firstValue)) := by
  rw [entry?_copyBlock array block m₀ parentColumn copyNumber localColumn row value
    lastColumn column hColumn hValue]
  simp [copiedValue, hAscending, hFirst, hLast]

/-- 复制块首列在 ascending 行上的坐标公式，以 `entry?` 形式给出。 -/
theorem entry?_copyBlock_first_of_ascending (array block : BMSArray)
    (m₀ parentColumn copyNumber row firstValue lastValue : Nat)
    (lastColumn : List Nat)
    (hFirstEntry : entry? block 0 row = some firstValue)
    (hAscending : ascending array m₀ parentColumn 0 row = true)
    (hLast : lastColumn[row]? = some lastValue) :
    entry? (copyBlock array block m₀ parentColumn copyNumber lastColumn) 0 row =
      some (firstValue + copyNumber * (lastValue - firstValue)) := by
  unfold entry? at hFirstEntry
  cases hColumn : block[0]? with
  | none => simp [hColumn] at hFirstEntry
  | some column =>
      have hValue : column[row]? = some firstValue := by
        simpa [hColumn] using hFirstEntry
      have hHead : (block.head?.getD [])[row]? = some firstValue := by
        rw [List.head?_eq_getElem?, hColumn]
        simpa using hValue
      exact entry?_copyBlock_of_ascending array block m₀ parentColumn copyNumber 0 row
        firstValue firstValue lastValue lastColumn column hColumn hValue hAscending hHead hLast

/-- `entry?` 命中的条目也可从列的默认值表示中读取。 -/
theorem getD_getElem?_of_entry?_eq_some (array : BMSArray)
    {column row value : Nat} (hEntry : entry? array column row = some value) :
    (array[column]?.getD [])[row]? = some value := by
  unfold entry? at hEntry
  cases hColumn : array[column]? with
  | none => simp [hColumn] at hEntry
  | some foundColumn =>
      simpa [hColumn] using hEntry

theorem entry?_copyBlock_of_not_ascending (array block : BMSArray)
    (m₀ parentColumn copyNumber localColumn row value : Nat) (lastColumn column : List Nat)
    (hColumn : block[localColumn]? = some column)
    (hValue : column[row]? = some value)
    (hAscending : ascending array m₀ parentColumn localColumn row = false) :
    entry? (copyBlock array block m₀ parentColumn copyNumber lastColumn) localColumn row =
      some value := by
  rw [entry?_copyBlock array block m₀ parentColumn copyNumber localColumn row value
    lastColumn column hColumn hValue]
  simp [copiedValue, hAscending]

private theorem length_flatMap_copyBlock (array block : BMSArray)
    (m₀ parentColumn copies : Nat) (lastColumn : List Nat) :
    ((List.range copies).flatMap fun copyNumber =>
      copyBlock array block m₀ parentColumn copyNumber lastColumn).length =
      copies * block.length := by
  induction copies with
  | zero => simp
  | succ copies ih =>
      rw [List.range_succ, List.flatMap_append]
      simp [ih, Nat.succ_mul]

private theorem getElem?_flatMap_copyBlock (array block : BMSArray)
    (m₀ parentColumn copies : Nat) (lastColumn : List Nat)
    {copyNumber localColumn : Nat}
    (hCopy : copyNumber < copies) (hLocal : localColumn < block.length) :
    let blocks := (List.range copies).flatMap fun number =>
      copyBlock array block m₀ parentColumn number lastColumn
    blocks[copyNumber * block.length + localColumn]? =
      (copyBlock array block m₀ parentColumn copyNumber lastColumn)[localColumn]? := by
  dsimp only
  induction copies with
  | zero => omega
  | succ copies ih =>
      rw [List.range_succ, List.flatMap_append]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hCopy) with hEarlier | hLast
      · rw [List.getElem?_append_left]
        · exact ih hEarlier
        · rw [length_flatMap_copyBlock]
          have hWithin : copyNumber * block.length + localColumn <
              (copyNumber + 1) * block.length := by
            rw [Nat.add_mul]
            omega
          have hNext : (copyNumber + 1) * block.length ≤ copies * block.length :=
            Nat.mul_le_mul_right block.length (Nat.succ_le_of_lt hEarlier)
          exact Nat.lt_of_lt_of_le hWithin hNext
      · subst copyNumber
        rw [List.getElem?_append_right]
        · rw [length_flatMap_copyBlock]
          simp
        · rw [length_flatMap_copyBlock]
          omega

theorem length_expandRaw {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) :
    (expandRaw array.raw index).length =
      context.parentColumn + (index + 1) * context.blockLength := by
  rw [context.expandRaw_eq_blocks index, List.length_append,
    length_flatMap_copyBlock]
  simp

/-- 相邻 expansion 的未裁剪数组具有精确的列前缀关系。 -/
theorem expandRaw_eq_take_succ {array : ValidArray}
    (context : ExpansionContext array) (index : Nat) :
    expandRaw array.raw index =
      (expandRaw array.raw (index + 1)).take
        (expandRaw array.raw index).length := by
  rw [context.expandRaw_eq_blocks index,
    context.expandRaw_eq_blocks (index + 1)]
  let blockFunction : Nat → BMSArray := fun copyNumber =>
    copyBlock array.raw context.badPart context.maximalRow
      context.parentColumn copyNumber
      (array.raw[context.lastIndex]?.getD [])
  change context.goodPart ++ (List.range (index + 1)).flatMap blockFunction =
    (context.goodPart ++ (List.range (index + 1 + 1)).flatMap blockFunction).take
      (context.goodPart ++ (List.range (index + 1)).flatMap blockFunction).length
  have hBlocks : (List.range (index + 1 + 1)).flatMap blockFunction =
      (List.range (index + 1)).flatMap blockFunction ++ blockFunction (index + 1) := by
    rw [show index + 1 + 1 = (index + 1) + 1 by omega,
      List.range_succ, List.flatMap_append]
    simp
  rw [hBlocks, ← List.append_assoc]
  exact List.take_append_length.symm

theorem getElem?_expandRaw_copy {array : ValidArray}
    (context : ExpansionContext array) {index copyNumber localColumn : Nat}
    (hCopy : copyNumber ≤ index) (hLocal : localColumn < context.blockLength) :
    (expandRaw array.raw index)[context.copyPosition copyNumber localColumn]? =
      (copyBlock array.raw context.badPart context.maximalRow
        context.parentColumn copyNumber
        (array.raw[context.lastIndex]?.getD []))[localColumn]? := by
  rw [context.expandRaw_eq_blocks index]
  rw [List.getElem?_append_right]
  · rw [context.length_goodPart]
    simp only [copyPosition, copyStart]
    have hOffset :
        context.parentColumn + copyNumber * context.blockLength + localColumn -
            context.parentColumn =
          copyNumber * context.blockLength + localColumn := by omega
    rw [hOffset]
    rw [← context.length_badPart] at hLocal ⊢
    exact getElem?_flatMap_copyBlock _ _ _ _ _ _ (by omega) hLocal
  · rw [context.length_goodPart]
    simp only [copyPosition, copyStart]
    omega

theorem getElem?_expandRaw_goodPart {array : ValidArray}
    (context : ExpansionContext array) (index : Nat)
    {column : Nat} (hColumn : column < context.parentColumn) :
    (expandRaw array.raw index)[column]? = array.raw[column]? := by
  rw [context.expandRaw_eq_blocks index]
  rw [List.getElem?_append_left]
  · unfold goodPart
    exact List.getElem?_take_of_lt hColumn
  · simpa using hColumn

theorem getElem?_expandRaw_copy_zero {array : ValidArray}
    (context : ExpansionContext array) (index : Nat)
    {localColumn : Nat} (hLocal : localColumn < context.blockLength) :
    (expandRaw array.raw index)[context.copyPosition 0 localColumn]? =
      array.raw[context.parentColumn + localColumn]? := by
  rw [context.getElem?_expandRaw_copy (Nat.zero_le index) hLocal, copyBlock_zero]
  exact context.getElem?_badPart hLocal

theorem entry?_expandRaw_copy {array : ValidArray}
    (context : ExpansionContext array) {index copyNumber localColumn row : Nat}
    (hCopy : copyNumber ≤ index) (hLocal : localColumn < context.blockLength) :
    entry? (expandRaw array.raw index) (context.copyPosition copyNumber localColumn) row =
      entry? (copyBlock array.raw context.badPart context.maximalRow
        context.parentColumn copyNumber
        (array.raw[context.lastIndex]?.getD [])) localColumn row := by
  unfold entry?
  rw [context.getElem?_expandRaw_copy hCopy hLocal]

theorem entry?_expandRaw_goodPart {array : ValidArray}
    (context : ExpansionContext array) (index : Nat)
    {column row : Nat} (hColumn : column < context.parentColumn) :
    entry? (expandRaw array.raw index) column row = entry? array.raw column row := by
  unfold entry?
  rw [context.getElem?_expandRaw_goodPart index hColumn]

theorem entry?_expandRaw_copy_zero {array : ValidArray}
    (context : ExpansionContext array) (index : Nat)
    {localColumn row : Nat} (hLocal : localColumn < context.blockLength) :
    entry? (expandRaw array.raw index) (context.copyPosition 0 localColumn) row =
      entry? array.raw (context.parentColumn + localColumn) row := by
  unfold entry?
  rw [context.getElem?_expandRaw_copy_zero index hLocal]

theorem entryLess_expandRaw_copy_zero_eq_original {array : ValidArray}
    (context : ExpansionContext array) (index row : Nat)
    {leftLocal rightLocal : Nat}
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength) :
    entryLess (expandRaw array.raw index) row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition 0 rightLocal) =
      entryLess array.raw row (context.parentColumn + leftLocal)
        (context.parentColumn + rightLocal) := by
  unfold entryLess
  rw [context.entry?_expandRaw_copy_zero index hLeftLocal,
    context.entry?_expandRaw_copy_zero index hRightLocal]

/-- 原数组最后一列以前的整个前缀在未裁剪 expansion 中逐项保持。 -/
theorem entry?_expandRaw_eq_of_lt_lastIndex {array : ValidArray}
    (context : ExpansionContext array) (index : Nat)
    {column row : Nat} (hColumn : column < context.lastIndex) :
    entry? (expandRaw array.raw index) column row = entry? array.raw column row := by
  by_cases hGood : column < context.parentColumn
  · exact context.entry?_expandRaw_goodPart index hGood
  · let localColumn := column - context.parentColumn
    have hColumnEq : column = context.parentColumn + localColumn := by
      dsimp only [localColumn]
      omega
    have hLocal : localColumn < context.blockLength := by
      simp only [localColumn, blockLength]
      omega
    have hCopyZero := context.entry?_expandRaw_copy_zero index
      (row := row) hLocal
    simpa [copyPosition, copyStart, hColumnEq] using hCopyZero

/-- 最后一列以前的目标，其 parent 在原数组与未裁剪 expansion 中相同。 -/
theorem parent_expandRaw_eq_of_lt_lastIndex {array : ValidArray}
    (context : ExpansionContext array) (index row : Nat)
    {target : Nat} (hTarget : target < context.lastIndex) :
    parent row (expandRaw array.raw index) target = parent row array.raw target := by
  symm
  apply parent_eq_of_entry?_eq_below
  · rw [context.array_length]
    omega
  · rw [context.length_expandRaw]
    have hLastEq : context.parentColumn + context.blockLength =
        context.lastIndex := by
      simp only [blockLength]
      have hParent := context.parentColumn_lt_lastIndex
      omega
    have hCopies : context.blockLength ≤
        (index + 1) * context.blockLength := by
      simpa using Nat.mul_le_mul_right context.blockLength
        (show 1 ≤ index + 1 by omega)
    omega
  · intro column hColumn entryRow
    symm
    exact context.entry?_expandRaw_eq_of_lt_lastIndex index
      (Nat.lt_of_le_of_lt hColumn hTarget)

/-- 最后一列以前的 ancestry 在原数组与未裁剪 expansion 中相同。 -/
theorem isAncestor_expandRaw_eq_of_lt_lastIndex {array : ValidArray}
    (context : ExpansionContext array) (index row : Nat)
    {ancestor target : Nat} (hTarget : target < context.lastIndex) :
    isAncestor (expandRaw array.raw index) row ancestor target =
      isAncestor array.raw row ancestor target := by
  apply isAncestor_congr_below
  intro column hColumn
  exact context.parent_expandRaw_eq_of_lt_lastIndex index row
    (Nat.lt_of_le_of_lt hColumn hTarget)

/-- 正编号 expansion 的原始结果至少保留到最大 parent 行。 -/
theorem maximalRow_le_trimHeight_expandRaw {array : ValidArray}
    (context : ExpansionContext array) {index : Nat} (hIndex : 0 < index) :
    context.maximalRow ≤ trimHeight (expandRaw array.raw index) := by
  cases hMaximalRow : context.maximalRow with
  | zero => exact Nat.zero_le _
  | succ lowerRow =>
      have hParent : parent (lowerRow + 1) array.raw context.lastIndex =
          some context.parentColumn := by
        simpa [hMaximalRow, Nat.succ_eq_add_one] using context.parent_eq
      have hParentSpec := parent_succ_some_spec
        (row := lowerRow) hParent
      have hAncestor : isAncestor array.raw lowerRow context.parentColumn
          context.lastIndex = true := hParentSpec.2.1
      rcases ancestor_entries_lt hAncestor with
        ⟨firstValue, lastValue, hFirstEntry, hLastEntry, hValueLt⟩
      have hLocal : 0 < context.blockLength := context.blockLength_pos
      have hBadFirst : entry? context.badPart 0 lowerRow = some firstValue := by
        rw [context.entry?_badPart hLocal]
        simpa using hFirstEntry
      have hAscending :
          ascending array.raw (lowerRow + 1) context.parentColumn 0 lowerRow = true := by
        simp [ascending]
      have hLast :
          (array.raw[context.lastIndex]?.getD [])[lowerRow]? = some lastValue :=
        getD_getElem?_of_entry?_eq_some array.raw hLastEntry
      have hCopiedFormula :
          entry? (expandRaw array.raw index) (context.copyPosition 1 0) lowerRow =
            some (firstValue + 1 * (lastValue - firstValue)) := by
        rw [context.entry?_expandRaw_copy (by omega) hLocal]
        rw [hMaximalRow]
        exact entry?_copyBlock_first_of_ascending array.raw context.badPart
          (lowerRow + 1) context.parentColumn 1 lowerRow firstValue lastValue
          (array.raw[context.lastIndex]?.getD []) hBadFirst hAscending hLast
      have hCopiedEntry :
          entry? (expandRaw array.raw index) (context.copyPosition 1 0) lowerRow =
            some lastValue := by
        rw [← show firstValue + 1 * (lastValue - firstValue) = lastValue by omega]
        exact hCopiedFormula
      unfold entry? at hCopiedEntry
      cases hColumn :
          (expandRaw array.raw index)[context.copyPosition 1 0]? with
      | none => simp [hColumn] at hCopiedEntry
      | some expandedColumn =>
          have hRowValue : expandedColumn[lowerRow]? = some lastValue := by
            simpa [hColumn] using hCopiedEntry
          have hNonzero : lastValue ≠ 0 := by omega
          have hSupport : lowerRow < supportHeight expandedColumn :=
            row_lt_supportHeight_of_getElem?_eq_some expandedColumn lowerRow
              lastValue hRowValue hNonzero
          have hMember : expandedColumn ∈ expandRaw array.raw index :=
            List.mem_of_getElem? hColumn
          have hHeight : supportHeight expandedColumn ≤
              trimHeight (expandRaw array.raw index) :=
            supportHeight_le_trimHeight_of_mem hMember
          omega

theorem entryLess_expandRaw_copy_eq_badPart {array : ValidArray}
    (context : ExpansionContext array)
    {index copyNumber leftLocal rightLocal row leftValue rightValue : Nat}
    {leftColumn rightColumn : List Nat}
    (hCopy : copyNumber ≤ index)
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hLeftColumn : context.badPart[leftLocal]? = some leftColumn)
    (hRightColumn : context.badPart[rightLocal]? = some rightColumn)
    (hLeftValue : leftColumn[row]? = some leftValue)
    (hRightValue : rightColumn[row]? = some rightValue)
    (hAscending : ascending array.raw context.maximalRow context.parentColumn leftLocal row =
      ascending array.raw context.maximalRow context.parentColumn rightLocal row) :
    entryLess (expandRaw array.raw index) row
        (context.copyPosition copyNumber leftLocal)
        (context.copyPosition copyNumber rightLocal) =
      entryLess context.badPart row leftLocal rightLocal := by
  have hExpandedLeft :
      entry? (expandRaw array.raw index) (context.copyPosition copyNumber leftLocal) row =
        some (copiedValue array.raw context.badPart context.maximalRow
          context.parentColumn copyNumber leftLocal row leftValue
          (array.raw[context.lastIndex]?.getD [])) := by
    rw [context.entry?_expandRaw_copy hCopy hLeftLocal]
    exact entry?_copyBlock _ _ _ _ _ _ _ _ _ _ hLeftColumn hLeftValue
  have hExpandedRight :
      entry? (expandRaw array.raw index) (context.copyPosition copyNumber rightLocal) row =
        some (copiedValue array.raw context.badPart context.maximalRow
          context.parentColumn copyNumber rightLocal row rightValue
          (array.raw[context.lastIndex]?.getD [])) := by
    rw [context.entry?_expandRaw_copy hCopy hRightLocal]
    exact entry?_copyBlock _ _ _ _ _ _ _ _ _ _ hRightColumn hRightValue
  have hSourceLeft : entry? context.badPart leftLocal row = some leftValue := by
    simp [entry?, hLeftColumn, hLeftValue]
  have hSourceRight : entry? context.badPart rightLocal row = some rightValue := by
    simp [entry?, hRightColumn, hRightValue]
  unfold entryLess
  rw [hExpandedLeft, hExpandedRight, hSourceLeft, hSourceRight]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using
    copiedValue_lt_copiedValue_iff array.raw context.badPart context.maximalRow
      context.parentColumn copyNumber (array.raw[context.lastIndex]?.getD []) hAscending

theorem entryLess_expandRaw_copies {array : ValidArray}
    (context : ExpansionContext array)
    {index copyNumber leftLocal rightLocal row leftValue rightValue : Nat}
    {leftColumn rightColumn : List Nat}
    (hCopy : copyNumber ≤ index)
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hLeftColumn : context.badPart[leftLocal]? = some leftColumn)
    (hRightColumn : context.badPart[rightLocal]? = some rightColumn)
    (hLeftValue : leftColumn[row]? = some leftValue)
    (hRightValue : rightColumn[row]? = some rightValue)
    (hAscending : ascending array.raw context.maximalRow context.parentColumn leftLocal row =
      ascending array.raw context.maximalRow context.parentColumn rightLocal row) :
    entryLess (expandRaw array.raw index) row
        (context.copyPosition copyNumber leftLocal)
        (context.copyPosition copyNumber rightLocal) =
      entryLess (expandRaw array.raw index) row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition 0 rightLocal) := by
  rw [context.entryLess_expandRaw_copy_eq_badPart hCopy hLeftLocal hRightLocal
    hLeftColumn hRightColumn hLeftValue hRightValue hAscending]
  symm
  exact context.entryLess_expandRaw_copy_eq_badPart (Nat.zero_le index)
    hLeftLocal hRightLocal hLeftColumn hRightColumn hLeftValue hRightValue hAscending

theorem entryLess_expandRaw_copies_of_uniform {array : ValidArray}
    (context : ExpansionContext array)
    {height index copyNumber leftLocal rightLocal row : Nat}
    (hUniform : UniformHeight height array.raw)
    (hRow : row < height)
    (hCopy : copyNumber ≤ index)
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hAscending : ascending array.raw context.maximalRow context.parentColumn leftLocal row =
      ascending array.raw context.maximalRow context.parentColumn rightLocal row) :
    entryLess (expandRaw array.raw index) row
        (context.copyPosition copyNumber leftLocal)
        (context.copyPosition copyNumber rightLocal) =
      entryLess (expandRaw array.raw index) row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition 0 rightLocal) := by
  rcases context.exists_badPart_entry hUniform hLeftLocal hRow with
    ⟨leftColumn, leftValue, hLeftColumn, hLeftValue⟩
  rcases context.exists_badPart_entry hUniform hRightLocal hRow with
    ⟨rightColumn, rightValue, hRightColumn, hRightValue⟩
  exact context.entryLess_expandRaw_copies hCopy hLeftLocal hRightLocal
    hLeftColumn hRightColumn hLeftValue hRightValue hAscending

theorem parentEligible_zero_expandRaw_copies {array : ValidArray}
    (context : ExpansionContext array)
    {index copyNumber leftLocal rightLocal leftValue rightValue : Nat}
    {leftColumn rightColumn : List Nat}
    (hCopy : copyNumber ≤ index)
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hLeftColumn : context.badPart[leftLocal]? = some leftColumn)
    (hRightColumn : context.badPart[rightLocal]? = some rightColumn)
    (hLeftValue : leftColumn[0]? = some leftValue)
    (hRightValue : rightColumn[0]? = some rightValue)
    (hAscending : ascending array.raw context.maximalRow context.parentColumn leftLocal 0 =
      ascending array.raw context.maximalRow context.parentColumn rightLocal 0) :
    parentEligible 0 (expandRaw array.raw index)
        (context.copyPosition copyNumber rightLocal)
        (context.copyPosition copyNumber leftLocal) =
      parentEligible 0 (expandRaw array.raw index)
        (context.copyPosition 0 rightLocal)
        (context.copyPosition 0 leftLocal) := by
  apply parentEligible_zero_congr_entryLess
  exact context.entryLess_expandRaw_copies hCopy hLeftLocal hRightLocal
    hLeftColumn hRightColumn hLeftValue hRightValue hAscending

theorem parentEligible_succ_expandRaw_copies {array : ValidArray}
    (context : ExpansionContext array)
    {index copyNumber leftLocal rightLocal row leftValue rightValue : Nat}
    {leftColumn rightColumn : List Nat}
    (hCopy : copyNumber ≤ index)
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hLeftColumn : context.badPart[leftLocal]? = some leftColumn)
    (hRightColumn : context.badPart[rightLocal]? = some rightColumn)
    (hLeftValue : leftColumn[row + 1]? = some leftValue)
    (hRightValue : rightColumn[row + 1]? = some rightValue)
    (hAscending : ascending array.raw context.maximalRow context.parentColumn leftLocal
        (row + 1) =
      ascending array.raw context.maximalRow context.parentColumn rightLocal (row + 1))
    (hAncestor : isAncestor (expandRaw array.raw index) row
        (context.copyPosition copyNumber leftLocal)
        (context.copyPosition copyNumber rightLocal) =
      isAncestor (expandRaw array.raw index) row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition 0 rightLocal)) :
    parentEligible (row + 1) (expandRaw array.raw index)
        (context.copyPosition copyNumber rightLocal)
        (context.copyPosition copyNumber leftLocal) =
      parentEligible (row + 1) (expandRaw array.raw index)
        (context.copyPosition 0 rightLocal)
        (context.copyPosition 0 leftLocal) := by
  apply parentEligible_succ_congr_entryLess hAncestor
  exact context.entryLess_expandRaw_copies hCopy hLeftLocal hRightLocal
    hLeftColumn hRightColumn hLeftValue hRightValue hAscending

theorem parentEligible_zero_expandRaw_copies_of_uniform {array : ValidArray}
    (context : ExpansionContext array)
    {height index copyNumber leftLocal rightLocal : Nat}
    (hUniform : UniformHeight height array.raw)
    (hHeight : 0 < height)
    (hCopy : copyNumber ≤ index)
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hAscending : ascending array.raw context.maximalRow context.parentColumn leftLocal 0 =
      ascending array.raw context.maximalRow context.parentColumn rightLocal 0) :
    parentEligible 0 (expandRaw array.raw index)
        (context.copyPosition copyNumber rightLocal)
        (context.copyPosition copyNumber leftLocal) =
      parentEligible 0 (expandRaw array.raw index)
        (context.copyPosition 0 rightLocal)
        (context.copyPosition 0 leftLocal) := by
  apply parentEligible_zero_congr_entryLess
  exact context.entryLess_expandRaw_copies_of_uniform hUniform hHeight hCopy
    hLeftLocal hRightLocal hAscending

theorem parentEligible_succ_expandRaw_copies_of_uniform {array : ValidArray}
    (context : ExpansionContext array)
    {height index copyNumber leftLocal rightLocal row : Nat}
    (hUniform : UniformHeight height array.raw)
    (hRow : row + 1 < height)
    (hCopy : copyNumber ≤ index)
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hAscending : ascending array.raw context.maximalRow context.parentColumn leftLocal
        (row + 1) =
      ascending array.raw context.maximalRow context.parentColumn rightLocal (row + 1))
    (hAncestor : isAncestor (expandRaw array.raw index) row
        (context.copyPosition copyNumber leftLocal)
        (context.copyPosition copyNumber rightLocal) =
      isAncestor (expandRaw array.raw index) row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition 0 rightLocal)) :
    parentEligible (row + 1) (expandRaw array.raw index)
        (context.copyPosition copyNumber rightLocal)
        (context.copyPosition copyNumber leftLocal) =
      parentEligible (row + 1) (expandRaw array.raw index)
        (context.copyPosition 0 rightLocal)
        (context.copyPosition 0 leftLocal) := by
  apply parentEligible_succ_congr_entryLess hAncestor
  exact context.entryLess_expandRaw_copies_of_uniform hUniform hRow hCopy
    hLeftLocal hRightLocal hAscending

theorem entry?_expand_of_lt {array : ValidArray}
    (index column row : Nat)
    (hRow : row < trimHeight (expandRaw array.raw index)) :
    entry? (array.expand index).raw column row =
      entry? (expandRaw array.raw index) column row := by
  rw [ValidArray.raw_expand]
  exact entry?_trimZeroRows_of_lt (expandRaw array.raw index) column row hRow

theorem entryLess_expand_of_lt {array : ValidArray}
    (index left right row : Nat)
    (hRow : row < trimHeight (expandRaw array.raw index)) :
    entryLess (array.expand index).raw row left right =
      entryLess (expandRaw array.raw index) row left right := by
  unfold entryLess
  rw [entry?_expand_of_lt index left row hRow,
    entry?_expand_of_lt index right row hRow]

theorem entryLess_expand_copies_of_uniform {array : ValidArray}
    (context : ExpansionContext array)
    {height index copyNumber leftLocal rightLocal row : Nat}
    (hUniform : UniformHeight height array.raw)
    (hRow : row < trimHeight (expandRaw array.raw index))
    (hCopy : copyNumber ≤ index)
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hAscending : ascending array.raw context.maximalRow context.parentColumn leftLocal row =
      ascending array.raw context.maximalRow context.parentColumn rightLocal row) :
    entryLess (array.expand index).raw row
        (context.copyPosition copyNumber leftLocal)
        (context.copyPosition copyNumber rightLocal) =
      entryLess (array.expand index).raw row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition 0 rightLocal) := by
  rw [entryLess_expand_of_lt index _ _ row hRow,
    entryLess_expand_of_lt index _ _ row hRow]
  apply context.entryLess_expandRaw_copies_of_uniform hUniform
  · exact Nat.lt_of_lt_of_le hRow
      (trimHeight_le_of_uniform (uniformHeight_expandRaw hUniform))
  · exact hCopy
  · exact hLeftLocal
  · exact hRightLocal
  · exact hAscending

/-- 目标坐标不 ascending 时，复制块中的严格比较可反推回第零副本。 -/
theorem entryLess_expand_copy_zero_of_not_ascending {array : ValidArray}
    (context : ExpansionContext array)
    {height index copyNumber leftLocal rightLocal row : Nat}
    (hUniform : UniformHeight height array.raw)
    (hRow : row < trimHeight (expandRaw array.raw index))
    (hCopy : copyNumber ≤ index)
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hRightNotAscending :
      ascending array.raw context.maximalRow context.parentColumn rightLocal row = false)
    (hEntryLess : entryLess (array.expand index).raw row
      (context.copyPosition copyNumber leftLocal)
      (context.copyPosition copyNumber rightLocal) = true) :
    entryLess (array.expand index).raw row
      (context.copyPosition 0 leftLocal)
      (context.copyPosition 0 rightLocal) = true := by
  have hSourceRow : row < height := Nat.lt_of_lt_of_le hRow
    (trimHeight_le_of_uniform (uniformHeight_expandRaw hUniform))
  rcases context.exists_badPart_entry hUniform hLeftLocal hSourceRow with
    ⟨leftColumn, leftValue, hLeftColumn, hLeftValue⟩
  rcases context.exists_badPart_entry hUniform hRightLocal hSourceRow with
    ⟨rightColumn, rightValue, hRightColumn, hRightValue⟩
  have hCopiedLeft : entry? (expandRaw array.raw index)
      (context.copyPosition copyNumber leftLocal) row =
      some (copiedValue array.raw context.badPart context.maximalRow
        context.parentColumn copyNumber leftLocal row leftValue
        (array.raw[context.lastIndex]?.getD [])) := by
    rw [context.entry?_expandRaw_copy hCopy hLeftLocal]
    exact entry?_copyBlock _ _ _ _ _ _ _ _ _ _ hLeftColumn hLeftValue
  have hCopiedRight : entry? (expandRaw array.raw index)
      (context.copyPosition copyNumber rightLocal) row = some rightValue := by
    rw [context.entry?_expandRaw_copy hCopy hRightLocal]
    exact entry?_copyBlock_of_not_ascending _ _ _ _ _ _ _ _ _ _
      hRightColumn hRightValue hRightNotAscending
  have hZeroLeft : entry? (expandRaw array.raw index)
      (context.copyPosition 0 leftLocal) row = some leftValue := by
    rw [context.entry?_expandRaw_copy_zero index hLeftLocal,
      ← context.entry?_badPart hLeftLocal]
    simp [entry?, hLeftColumn, hLeftValue]
  have hZeroRight : entry? (expandRaw array.raw index)
      (context.copyPosition 0 rightLocal) row = some rightValue := by
    rw [context.entry?_expandRaw_copy_zero index hRightLocal,
      ← context.entry?_badPart hRightLocal]
    simp [entry?, hRightColumn, hRightValue]
  rw [entryLess_expand_of_lt index _ _ row hRow] at hEntryLess ⊢
  unfold entryLess at hEntryLess ⊢
  rw [hCopiedLeft, hCopiedRight] at hEntryLess
  rw [hZeroLeft, hZeroRight]
  simp at hEntryLess ⊢
  exact Nat.lt_of_le_of_lt
    (value_le_copiedValue array.raw context.badPart context.maximalRow
      context.parentColumn copyNumber leftLocal row leftValue
      (array.raw[context.lastIndex]?.getD [])) hEntryLess

/-- 右端目标不 ascending 时，其任意副本与第零副本具有相同坐标。 -/
theorem entryLess_expand_zero_to_copy_eq_zero_of_not_ascending
    {array : ValidArray} (context : ExpansionContext array)
    {height index copyNumber leftLocal rightLocal row : Nat}
    (hUniform : UniformHeight height array.raw)
    (hRow : row < trimHeight (expandRaw array.raw index))
    (hCopy : copyNumber ≤ index)
    (hRightLocal : rightLocal < context.blockLength)
    (hRightNotAscending : ascending array.raw context.maximalRow
      context.parentColumn rightLocal row = false) :
    entryLess (array.expand index).raw row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition copyNumber rightLocal) =
      entryLess (array.expand index).raw row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition 0 rightLocal) := by
  have hSourceRow : row < height := Nat.lt_of_lt_of_le hRow
    (trimHeight_le_of_uniform (uniformHeight_expandRaw hUniform))
  rcases context.exists_badPart_entry hUniform hRightLocal hSourceRow with
    ⟨rightColumn, rightValue, hRightColumn, hRightValue⟩
  have hCopiedRight : entry? (expandRaw array.raw index)
      (context.copyPosition copyNumber rightLocal) row = some rightValue := by
    rw [context.entry?_expandRaw_copy hCopy hRightLocal]
    exact entry?_copyBlock_of_not_ascending _ _ _ _ _ _ _ _ _ _
      hRightColumn hRightValue hRightNotAscending
  have hZeroRight : entry? (expandRaw array.raw index)
      (context.copyPosition 0 rightLocal) row = some rightValue := by
    rw [context.entry?_expandRaw_copy_zero index hRightLocal,
      ← context.entry?_badPart hRightLocal]
    simp [entry?, hRightColumn, hRightValue]
  rw [entryLess_expand_of_lt index _ _ row hRow,
    entryLess_expand_of_lt index _ _ row hRow]
  unfold entryLess
  rw [hCopiedRight, hZeroRight]

/-- 右端不 ascending 时，把它放在哪个副本都不改变与固定左列的比较。 -/
theorem entryLess_expand_copy_to_copy_eq_same_of_not_ascending
    {array : ValidArray} (context : ExpansionContext array)
    {height index leftCopy rightCopy leftLocal rightLocal row : Nat}
    (hUniform : UniformHeight height array.raw)
    (hRow : row < trimHeight (expandRaw array.raw index))
    (hLeftCopy : leftCopy ≤ index)
    (hRightCopy : rightCopy ≤ index)
    (hRightLocal : rightLocal < context.blockLength)
    (hRightNotAscending : ascending array.raw context.maximalRow
      context.parentColumn rightLocal row = false) :
    entryLess (array.expand index).raw row
        (context.copyPosition leftCopy leftLocal)
        (context.copyPosition rightCopy rightLocal) =
      entryLess (array.expand index).raw row
        (context.copyPosition leftCopy leftLocal)
        (context.copyPosition leftCopy rightLocal) := by
  have hSourceRow : row < height := Nat.lt_of_lt_of_le hRow
    (trimHeight_le_of_uniform (uniformHeight_expandRaw hUniform))
  rcases context.exists_badPart_entry hUniform hRightLocal hSourceRow with
    ⟨rightColumn, rightValue, hRightColumn, hRightValue⟩
  have hRightEntry : entry? (expandRaw array.raw index)
      (context.copyPosition rightCopy rightLocal) row = some rightValue := by
    rw [context.entry?_expandRaw_copy hRightCopy hRightLocal]
    exact entry?_copyBlock_of_not_ascending _ _ _ _ _ _ _ _ _ _
      hRightColumn hRightValue hRightNotAscending
  have hLeftCopyRightEntry : entry? (expandRaw array.raw index)
      (context.copyPosition leftCopy rightLocal) row = some rightValue := by
    rw [context.entry?_expandRaw_copy hLeftCopy hRightLocal]
    exact entry?_copyBlock_of_not_ascending _ _ _ _ _ _ _ _ _ _
      hRightColumn hRightValue hRightNotAscending
  rw [entryLess_expand_of_lt index _ _ row hRow,
    entryLess_expand_of_lt index _ _ row hRow]
  unfold entryLess
  rw [hRightEntry, hLeftCopyRightEntry]

/-- 非 ascending 坐标在最终 expansion 的所有副本中与第零副本逐项相同。 -/
theorem entry?_expand_copy_eq_zero_of_not_ascending
    {array : ValidArray} (context : ExpansionContext array)
    {height index copyNumber localColumn row : Nat}
    (hUniform : UniformHeight height array.raw)
    (hRow : row < trimHeight (expandRaw array.raw index))
    (hCopy : copyNumber ≤ index)
    (hLocal : localColumn < context.blockLength)
    (hNotAscending : ascending array.raw context.maximalRow
      context.parentColumn localColumn row = false) :
    entry? (array.expand index).raw
        (context.copyPosition copyNumber localColumn) row =
      entry? (array.expand index).raw
        (context.copyPosition 0 localColumn) row := by
  have hSourceRow : row < height := Nat.lt_of_lt_of_le hRow
    (trimHeight_le_of_uniform (uniformHeight_expandRaw hUniform))
  rcases context.exists_badPart_entry hUniform hLocal hSourceRow with
    ⟨column, value, hColumn, hValue⟩
  rw [entry?_expand_of_lt index _ row hRow,
    entry?_expand_of_lt index _ row hRow]
  have hCopied : entry? (expandRaw array.raw index)
      (context.copyPosition copyNumber localColumn) row = some value := by
    rw [context.entry?_expandRaw_copy hCopy hLocal]
    exact entry?_copyBlock_of_not_ascending _ _ _ _ _ _ _ _ _ _
      hColumn hValue hNotAscending
  have hZero : entry? (expandRaw array.raw index)
      (context.copyPosition 0 localColumn) row = some value := by
    rw [context.entry?_expandRaw_copy_zero index hLocal,
      ← context.entry?_badPart hLocal]
    simp [entry?, hColumn, hValue]
  rw [hCopied, hZero]

/-- 相邻副本边界的比较精确对应原数组中 `B₀ → C` 的比较。 -/
theorem entryLess_expand_previous_to_next_eq_original {array : ValidArray}
    (context : ExpansionContext array)
    {height index localColumn row : Nat}
    (hUniform : UniformHeight height array.raw)
    (hIndex : 0 < index)
    (hLocal : localColumn < context.blockLength)
    (hRow : row < trimHeight (expandRaw array.raw index))
    (hAscending : ascending array.raw context.maximalRow
      context.parentColumn localColumn row = true) :
    entryLess (array.expand index).raw row
        (context.copyPosition (index - 1) localColumn)
        (context.copyPosition index 0) =
      entryLess array.raw row (context.parentColumn + localColumn)
        context.lastIndex := by
  have hSourceRow : row < height := Nat.lt_of_lt_of_le hRow
    (trimHeight_le_of_uniform (uniformHeight_expandRaw hUniform))
  rcases context.exists_badPart_entry hUniform hLocal hSourceRow with
    ⟨localList, localValue, hLocalList, hLocalValue⟩
  rcases context.exists_badPart_entry hUniform context.blockLength_pos hSourceRow with
    ⟨firstList, firstValue, hFirstList, hFirstValue⟩
  have hLastIndex : context.lastIndex < array.raw.length := by
    rw [context.array_length]
    omega
  rcases exists_entry_of_uniformHeight hUniform hLastIndex hSourceRow with
    ⟨lastValue, hLastEntry⟩
  have hFirstEntry : entry? array.raw context.parentColumn row = some firstValue := by
    have hBadEntry : entry? context.badPart 0 row = some firstValue := by
      simp [entry?, hFirstList, hFirstValue]
    have hBridge := context.entry?_badPart
      (localColumn := 0) (row := row) context.blockLength_pos
    rw [hBadEntry] at hBridge
    simpa using hBridge.symm
  have hAscendingData : row < context.maximalRow ∧
      (localColumn = 0 ∨ isAncestor array.raw row context.parentColumn
        (context.parentColumn + localColumn) = true) := by
    simpa [ascending] using hAscending
  have hFirstAncestor : isAncestor array.raw row context.parentColumn
      context.lastIndex = true := by
    have hAtMaximal := direct_parent_isAncestor context.parent_eq
    exact isAncestor_of_lt_row
      hAscendingData.1 hAtMaximal
  rcases ancestor_entries_lt hFirstAncestor with
    ⟨firstValue', lastValue', hFirstEntry', hLastEntry', hFirstLt⟩
  have hFirstValueEq : firstValue' = firstValue := by
    rw [hFirstEntry] at hFirstEntry'
    exact Option.some.inj hFirstEntry'.symm
  have hLastValueEq : lastValue' = lastValue := by
    rw [hLastEntry] at hLastEntry'
    exact Option.some.inj hLastEntry'.symm
  subst firstValue'
  subst lastValue'
  have hLastGetD : (array.raw[context.lastIndex]?.getD [])[row]? = some lastValue :=
    getD_getElem?_of_entry?_eq_some array.raw hLastEntry
  have hFirstBadEntry : entry? context.badPart 0 row = some firstValue := by
    simp [entry?, hFirstList, hFirstValue]
  have hFirstAscending : ascending array.raw context.maximalRow
      context.parentColumn 0 row = true := by
    simp [ascending, hAscendingData.1]
  have hPreviousEntry : entry? (expandRaw array.raw index)
      (context.copyPosition (index - 1) localColumn) row =
      some (localValue + (index - 1) * (lastValue - firstValue)) := by
    rw [context.entry?_expandRaw_copy (by omega) hLocal]
    exact entry?_copyBlock_of_ascending array.raw context.badPart
      context.maximalRow context.parentColumn (index - 1) localColumn row
      localValue firstValue lastValue (array.raw[context.lastIndex]?.getD [])
      localList hLocalList hLocalValue hAscending
      (by
        rw [List.head?_eq_getElem?, hFirstList]
        simpa using hFirstValue)
      hLastGetD
  have hNextEntry : entry? (expandRaw array.raw index)
      (context.copyPosition index 0) row =
      some (firstValue + index * (lastValue - firstValue)) := by
    rw [context.entry?_expandRaw_copy (Nat.le_refl index) context.blockLength_pos]
    exact entry?_copyBlock_first_of_ascending array.raw context.badPart
      context.maximalRow context.parentColumn index row firstValue lastValue
      (array.raw[context.lastIndex]?.getD [])
      hFirstBadEntry hFirstAscending hLastGetD
  have hOriginalLocal : entry? array.raw
      (context.parentColumn + localColumn) row = some localValue := by
    rw [← context.entry?_badPart hLocal]
    simp [entry?, hLocalList, hLocalValue]
  rw [entryLess_expand_of_lt index _ _ row hRow]
  unfold entryLess
  rw [hPreviousEntry, hNextEntry, hOriginalLocal, hLastEntry]
  simp
  have hIndexEq : index - 1 + 1 = index := by omega
  have hMul : index * (lastValue - firstValue) =
      (index - 1) * (lastValue - firstValue) + (lastValue - firstValue) := by
    calc
      index * (lastValue - firstValue) =
          ((index - 1) + 1) * (lastValue - firstValue) :=
        congrArg (fun number => number * (lastValue - firstValue)) hIndexEq.symm
      _ = (index - 1) * (lastValue - firstValue) +
          (lastValue - firstValue) := by
        rw [Nat.add_mul, Nat.one_mul]
  omega

theorem parent_expand_of_lt {array : ValidArray}
    (index target : Nat) {row : Nat}
    (hRow : row < trimHeight (expandRaw array.raw index)) :
    parent row (array.expand index).raw target =
      parent row (expandRaw array.raw index) target := by
  rw [ValidArray.raw_expand]
  exact parent_trimZeroRows_of_lt (expandRaw array.raw index) hRow target

theorem isAncestor_expand_of_lt {array : ValidArray}
    (index ancestor target : Nat) {row : Nat}
    (hRow : row < trimHeight (expandRaw array.raw index)) :
    isAncestor (array.expand index).raw row ancestor target =
      isAncestor (expandRaw array.raw index) row ancestor target := by
  rw [ValidArray.raw_expand]
  exact isAncestor_trimZeroRows_of_lt
    (expandRaw array.raw index) hRow ancestor target

/-- 在裁剪保留的行上，原数组最后一列以前的 ancestry 在最终 expansion 中保持。 -/
theorem isAncestor_expand_eq_original_of_lt_lastIndex {array : ValidArray}
    (context : ExpansionContext array) (index row : Nat)
    {ancestor target : Nat}
    (hRow : row < trimHeight (expandRaw array.raw index))
    (hTarget : target < context.lastIndex) :
    isAncestor (array.expand index).raw row ancestor target =
      isAncestor array.raw row ancestor target := by
  rw [isAncestor_expand_of_lt index ancestor target hRow]
  exact context.isAncestor_expandRaw_eq_of_lt_lastIndex index row hTarget

/-- `ascending` 等价于复制块首列是本列的非严格 ancestor。 -/
theorem ascending_iff_first_nonstrict_ancestor_expand {array : ValidArray}
    (context : ExpansionContext array) (index : Nat)
    {localColumn row : Nat}
    (hLocal : localColumn < context.blockLength)
    (hAscendingRow : row < context.maximalRow)
    (hRow : row < trimHeight (expandRaw array.raw index)) :
    ascending array.raw context.maximalRow context.parentColumn localColumn row = true ↔
      localColumn = 0 ∨
        isAncestor (array.expand index).raw row
          (context.copyPosition 0 0)
          (context.copyPosition 0 localColumn) = true := by
  have hTarget : context.parentColumn + localColumn < context.lastIndex := by
    simp only [blockLength] at hLocal
    omega
  simp only [copyPosition, copyStart]
  simp only [Nat.zero_mul, Nat.add_zero]
  rw [context.isAncestor_expand_eq_original_of_lt_lastIndex index row hRow hTarget]
  simp [ascending, hAscendingRow]

/-- 第零副本内部的 ancestry 就是原数组 `B₀` 区间内的 ancestry。 -/
theorem isAncestor_expand_copy_zero_eq_original {array : ValidArray}
    (context : ExpansionContext array) (index row : Nat)
    {leftLocal rightLocal : Nat}
    (hRightLocal : rightLocal < context.blockLength)
    (hRow : row < trimHeight (expandRaw array.raw index)) :
    isAncestor (array.expand index).raw row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition 0 rightLocal) =
      isAncestor array.raw row
        (context.parentColumn + leftLocal)
        (context.parentColumn + rightLocal) := by
  have hTarget : context.parentColumn + rightLocal < context.lastIndex := by
    simp only [blockLength] at hRightLocal
    omega
  simp only [copyPosition, copyStart, Nat.zero_mul, Nat.add_zero]
  exact context.isAncestor_expand_eq_original_of_lt_lastIndex
    index row hRow hTarget

theorem parent_expand_eq_none_of_le {array : ValidArray}
    (index target : Nat) {row : Nat}
    (hRow : trimHeight (expandRaw array.raw index) ≤ row) :
    parent row (array.expand index).raw target = none := by
  rw [ValidArray.raw_expand]
  exact parent_trimZeroRows_eq_none_of_le (expandRaw array.raw index) hRow target

theorem isAncestor_expand_eq_false_of_le {array : ValidArray}
    (index ancestor target : Nat) {row : Nat}
    (hRow : trimHeight (expandRaw array.raw index) ≤ row) :
    isAncestor (array.expand index).raw row ancestor target = false := by
  rw [ValidArray.raw_expand]
  exact isAncestor_trimZeroRows_eq_false_of_le
    (expandRaw array.raw index) hRow ancestor target

theorem length_expand {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) :
    (array.expand index).raw.length =
    context.parentColumn + (index + 1) * context.blockLength := by
  rw [ValidArray.raw_expand, BMS.length_expand]
  exact context.length_expandRaw index

/-- `A[0]` 恰为原数组末列之前的前缀。 -/
theorem length_expand_zero {array : ValidArray}
    (context : ExpansionContext array) :
    (array.expand 0).raw.length = context.lastIndex := by
  have hParent := context.parentColumn_lt_lastIndex
  rw [context.length_expand]
  simp only [Nat.zero_add, Nat.one_mul, blockLength]
  omega

/-- expansion 索引增大时列数单调不减。 -/
theorem length_expand_mono {array : ValidArray}
    (context : ExpansionContext array) {smallerIndex largerIndex : Nat}
    (hIndices : smallerIndex ≤ largerIndex) :
    (array.expand smallerIndex).raw.length ≤
      (array.expand largerIndex).raw.length := by
  rw [context.length_expand, context.length_expand]
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul_right context.blockLength
    (Nat.succ_le_succ hIndices)

@[simp]
theorem copyPosition_zero {array : ValidArray} (context : ExpansionContext array)
    (localColumn : Nat) :
    context.copyPosition 0 localColumn = context.parentColumn + localColumn := by
  simp [copyPosition, copyStart]

theorem copyPosition_lt_length {array : ValidArray} (context : ExpansionContext array)
    {index copyNumber localColumn : Nat}
    (hCopy : copyNumber ≤ index) (hLocal : localColumn < context.blockLength) :
    context.copyPosition copyNumber localColumn <
      (array.expand index).raw.length := by
  rw [context.length_expand index]
  have hWithin : copyNumber * context.blockLength + localColumn <
      (copyNumber + 1) * context.blockLength := by
    rw [Nat.add_mul]
    omega
  have hNext : (copyNumber + 1) * context.blockLength ≤
      (index + 1) * context.blockLength :=
    Nat.mul_le_mul_right context.blockLength (Nat.succ_le_succ hCopy)
  have hPosition := Nat.lt_of_lt_of_le hWithin hNext
  simpa [copyPosition, copyStart, Nat.add_assoc] using
    Nat.add_lt_add_left hPosition context.parentColumn

theorem copyPosition_in_block {array : ValidArray} (context : ExpansionContext array)
    {copyNumber localColumn : Nat} (hLocal : localColumn < context.blockLength) :
    context.copyStart copyNumber ≤ context.copyPosition copyNumber localColumn ∧
      context.copyPosition copyNumber localColumn < context.copyStart (copyNumber + 1) := by
  simp only [copyPosition, copyStart]
  constructor
  · omega
  · rw [Nat.add_mul]
    omega

theorem copyPosition_injective {array : ValidArray} (context : ExpansionContext array)
    {leftCopy rightCopy leftLocal rightLocal : Nat}
    (hLeft : leftLocal < context.blockLength)
    (hRight : rightLocal < context.blockLength)
    (hEqual : context.copyPosition leftCopy leftLocal =
      context.copyPosition rightCopy rightLocal) :
    leftCopy = rightCopy ∧ leftLocal = rightLocal := by
  have hBlock := context.blockLength_pos
  rcases Nat.lt_trichotomy leftCopy rightCopy with hCopies | hCopies | hCopies
  · have hMul : (leftCopy + 1) * context.blockLength ≤
        rightCopy * context.blockLength :=
      Nat.mul_le_mul_right context.blockLength (Nat.succ_le_of_lt hCopies)
    simp only [copyPosition, copyStart] at hEqual
    rw [Nat.add_mul] at hMul
    omega
  · subst rightCopy
    simp only [copyPosition, copyStart] at hEqual
    exact ⟨rfl, by omega⟩
  · have hMul : (rightCopy + 1) * context.blockLength ≤
        leftCopy * context.blockLength :=
      Nat.mul_le_mul_right context.blockLength (Nat.succ_le_of_lt hCopies)
    simp only [copyPosition, copyStart] at hEqual
    rw [Nat.add_mul] at hMul
    omega

theorem copyPosition_strictMono_copy {array : ValidArray}
    (context : ExpansionContext array) {leftCopy rightCopy localColumn : Nat}
    (hCopies : leftCopy < rightCopy) :
    context.copyPosition leftCopy localColumn <
      context.copyPosition rightCopy localColumn := by
  simp only [copyPosition, copyStart]
  have hProduct := Nat.mul_lt_mul_of_pos_right hCopies context.blockLength_pos
  simpa [Nat.add_assoc] using
    Nat.add_lt_add_left (Nat.add_lt_add_right hProduct localColumn)
      context.parentColumn

/-- `G` 之后的每个合法输出列都有唯一的复制块坐标。 -/
theorem exists_copyPosition_of_not_good {array : ValidArray}
    (context : ExpansionContext array) {index column : Nat}
    (hColumn : column < (array.expand index).raw.length)
    (hNotGood : context.parentColumn ≤ column) :
    ∃ copyNumber localColumn,
      copyNumber ≤ index ∧ localColumn < context.blockLength ∧
        column = context.copyPosition copyNumber localColumn := by
  let offset := column - context.parentColumn
  let copyNumber := offset / context.blockLength
  let localColumn := offset % context.blockLength
  have hColumnEq : column = context.parentColumn + offset := by
    dsimp only [offset]
    omega
  have hOffsetBound : offset < (index + 1) * context.blockLength := by
    rw [context.length_expand] at hColumn
    omega
  have hLocal : localColumn < context.blockLength := by
    dsimp only [localColumn]
    exact Nat.mod_lt offset context.blockLength_pos
  have hCopyLt : copyNumber < index + 1 := by
    dsimp only [copyNumber]
    exact (Nat.div_lt_iff_lt_mul context.blockLength_pos).2 hOffsetBound
  have hDecomposition :
      copyNumber * context.blockLength + localColumn = offset := by
    dsimp only [copyNumber, localColumn]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod offset context.blockLength
  exact ⟨copyNumber, localColumn, by omega, hLocal, by
    simp only [copyPosition, copyStart]
    omega⟩

theorem inCopy_iff_exists_copyPosition {array : ValidArray}
    (context : ExpansionContext array) {copyNumber column : Nat} :
    context.InCopy copyNumber column ↔
      ∃ localColumn, localColumn < context.blockLength ∧
        column = context.copyPosition copyNumber localColumn := by
  constructor
  · rintro ⟨hStart, hEnd⟩
    let localColumn := column - context.copyStart copyNumber
    have hColumnEq : column = context.copyStart copyNumber + localColumn := by
      dsimp only [localColumn]
      omega
    have hNextStart : context.copyStart (copyNumber + 1) =
        context.copyStart copyNumber + context.blockLength := by
      simp only [copyStart, Nat.add_mul]
      omega
    have hLocal : localColumn < context.blockLength := by
      rw [hNextStart, hColumnEq] at hEnd
      omega
    exact ⟨localColumn, hLocal, by
      simp only [copyPosition]
      exact hColumnEq⟩
  · rintro ⟨localColumn, hLocal, rfl⟩
    exact context.copyPosition_in_block hLocal

theorem inCopy_unique {array : ValidArray} (context : ExpansionContext array)
    {leftCopy rightCopy column : Nat}
    (hLeft : context.InCopy leftCopy column)
    (hRight : context.InCopy rightCopy column) :
    leftCopy = rightCopy := by
  rcases context.inCopy_iff_exists_copyPosition.mp hLeft with
    ⟨leftLocal, hLeftLocal, hLeftPosition⟩
  rcases context.inCopy_iff_exists_copyPosition.mp hRight with
    ⟨rightLocal, hRightLocal, hRightPosition⟩
  exact (context.copyPosition_injective hLeftLocal hRightLocal
    (hLeftPosition.symm.trans hRightPosition)).1

theorem column_lt_of_inCopy_of_lt_copy {array : ValidArray}
    (context : ExpansionContext array) {leftCopy rightCopy leftColumn rightColumn : Nat}
    (hCopies : leftCopy < rightCopy)
    (hLeft : context.InCopy leftCopy leftColumn)
    (hRight : context.InCopy rightCopy rightColumn) :
    leftColumn < rightColumn := by
  have hStarts : context.copyStart (leftCopy + 1) ≤
      context.copyStart rightCopy := by
    simp only [copyStart]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right context.blockLength (Nat.succ_le_of_lt hCopies))
      context.parentColumn
  exact Nat.lt_of_lt_of_le hLeft.2 (Nat.le_trans hStarts hRight.1)

theorem copyNumber_le_of_column_lt {array : ValidArray}
    (context : ExpansionContext array)
    {leftCopy rightCopy leftColumn rightColumn : Nat}
    (hLeft : context.InCopy leftCopy leftColumn)
    (hRight : context.InCopy rightCopy rightColumn)
    (hColumns : leftColumn < rightColumn) :
    leftCopy ≤ rightCopy := by
  apply Nat.le_of_not_gt
  intro hReverse
  have := context.column_lt_of_inCopy_of_lt_copy hReverse hRight hLeft
  omega

/-- 复制块中目标的 parent 只能在 `G` 或某个不晚于目标的复制块。 -/
theorem parent_in_good_or_not_later_copy {array : ValidArray}
    (context : ExpansionContext array)
    {index targetCopy localColumn row found : Nat}
    (hTargetCopy : targetCopy ≤ index)
    (hLocal : localColumn < context.blockLength)
    (hParent : parent row (array.expand index).raw
      (context.copyPosition targetCopy localColumn) = some found) :
    found < context.parentColumn ∨
      ∃ foundCopy foundLocal,
        foundCopy ≤ targetCopy ∧ foundLocal < context.blockLength ∧
          found = context.copyPosition foundCopy foundLocal := by
  have hFoundLt := parent_some_lt hParent
  by_cases hGood : found < context.parentColumn
  · exact Or.inl hGood
  · have hTargetLength := context.copyPosition_lt_length hTargetCopy hLocal
    rcases context.exists_copyPosition_of_not_good
        (Nat.lt_trans hFoundLt hTargetLength) (Nat.le_of_not_gt hGood) with
      ⟨foundCopy, foundLocal, hFoundCopy, hFoundLocal, hFoundPosition⟩
    have hFoundInCopy : context.InCopy foundCopy found := by
      rw [hFoundPosition]
      exact context.copyPosition_in_block hFoundLocal
    have hTargetInCopy : context.InCopy targetCopy
        (context.copyPosition targetCopy localColumn) :=
      context.copyPosition_in_block hLocal
    have hCopyOrder := context.copyNumber_le_of_column_lt
      hFoundInCopy hTargetInCopy hFoundLt
    exact Or.inr ⟨foundCopy, foundLocal, hCopyOrder, hFoundLocal, hFoundPosition⟩

/-- 较小 expansion 的全部原始列是较大 expansion 的逐项前缀。 -/
theorem entry?_expandRaw_indices_eq_of_lt_length {array : ValidArray}
    (context : ExpansionContext array)
    {smallerIndex largerIndex column row : Nat}
    (hIndices : smallerIndex ≤ largerIndex)
    (hColumn : column < (array.expand smallerIndex).raw.length) :
    entry? (expandRaw array.raw smallerIndex) column row =
      entry? (expandRaw array.raw largerIndex) column row := by
  by_cases hGood : column < context.parentColumn
  · rw [context.entry?_expandRaw_goodPart smallerIndex hGood,
      context.entry?_expandRaw_goodPart largerIndex hGood]
  · rcases context.exists_copyPosition_of_not_good hColumn
        (Nat.le_of_not_gt hGood) with
      ⟨copyNumber, localColumn, hCopy, hLocal, rfl⟩
    rw [context.entry?_expandRaw_copy hCopy hLocal,
      context.entry?_expandRaw_copy (Nat.le_trans hCopy hIndices) hLocal]

/-- 同一行在两个 expansion 中都未被裁剪时，前缀条目相同。 -/
theorem entry?_expand_indices_eq_of_rows {array : ValidArray}
    (context : ExpansionContext array)
    {smallerIndex largerIndex column row : Nat}
    (hIndices : smallerIndex ≤ largerIndex)
    (hColumn : column < (array.expand smallerIndex).raw.length)
    (hSmallerRow : row < trimHeight (expandRaw array.raw smallerIndex))
    (hLargerRow : row < trimHeight (expandRaw array.raw largerIndex)) :
    entry? (array.expand smallerIndex).raw column row =
      entry? (array.expand largerIndex).raw column row := by
  rw [entry?_expand_of_lt smallerIndex column row hSmallerRow,
    entry?_expand_of_lt largerIndex column row hLargerRow]
  exact context.entry?_expandRaw_indices_eq_of_lt_length hIndices hColumn

/-- 在共同保留行上，较小 expansion 前缀中的 parent 不受后续副本影响。 -/
theorem parent_expand_indices_eq_of_rows {array : ValidArray}
    (context : ExpansionContext array)
    {smallerIndex largerIndex target row : Nat}
    (hIndices : smallerIndex ≤ largerIndex)
    (hTarget : target < (array.expand smallerIndex).raw.length)
    (hSmallerRow : row < trimHeight (expandRaw array.raw smallerIndex))
    (hLargerRow : row < trimHeight (expandRaw array.raw largerIndex)) :
    parent row (array.expand smallerIndex).raw target =
      parent row (array.expand largerIndex).raw target := by
  induction row generalizing target with
  | zero =>
      apply parent_congr_below_target hTarget
        (by
          rw [context.length_expand smallerIndex] at hTarget
          rw [context.length_expand largerIndex]
          have hLength := Nat.mul_le_mul_right context.blockLength
            (Nat.succ_le_succ hIndices)
          exact Nat.lt_of_lt_of_le hTarget
            (Nat.add_le_add_left hLength context.parentColumn))
      intro candidate hCandidate
      apply parentEligible_zero_congr
      · exact context.entry?_expand_indices_eq_of_rows hIndices
          (Nat.lt_trans hCandidate hTarget) hSmallerRow hLargerRow
      · exact context.entry?_expand_indices_eq_of_rows hIndices hTarget
          hSmallerRow hLargerRow
  | succ lowerRow ih =>
      apply parent_congr_below_target hTarget
        (by
          rw [context.length_expand smallerIndex] at hTarget
          rw [context.length_expand largerIndex]
          have hLength := Nat.mul_le_mul_right context.blockLength
            (Nat.succ_le_succ hIndices)
          exact Nat.lt_of_lt_of_le hTarget
            (Nat.add_le_add_left hLength context.parentColumn))
      intro candidate hCandidate
      apply parentEligible_succ_congr
      · apply isAncestor_congr_below
        intro column hColumn
        exact ih (Nat.lt_of_le_of_lt hColumn hTarget)
          (Nat.lt_trans (Nat.lt_succ_self lowerRow) hSmallerRow)
          (Nat.lt_trans (Nat.lt_succ_self lowerRow) hLargerRow)
      · exact context.entry?_expand_indices_eq_of_rows hIndices
          (Nat.lt_trans hCandidate hTarget) hSmallerRow hLargerRow
      · exact context.entry?_expand_indices_eq_of_rows hIndices hTarget
          hSmallerRow hLargerRow

/-- 在共同保留行上，较小 expansion 前缀中的 ancestry 不受后续副本影响。 -/
theorem isAncestor_expand_indices_eq_of_rows {array : ValidArray}
    (context : ExpansionContext array)
    {smallerIndex largerIndex ancestor target row : Nat}
    (hIndices : smallerIndex ≤ largerIndex)
    (hTarget : target < (array.expand smallerIndex).raw.length)
    (hSmallerRow : row < trimHeight (expandRaw array.raw smallerIndex))
    (hLargerRow : row < trimHeight (expandRaw array.raw largerIndex)) :
    isAncestor (array.expand smallerIndex).raw row ancestor target =
      isAncestor (array.expand largerIndex).raw row ancestor target := by
  apply isAncestor_congr_below
  intro column hColumn
  exact context.parent_expand_indices_eq_of_rows hIndices
    (Nat.lt_of_le_of_lt hColumn hTarget) hSmallerRow hLargerRow

/--
若较大 expansion 的 ancestry 目标仍位于较小 expansion 的前缀中，
则该条真 ancestry 可以向下运输到较小 expansion。目标坐标的严格增长
保证其行值非零，因而该行不会在较小 expansion 中被裁掉。
-/
theorem isAncestor_expand_of_le_index {array : ValidArray}
    (context : ExpansionContext array)
    {smallerIndex largerIndex ancestor target row : Nat}
    (hIndices : smallerIndex ≤ largerIndex)
    (hTarget : target < (array.expand smallerIndex).raw.length)
    (hAncestor : isAncestor (array.expand largerIndex).raw row ancestor target = true) :
    isAncestor (array.expand smallerIndex).raw row ancestor target = true := by
  rcases ancestor_entries_lt hAncestor with
    ⟨ancestorValue, targetValue, _hAncestorEntry, hTargetEntry, hValueLt⟩
  have hExpandedUniform := ValidArray.uniformHeight_expand
    (index := largerIndex)
    (rectangular_iff_exists_uniformHeight.mp array.rectangular_eq).choose_spec
  have hLargerRow : row < trimHeight (expandRaw array.raw largerIndex) :=
    row_lt_uniformHeight_of_entry?_eq_some hExpandedUniform hTargetEntry
  have hRawLargerEntry : entry? (expandRaw array.raw largerIndex) target row =
      some targetValue := by
    rw [← entry?_expand_of_lt largerIndex target row hLargerRow]
    exact hTargetEntry
  have hRawSmallerEntry : entry? (expandRaw array.raw smallerIndex) target row =
      some targetValue := by
    rw [context.entry?_expandRaw_indices_eq_of_lt_length hIndices hTarget]
    exact hRawLargerEntry
  have hTargetNonzero : targetValue ≠ 0 := by omega
  have hSmallerRow : row < trimHeight (expandRaw array.raw smallerIndex) :=
    row_lt_trimHeight_of_entry?_eq_some_of_ne_zero
      hRawSmallerEntry hTargetNonzero
  rw [context.isAncestor_expand_indices_eq_of_rows hIndices hTarget
    hSmallerRow hLargerRow]
  exact hAncestor

/-- 较小 expansion 前缀中的真 ancestry 在加入更多复制块后仍为真。 -/
theorem isAncestor_expand_of_ge_index {array : ValidArray}
    (context : ExpansionContext array)
    {smallerIndex largerIndex ancestor target row : Nat}
    (hIndices : smallerIndex ≤ largerIndex)
    (hTarget : target < (array.expand smallerIndex).raw.length)
    (hAncestor : isAncestor (array.expand smallerIndex).raw row ancestor target = true) :
    isAncestor (array.expand largerIndex).raw row ancestor target = true := by
  rcases ancestor_entries_lt hAncestor with
    ⟨_ancestorValue, targetValue, _hAncestorEntry, hTargetEntry, hValueLt⟩
  have hExpandedUniform := ValidArray.uniformHeight_expand
    (index := smallerIndex)
    (rectangular_iff_exists_uniformHeight.mp array.rectangular_eq).choose_spec
  have hSmallerRow : row < trimHeight (expandRaw array.raw smallerIndex) :=
    row_lt_uniformHeight_of_entry?_eq_some hExpandedUniform hTargetEntry
  have hRawSmallerEntry : entry? (expandRaw array.raw smallerIndex) target row =
      some targetValue := by
    rw [← entry?_expand_of_lt smallerIndex target row hSmallerRow]
    exact hTargetEntry
  have hRawLargerEntry : entry? (expandRaw array.raw largerIndex) target row =
      some targetValue := by
    rw [← context.entry?_expandRaw_indices_eq_of_lt_length hIndices hTarget]
    exact hRawSmallerEntry
  have hTargetNonzero : targetValue ≠ 0 := by omega
  have hLargerRow : row < trimHeight (expandRaw array.raw largerIndex) :=
    row_lt_trimHeight_of_entry?_eq_some_of_ne_zero
      hRawLargerEntry hTargetNonzero
  rw [← context.isAncestor_expand_indices_eq_of_rows hIndices hTarget
    hSmallerRow hLargerRow]
  exact hAncestor

/-- expansion 中以原末列之前的列为目标的真 ancestry 可回运到原数组。 -/
theorem isAncestor_original_of_expand {array : ValidArray}
    (context : ExpansionContext array) {index ancestor target row : Nat}
    (hTarget : target < context.lastIndex)
    (hAncestor : isAncestor (array.expand index).raw row ancestor target = true) :
    isAncestor array.raw row ancestor target = true := by
  rcases ancestor_entries_lt hAncestor with
    ⟨_ancestorValue, _targetValue, _hAncestorEntry, hTargetEntry, _hValueLt⟩
  have hExpandedUniform := ValidArray.uniformHeight_expand
    (index := index)
    (rectangular_iff_exists_uniformHeight.mp array.rectangular_eq).choose_spec
  have hRow : row < trimHeight (expandRaw array.raw index) :=
    row_lt_uniformHeight_of_entry?_eq_some hExpandedUniform hTargetEntry
  rw [context.isAncestor_expand_eq_original_of_lt_lastIndex
    index row hRow hTarget] at hAncestor
  exact hAncestor

/-- 正 expansion 之间，较小 expansion 的全部列在 `row < m₀` 上逐项构成前缀。 -/
theorem entry?_expand_indices_eq_of_lt_length {array : ValidArray}
    (context : ExpansionContext array)
    {smallerIndex largerIndex column row : Nat}
    (hSmallerPositive : 0 < smallerIndex)
    (hIndices : smallerIndex ≤ largerIndex)
    (hColumn : column < (array.expand smallerIndex).raw.length)
    (hRow : row < context.maximalRow) :
    entry? (array.expand smallerIndex).raw column row =
      entry? (array.expand largerIndex).raw column row := by
  have hSmallerRow : row < trimHeight (expandRaw array.raw smallerIndex) :=
    Nat.lt_of_lt_of_le hRow
      (context.maximalRow_le_trimHeight_expandRaw hSmallerPositive)
  have hLargerPositive : 0 < largerIndex := Nat.lt_of_lt_of_le hSmallerPositive hIndices
  have hLargerRow : row < trimHeight (expandRaw array.raw largerIndex) :=
    Nat.lt_of_lt_of_le hRow
      (context.maximalRow_le_trimHeight_expandRaw hLargerPositive)
  rw [entry?_expand_of_lt smallerIndex column row hSmallerRow,
    entry?_expand_of_lt largerIndex column row hLargerRow]
  by_cases hGood : column < context.parentColumn
  · rw [context.entry?_expandRaw_goodPart smallerIndex hGood,
      context.entry?_expandRaw_goodPart largerIndex hGood]
  · rcases context.exists_copyPosition_of_not_good hColumn
        (Nat.le_of_not_gt hGood) with
      ⟨copyNumber, localColumn, hCopy, hLocal, rfl⟩
    rw [context.entry?_expandRaw_copy hCopy hLocal,
      context.entry?_expandRaw_copy (Nat.le_trans hCopy hIndices) hLocal]

/-- 正 expansion 之间，较小 expansion 前缀内的 parent 在 `row < m₀` 上相同。 -/
theorem parent_expand_indices_eq_of_lt_length {array : ValidArray}
    (context : ExpansionContext array)
    {smallerIndex largerIndex target row : Nat}
    (hSmallerPositive : 0 < smallerIndex)
    (hIndices : smallerIndex ≤ largerIndex)
    (hTarget : target < (array.expand smallerIndex).raw.length)
    (hRow : row < context.maximalRow) :
    parent row (array.expand smallerIndex).raw target =
      parent row (array.expand largerIndex).raw target := by
  induction row generalizing target with
  | zero =>
      apply parent_congr_below_target hTarget
      · rw [context.length_expand] at hTarget ⊢
        have hProduct : (smallerIndex + 1) * context.blockLength ≤
            (largerIndex + 1) * context.blockLength :=
          Nat.mul_le_mul_right context.blockLength
          (Nat.succ_le_succ hIndices)
        omega
      · intro candidate hCandidate
        apply parentEligible_zero_congr
        · exact context.entry?_expand_indices_eq_of_lt_length hSmallerPositive
            hIndices (Nat.lt_trans hCandidate hTarget) hRow
        · exact context.entry?_expand_indices_eq_of_lt_length hSmallerPositive
            hIndices hTarget hRow
  | succ lowerRow ih =>
      apply parent_congr_below_target hTarget
      · rw [context.length_expand] at hTarget ⊢
        have hProduct : (smallerIndex + 1) * context.blockLength ≤
            (largerIndex + 1) * context.blockLength :=
          Nat.mul_le_mul_right context.blockLength
          (Nat.succ_le_succ hIndices)
        omega
      · intro candidate hCandidate
        apply parentEligible_succ_congr
        · apply isAncestor_congr_below
          intro column hColumn
          apply ih
          · exact Nat.lt_of_le_of_lt hColumn hTarget
          · omega
        · exact context.entry?_expand_indices_eq_of_lt_length hSmallerPositive
            hIndices (Nat.lt_trans hCandidate hTarget) hRow
        · exact context.entry?_expand_indices_eq_of_lt_length hSmallerPositive
            hIndices hTarget hRow

/-- 正 expansion 之间，较小 expansion 前缀内的 ancestry 在 `row < m₀` 上相同。 -/
theorem isAncestor_expand_indices_eq_of_lt_length {array : ValidArray}
    (context : ExpansionContext array)
    {smallerIndex largerIndex ancestor target row : Nat}
    (hSmallerPositive : 0 < smallerIndex)
    (hIndices : smallerIndex ≤ largerIndex)
    (hTarget : target < (array.expand smallerIndex).raw.length)
    (hRow : row < context.maximalRow) :
    isAncestor (array.expand smallerIndex).raw row ancestor target =
      isAncestor (array.expand largerIndex).raw row ancestor target := by
  apply isAncestor_congr_below
  intro column hColumn
  exact context.parent_expand_indices_eq_of_lt_length hSmallerPositive hIndices
    (Nat.lt_of_le_of_lt hColumn hTarget) hRow

end ExpansionContext

end BMS
end YesMetaZFC
