import YesMetaZFC.BMS.Ancestor

/-!
# BM4 expansion 的合法性

本文件只证明 Stage 0 参考实现的结构性质：复制不改变列高，未 trim 的 expansion 保持
矩形，trim 是幂等的。由此得到面向后续证明的总函数 `ValidArray.expand`。
-/

namespace YesMetaZFC
namespace BMS

/-- 每一列都具有指定高度。这个命题比布尔矩形判定更适合列表归纳。 -/
def UniformHeight (height : Nat) (array : BMSArray) : Prop :=
  ∀ column ∈ array, column.length = height

theorem rectangular_iff_exists_uniformHeight {array : BMSArray} :
    rectangular array = true ↔ ∃ height, UniformHeight height array := by
  cases array with
  | nil => exact ⟨fun _ => ⟨0, by simp [UniformHeight]⟩, fun _ => by rfl⟩
  | cons first rest =>
      simp only [rectangular, List.all_eq_true, beq_iff_eq]
      constructor
      · intro h
        refine ⟨first.length, ?_⟩
        intro column hMem
        simp only [List.mem_cons] at hMem
        rcases hMem with rfl | hMem
        · rfl
        · exact h column hMem
      · rintro ⟨height, h⟩ column hMem
        exact (h column (List.mem_cons_of_mem first hMem)).trans
          (h first List.mem_cons_self).symm

private theorem uniformHeight_take {height count : Nat} {array : BMSArray}
    (hUniform : UniformHeight height array) :
    UniformHeight height (array.take count) := by
  intro column hMem
  exact hUniform column (List.mem_of_mem_take hMem)

private theorem uniformHeight_drop {height count : Nat} {array : BMSArray}
    (hUniform : UniformHeight height array) :
    UniformHeight height (array.drop count) := by
  intro column hMem
  exact hUniform column (List.mem_of_mem_drop hMem)

private theorem uniformHeight_slice {height start count : Nat} {array : BMSArray}
    (hUniform : UniformHeight height array) :
    UniformHeight height (slice array start count) :=
  uniformHeight_take (uniformHeight_drop hUniform)

private theorem uniformHeight_append {height : Nat} {left right : BMSArray}
    (hLeft : UniformHeight height left) (hRight : UniformHeight height right) :
    UniformHeight height (left ++ right) := by
  intro column hMem
  rcases List.mem_append.mp hMem with hMem | hMem
  · exact hLeft column hMem
  · exact hRight column hMem

theorem uniformHeight_copyBlock {height : Nat} {array block : BMSArray}
    {m₀ parentColumn copyNumber : Nat} {lastColumn : List Nat}
    (hUniform : UniformHeight height block) :
    UniformHeight height
      (copyBlock array block m₀ parentColumn copyNumber lastColumn) := by
  intro column hMem
  unfold copyBlock at hMem
  dsimp only at hMem
  rcases List.mem_mapIdx.mp hMem with ⟨index, hIndex, hColumn⟩
  subst column
  simp only [List.length_mapIdx]
  exact hUniform block[index] (List.getElem_mem hIndex)

private theorem uniformHeight_flatMap_copyBlock
    {height : Nat} {array block : BMSArray} {copies m₀ parentColumn : Nat}
    {lastColumn : List Nat} (hUniform : UniformHeight height block) :
    UniformHeight height
      ((List.range copies).flatMap fun copyNumber =>
        copyBlock array block m₀ parentColumn copyNumber lastColumn) := by
  intro column hMem
  rcases List.mem_flatMap.mp hMem with ⟨copyNumber, _, hColumn⟩
  exact uniformHeight_copyBlock hUniform column hColumn

theorem uniformHeight_expandRaw {height index : Nat} {array : BMSArray}
    (hUniform : UniformHeight height array) :
    UniformHeight height (expandRaw array index) := by
  unfold expandRaw
  split
  next hEmpty =>
    simp [UniformHeight]
  next lastIndex hLength =>
    dsimp only
    split
    next => exact uniformHeight_take hUniform
    next m₀ hMaximal =>
      split
      next => exact uniformHeight_take hUniform
      next parentColumn hParent =>
        apply uniformHeight_append (uniformHeight_take hUniform)
        exact uniformHeight_flatMap_copyBlock
          (uniformHeight_slice hUniform)

private def supportFold (array : BMSArray) (initial : Nat) : Nat :=
  array.foldl (fun result column => max result (supportHeight column)) initial

@[simp]
private theorem supportFold_zero_eq_trimHeight (array : BMSArray) :
    supportFold array 0 = trimHeight array := rfl

private theorem initial_le_supportFold (array : BMSArray) (initial : Nat) :
    initial ≤ supportFold array initial := by
  induction array generalizing initial with
  | nil => exact Nat.le_refl initial
  | cons column rest ih =>
      exact Nat.le_trans (Nat.le_max_left _ _) (ih (max initial (supportHeight column)))

private theorem member_support_le_supportFold {array : BMSArray} {column : List Nat}
    (hMem : column ∈ array) (initial : Nat) :
    supportHeight column ≤ supportFold array initial := by
  induction array generalizing initial with
  | nil => simp at hMem
  | cons head rest ih =>
      simp only [List.mem_cons] at hMem
      rcases hMem with hEqual | hMem
      · subst column
        exact Nat.le_trans (Nat.le_max_right _ _)
          (initial_le_supportFold rest (max initial (supportHeight head)))
      · change supportHeight column ≤
          supportFold rest (max initial (supportHeight head))
        exact ih hMem (max initial (supportHeight head))

/-- 数组中每一列的支撑高度都不超过整个数组的裁剪高度。 -/
theorem supportHeight_le_trimHeight_of_mem {array : BMSArray} {column : List Nat}
    (hMem : column ∈ array) :
    supportHeight column ≤ trimHeight array := by
  rw [← supportFold_zero_eq_trimHeight]
  exact member_support_le_supportFold hMem 0

/-- 矩形数组中任意已定义条目的行号小于公共高度。 -/
theorem row_lt_uniformHeight_of_entry?_eq_some {array : BMSArray}
    {height column row value : Nat}
    (hUniform : UniformHeight height array)
    (hEntry : entry? array column row = some value) : row < height := by
  unfold entry? at hEntry
  cases hColumn : array[column]? with
  | none => simp [hColumn] at hEntry
  | some entries =>
      have hColumnData := List.getElem?_eq_some_iff.mp hColumn
      have hEntriesMem : entries ∈ array := by
        rw [← hColumnData.2]
        exact List.getElem_mem hColumnData.1
      have hRow : row < entries.length := by
        have hEntryData : entries[row]? = some value := by
          simpa [hColumn] using hEntry
        exact (List.getElem?_eq_some_iff.mp hEntryData).1
      rw [hUniform entries hEntriesMem] at hRow
      exact hRow

/-- 非零条目保证其行仍在 `trimHeight` 以内。 -/
theorem row_lt_trimHeight_of_entry?_eq_some_of_ne_zero {array : BMSArray}
    {column row value : Nat}
    (hEntry : entry? array column row = some value)
    (hValue : value ≠ 0) : row < trimHeight array := by
  unfold entry? at hEntry
  cases hColumn : array[column]? with
  | none => simp [hColumn] at hEntry
  | some entries =>
      have hColumnData := List.getElem?_eq_some_iff.mp hColumn
      have hEntriesMem : entries ∈ array := by
        rw [← hColumnData.2]
        exact List.getElem_mem hColumnData.1
      have hEntryData : entries[row]? = some value := by
        simpa [hColumn] using hEntry
      exact Nat.lt_of_lt_of_le
        (row_lt_supportHeight_of_getElem?_eq_some entries row value
          hEntryData hValue)
        (supportHeight_le_trimHeight_of_mem hEntriesMem)

private theorem supportFold_le_of_uniform {array : BMSArray} {height initial : Nat}
    (hUniform : UniformHeight height array) (hInitial : initial ≤ height) :
    supportFold array initial ≤ height := by
  induction array generalizing initial with
  | nil => exact hInitial
  | cons column rest ih =>
      apply ih
      · intro member hMem
        exact hUniform member (List.mem_cons_of_mem column hMem)
      · exact Nat.max_le.mpr ⟨hInitial, by
          exact Nat.le_trans (supportHeight_le_length column)
            (Nat.le_of_eq (hUniform column List.mem_cons_self))⟩

private theorem supportFold_le_of_supportBound
    {array : BMSArray} {bound initial : Nat}
    (hBound : ∀ column ∈ array, supportHeight column ≤ bound)
    (hInitial : initial ≤ bound) :
    supportFold array initial ≤ bound := by
  induction array generalizing initial with
  | nil => exact hInitial
  | cons head rest ih =>
      apply ih
      · intro column hMem
        exact hBound column (List.mem_cons_of_mem head hMem)
      · exact Nat.max_le.mpr
          ⟨hInitial, hBound head List.mem_cons_self⟩

/-- 取列前缀不会增大需要保留的行高。 -/
theorem trimHeight_take_le (array : BMSArray) (count : Nat) :
    trimHeight (array.take count) ≤ trimHeight array := by
  apply supportFold_le_of_supportBound
  · intro column hMem
    exact supportHeight_le_trimHeight_of_mem (List.mem_of_mem_take hMem)
  · exact Nat.zero_le _

theorem trimHeight_le_of_uniform {array : BMSArray} {height : Nat}
    (hUniform : UniformHeight height array) :
    trimHeight array ≤ height := by
  rw [← supportFold_zero_eq_trimHeight]
  exact supportFold_le_of_uniform hUniform (Nat.zero_le height)

private theorem supportFold_map_take
    (array : BMSArray) (count initial : Nat)
    (hBound : ∀ column ∈ array, supportHeight column ≤ count) :
    supportFold (array.map fun column => column.take count) initial =
      supportFold array initial := by
  induction array generalizing initial with
  | nil => rfl
  | cons column rest ih =>
      simp only [List.map_cons, supportFold, List.foldl_cons]
      rw [supportHeight_take_of_le column count (hBound column List.mem_cons_self)]
      exact ih (max initial (supportHeight column))
        (fun member hMem => hBound member (List.mem_cons_of_mem column hMem))

/-- 先规范化再取列前缀，最后重新规范化，等于直接规范化该前缀。 -/
theorem trimZeroRows_take_trimZeroRows (array : BMSArray) (count : Nat) :
    trimZeroRows ((trimZeroRows array).take count) =
      trimZeroRows (array.take count) := by
  let height := trimHeight array
  let prefixHeight := trimHeight (array.take count)
  have hPrefix : (trimZeroRows array).take count =
      (array.take count).map (fun column => column.take height) := by
    simp [trimZeroRows, height]
  have hBound : ∀ column ∈ array.take count,
      supportHeight column ≤ height := by
    intro column hMem
    exact supportHeight_le_trimHeight_of_mem (List.mem_of_mem_take hMem)
  have hHeight : trimHeight ((trimZeroRows array).take count) =
      prefixHeight := by
    rw [hPrefix]
    change supportFold
        ((array.take count).map (fun column => column.take height)) 0 =
      supportFold (array.take count) 0
    exact supportFold_map_take (array.take count) height 0 hBound
  rw [show trimZeroRows ((trimZeroRows array).take count) =
      ((trimZeroRows array).take count).map
        (fun column => column.take
          (trimHeight ((trimZeroRows array).take count))) from rfl]
  rw [hHeight, hPrefix]
  rw [show trimZeroRows (array.take count) =
      (array.take count).map (fun column => column.take prefixHeight) from rfl]
  simp only [List.map_map]
  apply List.map_congr_left
  intro column hMem
  change (column.take height).take prefixHeight = column.take prefixHeight
  rw [List.take_take]
  rw [Nat.min_eq_left]
  exact trimHeight_take_le array count

theorem trimZeroRows_idempotent (array : BMSArray) :
    trimZeroRows (trimZeroRows array) = trimZeroRows array := by
  let height := supportFold array 0
  have hBound : ∀ column ∈ array, supportHeight column ≤ height :=
    fun column hMem => member_support_le_supportFold hMem 0
  have hFold :
      supportFold (array.map fun column => column.take height) 0 = height := by
    simpa [height] using supportFold_map_take array height 0 hBound
  change
    let outerHeight := supportFold (array.map fun column => column.take height) 0
    (array.map fun column => column.take height).map
        (fun column => column.take outerHeight) =
      array.map fun column => column.take height
  dsimp only
  rw [hFold]
  simp [List.map_map, List.take_take]

theorem trimHeight_trimZeroRows (array : BMSArray) :
    trimHeight (trimZeroRows array) = trimHeight array := by
  let height := supportFold array 0
  have hBound : ∀ column ∈ array, supportHeight column ≤ height :=
    fun column hMem => member_support_le_supportFold hMem 0
  have hFold :
      supportFold (array.map fun column => column.take height) 0 = height :=
    supportFold_map_take array height 0 hBound
  simpa [trimHeight, trimZeroRows, supportFold, height] using hFold

theorem entry?_trimZeroRows_of_lt (array : BMSArray) (column row : Nat)
    (hRow : row < trimHeight array) :
    entry? (trimZeroRows array) column row = entry? array column row := by
  unfold entry? trimZeroRows
  rw [List.getElem?_map]
  cases hColumn : array[column]? with
  | none => rfl
  | some source =>
      simp only [Option.map_some, Option.bind_some]
      rw [List.getElem?_take_of_lt hRow]

theorem entry?_trimZeroRows_eq_none_of_le (array : BMSArray) (column row : Nat)
    (hRow : trimHeight array ≤ row) :
    entry? (trimZeroRows array) column row = none := by
  unfold entry? trimZeroRows
  rw [List.getElem?_map]
  cases hColumn : array[column]? with
  | none => rfl
  | some source =>
      simp only [Option.map_some, Option.bind_some]
      exact List.getElem?_take_eq_none hRow

theorem parent_trimZeroRows_of_lt (array : BMSArray) {row : Nat}
    (hRow : row < trimHeight array) (target : Nat) :
    parent row (trimZeroRows array) target = parent row array target := by
  induction row generalizing target with
  | zero =>
      have hEligible : parentEligible 0 (trimZeroRows array) target =
          parentEligible 0 array target := by
        funext candidate
        simp only [parentEligible]
        rw [entry?_trimZeroRows_of_lt array candidate 0 hRow,
          entry?_trimZeroRows_of_lt array target 0 hRow]
      have hLength : (trimZeroRows array).length = array.length := by
        simp [trimZeroRows]
      rw [parent_eq_greatestBelow?, parent_eq_greatestBelow?, hLength, hEligible]
  | succ lowerRow ih =>
      have hLower : lowerRow < trimHeight array :=
        Nat.lt_trans (Nat.lt_succ_self lowerRow) hRow
      have hParentFunctions : parent lowerRow (trimZeroRows array) = parent lowerRow array := by
        funext column
        exact ih hLower column
      have hEligible : parentEligible (lowerRow + 1) (trimZeroRows array) target =
          parentEligible (lowerRow + 1) array target := by
        funext candidate
        simp only [parentEligible]
        rw [show isAncestor (trimZeroRows array) lowerRow candidate target =
            isAncestor array lowerRow candidate target by
              simp [isAncestor, hParentFunctions]]
        rw [entry?_trimZeroRows_of_lt array candidate (lowerRow + 1) hRow,
          entry?_trimZeroRows_of_lt array target (lowerRow + 1) hRow]
      have hLength : (trimZeroRows array).length = array.length := by
        simp [trimZeroRows]
      rw [parent_eq_greatestBelow?, parent_eq_greatestBelow?, hLength, hEligible]

theorem isAncestor_trimZeroRows_of_lt (array : BMSArray) {row : Nat}
    (hRow : row < trimHeight array) (ancestor target : Nat) :
    isAncestor (trimZeroRows array) row ancestor target =
      isAncestor array row ancestor target := by
  have hParents : parent row (trimZeroRows array) = parent row array := by
    funext column
    exact parent_trimZeroRows_of_lt array hRow column
  simp [isAncestor, hParents]

theorem parent_trimZeroRows_eq_none_of_le (array : BMSArray) {row : Nat}
    (hRow : trimHeight array ≤ row) (target : Nat) :
    parent row (trimZeroRows array) target = none := by
  apply parent_eq_none_iff.mpr
  right
  intro candidate hCandidate
  cases row with
  | zero =>
      simp [parentEligible,
        entry?_trimZeroRows_eq_none_of_le array candidate 0 hRow,
        entry?_trimZeroRows_eq_none_of_le array target 0 hRow]
  | succ lowerRow =>
      simp [parentEligible,
        entry?_trimZeroRows_eq_none_of_le array candidate (lowerRow + 1) hRow,
        entry?_trimZeroRows_eq_none_of_le array target (lowerRow + 1) hRow]

theorem isAncestor_trimZeroRows_eq_false_of_le (array : BMSArray) {row : Nat}
    (hRow : trimHeight array ≤ row) (ancestor target : Nat) :
    isAncestor (trimZeroRows array) row ancestor target = false := by
  cases target with
  | zero => simp [isAncestor, ancestorChain]
  | succ target =>
      simp [isAncestor, ancestorChain,
        parent_trimZeroRows_eq_none_of_le array hRow]

@[simp]
theorem length_trimZeroRows (array : BMSArray) :
    (trimZeroRows array).length = array.length := by
  simp [trimZeroRows]

@[simp]
theorem length_expand (array : BMSArray) (index : Nat) :
    (BMS.expand array index).length = (expandRaw array index).length := by
  simp [BMS.expand]

theorem rectangular_trimZeroRows {array : BMSArray}
    (hRectangular : rectangular array = true) :
    rectangular (trimZeroRows array) = true := by
  rcases rectangular_iff_exists_uniformHeight.mp hRectangular with ⟨height, hUniform⟩
  apply rectangular_iff_exists_uniformHeight.mpr
  let trimmedHeight := supportFold array 0
  refine ⟨trimmedHeight, ?_⟩
  intro column hMem
  unfold trimZeroRows at hMem
  change column ∈ array.map (fun member => member.take trimmedHeight) at hMem
  rcases List.mem_map.mp hMem with ⟨source, hSource, rfl⟩
  rw [List.length_take, hUniform source hSource]
  exact Nat.min_eq_left (supportFold_le_of_uniform hUniform (Nat.zero_le height))

theorem uniformHeight_trimZeroRows {array : BMSArray} {height : Nat}
    (hUniform : UniformHeight height array) :
    UniformHeight (trimHeight array) (trimZeroRows array) := by
  intro column hMem
  unfold trimZeroRows at hMem
  rcases List.mem_map.mp hMem with ⟨source, hSource, rfl⟩
  rw [List.length_take, hUniform source hSource]
  exact Nat.min_eq_left (trimHeight_le_of_uniform hUniform)

theorem exists_entry_of_uniformHeight {array : BMSArray} {height column row : Nat}
    (hUniform : UniformHeight height array)
    (hColumn : column < array.length) (hRow : row < height) :
    ∃ value, entry? array column row = some value := by
  let foundColumn := array[column]
  have hFoundColumn : array[column]? = some foundColumn :=
    List.getElem?_eq_some_iff.mpr ⟨hColumn, rfl⟩
  have hFoundLength : foundColumn.length = height :=
    hUniform foundColumn (List.getElem_mem hColumn)
  let value := foundColumn[row]
  have hValue : foundColumn[row]? = some value :=
    List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩
  exact ⟨value, by simp [entry?, hFoundColumn, hValue]⟩

theorem normalized_expand {array : BMSArray} {index : Nat}
    (hNormalized : normalized array = true) :
    normalized (expand array index) = true := by
  have hRectangular : rectangular array = true := by
    simp [normalized] at hNormalized
    exact hNormalized.1
  have hRawRectangular : rectangular (expandRaw array index) = true := by
    rcases rectangular_iff_exists_uniformHeight.mp hRectangular with ⟨height, hUniform⟩
    exact rectangular_iff_exists_uniformHeight.mpr
      ⟨height, uniformHeight_expandRaw hUniform⟩
  simp [normalized, expand, rectangular_trimZeroRows hRawRectangular,
    trimZeroRows_idempotent]

namespace ValidArray

/-- Stage 0 expansion 在合法数组上的总封装。 -/
def expand (array : ValidArray) (index : Nat) : ValidArray where
  raw := BMS.expand array.raw index
  rectangular_eq := by
    have hNormalized := normalized_expand (index := index) array.normalized_eq
    simp [normalized] at hNormalized
    exact hNormalized.1
  trimmed_eq := by
    simp [BMS.expand, trimZeroRows_idempotent]

@[simp]
theorem raw_expand (array : ValidArray) (index : Nat) :
    (array.expand index).raw = BMS.expand array.raw index := rfl

theorem uniformHeight_expand {array : ValidArray} {height index : Nat}
    (hUniform : UniformHeight height array.raw) :
    UniformHeight (trimHeight (expandRaw array.raw index))
      (array.expand index).raw := by
  rw [raw_expand]
  exact uniformHeight_trimZeroRows (uniformHeight_expandRaw hUniform)

end ValidArray

end BMS
end YesMetaZFC
