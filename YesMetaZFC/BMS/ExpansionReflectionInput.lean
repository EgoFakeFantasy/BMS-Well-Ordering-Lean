import YesMetaZFC.BMS.ExpansionAssembly

/-!
# expansion 迭代的有限反射输入

本文件把 Theorem 2.7 第 `i` 轮使用 Lemma 2.6 的 `X,Y,α,β` 从当前
稳定表示中规范地取出，并证明 `FiniteReflectionInput` 的全部边界前提。
-/

namespace YesMetaZFC
namespace BMS

universe u

namespace StabilityFrame

/--
第 `expansionIndex` 轮的表示状态：当前最后复制块仍使用原 `B₀` 的标签。
-/
structure ExpansionReflectionState {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat)
    (original : StableRepresentation frame array) where
  current : StableRepresentation frame (array.expand expansionIndex)
  good_eq : ∀ column : Fin context.parentColumn,
    current.label ⟨column.1, by
      rw [context.length_expand]
      omega⟩ = original.label ⟨column.1, by
        rw [context.array_length]
        have hParent := context.parentColumn_lt_lastIndex
        omega⟩
  stabilityCutoff : Nat
  lower_stableLt_below_cutoff : ∀
      (lowerIndex : Fin (context.copyStart expansionIndex))
      (upperIndex : Fin context.blockLength) stableLevel,
    frame.stableLt stableLevel
        (current.label ⟨lowerIndex.1, by
          rw [context.length_expand]
          simp only [ExpansionContext.copyStart] at lowerIndex ⊢
          rw [Nat.add_mul]
          omega⟩)
        (original.label ⟨context.parentColumn + upperIndex.1, by
          rw [context.array_length]
          have hLocal := upperIndex.isLt
          change upperIndex.1 < context.lastIndex - context.parentColumn at hLocal
          have hParent := context.parentColumn_lt_lastIndex
          omega⟩) →
      stableLevel < stabilityCutoff
  upper_stableLt_below_cutoff : ∀
      (left right : Fin context.blockLength) stableLevel,
    frame.stableLt stableLevel
        (original.label ⟨context.parentColumn + left.1, by
          rw [context.array_length]
          have hLocal := left.isLt
          change left.1 < context.lastIndex - context.parentColumn at hLocal
          have hParent := context.parentColumn_lt_lastIndex
          omega⟩)
        (original.label ⟨context.parentColumn + right.1, by
          rw [context.array_length]
          have hLocal := right.isLt
          change right.1 < context.lastIndex - context.parentColumn at hLocal
          have hParent := context.parentColumn_lt_lastIndex
          omega⟩) →
      stableLevel < stabilityCutoff
  lastCopy_eq : ∀ localColumn : Fin context.blockLength,
    current.label
        ⟨context.copyPosition expansionIndex localColumn.1,
          context.copyPosition_lt_length (Nat.le_refl _) localColumn.isLt⟩ =
      original.label
        ⟨context.parentColumn + localColumn.1, by
          rw [context.array_length]
          have hLocal := localColumn.isLt
          change localColumn.1 <
            context.lastIndex - context.parentColumn at hLocal
          have hParent := context.parentColumn_lt_lastIndex
          omega⟩

namespace ExpansionReflectionState

/-- `X` 中的列号嵌入当前 expansion。 -/
def lowerColumn {Label : Type u} {frame : StabilityFrame Label}
    {array : ValidArray} {context : ExpansionContext array}
    {expansionIndex : Nat} {original : StableRepresentation frame array}
    (_state : ExpansionReflectionState context expansionIndex original)
    (index : Fin (context.copyStart expansionIndex)) :
    Fin (array.expand expansionIndex).raw.length :=
  ⟨index.1, by
    rw [context.length_expand]
    simp only [ExpansionContext.copyStart] at index ⊢
    rw [Nat.add_mul]
    omega⟩

/-- 原 `B₀` 的局部列号嵌入原数组。 -/
def upperColumn {Label : Type u} {frame : StabilityFrame Label}
    {array : ValidArray} {context : ExpansionContext array}
    {expansionIndex : Nat} {original : StableRepresentation frame array}
    (_state : ExpansionReflectionState context expansionIndex original)
    (localColumn : Fin context.blockLength) : Fin array.raw.length :=
  ⟨context.parentColumn + localColumn.1, by
    rw [context.array_length]
    have hLocal := localColumn.isLt
    change localColumn.1 <
      context.lastIndex - context.parentColumn at hLocal
    have hParent := context.parentColumn_lt_lastIndex
    omega⟩

/-- 原数组的末列。 -/
def lastColumn {Label : Type u} {frame : StabilityFrame Label}
    {array : ValidArray} {context : ExpansionContext array}
    {expansionIndex : Nat} {original : StableRepresentation frame array}
    (_state : ExpansionReflectionState context expansionIndex original) :
    Fin array.raw.length :=
  ⟨context.lastIndex, by rw [context.array_length]; omega⟩

/-- 当前最后复制块的首列。 -/
def lowerBoundColumn {Label : Type u} {frame : StabilityFrame Label}
    {array : ValidArray} {context : ExpansionContext array}
    {expansionIndex : Nat} {original : StableRepresentation frame array}
    (_state : ExpansionReflectionState context expansionIndex original) :
    Fin (array.expand expansionIndex).raw.length :=
  ⟨context.copyPosition expansionIndex 0,
    context.copyPosition_lt_length (Nat.le_refl _) context.blockLength_pos⟩

/-- 第 `i` 轮反射的规范 `FiniteReflectionInput`。 -/
def reflectionInput {Label : Type u} {frame : StabilityFrame Label}
    {array : ValidArray} {context : ExpansionContext array}
    {expansionIndex : Nat} {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original) :
    FiniteReflectionInput frame (context.copyStart expansionIndex)
      context.blockLength where
  level := context.maximalRow
  stabilityCutoff := state.stabilityCutoff
  lowerBound := state.current.label state.lowerBoundColumn
  upperBound := original.label state.lastColumn
  lower := fun index => state.current.label (state.lowerColumn index)
  upper := fun localColumn => original.label (state.upperColumn localColumn)
  lowerBound_stableLt_upperBound := by
    have hAncestor : isAncestor array.raw context.maximalRow
        context.parentColumn context.lastIndex = true :=
      direct_parent_isAncestor context.parent_eq
    have hParentIndex : context.parentColumn < array.raw.length := by
      rw [context.array_length]
      have hParent := context.parentColumn_lt_lastIndex
      omega
    have hLastIndex : context.lastIndex < array.raw.length := by
      rw [context.array_length]
      omega
    have hStable := original.preservesAncestor
      (left := ⟨context.parentColumn, hParentIndex⟩)
      (right := ⟨context.lastIndex, hLastIndex⟩) hAncestor
    have hLastCopy := state.lastCopy_eq
      (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)
    simpa [lowerBoundColumn, upperColumn, lastColumn,
      ExpansionContext.copyPosition, ExpansionContext.copyStart] using
      hLastCopy.symm ▸ hStable
  lower_lt_lowerBound := by
    intro index
    apply state.current.strictlyIncreasing
    change index.1 < context.copyPosition expansionIndex 0
    exact index.isLt
  lowerBound_le_upper := by
    intro localColumn
    rcases Nat.eq_zero_or_pos localColumn.1 with hZero | hPositive
    · right
      have hLastCopy := state.lastCopy_eq
        (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)
      simpa [lowerBoundColumn, upperColumn, hZero,
        ExpansionContext.copyPosition, ExpansionContext.copyStart] using
        hLastCopy
    · left
      have hOriginalLt : frame.lt (original.label
          (state.upperColumn (⟨0, context.blockLength_pos⟩ :
            Fin context.blockLength))) (original.label
          (state.upperColumn localColumn)) := by
        apply original.strictlyIncreasing
        change context.parentColumn + 0 <
          context.parentColumn + localColumn.1
        omega
      have hLastCopy := state.lastCopy_eq
        (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)
      have hBoundEq : state.current.label state.lowerBoundColumn =
          original.label (state.upperColumn
            (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)) := by
        simpa [lowerBoundColumn, upperColumn,
          ExpansionContext.copyPosition, ExpansionContext.copyStart] using
          hLastCopy
      rw [hBoundEq]
      exact hOriginalLt
  upper_lt_upperBound := by
    intro localColumn
    apply original.strictlyIncreasing
    change context.parentColumn + localColumn.1 < context.lastIndex
    have hLocal := localColumn.isLt
    change localColumn.1 <
      context.lastIndex - context.parentColumn at hLocal
    have hParent := context.parentColumn_lt_lastIndex
    omega
  lower_stableLt_below_cutoff := by
    intro lowerIndex upperIndex stableLevel hStable
    exact state.lower_stableLt_below_cutoff lowerIndex upperIndex
      stableLevel hStable
  upper_stableLt_below_cutoff := by
    intro left right stableLevel hStable
    exact state.upper_stableLt_below_cutoff left right stableLevel hStable

/-- 由 Lemma 2.6 原理选取当前轮的规范反射见证。 -/
noncomputable def reflectionWitness {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (hReflection : FiniteReflectionPrinciple frame) :
    FiniteReflectionWitness state.reflectionInput :=
  Classical.choice (hReflection state.reflectionInput)

/--
从第 `i` 轮状态和反射见证生成 `A[i+1]` 的分块标签族：早期块保留，
`Bᵢ` 改用反射图像，`Bᵢ₊₁` 恢复原 `B₀` 标签。
-/
noncomputable def successorFamily {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput) :
    ExpansionLabelFamily (Label := Label) context (expansionIndex + 1) where
  goodLabel := fun column =>
    state.current.label ⟨column.1, by
      rw [context.length_expand]
      have hBlock := context.blockLength_pos
      omega⟩
  copyLabel := fun copyNumber localColumn =>
    if hEarlier : copyNumber.1 < expansionIndex then
      state.current.label
        ⟨context.copyPosition copyNumber.1 localColumn.1,
          context.copyPosition_lt_length (Nat.le_of_lt hEarlier)
            localColumn.isLt⟩
    else if _hCurrent : copyNumber.1 = expansionIndex then
      witness.image localColumn
    else
      original.label (state.upperColumn localColumn)

@[simp]
theorem successorFamily_goodLabel {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (column : Fin context.parentColumn) :
    (state.successorFamily witness).goodLabel column =
      state.current.label ⟨column.1, by
        rw [context.length_expand]
        omega⟩ := rfl

@[simp]
theorem successorFamily_copyLabel_earlier {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (copyNumber : Fin (expansionIndex + 2))
    (localColumn : Fin context.blockLength)
    (hEarlier : copyNumber.1 < expansionIndex) :
    (state.successorFamily witness).copyLabel copyNumber localColumn =
      state.current.label
        ⟨context.copyPosition copyNumber.1 localColumn.1,
          context.copyPosition_lt_length (Nat.le_of_lt hEarlier)
            localColumn.isLt⟩ := by
  simp [successorFamily, hEarlier]

@[simp]
theorem successorFamily_copyLabel_current {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (localColumn : Fin context.blockLength) :
    (state.successorFamily witness).copyLabel
        ⟨expansionIndex, by omega⟩ localColumn = witness.image localColumn := by
  simp [successorFamily]

@[simp]
theorem successorFamily_copyLabel_last {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (localColumn : Fin context.blockLength) :
    (state.successorFamily witness).copyLabel
        ⟨expansionIndex + 1, by omega⟩ localColumn =
      original.label (state.upperColumn localColumn) := by
  simp only [successorFamily]
  rw [dif_neg (by omega), dif_neg (by omega)]

/-- 后继标签族在 `G×G` 上严格递增。 -/
theorem successorFamily_good_lt_good {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    {left right : Fin context.parentColumn} (hOrder : left < right) :
    frame.lt ((state.successorFamily witness).goodLabel left)
      ((state.successorFamily witness).goodLabel right) := by
  apply state.current.strictlyIncreasing
  exact hOrder

/-- 后继标签族在每个 `Bᵢ×Bᵢ` 上严格递增。 -/
theorem successorFamily_inside_copy_lt {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (copyNumber : Fin (expansionIndex + 2))
    {leftLocal rightLocal : Fin context.blockLength}
    (hOrder : leftLocal < rightLocal) :
    frame.lt ((state.successorFamily witness).copyLabel copyNumber leftLocal)
      ((state.successorFamily witness).copyLabel copyNumber rightLocal) := by
  by_cases hEarlier : copyNumber.1 < expansionIndex
  · rw [state.successorFamily_copyLabel_earlier witness copyNumber
        leftLocal hEarlier,
      state.successorFamily_copyLabel_earlier witness copyNumber
        rightLocal hEarlier]
    apply state.current.strictlyIncreasing
    change context.copyPosition copyNumber.1 leftLocal.1 <
      context.copyPosition copyNumber.1 rightLocal.1
    simpa only [ExpansionContext.copyPosition] using
      Nat.add_lt_add_left hOrder (context.copyStart copyNumber.1)
  · by_cases hCurrent : copyNumber.1 = expansionIndex
    · have hCopyEq : copyNumber = ⟨expansionIndex, by omega⟩ :=
        Fin.ext hCurrent
      rw [hCopyEq]
      rw [state.successorFamily_copyLabel_current witness,
        state.successorFamily_copyLabel_current witness]
      apply witness.preserves_upper_lt
      apply original.strictlyIncreasing
      change context.parentColumn + leftLocal.1 <
        context.parentColumn + rightLocal.1
      exact Nat.add_lt_add_left hOrder context.parentColumn
    · have hLast : copyNumber.1 = expansionIndex + 1 := by
        omega
      have hCopyEq : copyNumber = ⟨expansionIndex + 1, by omega⟩ :=
        Fin.ext hLast
      rw [hCopyEq]
      rw [state.successorFamily_copyLabel_last witness,
        state.successorFamily_copyLabel_last witness]
      apply original.strictlyIncreasing
      change context.parentColumn + leftLocal.1 <
        context.parentColumn + rightLocal.1
      exact Nat.add_lt_add_left hOrder context.parentColumn

/-- `G` 的标签严格低于后继族中任一复制块标签。 -/
theorem successorFamily_good_lt_copy {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (goodColumn : Fin context.parentColumn)
    (copyNumber : Fin (expansionIndex + 2))
    (localColumn : Fin context.blockLength) :
    frame.lt ((state.successorFamily witness).goodLabel goodColumn)
      ((state.successorFamily witness).copyLabel copyNumber localColumn) := by
  by_cases hEarlier : copyNumber.1 < expansionIndex
  · rw [state.successorFamily_copyLabel_earlier witness copyNumber
      localColumn hEarlier]
    apply state.current.strictlyIncreasing
    change goodColumn.1 <
      context.copyPosition copyNumber.1 localColumn.1
    have hStart := context.copyPosition_in_block
      (copyNumber := copyNumber.1) localColumn.isLt
    have hParentStart : context.parentColumn ≤
        context.copyStart copyNumber.1 := by
      simp [ExpansionContext.copyStart]
    exact Nat.lt_of_lt_of_le goodColumn.isLt
      (Nat.le_trans hParentStart hStart.1)
  · by_cases hCurrent : copyNumber.1 = expansionIndex
    · have hCopyEq : copyNumber = ⟨expansionIndex, by omega⟩ :=
        Fin.ext hCurrent
      rw [hCopyEq]
      rw [state.successorFamily_copyLabel_current witness]
      let lowerIndex : Fin (context.copyStart expansionIndex) :=
        ⟨goodColumn.1, Nat.lt_of_lt_of_le goodColumn.isLt (by
          simp [ExpansionContext.copyStart])⟩
      exact witness.lower_lt_image lowerIndex localColumn
    · have hLast : copyNumber.1 = expansionIndex + 1 := by omega
      have hCopyEq : copyNumber = ⟨expansionIndex + 1, by omega⟩ :=
        Fin.ext hLast
      rw [hCopyEq]
      rw [state.successorFamily_copyLabel_last witness]
      rw [state.successorFamily_goodLabel witness goodColumn]
      rw [state.good_eq goodColumn]
      apply original.strictlyIncreasing
      change goodColumn.1 < context.parentColumn + localColumn.1
      omega

/-- 后继标签族在不同复制块之间严格递增。 -/
theorem successorFamily_between_copies_lt {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    {leftCopy rightCopy : Fin (expansionIndex + 2)}
    (hCopies : leftCopy < rightCopy)
    (leftLocal rightLocal : Fin context.blockLength) :
    frame.lt ((state.successorFamily witness).copyLabel leftCopy leftLocal)
      ((state.successorFamily witness).copyLabel rightCopy rightLocal) := by
  by_cases hRightEarlier : rightCopy.1 < expansionIndex
  · have hLeftEarlier : leftCopy.1 < expansionIndex :=
      Nat.lt_trans hCopies hRightEarlier
    rw [state.successorFamily_copyLabel_earlier witness leftCopy
        leftLocal hLeftEarlier,
      state.successorFamily_copyLabel_earlier witness rightCopy
        rightLocal hRightEarlier]
    apply state.current.strictlyIncreasing
    exact context.column_lt_of_inCopy_of_lt_copy hCopies
      (context.copyPosition_in_block leftLocal.isLt)
      (context.copyPosition_in_block rightLocal.isLt)
  · by_cases hRightCurrent : rightCopy.1 = expansionIndex
    · have hLeftEarlier : leftCopy.1 < expansionIndex := by omega
      have hRightEq : rightCopy = ⟨expansionIndex, by omega⟩ :=
        Fin.ext hRightCurrent
      rw [state.successorFamily_copyLabel_earlier witness leftCopy
          leftLocal hLeftEarlier,
        hRightEq, state.successorFamily_copyLabel_current witness]
      let lowerIndex : Fin (context.copyStart expansionIndex) :=
        ⟨context.copyPosition leftCopy.1 leftLocal.1, by
          have hBefore := context.column_lt_of_inCopy_of_lt_copy
            hLeftEarlier (context.copyPosition_in_block leftLocal.isLt)
            (context.copyPosition_in_block
              (copyNumber := expansionIndex) context.blockLength_pos)
          simpa [ExpansionContext.copyPosition] using hBefore⟩
      exact witness.lower_lt_image lowerIndex rightLocal
    · have hRightLast : rightCopy.1 = expansionIndex + 1 := by omega
      have hRightEq : rightCopy = ⟨expansionIndex + 1, by omega⟩ :=
        Fin.ext hRightLast
      rw [hRightEq, state.successorFamily_copyLabel_last witness]
      rcases state.reflectionInput.lowerBound_le_upper rightLocal with
        hBoundStrict | hBoundEqual
      · by_cases hLeftEarlier : leftCopy.1 < expansionIndex
        · rw [state.successorFamily_copyLabel_earlier witness leftCopy
            leftLocal hLeftEarlier]
          apply hLtTransitive _ hBoundStrict
          apply state.current.strictlyIncreasing
          have hBefore := context.column_lt_of_inCopy_of_lt_copy
            hLeftEarlier (context.copyPosition_in_block leftLocal.isLt)
            (context.copyPosition_in_block
              (copyNumber := expansionIndex) context.blockLength_pos)
          change context.copyStart leftCopy.1 + leftLocal.1 <
            context.copyStart expansionIndex
          exact hBefore
        · have hLeftCurrent : leftCopy.1 = expansionIndex := by omega
          have hLeftEq : leftCopy = ⟨expansionIndex, by omega⟩ :=
            Fin.ext hLeftCurrent
          rw [hLeftEq, state.successorFamily_copyLabel_current witness]
          exact hLtTransitive (witness.image_lt_lowerBound leftLocal)
            hBoundStrict
      · change state.current.label state.lowerBoundColumn =
            original.label (state.upperColumn rightLocal) at hBoundEqual
        rw [← hBoundEqual]
        by_cases hLeftEarlier : leftCopy.1 < expansionIndex
        · rw [state.successorFamily_copyLabel_earlier witness leftCopy
            leftLocal hLeftEarlier]
          apply state.current.strictlyIncreasing
          have hBefore := context.column_lt_of_inCopy_of_lt_copy
            hLeftEarlier (context.copyPosition_in_block leftLocal.isLt)
            (context.copyPosition_in_block
              (copyNumber := expansionIndex) context.blockLength_pos)
          change context.copyStart leftCopy.1 + leftLocal.1 <
            context.copyStart expansionIndex
          exact hBefore
        · have hLeftCurrent : leftCopy.1 = expansionIndex := by omega
          have hLeftEq : leftCopy = ⟨expansionIndex, by omega⟩ :=
            Fin.ext hLeftCurrent
          rw [hLeftEq, state.successorFamily_copyLabel_current witness]
          exact witness.image_lt_lowerBound leftLocal

/-- 后继标签族在 `G×G` 上保留全部 ancestry。 -/
theorem successorFamily_preserves_good {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    {row : Nat} {left right : Fin context.parentColumn}
    (hAncestor : isAncestor (array.expand (expansionIndex + 1)).raw row
      left.1 right.1 = true) :
    frame.stableLt row
      ((state.successorFamily witness).goodLabel left)
      ((state.successorFamily witness).goodLabel right) := by
  have hRow : row < trimHeight
      (expandRaw array.raw (expansionIndex + 1)) := by
    apply Nat.lt_of_not_ge
    intro hBeyond
    have hFalse := ExpansionContext.isAncestor_expand_eq_false_of_le
      (expansionIndex + 1) left.1 right.1 hBeyond
    rw [hFalse] at hAncestor
    contradiction
  have hTarget : right.1 < context.lastIndex :=
    Nat.lt_trans right.isLt context.parentColumn_lt_lastIndex
  have hOriginalAncestor : isAncestor array.raw row left.1 right.1 = true := by
    rw [← context.isAncestor_expand_eq_original_of_lt_lastIndex
      (expansionIndex + 1) row hRow hTarget]
    exact hAncestor
  have hParent := context.parentColumn_lt_lastIndex
  have hStable := original.preservesAncestor
    (left := ⟨left.1, by
      rw [context.array_length]
      omega⟩)
    (right := ⟨right.1, by
      rw [context.array_length]
      omega⟩) hOriginalAncestor
  rw [state.successorFamily_goodLabel witness,
    state.successorFamily_goodLabel witness,
    state.good_eq left, state.good_eq right]
  exact hStable

/-- 后继标签族在 `G×Bᵢ` 上保留全部 ancestry。 -/
theorem successorFamily_preserves_good_to_copy {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    {row : Nat} {left : Fin context.parentColumn}
    {copyNumber : Fin (expansionIndex + 2)}
    {localColumn : Fin context.blockLength}
    (hAncestor : isAncestor (array.expand (expansionIndex + 1)).raw row
      left.1 (context.copyPosition copyNumber.1 localColumn.1) = true) :
    frame.stableLt row
      ((state.successorFamily witness).goodLabel left)
      ((state.successorFamily witness).copyLabel copyNumber localColumn) := by
  by_cases hEarlier : copyNumber.1 < expansionIndex
  · have hTargetSmall : context.copyPosition copyNumber.1 localColumn.1 <
        (array.expand expansionIndex).raw.length :=
      context.copyPosition_lt_length (Nat.le_of_lt hEarlier) localColumn.isLt
    have hCurrentAncestor := context.isAncestor_expand_of_le_index
      (smallerIndex := expansionIndex) (largerIndex := expansionIndex + 1)
      (Nat.le_succ expansionIndex) hTargetSmall hAncestor
    rw [state.successorFamily_goodLabel witness,
      state.successorFamily_copyLabel_earlier witness copyNumber
        localColumn hEarlier]
    exact state.current.preservesAncestor hCurrentAncestor
  · by_cases hCurrent : copyNumber.1 = expansionIndex
    · have hCopyEq : copyNumber = ⟨expansionIndex, by omega⟩ :=
        Fin.ext hCurrent
      rw [hCopyEq] at hAncestor ⊢
      have hTargetSmall : context.copyPosition expansionIndex localColumn.1 <
          (array.expand expansionIndex).raw.length :=
        context.copyPosition_lt_length (Nat.le_refl _) localColumn.isLt
      have hCurrentAncestor := context.isAncestor_expand_of_le_index
        (smallerIndex := expansionIndex) (largerIndex := expansionIndex + 1)
        (Nat.le_succ expansionIndex) hTargetSmall hAncestor
      have hZeroAncestor : isAncestor (array.expand expansionIndex).raw row
          left.1 (context.copyPosition 0 localColumn.1) = true := by
        rw [context.good_to_copy_all_rows expansionIndex row
          left.isLt localColumn.isLt]
        exact hCurrentAncestor
      have hOriginalAncestor : isAncestor array.raw row left.1
          (context.parentColumn + localColumn.1) = true := by
        apply context.isAncestor_original_of_expand
          (index := expansionIndex)
        · have hLocal := localColumn.isLt
          change localColumn.1 < context.lastIndex - context.parentColumn at hLocal
          omega
        simpa [ExpansionContext.copyPosition,
          ExpansionContext.copyStart] using hZeroAncestor
      rw [state.successorFamily_goodLabel witness,
        state.successorFamily_copyLabel_current witness]
      let lowerIndex : Fin (context.copyStart expansionIndex) :=
        ⟨left.1, by
          simp [ExpansionContext.copyStart]
          exact Nat.lt_of_lt_of_le left.isLt (Nat.le_add_right _ _)⟩
      have hSource : frame.stableLt row
          (state.reflectionInput.lower lowerIndex)
          (state.reflectionInput.upper localColumn) := by
        change frame.stableLt row
          (state.current.label (state.lowerColumn lowerIndex))
          (original.label (state.upperColumn localColumn))
        have hLowerColumn : state.lowerColumn lowerIndex =
            ⟨left.1, by rw [context.length_expand]; omega⟩ := Fin.ext rfl
        rw [hLowerColumn, state.good_eq left]
        exact original.preservesAncestor hOriginalAncestor
      have hReflected := witness.preserves_lower_stableLt hSource
      simpa [reflectionInput, lowerColumn, lowerIndex] using hReflected
    · have hLast : copyNumber.1 = expansionIndex + 1 := by omega
      have hCopyEq : copyNumber = ⟨expansionIndex + 1, by omega⟩ :=
        Fin.ext hLast
      rw [hCopyEq] at hAncestor ⊢
      have hZeroAncestor : isAncestor
          (array.expand (expansionIndex + 1)).raw row left.1
          (context.copyPosition 0 localColumn.1) = true := by
        rw [context.good_to_copy_all_rows (expansionIndex + 1) row
          left.isLt localColumn.isLt]
        exact hAncestor
      have hOriginalAncestor : isAncestor array.raw row left.1
          (context.parentColumn + localColumn.1) = true := by
        apply context.isAncestor_original_of_expand
          (index := expansionIndex + 1)
        · have hLocal := localColumn.isLt
          change localColumn.1 < context.lastIndex - context.parentColumn at hLocal
          omega
        simpa [ExpansionContext.copyPosition,
          ExpansionContext.copyStart] using hZeroAncestor
      rw [state.successorFamily_goodLabel witness,
        state.successorFamily_copyLabel_last witness, state.good_eq left]
      exact original.preservesAncestor hOriginalAncestor

/-- 后继标签族在每个 `Bᵢ×Bᵢ` 上保留全部 ancestry。 -/
theorem successorFamily_preserves_inside_copy {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    {row : Nat} {copyNumber : Fin (expansionIndex + 2)}
    {leftLocal rightLocal : Fin context.blockLength}
    (hAncestor : isAncestor (array.expand (expansionIndex + 1)).raw row
      (context.copyPosition copyNumber.1 leftLocal.1)
      (context.copyPosition copyNumber.1 rightLocal.1) = true) :
    frame.stableLt row
      ((state.successorFamily witness).copyLabel copyNumber leftLocal)
      ((state.successorFamily witness).copyLabel copyNumber rightLocal) := by
  by_cases hEarlier : copyNumber.1 < expansionIndex
  · have hTargetSmall : context.copyPosition copyNumber.1 rightLocal.1 <
        (array.expand expansionIndex).raw.length :=
      context.copyPosition_lt_length (Nat.le_of_lt hEarlier) rightLocal.isLt
    have hCurrentAncestor := context.isAncestor_expand_of_le_index
      (smallerIndex := expansionIndex) (largerIndex := expansionIndex + 1)
      (Nat.le_succ expansionIndex) hTargetSmall hAncestor
    rw [state.successorFamily_copyLabel_earlier witness copyNumber
        leftLocal hEarlier,
      state.successorFamily_copyLabel_earlier witness copyNumber
        rightLocal hEarlier]
    exact state.current.preservesAncestor hCurrentAncestor
  · by_cases hCurrent : copyNumber.1 = expansionIndex
    · have hCopyEq : copyNumber = ⟨expansionIndex, by omega⟩ :=
        Fin.ext hCurrent
      rw [hCopyEq] at hAncestor ⊢
      have hTargetSmall : context.copyPosition expansionIndex rightLocal.1 <
          (array.expand expansionIndex).raw.length :=
        context.copyPosition_lt_length (Nat.le_refl _) rightLocal.isLt
      have hCurrentAncestor := context.isAncestor_expand_of_le_index
        (smallerIndex := expansionIndex) (largerIndex := expansionIndex + 1)
        (Nat.le_succ expansionIndex) hTargetSmall hAncestor
      have hZeroAncestor : isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition 0 leftLocal.1)
          (context.copyPosition 0 rightLocal.1) = true := by
        rw [context.inside_copy_all_rows expansionIndex row
          leftLocal.isLt rightLocal.isLt]
        exact hCurrentAncestor
      have hOriginalAncestor : isAncestor array.raw row
          (context.parentColumn + leftLocal.1)
          (context.parentColumn + rightLocal.1) = true := by
        apply context.isAncestor_original_of_expand
          (index := expansionIndex)
        · have hLocal := rightLocal.isLt
          change rightLocal.1 < context.lastIndex - context.parentColumn at hLocal
          omega
        simpa [ExpansionContext.copyPosition,
          ExpansionContext.copyStart] using hZeroAncestor
      rw [state.successorFamily_copyLabel_current witness,
        state.successorFamily_copyLabel_current witness]
      exact witness.preserves_upper_stableLt
        (original.preservesAncestor hOriginalAncestor)
    · have hLast : copyNumber.1 = expansionIndex + 1 := by omega
      have hCopyEq : copyNumber = ⟨expansionIndex + 1, by omega⟩ :=
        Fin.ext hLast
      rw [hCopyEq] at hAncestor ⊢
      have hZeroAncestor : isAncestor
          (array.expand (expansionIndex + 1)).raw row
          (context.copyPosition 0 leftLocal.1)
          (context.copyPosition 0 rightLocal.1) = true := by
        rw [context.inside_copy_all_rows (expansionIndex + 1) row
          leftLocal.isLt rightLocal.isLt]
        exact hAncestor
      have hOriginalAncestor : isAncestor array.raw row
          (context.parentColumn + leftLocal.1)
          (context.parentColumn + rightLocal.1) = true := by
        apply context.isAncestor_original_of_expand
          (index := expansionIndex + 1)
        · have hLocal := rightLocal.isLt
          change rightLocal.1 < context.lastIndex - context.parentColumn at hLocal
          omega
        simpa [ExpansionContext.copyPosition,
          ExpansionContext.copyStart] using hZeroAncestor
      rw [state.successorFamily_copyLabel_last witness,
        state.successorFamily_copyLabel_last witness]
      exact original.preservesAncestor hOriginalAncestor

/-- 后继标签族在 `Bᵢ×Bⱼ`（`i<j`）上保留全部 ancestry。 -/
theorem successorFamily_preserves_between_copies {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third)
    {row : Nat} {leftCopy rightCopy : Fin (expansionIndex + 2)}
    {leftLocal rightLocal : Fin context.blockLength}
    (hCopies : leftCopy < rightCopy)
    (hAncestor : isAncestor (array.expand (expansionIndex + 1)).raw row
      (context.copyPosition leftCopy.1 leftLocal.1)
      (context.copyPosition rightCopy.1 rightLocal.1) = true) :
    frame.stableLt row
      ((state.successorFamily witness).copyLabel leftCopy leftLocal)
      ((state.successorFamily witness).copyLabel rightCopy rightLocal) := by
  by_cases hRightEarlier : rightCopy.1 < expansionIndex
  · have hLeftEarlier : leftCopy.1 < expansionIndex :=
      Nat.lt_trans hCopies hRightEarlier
    have hTargetSmall : context.copyPosition rightCopy.1 rightLocal.1 <
        (array.expand expansionIndex).raw.length :=
      context.copyPosition_lt_length (Nat.le_of_lt hRightEarlier)
        rightLocal.isLt
    have hCurrentAncestor := context.isAncestor_expand_of_le_index
      (smallerIndex := expansionIndex) (largerIndex := expansionIndex + 1)
      (Nat.le_succ expansionIndex) hTargetSmall hAncestor
    rw [state.successorFamily_copyLabel_earlier witness leftCopy
        leftLocal hLeftEarlier,
      state.successorFamily_copyLabel_earlier witness rightCopy
        rightLocal hRightEarlier]
    exact state.current.preservesAncestor hCurrentAncestor
  · by_cases hRightCurrent : rightCopy.1 = expansionIndex
    · have hLeftEarlier : leftCopy.1 < expansionIndex := by omega
      have hRightEq : rightCopy = ⟨expansionIndex, by omega⟩ :=
        Fin.ext hRightCurrent
      rw [hRightEq] at hAncestor ⊢
      have hTargetSmall : context.copyPosition expansionIndex rightLocal.1 <
          (array.expand expansionIndex).raw.length :=
        context.copyPosition_lt_length (Nat.le_refl _) rightLocal.isLt
      have hCurrentAncestor := context.isAncestor_expand_of_le_index
        (smallerIndex := expansionIndex) (largerIndex := expansionIndex + 1)
        (Nat.le_succ expansionIndex) hTargetSmall hAncestor
      have hCurrentStable : frame.stableLt row
          (state.current.label
            ⟨context.copyPosition leftCopy.1 leftLocal.1,
              context.copyPosition_lt_length (Nat.le_of_lt hLeftEarlier)
                leftLocal.isLt⟩)
          (state.current.label
            ⟨context.copyPosition expansionIndex rightLocal.1,
              context.copyPosition_lt_length (Nat.le_refl _)
                rightLocal.isLt⟩) :=
        state.current.preservesAncestor hCurrentAncestor
      let lowerIndex : Fin (context.copyStart expansionIndex) :=
        ⟨context.copyPosition leftCopy.1 leftLocal.1, by
          have hBefore := context.column_lt_of_inCopy_of_lt_copy
            hLeftEarlier (context.copyPosition_in_block leftLocal.isLt)
            (context.copyPosition_in_block
              (copyNumber := expansionIndex) context.blockLength_pos)
          simpa [ExpansionContext.copyPosition] using hBefore⟩
      have hSource : frame.stableLt row
          (state.reflectionInput.lower lowerIndex)
          (state.reflectionInput.upper rightLocal) := by
        change frame.stableLt row
          (state.current.label (state.lowerColumn lowerIndex))
          (original.label (state.upperColumn rightLocal))
        have hLowerColumn : state.lowerColumn lowerIndex =
            ⟨context.copyPosition leftCopy.1 leftLocal.1,
              context.copyPosition_lt_length (Nat.le_of_lt hLeftEarlier)
                leftLocal.isLt⟩ := Fin.ext rfl
        rw [hLowerColumn]
        have hLastLabel : state.current.label
              ⟨context.copyPosition expansionIndex rightLocal.1,
                context.copyPosition_lt_length (Nat.le_refl _)
                  rightLocal.isLt⟩ =
            original.label (state.upperColumn rightLocal) := by
          simpa [upperColumn] using state.lastCopy_eq rightLocal
        rw [← hLastLabel]
        exact hCurrentStable
      have hReflected := witness.preserves_lower_stableLt hSource
      rw [state.successorFamily_copyLabel_earlier witness leftCopy
          leftLocal hLeftEarlier,
        state.successorFamily_copyLabel_current witness]
      simpa [reflectionInput, lowerColumn, lowerIndex] using hReflected
    · have hRightLast : rightCopy.1 = expansionIndex + 1 := by omega
      have hRightEq : rightCopy = ⟨expansionIndex + 1, by omega⟩ :=
        Fin.ext hRightLast
      rw [hRightEq] at hAncestor ⊢
      by_cases hLeftEarlier : leftCopy.1 < expansionIndex
      · have hToCurrent : isAncestor
            (array.expand (expansionIndex + 1)).raw row
            (context.copyPosition leftCopy.1 leftLocal.1)
            (context.copyPosition expansionIndex rightLocal.1) = true := by
          rw [context.earlier_to_successive_all_rows
            (expansionIndex + 1) row leftLocal.isLt rightLocal.isLt
            hLeftEarlier (by omega)]
          exact hAncestor
        have hTargetSmall : context.copyPosition expansionIndex rightLocal.1 <
            (array.expand expansionIndex).raw.length :=
          context.copyPosition_lt_length (Nat.le_refl _) rightLocal.isLt
        have hCurrentAncestor := context.isAncestor_expand_of_le_index
          (smallerIndex := expansionIndex) (largerIndex := expansionIndex + 1)
          (Nat.le_succ expansionIndex) hTargetSmall hToCurrent
        have hCurrentStable : frame.stableLt row
            (state.current.label
              ⟨context.copyPosition leftCopy.1 leftLocal.1,
                context.copyPosition_lt_length (Nat.le_of_lt hLeftEarlier)
                  leftLocal.isLt⟩)
            (state.current.label
              ⟨context.copyPosition expansionIndex rightLocal.1,
                context.copyPosition_lt_length (Nat.le_refl _)
                  rightLocal.isLt⟩) :=
          state.current.preservesAncestor hCurrentAncestor
        rw [state.successorFamily_copyLabel_earlier witness leftCopy
            leftLocal hLeftEarlier,
          state.successorFamily_copyLabel_last witness]
        have hLastLabel : state.current.label
              ⟨context.copyPosition expansionIndex rightLocal.1,
                context.copyPosition_lt_length (Nat.le_refl _)
                  rightLocal.isLt⟩ =
            original.label (state.upperColumn rightLocal) := by
          simpa [upperColumn] using state.lastCopy_eq rightLocal
        rw [← hLastLabel]
        exact hCurrentStable
      · have hLeftCurrent : leftCopy.1 = expansionIndex := by omega
        have hLeftEq : leftCopy = ⟨expansionIndex, by omega⟩ :=
          Fin.ext hLeftCurrent
        rw [hLeftEq] at hAncestor ⊢
        have hStructure := context.earlier_ancestor_later_first_of_ancestor
          (expansionIndex := expansionIndex + 1)
          leftLocal.isLt rightLocal.isLt (by omega) (Nat.le_refl _)
          hAncestor
        have hOriginalTop : isAncestor array.raw row
            (context.parentColumn + leftLocal.1) context.lastIndex = true := by
          have hBoundary := context.previous_to_next_all_rows
            (expansionIndex := expansionIndex + 1) (by omega) row
            hStructure.1 leftLocal.isLt
          rw [hBoundary]
          simpa using hStructure.2
        have hTopStable : frame.stableLt row
            (original.label (state.upperColumn leftLocal))
            (original.label state.lastColumn) :=
          original.preservesAncestor hOriginalTop
        have hReflected : frame.stableLt row (witness.image leftLocal)
            state.reflectionInput.lowerBound :=
          witness.reflects_to_lowerBound hStructure.1 hTopStable
        rw [state.successorFamily_copyLabel_current witness,
          state.successorFamily_copyLabel_last witness]
        rcases Nat.eq_zero_or_pos rightLocal.1 with hRightZero | hRightPositive
        · have hRightEq : rightLocal =
              ⟨0, context.blockLength_pos⟩ := Fin.ext hRightZero
          rw [hRightEq]
          have hBoundEq : state.reflectionInput.lowerBound =
              original.label (state.upperColumn
                (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)) := by
            simpa [reflectionInput, lowerBoundColumn, upperColumn] using
              state.lastCopy_eq
                (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)
          rwa [hBoundEq] at hReflected
        · have hFirstInside : isAncestor
              (array.expand (expansionIndex + 1)).raw row
              (context.copyPosition 0 0)
              (context.copyPosition 0 rightLocal.1) = true := by
            have hLastInside : isAncestor
                (array.expand (expansionIndex + 1)).raw row
                (context.copyPosition (expansionIndex + 1) 0)
                (context.copyPosition (expansionIndex + 1) rightLocal.1) = true := by
              rcases context.first_later_nonstrict_ancestor_of_earlier_ancestor
                  leftLocal.isLt rightLocal.isLt (by omega) (Nat.le_refl _)
                  hAncestor with hImpossible | hInside
              · exact (Nat.ne_of_gt hRightPositive hImpossible).elim
              · exact hInside
            rw [context.inside_copy_all_rows (expansionIndex + 1) row
              context.blockLength_pos rightLocal.isLt]
            exact hLastInside
          have hOriginalInside : isAncestor array.raw row context.parentColumn
              (context.parentColumn + rightLocal.1) = true := by
            apply context.isAncestor_original_of_expand
              (index := expansionIndex + 1)
            · have hLocal := rightLocal.isLt
              change rightLocal.1 < context.lastIndex - context.parentColumn at hLocal
              omega
            simpa [ExpansionContext.copyPosition,
              ExpansionContext.copyStart] using hFirstInside
          have hInsideStable : frame.stableLt row
              (original.label (state.upperColumn
                (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)))
              (original.label (state.upperColumn rightLocal)) :=
            original.preservesAncestor hOriginalInside
          have hBoundEq : state.reflectionInput.lowerBound =
              original.label (state.upperColumn
                (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)) := by
            have hLast := state.lastCopy_eq
              (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)
            change state.current.label state.lowerBoundColumn = _
            have hLowerColumn : state.lowerBoundColumn =
                ⟨context.copyPosition expansionIndex 0,
                  context.copyPosition_lt_length (Nat.le_refl _)
                    context.blockLength_pos⟩ := by
              apply Fin.ext
              rfl
            rw [hLowerColumn, hLast]
            apply congrArg original.label
            apply Fin.ext
            rfl
          rw [hBoundEq] at hReflected
          exact hStableTransitive hReflected hInsideStable

/-- 单轮反射产生后继 expansion 的完整八区域证书。 -/
noncomputable def successorCertificate {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third) :
    ExpansionRegionCertificate (frame := frame) context
      (expansionIndex + 1) where
  family := state.successorFamily witness
  good_lt_good := state.successorFamily_good_lt_good witness
  good_lt_copy := state.successorFamily_good_lt_copy witness
  inside_copy_lt := state.successorFamily_inside_copy_lt witness
  between_copies_lt := state.successorFamily_between_copies_lt witness
    hLtTransitive
  preserves_good := state.successorFamily_preserves_good witness
  preserves_good_to_copy :=
    state.successorFamily_preserves_good_to_copy witness
  preserves_inside_copy :=
    state.successorFamily_preserves_inside_copy witness
  preserves_between_copies := fun hCopies hAncestor =>
    state.successorFamily_preserves_between_copies witness
      hStableTransitive hCopies hAncestor

/-- 单轮反射产生 `A[i+1]` 的稳定表示。 -/
noncomputable def successorRepresentation {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third) :
    StableRepresentation frame (array.expand (expansionIndex + 1)) :=
  (state.successorCertificate witness hLtTransitive hStableTransitive).labeling.representation

@[simp]
theorem successorRepresentation_good {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third)
    (column : Fin context.parentColumn) :
    (state.successorRepresentation witness hLtTransitive hStableTransitive).label
        ⟨column.1, by rw [context.length_expand]; omega⟩ =
      original.label ⟨column.1, by
        rw [context.array_length]
        exact Nat.lt_trans column.isLt
          (Nat.lt_succ_of_lt context.parentColumn_lt_lastIndex)⟩ := by
  rw [show
    (state.successorRepresentation witness hLtTransitive
      hStableTransitive).label
        ⟨column.1, by rw [context.length_expand]; omega⟩ =
      (state.successorFamily witness).assembled
        ⟨column.1, by rw [context.length_expand]; omega⟩ from rfl]
  rw [(state.successorFamily witness).assembled_good column,
    state.successorFamily_goodLabel witness, state.good_eq column]

@[simp]
theorem successorRepresentation_lastCopy {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third)
    (localColumn : Fin context.blockLength) :
    (state.successorRepresentation witness hLtTransitive hStableTransitive).label
        ⟨context.copyPosition (expansionIndex + 1) localColumn.1,
          context.copyPosition_lt_length (Nat.le_refl _) localColumn.isLt⟩ =
      original.label (state.upperColumn localColumn) := by
  rw [show
    (state.successorRepresentation witness hLtTransitive
      hStableTransitive).label
        ⟨context.copyPosition (expansionIndex + 1) localColumn.1,
          context.copyPosition_lt_length (Nat.le_refl _) localColumn.isLt⟩ =
      (state.successorFamily witness).assembled
        ⟨context.copyPosition (expansionIndex + 1) localColumn.1,
          context.copyPosition_lt_length (Nat.le_refl _) localColumn.isLt⟩ from rfl]
  rw [(state.successorFamily witness).assembled_copy
    (⟨expansionIndex + 1, by omega⟩ : Fin (expansionIndex + 2)) localColumn,
    state.successorFamily_copyLabel_last witness]

/-- 有限层级支撑为后继表示补上下一轮反射所需的 cutoff 不变式。 -/
theorem exists_successorState {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context expansionIndex original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (hFinite : frame.FiniteLevelSupport)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third) :
    Nonempty (ExpansionReflectionState context (expansionIndex + 1) original) := by
  let nextRepresentation := state.successorRepresentation witness
    hLtTransitive hStableTransitive
  let nextLower : Fin (context.copyStart (expansionIndex + 1)) → Label :=
    fun lowerIndex => nextRepresentation.label
      ⟨lowerIndex.1, by
        apply Nat.lt_of_lt_of_le lowerIndex.isLt
        rw [context.length_expand]
        simp only [ExpansionContext.copyStart]
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_right context.blockLength (by omega)) _⟩
  let originalUpper : Fin context.blockLength → Label :=
    fun upperIndex => original.label (state.upperColumn upperIndex)
  rcases frame.exists_reflectionStabilityCutoff hFinite nextLower originalUpper with
    ⟨cutoff, hLower, hUpper⟩
  refine ⟨{
    current := nextRepresentation
    good_eq := ?_
    stabilityCutoff := cutoff
    lower_stableLt_below_cutoff := ?_
    upper_stableLt_below_cutoff := ?_
    lastCopy_eq := ?_ }⟩
  · intro column
    exact state.successorRepresentation_good witness hLtTransitive
      hStableTransitive column
  · intro lowerIndex upperIndex stableLevel hStable
    apply hLower lowerIndex upperIndex stableLevel
    simpa [nextLower, originalUpper, nextRepresentation, upperColumn] using hStable
  · intro left right stableLevel hStable
    apply hUpper left right stableLevel
    simpa [originalUpper, upperColumn] using hStable
  · intro localColumn
    exact state.successorRepresentation_lastCopy witness hLtTransitive
      hStableTransitive localColumn

/-- 原表示限制到 `A[0]=G⌒B₀`，得到反射迭代的初始稳定表示。 -/
def initialRepresentation {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    (context : ExpansionContext array)
    (original : StableRepresentation frame array) :
    StableRepresentation frame (array.expand 0) where
  label := fun column => original.label ⟨column.1, by
    rw [context.array_length]
    calc
      column.1 < (array.expand 0).raw.length := column.isLt
      _ = context.lastIndex := context.length_expand_zero
      _ < context.lastIndex + 1 := Nat.lt_succ_self _⟩
  strictlyIncreasing := by
    intro left right hOrder
    exact original.strictlyIncreasing hOrder
  preservesAncestor := by
    intro row left right hAncestor
    have hTarget : right.1 < context.lastIndex := by
      calc
        right.1 < (array.expand 0).raw.length := right.isLt
        _ = context.lastIndex := context.length_expand_zero
    exact original.preservesAncestor
      (context.isAncestor_original_of_expand hTarget hAncestor)

@[simp]
theorem initialRepresentation_label {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    (context : ExpansionContext array)
    (original : StableRepresentation frame array)
    (column : Fin (array.expand 0).raw.length) :
    (initialRepresentation context original).label column =
      original.label ⟨column.1, by
        rw [context.array_length]
        calc
          column.1 < (array.expand 0).raw.length := column.isLt
          _ = context.lastIndex := context.length_expand_zero
          _ < context.lastIndex + 1 := Nat.lt_succ_self _⟩ :=
  rfl

/-- 有限层级支撑为 `A[0]` 构造完整的初始反射状态。 -/
theorem exists_initialState {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    (context : ExpansionContext array)
    (original : StableRepresentation frame array)
    (hFinite : frame.FiniteLevelSupport) :
    Nonempty (ExpansionReflectionState context 0 original) := by
  let current := initialRepresentation context original
  let lower : Fin (context.copyStart 0) → Label :=
    fun index => current.label ⟨index.1, by
      apply Nat.lt_of_lt_of_le index.isLt
      rw [context.length_expand]
      simp [ExpansionContext.copyStart]⟩
  let upper : Fin context.blockLength → Label :=
    fun index => original.label ⟨context.parentColumn + index.1, by
      rw [context.array_length]
      have hLocal := index.isLt
      change index.1 < context.lastIndex - context.parentColumn at hLocal
      omega⟩
  rcases frame.exists_reflectionStabilityCutoff hFinite lower upper with
    ⟨cutoff, hLower, hUpper⟩
  refine ⟨{
    current := current
    good_eq := ?_
    stabilityCutoff := cutoff
    lower_stableLt_below_cutoff := ?_
    upper_stableLt_below_cutoff := ?_
    lastCopy_eq := ?_ }⟩
  · intro column
    rfl
  · intro lowerIndex upperIndex stableLevel hStable
    apply hLower lowerIndex upperIndex stableLevel
    simpa [lower, upper, current, initialRepresentation,
      ExpansionContext.copyStart] using hStable
  · intro left right stableLevel hStable
    apply hUpper left right stableLevel
    simpa [upper] using hStable
  · intro localColumn
    change original.label _ = original.label _
    apply congrArg original.label
    apply Fin.ext
    simp [ExpansionContext.copyPosition, ExpansionContext.copyStart]

/-- 从初始状态反复应用有限反射，得到每个 `A[index]` 的规范状态。 -/
noncomputable def iteratedState {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    (context : ExpansionContext array)
    (original : StableRepresentation frame array)
    (hReflection : FiniteReflectionPrinciple frame)
    (hFinite : frame.FiniteLevelSupport)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third) :
    (index : Nat) → ExpansionReflectionState context index original
  | 0 => Classical.choice (exists_initialState context original hFinite)
  | index + 1 =>
      let prior := iteratedState context original hReflection hFinite
        hLtTransitive hStableTransitive index
      let witness := prior.reflectionWitness hReflection
      Classical.choice (prior.exists_successorState witness hFinite
        hLtTransitive hStableTransitive)

/--
在 `A[index+1]` 中构造一轮额外反射后，限制到其前缀 `A[index]`。
额外的末复制块只作反射脚手架，不进入最终表示。
-/
noncomputable def boundedExpansionRepresentation {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {index : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context index original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third) :
    StableRepresentation frame (array.expand index) := by
  let successor := state.successorRepresentation witness
    hLtTransitive hStableTransitive
  let embed : Fin (array.expand index).raw.length →
      Fin (array.expand (index + 1)).raw.length := fun column =>
    ⟨column.1, Nat.lt_of_lt_of_le column.isLt
      (context.length_expand_mono (Nat.le_succ index))⟩
  exact {
    label := fun column => successor.label (embed column)
    strictlyIncreasing := by
      intro left right hOrder
      exact successor.strictlyIncreasing hOrder
    preservesAncestor := by
      intro row left right hAncestor
      apply successor.preservesAncestor
      exact context.isAncestor_expand_of_ge_index
        (Nat.le_succ index) right.isLt hAncestor }

/-- 额外反射后所得 `A[index]` 表示严格受当前末块首标签约束。 -/
theorem boundedExpansionRepresentation_boundedBy {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {index : Nat}
    {original : StableRepresentation frame array}
    (state : ExpansionReflectionState context index original)
    (witness : FiniteReflectionWitness state.reflectionInput)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third) :
    (state.boundedExpansionRepresentation witness hLtTransitive
      hStableTransitive).BoundedBy state.reflectionInput.lowerBound := by
  intro column
  let successor := state.successorRepresentation witness
    hLtTransitive hStableTransitive
  let embeddedColumn : Fin (array.expand (index + 1)).raw.length :=
    ⟨column.1, Nat.lt_of_lt_of_le column.isLt
      (context.length_expand_mono (Nat.le_succ index))⟩
  let boundaryColumn : Fin (array.expand (index + 1)).raw.length :=
    ⟨context.copyPosition (index + 1) 0,
      context.copyPosition_lt_length (Nat.le_refl _)
        context.blockLength_pos⟩
  have hColumnBoundary : embeddedColumn < boundaryColumn := by
    change column.1 < context.copyPosition (index + 1) 0
    calc
      column.1 < (array.expand index).raw.length := column.isLt
      _ = context.copyPosition (index + 1) 0 := by
        rw [context.length_expand]
        simp [ExpansionContext.copyPosition, ExpansionContext.copyStart]
  have hStrict := successor.strictlyIncreasing hColumnBoundary
  have hBoundaryLabel : successor.label boundaryColumn =
      state.reflectionInput.lowerBound := by
    have hSuccessorLast := state.successorRepresentation_lastCopy witness
      hLtTransitive hStableTransitive
      (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)
    have hStateLast := state.lastCopy_eq
      (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)
    change successor.label boundaryColumn = state.current.label state.lowerBoundColumn
    rw [hSuccessorLast]
    simpa [lowerBoundColumn, upperColumn] using hStateLast.symm
  change frame.lt (successor.label embeddedColumn)
    state.reflectionInput.lowerBound
  rwa [← hBoundaryLabel]

/--
在给定非退化 expansion 上下文时，完整反射迭代把任意原表示上界
严格下降为 `A[index]` 的新表示上界。
-/
theorem expand_bounded_of_context {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    (context : ExpansionContext array) (index : Nat)
    {bound : Label} (original : StableRepresentation frame array)
    (hBounded : original.BoundedBy bound)
    (hReflection : FiniteReflectionPrinciple frame)
    (hFinite : frame.FiniteLevelSupport)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third) :
    ∃ smallerBound,
      frame.lt smallerBound bound ∧
        ∃ expandedRepresentation : StableRepresentation frame
            (array.expand index),
          expandedRepresentation.BoundedBy smallerBound := by
  let state := iteratedState context original hReflection hFinite
    hLtTransitive hStableTransitive index
  let witness := state.reflectionWitness hReflection
  refine ⟨state.reflectionInput.lowerBound, ?_,
    state.boundedExpansionRepresentation witness hLtTransitive
      hStableTransitive,
    state.boundedExpansionRepresentation_boundedBy witness
      hLtTransitive hStableTransitive⟩
  have hOriginalBound := hBounded
    (state.upperColumn
      (⟨0, context.blockLength_pos⟩ : Fin context.blockLength))
  have hLast := state.lastCopy_eq
    (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)
  change frame.lt (state.current.label state.lowerBoundColumn) bound
  have hBoundEq : state.current.label state.lowerBoundColumn =
      original.label (state.upperColumn
        (⟨0, context.blockLength_pos⟩ : Fin context.blockLength)) := by
    simpa [lowerBoundColumn, upperColumn] using hLast
  rw [hBoundEq]
  exact hOriginalBound

/-- 无 maximal parent 时，expansion 仅删除末列；原表示限制即给出下降。 -/
def terminalExpansionRepresentation {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    (index lastIndex : Nat)
    (hLength : array.raw.length = lastIndex + 1)
    (hMaximal : maximalParentRow array.raw = none)
    (original : StableRepresentation frame array) :
    StableRepresentation frame (array.expand index) := by
  have hRaw : (array.expand index).raw =
      trimZeroRows (array.raw.take lastIndex) := by
    rw [ValidArray.raw_expand]
    simp [BMS.expand, expandRaw, hLength, hMaximal]
  have hExpandedLength : (array.expand index).raw.length = lastIndex := by
    rw [hRaw, length_trimZeroRows, List.length_take, hLength]
    simp
  exact {
    label := fun column => original.label ⟨column.1, by
      rw [hLength]
      calc
        column.1 < (array.expand index).raw.length := column.isLt
        _ = lastIndex := hExpandedLength
        _ < lastIndex + 1 := Nat.lt_succ_self _⟩
    strictlyIncreasing := by
      intro left right hOrder
      exact original.strictlyIncreasing hOrder
    preservesAncestor := by
      intro row left right hAncestor
      have hTarget : right.1 < lastIndex := by
        calc
          right.1 < (array.expand index).raw.length := right.isLt
          _ = lastIndex := hExpandedLength
      let leftColumn : Nat := left.1
      let rightColumn : Nat := right.1
      have hExpandedAncestor : isAncestor (array.expand index).raw row
          leftColumn rightColumn = true := hAncestor
      have hTrimmedAncestor : isAncestor
          (trimZeroRows (array.raw.take lastIndex)) row
          leftColumn rightColumn = true := by
        rw [← hRaw]
        exact hExpandedAncestor
      have hOriginalAncestor := isAncestor_original_of_trimZeroRows_take
        (by rw [hLength]; omega) hTarget hTrimmedAncestor
      exact original.preservesAncestor hOriginalAncestor }

/-- 退化删除末列分支受原末标签严格约束。 -/
theorem terminalExpansionRepresentation_boundedBy {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    (index lastIndex : Nat)
    (hLength : array.raw.length = lastIndex + 1)
    (hMaximal : maximalParentRow array.raw = none)
    (original : StableRepresentation frame array) :
    (terminalExpansionRepresentation index lastIndex hLength hMaximal original).BoundedBy
      (original.label ⟨lastIndex, by rw [hLength]; omega⟩) := by
  intro column
  apply original.strictlyIncreasing
  change column.1 < lastIndex
  have hRaw : (array.expand index).raw =
      trimZeroRows (array.raw.take lastIndex) := by
    rw [ValidArray.raw_expand]
    simp [BMS.expand, expandRaw, hLength, hMaximal]
  calc
    column.1 < (array.expand index).raw.length := column.isLt
    _ = lastIndex := by
      rw [hRaw, length_trimZeroRows, List.length_take, hLength]
      simp

/-- Lemma 2.6 与有限支撑推出 `RepresentationDescentSystem` 的总 expansion 字段。 -/
theorem expand_bounded {Label : Type u}
    {frame : StabilityFrame Label}
    (hReflection : FiniteReflectionPrinciple frame)
    (hFinite : frame.FiniteLevelSupport)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third)
    {array : ValidArray} (index : Nat) {bound : Label}
    (original : StableRepresentation frame array)
    (hBounded : original.BoundedBy bound)
    (hChanged : array.expand index ≠ array) :
    ∃ smallerBound,
      frame.lt smallerBound bound ∧
        ∃ expandedRepresentation : StableRepresentation frame
            (array.expand index),
          expandedRepresentation.BoundedBy smallerBound := by
  cases hLength : array.raw.length with
  | zero =>
      exfalso
      apply hChanged
      apply ValidArray.ext
      have hEmpty : array.raw = [] := List.eq_nil_of_length_eq_zero hLength
      rw [ValidArray.raw_expand, hEmpty]
      rfl
  | succ lastIndex =>
      cases hMaximal : maximalParentRow array.raw with
      | some maximalRow =>
          let context := Classical.choice
            (exists_expansionContext_of_maximalParentRow_eq_some hMaximal)
          exact expand_bounded_of_context context index original hBounded
            hReflection hFinite hLtTransitive hStableTransitive
      | none =>
          let smallerBound := original.label
            ⟨lastIndex, by rw [hLength]; omega⟩
          refine ⟨smallerBound, hBounded _,
            terminalExpansionRepresentation index lastIndex hLength hMaximal original,
            terminalExpansionRepresentation_boundedBy index lastIndex hLength
              hMaximal original⟩

end ExpansionReflectionState
end StabilityFrame
end BMS
end YesMetaZFC
