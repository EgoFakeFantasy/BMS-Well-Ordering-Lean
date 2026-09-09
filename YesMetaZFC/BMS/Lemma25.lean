import YesMetaZFC.BMS.Decomposition

/-!
# Hunter Lemma 2.5 的正式目标

五个字段逐项对应论文 Lemma 2.5 (i)--(v)。本文件只冻结目标接口；证明将在行号的
同时强归纳中构造 `Lemma25AtRow`。
-/

namespace YesMetaZFC
namespace BMS

namespace ExpansionContext

/-- Hunter Lemma 2.5 在固定行 `row` 上的五个结论。 -/
structure Lemma25AtRow {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex row : Nat) : Prop where
  /-- (i)：`G → B₀` 与 `G → Bₙ` 的 ancestry 相同。 -/
  good_to_copy :
    ∀ {goodColumn localColumn},
      goodColumn < context.parentColumn →
      localColumn < context.blockLength →
      isAncestor (array.expand expansionIndex).raw row goodColumn
          (context.copyPosition 0 localColumn) =
        isAncestor (array.expand expansionIndex).raw row goodColumn
          (context.copyPosition expansionIndex localColumn)

  /-- (ii)：`B₀` 与 `Bₙ` 内部的 ancestry 相同。 -/
  inside_copy :
    ∀ {leftLocal rightLocal},
      leftLocal < context.blockLength →
      rightLocal < context.blockLength →
      isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition 0 leftLocal)
          (context.copyPosition 0 rightLocal) =
        isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition expansionIndex leftLocal)
          (context.copyPosition expansionIndex rightLocal)

  /-- (iii)：原来的 `B₀ → C` 对应相邻副本边界上的 ancestry。 -/
  previous_to_next :
    0 < expansionIndex → row < context.maximalRow →
    ∀ {localColumn}, localColumn < context.blockLength →
      isAncestor array.raw row (context.parentColumn + localColumn)
          context.lastIndex =
        isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition (expansionIndex - 1) localColumn)
          (context.copyPosition expansionIndex 0)

  /-- (iv)：`Bₙ` 中非首列的 parent 只能落在 `G` 或同一个 `Bₙ`。 -/
  parent_locality :
    ∀ {localColumn found},
      0 < localColumn → localColumn < context.blockLength →
      parent row (array.expand expansionIndex).raw
          (context.copyPosition expansionIndex localColumn) = some found →
      found < context.parentColumn ∨ context.InCopy expansionIndex found

  /-- (v)：较早副本到相邻后两个目标副本的 ancestry 相同。 -/
  earlier_to_successive :
    ∀ {leftLocal rightLocal earlierCopy laterCopy},
      leftLocal < context.blockLength →
      rightLocal < context.blockLength →
      earlierCopy < laterCopy → laterCopy < expansionIndex →
      isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition earlierCopy leftLocal)
          (context.copyPosition laterCopy rightLocal) =
        isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition earlierCopy leftLocal)
          (context.copyPosition (laterCopy + 1) rightLocal)

/-- 同时归纳在当前行可使用的全部严格较低行结论。 -/
def Lemma25Below {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex row : Nat) : Prop :=
  ∀ lowerRow, lowerRow < row →
    Lemma25AtRow context expansionIndex lowerRow

/-- 分句 (ii) 自身所需的低行归纳假设。 -/
def InsideCopyBelow {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex row : Nat) : Prop :=
  ∀ lowerRow, lowerRow < row → ∀ {leftLocal rightLocal},
    leftLocal < context.blockLength → rightLocal < context.blockLength →
    isAncestor (array.expand expansionIndex).raw lowerRow
        (context.copyPosition 0 leftLocal) (context.copyPosition 0 rightLocal) =
      isAncestor (array.expand expansionIndex).raw lowerRow
        (context.copyPosition expansionIndex leftLocal)
        (context.copyPosition expansionIndex rightLocal)

/-- 分句 (iii) 自身所需的低行归纳假设。 -/
def PreviousToNextBelow {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex row : Nat) : Prop :=
  ∀ lowerRow, lowerRow < row → ∀ {localColumn},
    localColumn < context.blockLength →
    isAncestor array.raw lowerRow (context.parentColumn + localColumn)
        context.lastIndex =
      isAncestor (array.expand expansionIndex).raw lowerRow
        (context.copyPosition (expansionIndex - 1) localColumn)
        (context.copyPosition expansionIndex 0)

/-- Lemma 2.5 的最终组合目标。 -/
def Lemma25 {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex : Nat) : Prop :=
  ∀ row, Lemma25AtRow context expansionIndex row

/-- 零次复制时五个分句退化为恒等式或单个块内的坐标界。 -/
theorem lemma25AtRow_zero {array : ValidArray}
    (context : ExpansionContext array) (row : Nat) :
    Lemma25AtRow context 0 row := by
  constructor
  · intro goodColumn localColumn hGood hLocal
    rfl
  · intro leftLocal rightLocal hLeft hRight
    rfl
  · intro hPositive
    omega
  · intro localColumn found hPositive hLocal hParent
    have hFoundLt := parent_some_lt hParent
    by_cases hGood : found < context.parentColumn
    · exact Or.inl hGood
    · right
      constructor
      · simp [copyStart]
        omega
      · simp [copyStart]
        simp [copyPosition, copyStart] at hFoundLt
        omega
  · intro leftLocal rightLocal earlierCopy laterCopy hLeft hRight hEarlier hLater
    omega

theorem lemma25_zero {array : ValidArray} (context : ExpansionContext array) :
    Lemma25 context 0 := by
  intro row
  exact context.lemma25AtRow_zero row

/-- Lemma 2.5(ii) 的正向：`B₀` 内的 ancestry 会复制到任意 `Bᵢ`。 -/
theorem isAncestor_expand_copy_of_copy_zero {array : ValidArray}
    (context : ExpansionContext array) {expansionIndex row : Nat}
    (hBelow : InsideCopyBelow context expansionIndex row)
    (hRow : row < trimHeight (expandRaw array.raw expansionIndex))
    {leftLocal rightLocal : Nat}
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hAncestor : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition 0 leftLocal)
      (context.copyPosition 0 rightLocal) = true) :
    isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition expansionIndex leftLocal)
      (context.copyPosition expansionIndex rightLocal) = true := by
  rcases rectangular_iff_exists_uniformHeight.mp array.rectangular_eq with
    ⟨height, hUniform⟩
  have hExpandedUniform := ValidArray.uniformHeight_expand
    (index := expansionIndex) hUniform
  have hDefined : ∀ column,
      column < (array.expand expansionIndex).raw.length →
      ∃ value, entry? (array.expand expansionIndex).raw column row = some value := by
    intro column hColumn
    exact exists_entry_of_uniformHeight hExpandedUniform hColumn hRow
  have hZeroTarget := context.copyPosition_lt_length
    (index := expansionIndex) (copyNumber := 0) (Nat.zero_le _) hRightLocal
  have hCopyTarget := context.copyPosition_lt_length
    (Nat.le_refl expansionIndex) hRightLocal
  have hZeroCriterion :=
    (isAncestor_iff_ancestorBelow_and_recordMinimum hZeroTarget hDefined).mp hAncestor
  apply (isAncestor_iff_ancestorBelow_and_recordMinimum hCopyTarget hDefined).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [copyPosition, copyStart] using hZeroCriterion.1
  · intro lowerRow hLower
    have hLowerInside := hBelow lowerRow hLower hLeftLocal hRightLocal
    rw [← hLowerInside]
    exact hZeroCriterion.2.1 lowerRow hLower
  · have hOriginalAncestor : isAncestor array.raw row
        (context.parentColumn + leftLocal)
        (context.parentColumn + rightLocal) = true := by
      rw [← context.isAncestor_expand_copy_zero_eq_original
        expansionIndex row hRightLocal hRow]
      exact hAncestor
    have hAscending := ascending_eq_of_ancestor array.raw context.maximalRow
      context.parentColumn hOriginalAncestor
    rw [context.entryLess_expand_copies_of_uniform hUniform hRow
      (Nat.le_refl expansionIndex)
      hLeftLocal hRightLocal hAscending]
    exact hZeroCriterion.2.2.1
  · intro middle hLeftMiddle hMiddleRight hMiddleBelow
    have hMiddleInCopy : context.InCopy expansionIndex middle := by
      constructor
      · have hLeftInCopy := context.copyPosition_in_block
          (copyNumber := expansionIndex) hLeftLocal
        omega
      · have hRightInCopy := context.copyPosition_in_block
          (copyNumber := expansionIndex) hRightLocal
        omega
    rcases context.inCopy_iff_exists_copyPosition.mp hMiddleInCopy with
      ⟨middleLocal, hMiddleLocal, hMiddlePosition⟩
    have hLocalOrder : leftLocal < middleLocal ∧ middleLocal < rightLocal := by
      subst middle
      simp only [copyPosition, copyStart] at hLeftMiddle hMiddleRight
      omega
    have hZeroMiddleBelow : AncestorBelow (array.expand expansionIndex).raw row
        (context.copyPosition 0 middleLocal)
        (context.copyPosition 0 rightLocal) := by
      intro lowerRow hLower
      have hLowerInside := hBelow lowerRow hLower hMiddleLocal hRightLocal
      rw [hLowerInside]
      subst middle
      exact hMiddleBelow lowerRow hLower
    rcases hDefined (context.copyPosition 0 middleLocal)
        (context.copyPosition_lt_length (Nat.zero_le _) hMiddleLocal) with
      ⟨middleValue, hMiddleEntry⟩
    have hZeroLeftMiddle := isAncestor_of_ancestorBelow_between
      hAncestor hZeroMiddleBelow
      (by
        simp only [copyPosition, copyStart, Nat.zero_mul, Nat.add_zero]
        omega)
      (by
        simp only [copyPosition, copyStart, Nat.zero_mul, Nat.add_zero]
        omega)
      ⟨middleValue, hMiddleEntry⟩
    have hOriginalLeftMiddle : isAncestor array.raw row
        (context.parentColumn + leftLocal)
        (context.parentColumn + middleLocal) = true := by
      rw [← context.isAncestor_expand_copy_zero_eq_original
        expansionIndex row hMiddleLocal hRow]
      exact hZeroLeftMiddle
    have hAscending := ascending_eq_of_ancestor array.raw context.maximalRow
      context.parentColumn hOriginalLeftMiddle
    subst middle
    rw [context.entryLess_expand_copies_of_uniform hUniform hRow
      (Nat.le_refl expansionIndex)
      hLeftLocal hMiddleLocal hAscending]
    exact hZeroCriterion.2.2.2 (context.copyPosition 0 middleLocal)
      (by
        simp only [copyPosition, copyStart, Nat.zero_mul, Nat.add_zero]
        omega)
      (by
        simp only [copyPosition, copyStart, Nat.zero_mul, Nat.add_zero]
        omega)
      hZeroMiddleBelow

/-- Lemma 2.5(ii) 的反向：最后副本不会产生 `B₀` 中原本没有的内部 ancestry。 -/
theorem isAncestor_expand_copy_zero_of_copy {array : ValidArray}
    (context : ExpansionContext array) {expansionIndex row : Nat}
    (hBelow : InsideCopyBelow context expansionIndex row)
    (hRow : row < trimHeight (expandRaw array.raw expansionIndex))
    {leftLocal rightLocal : Nat}
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength)
    (hAncestor : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition expansionIndex leftLocal)
      (context.copyPosition expansionIndex rightLocal) = true) :
    isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition 0 leftLocal)
      (context.copyPosition 0 rightLocal) = true := by
  induction rightLocal using Nat.strongRecOn generalizing leftLocal with
  | ind rightLocal ih =>
      rcases rectangular_iff_exists_uniformHeight.mp array.rectangular_eq with
        ⟨height, hUniform⟩
      have hExpandedUniform := ValidArray.uniformHeight_expand
        (index := expansionIndex) hUniform
      have hDefined : ∀ column,
          column < (array.expand expansionIndex).raw.length →
          ∃ value, entry? (array.expand expansionIndex).raw column row = some value := by
        intro column hColumn
        exact exists_entry_of_uniformHeight hExpandedUniform hColumn hRow
      have hCopyTarget := context.copyPosition_lt_length
        (Nat.le_refl expansionIndex) hRightLocal
      have hZeroTarget := context.copyPosition_lt_length
        (index := expansionIndex) (copyNumber := 0) (Nat.zero_le _) hRightLocal
      have hCopyCriterion :=
        (isAncestor_iff_ancestorBelow_and_recordMinimum hCopyTarget hDefined).mp hAncestor
      have hZeroBelow : AncestorBelow (array.expand expansionIndex).raw row
          (context.copyPosition 0 leftLocal)
          (context.copyPosition 0 rightLocal) := by
        intro lowerRow hLower
        have hLowerInside := hBelow lowerRow hLower hLeftLocal hRightLocal
        rw [hLowerInside]
        exact hCopyCriterion.2.1 lowerRow hLower
      apply (isAncestor_iff_ancestorBelow_and_recordMinimum
        hZeroTarget hDefined).mpr
      refine ⟨?_, hZeroBelow, ?_, ?_⟩
      · simpa [copyPosition, copyStart] using hCopyCriterion.1
      · cases hRightAscending : ascending array.raw context.maximalRow
            context.parentColumn rightLocal row with
        | false =>
            exact context.entryLess_expand_copy_zero_of_not_ascending
              hUniform hRow (Nat.le_refl expansionIndex) hLeftLocal hRightLocal
              hRightAscending hCopyCriterion.2.2.1
        | true =>
            have hOriginalBelow : AncestorBelow array.raw row
                (context.parentColumn + leftLocal)
                (context.parentColumn + rightLocal) := by
              intro lowerRow hLower
              have hZeroAtLower := hZeroBelow lowerRow hLower
              rw [context.isAncestor_expand_copy_zero_eq_original
                expansionIndex lowerRow hRightLocal (Nat.lt_trans hLower hRow)] at hZeroAtLower
              exact hZeroAtLower
            have hSourceRow : row < height := Nat.lt_of_lt_of_le hRow
              (trimHeight_le_of_uniform (uniformHeight_expandRaw hUniform))
            rcases context.exists_badPart_entry hUniform hLeftLocal hSourceRow with
              ⟨leftColumn, leftValue, hLeftColumn, hLeftValue⟩
            have hLeftEntry : ∃ value,
                entry? array.raw (context.parentColumn + leftLocal) row = some value := by
              refine ⟨leftValue, ?_⟩
              rw [← context.entry?_badPart hLeftLocal]
              simp [entry?, hLeftColumn, hLeftValue]
            have hLeftAscending := ascending_of_ancestorBelow_of_ascending
              array.raw context.maximalRow context.parentColumn
              (by
                simpa [copyPosition, copyStart] using hCopyCriterion.1)
              hOriginalBelow hLeftEntry hRightAscending
            have hAscendingEqual : ascending array.raw context.maximalRow
                context.parentColumn leftLocal row =
                ascending array.raw context.maximalRow context.parentColumn rightLocal row := by
              rw [hLeftAscending, hRightAscending]
            rw [← context.entryLess_expand_copies_of_uniform hUniform hRow
              (Nat.le_refl expansionIndex) hLeftLocal hRightLocal hAscendingEqual]
            exact hCopyCriterion.2.2.1
      · intro middle hLeftMiddle hMiddleRight hMiddleBelow
        have hMiddleInZero : context.InCopy 0 middle := by
          constructor
          · have hLeftInZero := context.copyPosition_in_block
              (copyNumber := 0) hLeftLocal
            omega
          · have hRightInZero := context.copyPosition_in_block
              (copyNumber := 0) hRightLocal
            omega
        rcases context.inCopy_iff_exists_copyPosition.mp hMiddleInZero with
          ⟨middleLocal, hMiddleLocal, hMiddlePosition⟩
        have hLocalOrder : leftLocal < middleLocal ∧ middleLocal < rightLocal := by
          subst middle
          simp only [copyPosition, copyStart] at hLeftMiddle hMiddleRight
          omega
        have hCopyMiddleBelow : AncestorBelow (array.expand expansionIndex).raw row
            (context.copyPosition expansionIndex middleLocal)
            (context.copyPosition expansionIndex rightLocal) := by
          intro lowerRow hLower
          have hLowerInside := hBelow lowerRow hLower hMiddleLocal hRightLocal
          rw [← hLowerInside]
          subst middle
          exact hMiddleBelow lowerRow hLower
        have hCopyLeftMiddleEntry := hCopyCriterion.2.2.2
          (context.copyPosition expansionIndex middleLocal)
          (by
            simp only [copyPosition, copyStart]
            omega)
          (by
            simp only [copyPosition, copyStart]
            omega)
          hCopyMiddleBelow
        rcases hDefined (context.copyPosition expansionIndex middleLocal)
            (context.copyPosition_lt_length (Nat.le_refl expansionIndex) hMiddleLocal) with
          ⟨middleValue, hMiddleEntry⟩
        have hCopyLeftMiddle := isAncestor_of_ancestorBelow_between
          hAncestor hCopyMiddleBelow
          (by
            simp only [copyPosition, copyStart]
            omega)
          (by
            simp only [copyPosition, copyStart]
            omega)
          ⟨middleValue, hMiddleEntry⟩
        subst middle
        cases hMiddleAscending : ascending array.raw context.maximalRow
            context.parentColumn middleLocal row with
        | false =>
            exact context.entryLess_expand_copy_zero_of_not_ascending
              hUniform hRow (Nat.le_refl expansionIndex) hLeftLocal hMiddleLocal
              hMiddleAscending hCopyLeftMiddleEntry
        | true =>
            have hZeroLeftMiddle := ih middleLocal hLocalOrder.2 hLeftLocal
              hMiddleLocal hCopyLeftMiddle
            have hOriginalLeftMiddle : isAncestor array.raw row
                (context.parentColumn + leftLocal)
                (context.parentColumn + middleLocal) = true := by
              rw [← context.isAncestor_expand_copy_zero_eq_original
                expansionIndex row hMiddleLocal hRow]
              exact hZeroLeftMiddle
            have hAscendingEqual := ascending_eq_of_ancestor array.raw
              context.maximalRow context.parentColumn hOriginalLeftMiddle
            rw [← context.entryLess_expand_copies_of_uniform hUniform hRow
              (Nat.le_refl expansionIndex) hLeftLocal hMiddleLocal hAscendingEqual]
            exact hCopyLeftMiddleEntry

/-- 较低行五分句成立时，Lemma 2.5(ii) 在当前行成立。 -/
theorem isAncestor_expand_copies_eq {array : ValidArray}
    (context : ExpansionContext array) {expansionIndex row : Nat}
    (hBelow : InsideCopyBelow context expansionIndex row)
    (hRow : row < trimHeight (expandRaw array.raw expansionIndex))
    {leftLocal rightLocal : Nat}
    (hLeftLocal : leftLocal < context.blockLength)
    (hRightLocal : rightLocal < context.blockLength) :
    isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition 0 rightLocal) =
      isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition expansionIndex leftLocal)
        (context.copyPosition expansionIndex rightLocal) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact context.isAncestor_expand_copy_of_copy_zero hBelow hRow
      hLeftLocal hRightLocal
  · exact context.isAncestor_expand_copy_zero_of_copy hBelow hRow
      hLeftLocal hRightLocal

/-- Hunter Lemma 2.5(ii)，对所有行无条件成立。 -/
theorem inside_copy_all_rows {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat) :
    ∀ row {leftLocal rightLocal},
      leftLocal < context.blockLength → rightLocal < context.blockLength →
      isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition 0 leftLocal)
          (context.copyPosition 0 rightLocal) =
        isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition expansionIndex leftLocal)
          (context.copyPosition expansionIndex rightLocal) := by
  intro row
  induction row using Nat.strongRecOn with
  | ind row ih =>
      intro leftLocal rightLocal hLeftLocal hRightLocal
      by_cases hRow : row < trimHeight (expandRaw array.raw expansionIndex)
      · apply context.isAncestor_expand_copies_eq
          (fun lowerRow hLower => ih lowerRow hLower) hRow
          hLeftLocal hRightLocal
      · rw [isAncestor_expand_eq_false_of_le expansionIndex
          (context.copyPosition 0 leftLocal)
          (context.copyPosition 0 rightLocal) (by omega)]
        rw [isAncestor_expand_eq_false_of_le expansionIndex
          (context.copyPosition expansionIndex leftLocal)
          (context.copyPosition expansionIndex rightLocal) (by omega)]

/-- 较低行五分句成立时，Lemma 2.5(iii) 在当前行成立。 -/
theorem isAncestor_previous_to_next_eq {array : ValidArray}
    (context : ExpansionContext array) {expansionIndex row localColumn : Nat}
    (hBelow : PreviousToNextBelow context expansionIndex row)
    (hExpansionIndex : 0 < expansionIndex)
    (hMaximalRow : row < context.maximalRow)
    (hLocal : localColumn < context.blockLength)
    (hRow : row < trimHeight (expandRaw array.raw expansionIndex)) :
    isAncestor array.raw row (context.parentColumn + localColumn)
        context.lastIndex =
      isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition (expansionIndex - 1) localColumn)
        (context.copyPosition expansionIndex 0) := by
  rcases rectangular_iff_exists_uniformHeight.mp array.rectangular_eq with
    ⟨height, hUniform⟩
  have hSourceRow : row < height := Nat.lt_of_lt_of_le hRow
    (trimHeight_le_of_uniform (uniformHeight_expandRaw hUniform))
  have hSourceDefined : ∀ column, column < array.raw.length →
      ∃ value, entry? array.raw column row = some value := by
    intro column hColumn
    exact exists_entry_of_uniformHeight hUniform hColumn hSourceRow
  have hExpandedUniform := ValidArray.uniformHeight_expand
    (index := expansionIndex) hUniform
  have hExpandedDefined : ∀ column,
      column < (array.expand expansionIndex).raw.length →
      ∃ value, entry? (array.expand expansionIndex).raw column row = some value := by
    intro column hColumn
    exact exists_entry_of_uniformHeight hExpandedUniform hColumn hRow
  have hLastValid : context.lastIndex < array.raw.length := by
    rw [context.array_length]
    omega
  have hNextValid := context.copyPosition_lt_length
    (index := expansionIndex) (copyNumber := expansionIndex)
    (Nat.le_refl expansionIndex) context.blockLength_pos
  have hFirstAncestor : isAncestor array.raw row context.parentColumn
      context.lastIndex = true :=
    isAncestor_of_lt_row hMaximalRow (direct_parent_isAncestor context.parent_eq)
  have hAscendingOfBelow : ∀ {candidateLocal},
      candidateLocal < context.blockLength →
      AncestorBelow array.raw row (context.parentColumn + candidateLocal)
        context.lastIndex →
      ascending array.raw context.maximalRow context.parentColumn
        candidateLocal row = true := by
    intro candidateLocal hCandidateLocal hCandidateBelow
    by_cases hCandidateZero : candidateLocal = 0
    · simp [ascending, hMaximalRow, hCandidateZero]
    · rcases context.exists_badPart_entry hUniform hCandidateLocal hSourceRow with
        ⟨candidateList, candidateValue, hCandidateList, hCandidateValue⟩
      have hCandidateEntry : entry? array.raw
          (context.parentColumn + candidateLocal) row = some candidateValue := by
        rw [← context.entry?_badPart hCandidateLocal]
        simp [entry?, hCandidateList, hCandidateValue]
      have hCandidateLast : context.parentColumn + candidateLocal <
          context.lastIndex := by
        simp only [blockLength] at hCandidateLocal
        omega
      have hFirstCandidate := isAncestor_of_ancestorBelow_between
        hFirstAncestor hCandidateBelow (by omega) hCandidateLast
        ⟨candidateValue, hCandidateEntry⟩
      simp [ascending, hMaximalRow, hFirstCandidate]
  have hPreviousCopy : expansionIndex - 1 ≤ expansionIndex := by omega
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hSourceAncestor
    have hSourceCriterion :=
      (isAncestor_iff_ancestorBelow_and_recordMinimum
        hLastValid hSourceDefined).mp hSourceAncestor
    have hCandidateAscending := hAscendingOfBelow hLocal hSourceCriterion.2.1
    apply (isAncestor_iff_ancestorBelow_and_recordMinimum
      hNextValid hExpandedDefined).mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hWithin := (context.copyPosition_in_block
          (copyNumber := expansionIndex - 1) hLocal).2
      have hEndEq : context.copyStart ((expansionIndex - 1) + 1) =
          context.copyPosition expansionIndex 0 := by
        simp only [copyPosition, Nat.add_zero]
        congr
        omega
      rwa [hEndEq] at hWithin
    · intro lowerRow hLower
      have hLowerBridge := hBelow lowerRow hLower hLocal
      rw [← hLowerBridge]
      exact hSourceCriterion.2.1 lowerRow hLower
    · rw [context.entryLess_expand_previous_to_next_eq_original
        hUniform hExpansionIndex hLocal hRow hCandidateAscending]
      exact hSourceCriterion.2.2.1
    · intro middle hLeftMiddle hMiddleNext hMiddleBelow
      have hMiddleInPrevious : context.InCopy (expansionIndex - 1) middle := by
        constructor
        · have hLeftInPrevious := context.copyPosition_in_block
            (copyNumber := expansionIndex - 1) hLocal
          omega
        · have hEndEq : context.copyStart ((expansionIndex - 1) + 1) =
              context.copyPosition expansionIndex 0 := by
            simp only [copyPosition, Nat.add_zero]
            congr
            omega
          rw [hEndEq]
          exact hMiddleNext
      rcases context.inCopy_iff_exists_copyPosition.mp hMiddleInPrevious with
        ⟨middleLocal, hMiddleLocal, hMiddlePosition⟩
      have hLocalMiddle : localColumn < middleLocal := by
        subst middle
        simp only [copyPosition, copyStart] at hLeftMiddle
        omega
      have hSourceMiddleBelow : AncestorBelow array.raw row
          (context.parentColumn + middleLocal) context.lastIndex := by
        intro lowerRow hLower
        have hLowerBridge := hBelow lowerRow hLower hMiddleLocal
        rw [hLowerBridge]
        subst middle
        exact hMiddleBelow lowerRow hLower
      have hMiddleAscending := hAscendingOfBelow hMiddleLocal hSourceMiddleBelow
      have hAscendingEqual : ascending array.raw context.maximalRow
          context.parentColumn localColumn row =
          ascending array.raw context.maximalRow context.parentColumn middleLocal row := by
        rw [hCandidateAscending, hMiddleAscending]
      subst middle
      rw [context.entryLess_expand_copies_of_uniform hUniform hRow hPreviousCopy
        hLocal hMiddleLocal hAscendingEqual]
      rw [entryLess_expand_of_lt expansionIndex _ _ row hRow]
      rw [context.entryLess_expandRaw_copy_zero_eq_original expansionIndex row
        hLocal hMiddleLocal]
      exact hSourceCriterion.2.2.2 (context.parentColumn + middleLocal)
        (by omega) (by
          simp only [blockLength] at hMiddleLocal
          omega) hSourceMiddleBelow
  · intro hExpandedAncestor
    have hExpandedCriterion :=
      (isAncestor_iff_ancestorBelow_and_recordMinimum
        hNextValid hExpandedDefined).mp hExpandedAncestor
    have hSourceBelow : AncestorBelow array.raw row
        (context.parentColumn + localColumn) context.lastIndex := by
      intro lowerRow hLower
      have hLowerBridge := hBelow lowerRow hLower hLocal
      rw [hLowerBridge]
      exact hExpandedCriterion.2.1 lowerRow hLower
    have hCandidateAscending := hAscendingOfBelow hLocal hSourceBelow
    apply (isAncestor_iff_ancestorBelow_and_recordMinimum
      hLastValid hSourceDefined).mpr
    refine ⟨?_, hSourceBelow, ?_, ?_⟩
    · simp only [blockLength] at hLocal
      omega
    · rw [← context.entryLess_expand_previous_to_next_eq_original
        hUniform hExpansionIndex hLocal hRow hCandidateAscending]
      exact hExpandedCriterion.2.2.1
    · intro middle hLeftMiddle hMiddleLast hMiddleBelow
      let middleLocal := middle - context.parentColumn
      have hMiddleEq : middle = context.parentColumn + middleLocal := by
        dsimp only [middleLocal]
        omega
      have hMiddleLocal : middleLocal < context.blockLength := by
        simp only [middleLocal, blockLength]
        omega
      have hLocalMiddle : localColumn < middleLocal := by
        dsimp only [middleLocal]
        omega
      have hExpandedMiddleBelow : AncestorBelow
          (array.expand expansionIndex).raw row
          (context.copyPosition (expansionIndex - 1) middleLocal)
          (context.copyPosition expansionIndex 0) := by
        intro lowerRow hLower
        have hLowerBridge := hBelow lowerRow hLower hMiddleLocal
        rw [← hLowerBridge]
        rw [← hMiddleEq]
        exact hMiddleBelow lowerRow hLower
      have hMiddleAscending := hAscendingOfBelow hMiddleLocal (by
        rw [← hMiddleEq]
        exact hMiddleBelow)
      have hAscendingEqual : ascending array.raw context.maximalRow
          context.parentColumn localColumn row =
          ascending array.raw context.maximalRow context.parentColumn middleLocal row := by
        rw [hCandidateAscending, hMiddleAscending]
      have hExpandedEntry := hExpandedCriterion.2.2.2
        (context.copyPosition (expansionIndex - 1) middleLocal)
        (by
          simp only [copyPosition, copyStart]
          omega)
        (by
          have hEndEq : context.copyStart ((expansionIndex - 1) + 1) =
              context.copyPosition expansionIndex 0 := by
            simp only [copyPosition, Nat.add_zero]
            congr
            omega
          exact Nat.lt_of_lt_of_le
            (context.copyPosition_in_block
              (copyNumber := expansionIndex - 1) hMiddleLocal).2
            (Nat.le_of_eq hEndEq))
        hExpandedMiddleBelow
      rw [context.entryLess_expand_copies_of_uniform hUniform hRow hPreviousCopy
        hLocal hMiddleLocal hAscendingEqual] at hExpandedEntry
      rw [entryLess_expand_of_lt expansionIndex _ _ row hRow] at hExpandedEntry
      rw [context.entryLess_expandRaw_copy_zero_eq_original expansionIndex row
        hLocal hMiddleLocal] at hExpandedEntry
      rwa [hMiddleEq]

/-- Hunter Lemma 2.5(iii)，对全部 `row < m₀` 无条件成立。 -/
theorem previous_to_next_all_rows {array : ValidArray}
    (context : ExpansionContext array) {expansionIndex : Nat}
    (hExpansionIndex : 0 < expansionIndex) :
    ∀ row, row < context.maximalRow → ∀ {localColumn},
      localColumn < context.blockLength →
      isAncestor array.raw row (context.parentColumn + localColumn)
          context.lastIndex =
        isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition (expansionIndex - 1) localColumn)
          (context.copyPosition expansionIndex 0) := by
  intro row
  induction row using Nat.strongRecOn with
  | ind row ih =>
      intro hMaximalRow localColumn hLocal
      have hRow : row < trimHeight (expandRaw array.raw expansionIndex) :=
        Nat.lt_of_lt_of_le hMaximalRow
          (context.maximalRow_le_trimHeight_expandRaw hExpansionIndex)
      apply context.isAncestor_previous_to_next_eq
        (fun lowerRow hLower => ih lowerRow hLower
          (Nat.lt_trans hLower hMaximalRow))
        hExpansionIndex hMaximalRow hLocal hRow

/-- 在一个较大的 expansion 中，相邻两个复制块的首列保持 `row < m₀` ancestry。 -/
theorem first_copy_ancestor_next {array : ValidArray}
    (context : ExpansionContext array) {expansionIndex row copyNumber : Nat}
    (hCopy : copyNumber < expansionIndex)
    (hRow : row < context.maximalRow) :
    isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition copyNumber 0)
      (context.copyPosition (copyNumber + 1) 0) = true := by
  have hSmallPositive : 0 < copyNumber + 1 := by omega
  have hSmallLe : copyNumber + 1 ≤ expansionIndex := by omega
  have hOriginalFirst : isAncestor array.raw row context.parentColumn
      context.lastIndex = true :=
    isAncestor_of_lt_row hRow (direct_parent_isAncestor context.parent_eq)
  have hBoundarySmall := context.previous_to_next_all_rows
    hSmallPositive row hRow (localColumn := 0) context.blockLength_pos
  have hPreviousEq : copyNumber + 1 - 1 = copyNumber := by omega
  rw [hPreviousEq] at hBoundarySmall
  have hSmallAncestor : isAncestor (array.expand (copyNumber + 1)).raw row
      (context.copyPosition copyNumber 0)
      (context.copyPosition (copyNumber + 1) 0) = true := by
    rw [← hBoundarySmall]
    exact hOriginalFirst
  have hTargetSmall := context.copyPosition_lt_length
    (index := copyNumber + 1) (copyNumber := copyNumber + 1)
    (Nat.le_refl _) context.blockLength_pos
  rw [← context.isAncestor_expand_indices_eq_of_lt_length
    hSmallPositive hSmallLe hTargetSmall hRow]
  exact hSmallAncestor

/-- 在 `row < m₀` 上，较早复制块的首列是任意较晚复制块首列的 ancestor。 -/
theorem first_copy_ancestor_of_lt {array : ValidArray}
    (context : ExpansionContext array) {expansionIndex row earlierCopy laterCopy : Nat}
    (hLater : laterCopy ≤ expansionIndex)
    (hCopies : earlierCopy < laterCopy)
    (hRow : row < context.maximalRow) :
    isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition earlierCopy 0)
      (context.copyPosition laterCopy 0) = true := by
  induction laterCopy using Nat.strongRecOn with
  | ind laterCopy ih =>
      by_cases hAdjacent : earlierCopy + 1 = laterCopy
      · subst laterCopy
        exact context.first_copy_ancestor_next (by omega) hRow
      · have hPrevious : earlierCopy < laterCopy - 1 := by omega
        have hPreviousLt : laterCopy - 1 < laterCopy := by omega
        have hEarlierPrevious := ih (laterCopy - 1) hPreviousLt (by omega)
          hPrevious
        have hPreviousNext := context.first_copy_ancestor_next
          (expansionIndex := expansionIndex) (copyNumber := laterCopy - 1)
          (by omega) hRow
        have hNextEq : laterCopy - 1 + 1 = laterCopy := by omega
        rw [hNextEq] at hPreviousNext
        exact isAncestor_trans hEarlierPrevious hPreviousNext

/-- 较早副本中的列若到达下一副本首列，则对应回原数组中的 `B₀ → C`。 -/
theorem original_last_ancestor_of_copy_to_next_first
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row copyNumber localColumn : Nat}
    (hCopy : copyNumber < expansionIndex)
    (hRow : row < context.maximalRow)
    (hLocal : localColumn < context.blockLength)
    (hAncestor : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition copyNumber localColumn)
      (context.copyPosition (copyNumber + 1) 0) = true) :
    isAncestor array.raw row (context.parentColumn + localColumn)
      context.lastIndex = true := by
  have hSmallPositive : 0 < copyNumber + 1 := by omega
  have hSmallLe : copyNumber + 1 ≤ expansionIndex := by omega
  have hTargetSmall := context.copyPosition_lt_length
    (index := copyNumber + 1) (copyNumber := copyNumber + 1)
    (Nat.le_refl _) context.blockLength_pos
  have hPrefix : isAncestor (array.expand (copyNumber + 1)).raw row
        (context.copyPosition copyNumber localColumn)
        (context.copyPosition (copyNumber + 1) 0) =
      isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition copyNumber localColumn)
        (context.copyPosition (copyNumber + 1) 0) :=
    context.isAncestor_expand_indices_eq_of_lt_length
      (ancestor := context.copyPosition copyNumber localColumn)
      hSmallPositive hSmallLe hTargetSmall hRow
  have hSmallAncestor : isAncestor (array.expand (copyNumber + 1)).raw row
      (context.copyPosition copyNumber localColumn)
      (context.copyPosition (copyNumber + 1) 0) = true := by
    rw [hPrefix]
    exact hAncestor
  have hBoundary := context.previous_to_next_all_rows
    hSmallPositive row hRow hLocal
  have hPreviousEq : copyNumber + 1 - 1 = copyNumber := by omega
  rw [hPreviousEq] at hBoundary
  rw [hBoundary]
  exact hSmallAncestor

/-- 较早副本中的低行 ancestor 可先截断到该副本的下一条边界。 -/
theorem original_last_ancestor_of_copy_ancestor_later_first
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row copyNumber localColumn : Nat}
    (hCopy : copyNumber < expansionIndex)
    (hRow : row < context.maximalRow)
    (hLocal : localColumn < context.blockLength)
    (hAncestor : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition copyNumber localColumn)
      (context.copyPosition expansionIndex 0) = true) :
    isAncestor array.raw row (context.parentColumn + localColumn)
      context.lastIndex = true := by
  have hNextLe : copyNumber + 1 ≤ expansionIndex := by omega
  have hNextToLast :
      context.copyPosition (copyNumber + 1) 0 =
          context.copyPosition expansionIndex 0 ∨
        isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition (copyNumber + 1) 0)
          (context.copyPosition expansionIndex 0) = true := by
    by_cases hNextEq : copyNumber + 1 = expansionIndex
    · exact Or.inl (by rw [hNextEq])
    · exact Or.inr (context.first_copy_ancestor_of_lt
        (expansionIndex := expansionIndex) (earlierCopy := copyNumber + 1)
        (laterCopy := expansionIndex) (Nat.le_refl expansionIndex)
        (by omega) hRow)
  have hCandidateNext : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition copyNumber localColumn)
      (context.copyPosition (copyNumber + 1) 0) = true := by
    rcases hNextToLast with hEqual | hNextAncestor
    · rwa [hEqual]
    · rcases ancestor_of_common_target_of_le hAncestor hNextAncestor
          (by
            have hCandidateInCopy := context.copyPosition_in_block
              (copyNumber := copyNumber) hLocal
            exact Nat.le_of_lt hCandidateInCopy.2) with
        hEqual | hCandidateAncestor
      · have hCandidateInCopy := context.copyPosition_in_block
            (copyNumber := copyNumber) hLocal
        rw [hEqual] at hCandidateInCopy
        simp only [copyPosition] at hCandidateInCopy
        omega
      · exact hCandidateAncestor
  exact context.original_last_ancestor_of_copy_to_next_first
    hCopy hRow hLocal hCandidateNext

/-- 最后副本首列的 `m₀`-parent 若存在，必定位于 `G`。 -/
theorem parent_first_last_at_maximalRow_in_good
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex found : Nat}
    (hParent : parent context.maximalRow (array.expand expansionIndex).raw
      (context.copyPosition expansionIndex 0) = some found) :
    found < context.parentColumn := by
  rcases context.parent_in_good_or_not_later_copy
      (Nat.le_refl expansionIndex) context.blockLength_pos hParent with
    hGood | ⟨foundCopy, foundLocal, hFoundCopyLe, hFoundLocal, hFoundPosition⟩
  · exact hGood
  · have hFoundLt := parent_some_lt hParent
    have hFoundCopyLt : foundCopy < expansionIndex := by
      apply Nat.lt_of_le_of_ne hFoundCopyLe
      intro hEqual
      have hFoundInCopy := context.copyPosition_in_block
        (copyNumber := foundCopy) hFoundLocal
      rw [hFoundPosition, hEqual] at hFoundLt
      simp only [copyPosition, copyStart] at hFoundLt
      omega
    have hOriginalBelow : AncestorBelow array.raw context.maximalRow
        (context.parentColumn + foundLocal) context.lastIndex := by
      intro lowerRow hLower
      have hExpandedAncestor :=
        (ancestorBelow_of_parentEligible (parent_some_eligible hParent))
          lowerRow hLower
      rw [hFoundPosition] at hExpandedAncestor
      exact context.original_last_ancestor_of_copy_ancestor_later_first
        hFoundCopyLt hLower hFoundLocal hExpandedAncestor
    have hTrimmedRow : context.maximalRow <
        trimHeight (expandRaw array.raw expansionIndex) := by
      by_cases hRow : context.maximalRow <
          trimHeight (expandRaw array.raw expansionIndex)
      · exact hRow
      · have hNone : parent context.maximalRow
            (array.expand expansionIndex).raw
            (context.copyPosition expansionIndex 0) = none :=
          parent_expand_eq_none_of_le (array := array) expansionIndex
            (context.copyPosition expansionIndex 0) (by omega)
        rw [hParent] at hNone
        simp at hNone
    rcases rectangular_iff_exists_uniformHeight.mp array.rectangular_eq with
      ⟨height, hUniform⟩
    have hNotAscending : ascending array.raw context.maximalRow
        context.parentColumn 0 context.maximalRow = false := by
      simp [ascending]
    rcases parent_some_entry_lt hParent with
      ⟨foundValue, targetValue, hFoundEntry, hTargetEntry, hValueLt⟩
    have hCrossEntryLess : entryLess (array.expand expansionIndex).raw
        context.maximalRow (context.copyPosition foundCopy foundLocal)
        (context.copyPosition expansionIndex 0) = true := by
      rw [hFoundPosition] at hFoundEntry
      unfold entryLess
      rw [hFoundEntry, hTargetEntry]
      simp [hValueLt]
    have hSameEntryLess : entryLess (array.expand expansionIndex).raw
        context.maximalRow (context.copyPosition foundCopy foundLocal)
        (context.copyPosition foundCopy 0) = true := by
      have hEntryEq :=
        context.entryLess_expand_copy_to_copy_eq_same_of_not_ascending
          (leftCopy := foundCopy) (rightCopy := expansionIndex)
          (leftLocal := foundLocal) (rightLocal := 0)
          hUniform hTrimmedRow hFoundCopyLe (Nat.le_refl expansionIndex)
          context.blockLength_pos hNotAscending
      rwa [hEntryEq] at hCrossEntryLess
    have hZeroEntryLess : entryLess (array.expand expansionIndex).raw
        context.maximalRow (context.copyPosition 0 foundLocal)
        (context.copyPosition 0 0) = true :=
      context.entryLess_expand_copy_zero_of_not_ascending hUniform
        hTrimmedRow hFoundCopyLe hFoundLocal context.blockLength_pos
        hNotAscending hSameEntryLess
    have hOriginalFirstEntryLess : entryLess array.raw context.maximalRow
        (context.parentColumn + foundLocal) context.parentColumn = true := by
      rw [entryLess_expand_of_lt expansionIndex _ _ context.maximalRow
        hTrimmedRow] at hZeroEntryLess
      rw [context.entryLess_expandRaw_copy_zero_eq_original expansionIndex
        context.maximalRow hFoundLocal context.blockLength_pos] at hZeroEntryLess
      simpa using hZeroEntryLess
    have hParentEntryLess : entryLess array.raw context.maximalRow
        context.parentColumn context.lastIndex = true := by
      rcases parent_some_entry_lt context.parent_eq with
        ⟨parentValue, lastValue, hParentEntry, hLastEntry, hParentValueLt⟩
      unfold entryLess
      rw [hParentEntry, hLastEntry]
      simp [hParentValueLt]
    have hCandidateEntryLess : entryLess array.raw context.maximalRow
        (context.parentColumn + foundLocal) context.lastIndex = true :=
      entryLess_trans hOriginalFirstEntryLess hParentEntryLess
    have hCandidateEligible := parentEligible_of_ancestorBelow_of_entryLess
      hOriginalBelow hCandidateEntryLess
    have hCandidateLt : context.parentColumn + foundLocal < context.lastIndex := by
      simp only [blockLength] at hFoundLocal
      omega
    have hCandidateLeParent := parent_some_isGreatest context.parent_eq
      (context.parentColumn + foundLocal) hCandidateLt hCandidateEligible
    have hFoundLocalZero : foundLocal = 0 := by omega
    subst foundLocal
    cases hEntry : entry? array.raw context.parentColumn context.maximalRow <;>
      simp [entryLess, hEntry] at hOriginalFirstEntryLess

/-- 最后副本首列的全部 `m₀`-ancestors 都位于 `G`。 -/
theorem ancestor_first_last_at_maximalRow_in_good
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex ancestor : Nat}
    (hAncestor : isAncestor (array.expand expansionIndex).raw
      context.maximalRow ancestor
      (context.copyPosition expansionIndex 0) = true) :
    ancestor < context.parentColumn := by
  have hTargetValid := context.copyPosition_lt_length
    (index := expansionIndex) (copyNumber := expansionIndex)
    (Nat.le_refl expansionIndex) context.blockLength_pos
  have hAncestorOrder := isAncestor_lt hAncestor
  rcases ancestor_entries_lt hAncestor with
    ⟨ancestorValue, targetValue, hAncestorEntry, hTargetEntry, hValueLt⟩
  have hEntryLess : entryLess (array.expand expansionIndex).raw
      context.maximalRow ancestor
      (context.copyPosition expansionIndex 0) = true := by
    unfold entryLess
    rw [hAncestorEntry, hTargetEntry]
    simp [hValueLt]
  have hEligible := parentEligible_of_ancestorBelow_of_entryLess
    (ancestorBelow_of_isAncestor hAncestor) hEntryLess
  rcases exists_parent_of_eligible hTargetValid hAncestorOrder hEligible with
    ⟨found, hParent, hAncestorLe⟩
  have hFoundGood := context.parent_first_last_at_maximalRow_in_good hParent
  omega

/-- 第零副本首列的任意 parent 都位于 `G`。 -/
theorem parent_first_zero_in_good
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row found : Nat}
    (hParent : parent row (array.expand expansionIndex).raw
      (context.copyPosition 0 0) = some found) :
    found < context.parentColumn := by
  have hFoundLt := parent_some_lt hParent
  simpa [copyPosition, copyStart] using hFoundLt

/-- `row ≥ m₀` 时，最后副本首列的任意 parent 都位于 `G`。 -/
theorem parent_first_last_of_maximalRow_le_in_good
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row found : Nat}
    (hMaximalRow : context.maximalRow ≤ row)
    (hParent : parent row (array.expand expansionIndex).raw
      (context.copyPosition expansionIndex 0) = some found) :
    found < context.parentColumn := by
  have hCurrentAncestor := direct_parent_isAncestor hParent
  have hAtMaximalRow : isAncestor (array.expand expansionIndex).raw
      context.maximalRow found (context.copyPosition expansionIndex 0) = true := by
    rcases Nat.eq_or_lt_of_le hMaximalRow with hEqual | hStrict
    · rwa [hEqual]
    · exact isAncestor_of_lt_row hStrict hCurrentAncestor
  exact context.ancestor_first_last_at_maximalRow_in_good hAtMaximalRow

/-- `row ≥ m₀` 时，第零与最后副本首列具有相同 parent。 -/
theorem parent_first_copies_eq_of_maximalRow_le
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row : Nat}
    (hMaximalRow : context.maximalRow ≤ row)
    (hBelow : ∀ lowerRow, lowerRow < row → ∀ {goodColumn},
      goodColumn < context.parentColumn →
      isAncestor (array.expand expansionIndex).raw lowerRow goodColumn
          (context.copyPosition 0 0) =
        isAncestor (array.expand expansionIndex).raw lowerRow goodColumn
          (context.copyPosition expansionIndex 0)) :
    parent row (array.expand expansionIndex).raw
        (context.copyPosition 0 0) =
      parent row (array.expand expansionIndex).raw
        (context.copyPosition expansionIndex 0) := by
  by_cases hTrimmedRow : row < trimHeight (expandRaw array.raw expansionIndex)
  · rcases rectangular_iff_exists_uniformHeight.mp array.rectangular_eq with
      ⟨height, hUniform⟩
    have hNotAscending : ascending array.raw context.maximalRow
        context.parentColumn 0 row = false := by
      simp [ascending]
      omega
    have hTargetEntry := context.entry?_expand_copy_eq_zero_of_not_ascending
      hUniform hTrimmedRow (Nat.le_refl expansionIndex)
      context.blockLength_pos hNotAscending
    have hEntryLess : ∀ candidate,
        entryLess (array.expand expansionIndex).raw row candidate
            (context.copyPosition 0 0) =
          entryLess (array.expand expansionIndex).raw row candidate
            (context.copyPosition expansionIndex 0) := by
      intro candidate
      unfold entryLess
      rw [hTargetEntry]
    apply parent_eq_of_bounded_results
      (context.copyPosition_lt_length (Nat.zero_le expansionIndex)
        context.blockLength_pos)
      (context.copyPosition_lt_length (Nat.le_refl expansionIndex)
        context.blockLength_pos)
      (by simp [copyPosition, copyStart])
      (by simp [copyPosition, copyStart])
      context.parent_first_zero_in_good
      (context.parent_first_last_of_maximalRow_le_in_good hMaximalRow)
    intro candidate hCandidate
    cases row with
    | zero =>
        exact parentEligible_zero_congr_entryLess (hEntryLess candidate)
    | succ lowerRow =>
        exact parentEligible_succ_congr_entryLess
          (hBelow lowerRow (by omega) hCandidate) (hEntryLess candidate)
  · have hRowLe : trimHeight (expandRaw array.raw expansionIndex) ≤ row := by
      omega
    rw [parent_expand_eq_none_of_le (array := array) expansionIndex
      (context.copyPosition 0 0) hRowLe]
    rw [parent_expand_eq_none_of_le (array := array) expansionIndex
      (context.copyPosition expansionIndex 0) hRowLe]

/-- `row ≥ m₀` 时，第零与最后副本首列从 `G` 看有相同 ancestry。 -/
theorem good_to_first_copies_of_maximalRow_le
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row goodColumn : Nat}
    (hMaximalRow : context.maximalRow ≤ row)
    (hBelow : ∀ lowerRow, lowerRow < row → ∀ {candidate},
      candidate < context.parentColumn →
      isAncestor (array.expand expansionIndex).raw lowerRow candidate
          (context.copyPosition 0 0) =
        isAncestor (array.expand expansionIndex).raw lowerRow candidate
          (context.copyPosition expansionIndex 0)) :
    isAncestor (array.expand expansionIndex).raw row goodColumn
        (context.copyPosition 0 0) =
      isAncestor (array.expand expansionIndex).raw row goodColumn
        (context.copyPosition expansionIndex 0) := by
  apply isAncestor_congr_of_parent_eq
  exact context.parent_first_copies_eq_of_maximalRow_le hMaximalRow hBelow

/-- 第零与最后副本的首列从 `G` 看在所有行上具有相同 ancestry。 -/
theorem good_to_first_copies_all_rows
    {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex : Nat) : ∀ row {goodColumn},
      goodColumn < context.parentColumn →
      isAncestor (array.expand expansionIndex).raw row goodColumn
          (context.copyPosition 0 0) =
        isAncestor (array.expand expansionIndex).raw row goodColumn
          (context.copyPosition expansionIndex 0) := by
  intro row
  induction row using Nat.strongRecOn with
  | ind row ih =>
      intro goodColumn hGood
      by_cases hExpansionIndex : 0 < expansionIndex
      · by_cases hRow : row < context.maximalRow
        · have hFirstAncestor := context.first_copy_ancestor_of_lt
            (expansionIndex := expansionIndex) (earlierCopy := 0)
            (laterCopy := expansionIndex) (Nat.le_refl expansionIndex)
            hExpansionIndex hRow
          apply Bool.eq_iff_iff.mpr
          constructor
          · intro hAncestor
            exact isAncestor_trans hAncestor hFirstAncestor
          · intro hAncestor
            rcases ancestor_of_common_target_of_le hAncestor hFirstAncestor
                (by
                  simp only [copyPosition, copyStart]
                  omega) with hEqual | hGoodAncestor
            · simp only [copyPosition, copyStart] at hEqual
              omega
            · exact hGoodAncestor
        · exact context.good_to_first_copies_of_maximalRow_le
            (Nat.le_of_not_gt hRow)
            (fun lowerRow hLower candidate hCandidate =>
              ih lowerRow hLower hCandidate)
      · have hIndexZero : expansionIndex = 0 := by omega
        subst expansionIndex
        rfl

/-- 非 ascending 目标的两个副本 parent：或同在 `G` 且相同，或为同一局部列。 -/
theorem parent_copies_eq_or_internal_of_not_ascending
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row targetLocal : Nat}
    (hRow : row < trimHeight (expandRaw array.raw expansionIndex))
    (hTargetLocal : 0 < targetLocal)
    (hTargetBound : targetLocal < context.blockLength)
    (hNotAscending : ascending array.raw context.maximalRow
      context.parentColumn targetLocal row = false)
    (hParentLocality : ∀ {found},
      parent row (array.expand expansionIndex).raw
          (context.copyPosition expansionIndex targetLocal) = some found →
      found < context.parentColumn ∨ context.InCopy expansionIndex found)
    (hBelow : ∀ lowerRow, lowerRow < row → ∀ {goodColumn},
      goodColumn < context.parentColumn →
      isAncestor (array.expand expansionIndex).raw lowerRow goodColumn
          (context.copyPosition 0 targetLocal) =
        isAncestor (array.expand expansionIndex).raw lowerRow goodColumn
          (context.copyPosition expansionIndex targetLocal)) :
    parent row (array.expand expansionIndex).raw
          (context.copyPosition 0 targetLocal) =
        parent row (array.expand expansionIndex).raw
          (context.copyPosition expansionIndex targetLocal) ∨
      ∃ parentLocal, parentLocal < targetLocal ∧
        parent row (array.expand expansionIndex).raw
            (context.copyPosition 0 targetLocal) =
          some (context.copyPosition 0 parentLocal) ∧
        parent row (array.expand expansionIndex).raw
            (context.copyPosition expansionIndex targetLocal) =
          some (context.copyPosition expansionIndex parentLocal) := by
  rcases rectangular_iff_exists_uniformHeight.mp array.rectangular_eq with
    ⟨height, hUniform⟩
  have hTargetEntry := context.entry?_expand_copy_eq_zero_of_not_ascending
    hUniform hRow (Nat.le_refl expansionIndex) hTargetBound hNotAscending
  have hEntryLess : ∀ candidate,
      entryLess (array.expand expansionIndex).raw row candidate
          (context.copyPosition 0 targetLocal) =
        entryLess (array.expand expansionIndex).raw row candidate
          (context.copyPosition expansionIndex targetLocal) := by
    intro candidate
    unfold entryLess
    rw [hTargetEntry]
  have hEligible : ∀ candidate, candidate < context.parentColumn →
      parentEligible row (array.expand expansionIndex).raw
          (context.copyPosition 0 targetLocal) candidate =
        parentEligible row (array.expand expansionIndex).raw
          (context.copyPosition expansionIndex targetLocal) candidate := by
    intro candidate hCandidate
    cases row with
    | zero => exact parentEligible_zero_congr_entryLess (hEntryLess candidate)
    | succ lowerRow =>
        exact parentEligible_succ_congr_entryLess
          (hBelow lowerRow (by omega) hCandidate) (hEntryLess candidate)
  have hInside : ∀ {leftLocal rightLocal},
      leftLocal < context.blockLength →
      rightLocal < context.blockLength →
      isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition 0 leftLocal)
          (context.copyPosition 0 rightLocal) =
        isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition expansionIndex leftLocal)
          (context.copyPosition expansionIndex rightLocal) := by
    intro leftLocal rightLocal hLeft hRight
    exact context.inside_copy_all_rows expansionIndex row hLeft hRight
  cases hZeroParent : parent row (array.expand expansionIndex).raw
      (context.copyPosition 0 targetLocal) with
  | none =>
      cases hLastParent : parent row (array.expand expansionIndex).raw
          (context.copyPosition expansionIndex targetLocal) with
      | none => exact Or.inl rfl
      | some lastFound =>
          rcases hParentLocality hLastParent with hLastGood | hLastCopy
          · have hParentsEqual := parent_eq_of_bounded_results
                (context.copyPosition_lt_length (Nat.zero_le expansionIndex)
                  hTargetBound)
                (context.copyPosition_lt_length (Nat.le_refl expansionIndex)
                  hTargetBound)
                (by simp only [copyPosition, copyStart]; omega)
                (by simp only [copyPosition, copyStart]; omega)
                (fun {found} hFound => by rw [hZeroParent] at hFound; simp at hFound)
                (fun {found} hFound => by
                  rw [hLastParent] at hFound
                  exact Option.some.inj hFound ▸ hLastGood)
                hEligible
            rw [hZeroParent, hLastParent] at hParentsEqual
            simp at hParentsEqual
          · rcases context.inCopy_iff_exists_copyPosition.mp hLastCopy with
              ⟨lastLocal, hLastLocal, hLastPosition⟩
            have hLastAncestor := direct_parent_isAncestor hLastParent
            rw [hLastPosition] at hLastAncestor
            have hZeroAncestor : isAncestor (array.expand expansionIndex).raw row
                (context.copyPosition 0 lastLocal)
                (context.copyPosition 0 targetLocal) = true := by
              rw [hInside hLastLocal hTargetBound]
              exact hLastAncestor
            have hImpossible := isAncestor_eq_false_of_parent_none
              (ancestor := context.copyPosition 0 lastLocal) hZeroParent
            rw [hImpossible] at hZeroAncestor
            simp at hZeroAncestor
  | some zeroFound =>
      rcases context.parent_in_good_or_not_later_copy
          (index := expansionIndex) (targetCopy := 0)
          (Nat.zero_le expansionIndex) hTargetBound hZeroParent with
        hZeroGood | ⟨zeroCopy, zeroLocal, hZeroCopy, hZeroLocal,
          hZeroPosition⟩
      · cases hLastParent : parent row (array.expand expansionIndex).raw
            (context.copyPosition expansionIndex targetLocal) with
        | none =>
            have hParentsEqual := parent_eq_of_bounded_results
              (context.copyPosition_lt_length (Nat.zero_le expansionIndex)
                hTargetBound)
              (context.copyPosition_lt_length (Nat.le_refl expansionIndex)
                hTargetBound)
              (by simp only [copyPosition, copyStart]; omega)
              (by simp only [copyPosition, copyStart]; omega)
              (fun {found} hFound => by
                rw [hZeroParent] at hFound
                exact Option.some.inj hFound ▸ hZeroGood)
              (fun {found} hFound => by rw [hLastParent] at hFound; simp at hFound)
              hEligible
            rw [hZeroParent, hLastParent] at hParentsEqual
            simp at hParentsEqual
        | some lastFound =>
            rcases hParentLocality hLastParent with hLastGood | hLastCopy
            · left
              have hParentsEqual := parent_eq_of_bounded_results
                (context.copyPosition_lt_length (Nat.zero_le expansionIndex)
                  hTargetBound)
                (context.copyPosition_lt_length (Nat.le_refl expansionIndex)
                  hTargetBound)
                (by simp only [copyPosition, copyStart]; omega)
                (by simp only [copyPosition, copyStart]; omega)
                (fun {found} hFound => by
                  rw [hZeroParent] at hFound
                  exact Option.some.inj hFound ▸ hZeroGood)
                (fun {found} hFound => by
                  rw [hLastParent] at hFound
                  exact Option.some.inj hFound ▸ hLastGood)
                hEligible
              rw [hZeroParent, hLastParent] at hParentsEqual
              exact hParentsEqual
            · rcases context.inCopy_iff_exists_copyPosition.mp hLastCopy with
                ⟨lastLocal, hLastLocal, hLastPosition⟩
              have hLastAncestor := direct_parent_isAncestor hLastParent
              rw [hLastPosition] at hLastAncestor
              have hZeroAncestor : isAncestor (array.expand expansionIndex).raw row
                  (context.copyPosition 0 lastLocal)
                  (context.copyPosition 0 targetLocal) = true := by
                rw [hInside hLastLocal hTargetBound]
                exact hLastAncestor
              have hLastLeZero := ancestor_le_parent hZeroParent hZeroAncestor
              have hLastInZero := context.copyPosition_in_block
                (copyNumber := 0) hLastLocal
              simp only [copyStart] at hLastInZero
              omega
      · have hZeroCopyEq : zeroCopy = 0 := by omega
        subst zeroCopy
        rw [hZeroPosition] at hZeroParent
        have hZeroLocalTarget : zeroLocal < targetLocal := by
          have := parent_some_lt hZeroParent
          simp only [copyPosition, copyStart] at this
          omega
        cases hLastParent : parent row (array.expand expansionIndex).raw
            (context.copyPosition expansionIndex targetLocal) with
        | none =>
            have hZeroAncestor := direct_parent_isAncestor hZeroParent
            have hLastAncestor : isAncestor (array.expand expansionIndex).raw row
                (context.copyPosition expansionIndex zeroLocal)
                (context.copyPosition expansionIndex targetLocal) = true := by
              rw [← hInside hZeroLocal hTargetBound]
              exact hZeroAncestor
            have hImpossible := isAncestor_eq_false_of_parent_none
              (ancestor := context.copyPosition expansionIndex zeroLocal) hLastParent
            rw [hImpossible] at hLastAncestor
            simp at hLastAncestor
        | some lastFound =>
            rcases hParentLocality hLastParent with hLastGood | hLastCopy
            · have hZeroAncestor := direct_parent_isAncestor hZeroParent
              have hLastAncestor : isAncestor (array.expand expansionIndex).raw row
                  (context.copyPosition expansionIndex zeroLocal)
                  (context.copyPosition expansionIndex targetLocal) = true := by
                rw [← hInside hZeroLocal hTargetBound]
                exact hZeroAncestor
              have hZeroLeLast := ancestor_le_parent hLastParent hLastAncestor
              have hZeroInLast := context.copyPosition_in_block
                (copyNumber := expansionIndex) hZeroLocal
              simp only [copyStart] at hZeroInLast
              omega
            · rcases context.inCopy_iff_exists_copyPosition.mp hLastCopy with
                ⟨lastLocal, hLastLocal, hLastPosition⟩
              rw [hLastPosition] at hLastParent
              have hLastLocalTarget : lastLocal < targetLocal := by
                have := parent_some_lt hLastParent
                simp only [copyPosition, copyStart] at this
                omega
              have hZeroAncestor := direct_parent_isAncestor hZeroParent
              have hZeroInLast : isAncestor (array.expand expansionIndex).raw row
                  (context.copyPosition expansionIndex zeroLocal)
                  (context.copyPosition expansionIndex targetLocal) = true := by
                rw [← hInside hZeroLocal hTargetBound]
                exact hZeroAncestor
              have hZeroLeLast := ancestor_le_parent hLastParent hZeroInLast
              have hLastAncestor := direct_parent_isAncestor hLastParent
              have hLastInZero : isAncestor (array.expand expansionIndex).raw row
                  (context.copyPosition 0 lastLocal)
                  (context.copyPosition 0 targetLocal) = true := by
                rw [hInside hLastLocal hTargetBound]
                exact hLastAncestor
              have hLastLeZero := ancestor_le_parent hZeroParent hLastInZero
              have hLocalEq : zeroLocal = lastLocal := by
                simp only [copyPosition, copyStart] at hZeroLeLast hLastLeZero
                omega
              subst lastLocal
              exact Or.inr ⟨zeroLocal, hZeroLocalTarget,
                congrArg some hZeroPosition, congrArg some hLastPosition⟩

/-- 若目标及其 parent 都在副本首列两侧，集合 `I` 的首列位于该 parent 之后。 -/
theorem parent_ancestor_first_of_first_below
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row targetLocal found : Nat}
    (hRow : row < trimHeight (expandRaw array.raw expansionIndex))
    (hFoundFirst : found < context.copyPosition expansionIndex 0)
    (hTargetLocal : 0 < targetLocal)
    (hFirstBelow : AncestorBelow (array.expand expansionIndex).raw row
      (context.copyPosition expansionIndex 0)
      (context.copyPosition expansionIndex targetLocal))
    (hParent : parent row (array.expand expansionIndex).raw
      (context.copyPosition expansionIndex targetLocal) = some found) :
    isAncestor (array.expand expansionIndex).raw row found
      (context.copyPosition expansionIndex 0) = true := by
  rcases rectangular_iff_exists_uniformHeight.mp array.rectangular_eq with
    ⟨height, hUniform⟩
  have hExpandedUniform := ValidArray.uniformHeight_expand
    (index := expansionIndex) hUniform
  have hFirstEntry := exists_entry_of_uniformHeight hExpandedUniform
    (context.copyPosition_lt_length (Nat.le_refl expansionIndex)
      context.blockLength_pos) hRow
  exact isAncestor_of_ancestorBelow_between (direct_parent_isAncestor hParent)
    hFirstBelow hFoundFirst
    (by
      simp only [copyPosition, copyStart]
      omega)
    hFirstEntry

/-- 若 ancestry 链未经过副本首列，则 parent-locality 使该链封闭于 `G ∪ Bₙ`。 -/
theorem ancestor_in_good_or_same_copy_of_first_not_ancestor {array : ValidArray}
    (context : ExpansionContext array) {expansionIndex row localColumn found : Nat}
    (hLocal : 0 < localColumn)
    (hLocalBound : localColumn < context.blockLength)
    (hParentLocality : ∀ {middleLocal parentColumn},
      0 < middleLocal → middleLocal < context.blockLength →
      parent row (array.expand expansionIndex).raw
        (context.copyPosition expansionIndex middleLocal) = some parentColumn →
      parentColumn < context.parentColumn ∨ context.InCopy expansionIndex parentColumn)
    (hFirstNotAncestor : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition expansionIndex 0)
      (context.copyPosition expansionIndex localColumn) = false)
    (hAncestor : isAncestor (array.expand expansionIndex).raw row found
      (context.copyPosition expansionIndex localColumn) = true) :
    found < context.parentColumn ∨ context.InCopy expansionIndex found := by
  have hStrict := isAncestor_iff_strictAncestor.mp hAncestor
  unfold StrictAncestor ParentEdge at hStrict
  induction hStrict with
  | single hParent =>
      exact hParentLocality hLocal hLocalBound hParent
  | tail path hParent ih =>
      have hPathAncestor : isAncestor (array.expand expansionIndex).raw row _
          (context.copyPosition expansionIndex localColumn) = true :=
        isAncestor_iff_strictAncestor.mpr path
      rcases ih hPathAncestor with hMiddleGood | hMiddleCopy
      · exact Or.inl (Nat.lt_trans (parent_some_lt hParent) hMiddleGood)
      · rcases context.inCopy_iff_exists_copyPosition.mp hMiddleCopy with
          ⟨middleLocal, hMiddleLocal, hMiddlePosition⟩
        by_cases hMiddleZero : middleLocal = 0
        · subst middleLocal
          have hFirstTrue : isAncestor (array.expand expansionIndex).raw row
              (context.copyPosition expansionIndex 0)
              (context.copyPosition expansionIndex localColumn) = true := by
            rw [← hMiddlePosition]
            exact hPathAncestor
          rw [hFirstNotAncestor] at hFirstTrue
          simp at hFirstTrue
        · apply hParentLocality (Nat.zero_lt_of_ne_zero hMiddleZero)
            hMiddleLocal
          rwa [← hMiddlePosition]

/-- 当前 parent 在某个低行看不到副本首列时，低行 locality 已足以推出当前 locality。 -/
theorem parent_in_good_or_same_copy_of_lower_first_not_ancestor
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row lowerRow localColumn found : Nat}
    (hLower : lowerRow < row)
    (hLocal : 0 < localColumn)
    (hLocalBound : localColumn < context.blockLength)
    (hLowerParentLocality : ∀ {middleLocal parentColumn},
      0 < middleLocal → middleLocal < context.blockLength →
      parent lowerRow (array.expand expansionIndex).raw
        (context.copyPosition expansionIndex middleLocal) = some parentColumn →
      parentColumn < context.parentColumn ∨ context.InCopy expansionIndex parentColumn)
    (hFirstNotAncestor : isAncestor (array.expand expansionIndex).raw lowerRow
      (context.copyPosition expansionIndex 0)
      (context.copyPosition expansionIndex localColumn) = false)
    (hParent : parent row (array.expand expansionIndex).raw
      (context.copyPosition expansionIndex localColumn) = some found) :
    found < context.parentColumn ∨ context.InCopy expansionIndex found := by
  have hCurrentAncestor := direct_parent_isAncestor hParent
  have hLowerAncestor := isAncestor_of_lt_row hLower hCurrentAncestor
  exact context.ancestor_in_good_or_same_copy_of_first_not_ancestor
    hLocal hLocalBound hLowerParentLocality hFirstNotAncestor hLowerAncestor

/-- parent 落在严格较早副本时，目标在自身副本内不可能还有当前行 ancestor。 -/
theorem no_same_copy_ancestor_of_parent_in_earlier_copy
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row targetLocal foundCopy foundLocal : Nat}
    (hFoundCopy : foundCopy < expansionIndex)
    (hFoundLocal : foundLocal < context.blockLength)
    (hParent : parent row (array.expand expansionIndex).raw
      (context.copyPosition expansionIndex targetLocal) =
        some (context.copyPosition foundCopy foundLocal)) :
    ∀ {candidateLocal}, candidateLocal < context.blockLength →
      isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition expansionIndex candidateLocal)
        (context.copyPosition expansionIndex targetLocal) = false := by
  intro candidateLocal hCandidateLocal
  cases hCandidateAncestor : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition expansionIndex candidateLocal)
      (context.copyPosition expansionIndex targetLocal) with
  | false => rfl
  | true =>
      rcases ancestor_entries_lt hCandidateAncestor with
        ⟨candidateValue, targetValue, hCandidateEntry, hTargetEntry, hValueLt⟩
      have hCandidateBelow := ancestorBelow_of_isAncestor hCandidateAncestor
      have hEntryLess : entryLess (array.expand expansionIndex).raw row
          (context.copyPosition expansionIndex candidateLocal)
          (context.copyPosition expansionIndex targetLocal) = true := by
        unfold entryLess
        rw [hCandidateEntry, hTargetEntry]
        simp [hValueLt]
      have hEligible := parentEligible_of_ancestorBelow_of_entryLess
        hCandidateBelow hEntryLess
      have hCandidateLt := isAncestor_lt hCandidateAncestor
      have hCandidateLeFound := parent_some_isGreatest hParent
        (context.copyPosition expansionIndex candidateLocal) hCandidateLt hEligible
      have hFoundInCopy := context.copyPosition_in_block
        (copyNumber := foundCopy) hFoundLocal
      have hCandidateInCopy := context.copyPosition_in_block
        (copyNumber := expansionIndex) hCandidateLocal
      have hFoundLtCandidate := context.column_lt_of_inCopy_of_lt_copy
        hFoundCopy hFoundInCopy hCandidateInCopy
      omega

/-- 在 `row < m₀` 时，目标的 parent 不可能落在严格较早的复制块。 -/
theorem no_parent_in_earlier_copy_of_lt_maximalRow
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row targetLocal foundCopy foundLocal : Nat}
    (hExpansionIndex : 0 < expansionIndex)
    (hRow : row < context.maximalRow)
    (hTargetLocal : 0 < targetLocal)
    (hTargetBound : targetLocal < context.blockLength)
    (hFoundCopy : foundCopy < expansionIndex)
    (hFoundLocal : foundLocal < context.blockLength)
    (hFirstBelow : AncestorBelow (array.expand expansionIndex).raw row
      (context.copyPosition expansionIndex 0)
      (context.copyPosition expansionIndex targetLocal))
    (hParent : parent row (array.expand expansionIndex).raw
      (context.copyPosition expansionIndex targetLocal) =
        some (context.copyPosition foundCopy foundLocal)) : False := by
  rcases rectangular_iff_exists_uniformHeight.mp array.rectangular_eq with
    ⟨height, hUniform⟩
  have hExpandedUniform := ValidArray.uniformHeight_expand
    (index := expansionIndex) hUniform
  have hTrimmedRow : row < trimHeight (expandRaw array.raw expansionIndex) :=
    Nat.lt_of_lt_of_le hRow
      (context.maximalRow_le_trimHeight_expandRaw hExpansionIndex)
  have hNoLastAncestor : ∀ {candidateLocal},
      candidateLocal < context.blockLength →
      isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition expansionIndex candidateLocal)
        (context.copyPosition expansionIndex targetLocal) = false :=
    context.no_same_copy_ancestor_of_parent_in_earlier_copy
      hFoundCopy hFoundLocal hParent
  have hInsideCopies := context.inside_copy_all_rows expansionIndex row
    context.blockLength_pos hTargetBound
  have hNoZeroFirst : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition 0 0)
      (context.copyPosition 0 targetLocal) = false := by
    rw [hInsideCopies]
    exact hNoLastAncestor context.blockLength_pos
  have hTargetNotAscending : ascending array.raw context.maximalRow
      context.parentColumn targetLocal row = false := by
    cases hAscending : ascending array.raw context.maximalRow
        context.parentColumn targetLocal row with
    | false => rfl
    | true =>
        rcases (context.ascending_iff_first_nonstrict_ancestor_expand
          expansionIndex hTargetBound hRow hTrimmedRow).mp hAscending with
          hTargetZero | hFirstAncestor
        · omega
        · rw [hNoZeroFirst] at hFirstAncestor
          simp at hFirstAncestor
  have hZeroBelow : AncestorBelow (array.expand expansionIndex).raw row
      (context.copyPosition 0 0)
      (context.copyPosition 0 targetLocal) := by
    intro lowerRow hLower
    have hLowerInside := context.inside_copy_all_rows expansionIndex lowerRow
      context.blockLength_pos hTargetBound
    rw [hLowerInside]
    exact hFirstBelow lowerRow hLower
  have hZeroEntryLess : entryLess (array.expand expansionIndex).raw row
      (context.copyPosition 0 0)
      (context.copyPosition 0 targetLocal) = false := by
    cases hEntryLess : entryLess (array.expand expansionIndex).raw row
        (context.copyPosition 0 0)
        (context.copyPosition 0 targetLocal) with
    | false => rfl
    | true =>
        have hEligible := parentEligible_of_ancestorBelow_of_entryLess
          hZeroBelow hEntryLess
        have hZeroTargetValid := context.copyPosition_lt_length
          (index := expansionIndex) (copyNumber := 0) (Nat.zero_le _)
          hTargetBound
        have hZeroOrder : context.copyPosition 0 0 <
            context.copyPosition 0 targetLocal := by
          simp only [copyPosition, copyStart]
          omega
        rcases exists_parent_of_eligible hZeroTargetValid hZeroOrder hEligible with
          ⟨zeroFound, hZeroParent, hFirstLe⟩
        have hZeroFoundLt := parent_some_lt hZeroParent
        have hZeroFoundInCopy : context.InCopy 0 zeroFound := by
          constructor
          · simpa [copyStart, copyPosition] using hFirstLe
          · have hTargetInCopy := context.copyPosition_in_block
              (copyNumber := 0) hTargetBound
            omega
        rcases context.inCopy_iff_exists_copyPosition.mp hZeroFoundInCopy with
          ⟨zeroFoundLocal, hZeroFoundLocal, hZeroFoundPosition⟩
        have hZeroFoundAncestor := direct_parent_isAncestor hZeroParent
        have hForbidden := hNoLastAncestor hZeroFoundLocal
        have hCopiedAncestor : isAncestor (array.expand expansionIndex).raw row
            (context.copyPosition expansionIndex zeroFoundLocal)
            (context.copyPosition expansionIndex targetLocal) = true := by
          rw [← context.inside_copy_all_rows expansionIndex row
            hZeroFoundLocal hTargetBound]
          rwa [← hZeroFoundPosition]
        rw [hForbidden] at hCopiedAncestor
        simp at hCopiedAncestor
  have hFirstZeroToTarget : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition 0 0)
      (context.copyPosition expansionIndex targetLocal) = true := by
    have hFoundToFirstLast : isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition foundCopy foundLocal)
        (context.copyPosition expansionIndex 0) = true := by
      have hParentAncestor := direct_parent_isAncestor hParent
      have hFirstEntry := exists_entry_of_uniformHeight hExpandedUniform
        (context.copyPosition_lt_length (Nat.le_refl expansionIndex)
          context.blockLength_pos) hTrimmedRow
      exact isAncestor_of_ancestorBelow_between hParentAncestor hFirstBelow
        (by
          have hFoundInCopy := context.copyPosition_in_block
            (copyNumber := foundCopy) hFoundLocal
          have hFirstLastInCopy := context.copyPosition_in_block
            (copyNumber := expansionIndex) context.blockLength_pos
          exact context.column_lt_of_inCopy_of_lt_copy hFoundCopy
            hFoundInCopy hFirstLastInCopy)
        (by
          simp only [copyPosition, copyStart]
          omega)
        hFirstEntry
    have hFirstFoundToFirstLast := context.first_copy_ancestor_of_lt
      (expansionIndex := expansionIndex) (earlierCopy := foundCopy)
      (laterCopy := expansionIndex) (Nat.le_refl expansionIndex)
      hFoundCopy hRow
    have hFirstFoundToFound :
        context.copyPosition foundCopy 0 =
            context.copyPosition foundCopy foundLocal ∨
          isAncestor (array.expand expansionIndex).raw row
            (context.copyPosition foundCopy 0)
            (context.copyPosition foundCopy foundLocal) = true :=
      ancestor_of_common_target_of_le hFirstFoundToFirstLast
        hFoundToFirstLast
        (by
          simp only [copyPosition, copyStart]
          omega)
    have hFirstZeroToFirstFound :
        context.copyPosition 0 0 = context.copyPosition foundCopy 0 ∨
          isAncestor (array.expand expansionIndex).raw row
            (context.copyPosition 0 0)
            (context.copyPosition foundCopy 0) = true := by
      by_cases hFoundCopyZero : foundCopy = 0
      · left
        subst foundCopy
        rfl
      · right
        exact context.first_copy_ancestor_of_lt
          (expansionIndex := expansionIndex) (earlierCopy := 0)
          (laterCopy := foundCopy) (by omega)
          (Nat.zero_lt_of_ne_zero hFoundCopyZero) hRow
    have hFirstZeroToFound :
        context.copyPosition 0 0 = context.copyPosition foundCopy foundLocal ∨
          isAncestor (array.expand expansionIndex).raw row
            (context.copyPosition 0 0)
            (context.copyPosition foundCopy foundLocal) = true := by
      rcases hFirstZeroToFirstFound with hZeroEqual | hZeroAncestor
      · rcases hFirstFoundToFound with hFoundEqual | hFoundAncestor
        · exact Or.inl (hZeroEqual.trans hFoundEqual)
        · exact Or.inr (by rwa [hZeroEqual])
      · rcases hFirstFoundToFound with hFoundEqual | hFoundAncestor
        · exact Or.inr (by rwa [← hFoundEqual])
        · exact Or.inr (isAncestor_trans hZeroAncestor hFoundAncestor)
    rcases hFirstZeroToFound with hEqual | hAncestor
    · rw [hEqual]
      exact direct_parent_isAncestor hParent
    · exact isAncestor_trans hAncestor (direct_parent_isAncestor hParent)
  rcases ancestor_entries_lt hFirstZeroToTarget with
    ⟨firstValue, targetValue, hFirstEntry, hTargetEntry, hValueLt⟩
  have hCrossEntryLess : entryLess (array.expand expansionIndex).raw row
      (context.copyPosition 0 0)
      (context.copyPosition expansionIndex targetLocal) = true := by
    unfold entryLess
    rw [hFirstEntry, hTargetEntry]
    simp [hValueLt]
  have hCrossEq := context.entryLess_expand_zero_to_copy_eq_zero_of_not_ascending
    (leftLocal := 0) (rightLocal := targetLocal)
    hUniform hTrimmedRow (Nat.le_refl expansionIndex)
    hTargetBound hTargetNotAscending
  rw [hZeroEntryLess] at hCrossEq
  rw [hCrossEq] at hCrossEntryLess
  simp at hCrossEntryLess

/-- 在 `row < m₀` 且全部低行都经过副本首列时，Lemma 2.5(iv) 成立。 -/
theorem parent_locality_of_lt_maximalRow_of_first_below
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row localColumn found : Nat}
    (hExpansionIndex : 0 < expansionIndex)
    (hRow : row < context.maximalRow)
    (hLocal : 0 < localColumn)
    (hLocalBound : localColumn < context.blockLength)
    (hFirstBelow : AncestorBelow (array.expand expansionIndex).raw row
      (context.copyPosition expansionIndex 0)
      (context.copyPosition expansionIndex localColumn))
    (hParent : parent row (array.expand expansionIndex).raw
      (context.copyPosition expansionIndex localColumn) = some found) :
    found < context.parentColumn ∨ context.InCopy expansionIndex found := by
  rcases context.parent_in_good_or_not_later_copy
      (Nat.le_refl expansionIndex) hLocalBound hParent with
    hGood | ⟨foundCopy, foundLocal, hFoundCopyLe, hFoundLocal, hFoundPosition⟩
  · exact Or.inl hGood
  · by_cases hFoundCopyEq : foundCopy = expansionIndex
    · right
      rw [hFoundPosition, hFoundCopyEq]
      exact context.copyPosition_in_block hFoundLocal
    · have hFoundCopyLt : foundCopy < expansionIndex := by omega
      exfalso
      apply context.no_parent_in_earlier_copy_of_lt_maximalRow
        hExpansionIndex hRow hLocal hLocalBound hFoundCopyLt hFoundLocal
        hFirstBelow
      rwa [hFoundPosition] at hParent

/-- 在 `row ≥ m₀` 且集合 `I` 包含首列时，parent 不可能落在较早副本。 -/
theorem no_parent_in_earlier_copy_of_maximalRow_le
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row targetLocal foundCopy foundLocal : Nat}
    (hMaximalRow : context.maximalRow ≤ row)
    (hTargetLocal : 0 < targetLocal)
    (hFoundCopy : foundCopy < expansionIndex)
    (hFoundLocal : foundLocal < context.blockLength)
    (hFirstBelow : AncestorBelow (array.expand expansionIndex).raw row
      (context.copyPosition expansionIndex 0)
      (context.copyPosition expansionIndex targetLocal))
    (hParent : parent row (array.expand expansionIndex).raw
      (context.copyPosition expansionIndex targetLocal) =
        some (context.copyPosition foundCopy foundLocal)) : False := by
  have hTrimmedRow : row < trimHeight (expandRaw array.raw expansionIndex) := by
    by_cases hRow : row < trimHeight (expandRaw array.raw expansionIndex)
    · exact hRow
    · have hNone : parent row (array.expand expansionIndex).raw
          (context.copyPosition expansionIndex targetLocal) = none :=
        parent_expand_eq_none_of_le (array := array) expansionIndex
          (context.copyPosition expansionIndex targetLocal) (by omega)
      rw [hParent] at hNone
      simp at hNone
  have hFoundFirst : context.copyPosition foundCopy foundLocal <
      context.copyPosition expansionIndex 0 := by
    exact context.column_lt_of_inCopy_of_lt_copy hFoundCopy
      (context.copyPosition_in_block hFoundLocal)
      (context.copyPosition_in_block context.blockLength_pos)
  have hFoundAncestorFirst := context.parent_ancestor_first_of_first_below
    hTrimmedRow hFoundFirst hTargetLocal hFirstBelow hParent
  have hAtMaximalRow : isAncestor (array.expand expansionIndex).raw
      context.maximalRow (context.copyPosition foundCopy foundLocal)
      (context.copyPosition expansionIndex 0) = true := by
    rcases Nat.eq_or_lt_of_le hMaximalRow with hEqual | hStrict
    · rwa [hEqual]
    · exact isAncestor_of_lt_row hStrict hFoundAncestorFirst
  have hFoundGood := context.ancestor_first_last_at_maximalRow_in_good
    hAtMaximalRow
  have hFoundInCopy := context.copyPosition_in_block
    (copyNumber := foundCopy) hFoundLocal
  simp only [copyStart] at hFoundInCopy
  omega

/-- 在 `row ≥ m₀` 且全部低行都经过副本首列时，Lemma 2.5(iv) 成立。 -/
theorem parent_locality_of_maximalRow_le_of_first_below
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row localColumn found : Nat}
    (hMaximalRow : context.maximalRow ≤ row)
    (hLocal : 0 < localColumn)
    (hLocalBound : localColumn < context.blockLength)
    (hFirstBelow : AncestorBelow (array.expand expansionIndex).raw row
      (context.copyPosition expansionIndex 0)
      (context.copyPosition expansionIndex localColumn))
    (hParent : parent row (array.expand expansionIndex).raw
      (context.copyPosition expansionIndex localColumn) = some found) :
    found < context.parentColumn ∨ context.InCopy expansionIndex found := by
  rcases context.parent_in_good_or_not_later_copy
      (Nat.le_refl expansionIndex) hLocalBound hParent with
    hGood | ⟨foundCopy, foundLocal, hFoundCopyLe, hFoundLocal, hFoundPosition⟩
  · exact Or.inl hGood
  · by_cases hFoundCopyEq : foundCopy = expansionIndex
    · right
      rw [hFoundPosition, hFoundCopyEq]
      exact context.copyPosition_in_block hFoundLocal
    · have hFoundCopyLt : foundCopy < expansionIndex := by omega
      exfalso
      apply context.no_parent_in_earlier_copy_of_maximalRow_le
        hMaximalRow hLocal hFoundCopyLt hFoundLocal hFirstBelow
      rwa [hFoundPosition] at hParent

/-- Hunter Lemma 2.5(iv)，对所有行无条件成立。 -/
theorem parent_locality_all_rows {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat) :
    ∀ row {localColumn found},
      0 < localColumn → localColumn < context.blockLength →
      parent row (array.expand expansionIndex).raw
          (context.copyPosition expansionIndex localColumn) = some found →
      found < context.parentColumn ∨ context.InCopy expansionIndex found := by
  classical
  intro row
  induction row using Nat.strongRecOn with
  | ind row ih =>
      intro localColumn found hLocal hLocalBound hParent
      by_cases hExpansionIndex : 0 < expansionIndex
      · by_cases hFirstBelow : AncestorBelow
            (array.expand expansionIndex).raw row
            (context.copyPosition expansionIndex 0)
            (context.copyPosition expansionIndex localColumn)
        · by_cases hRow : row < context.maximalRow
          · exact context.parent_locality_of_lt_maximalRow_of_first_below
              hExpansionIndex hRow hLocal hLocalBound hFirstBelow hParent
          · exact context.parent_locality_of_maximalRow_le_of_first_below
              (Nat.le_of_not_gt hRow) hLocal hLocalBound hFirstBelow hParent
        · simp only [AncestorBelow] at hFirstBelow
          rcases Classical.not_forall.mp hFirstBelow with
            ⟨lowerRow, hFailure⟩
          have hLower : lowerRow < row := by
            by_cases hLower : lowerRow < row
            · exact hLower
            · exfalso
              apply hFailure
              intro hImpossible
              omega
          have hFirstNotAncestor : ¬ isAncestor
              (array.expand expansionIndex).raw lowerRow
              (context.copyPosition expansionIndex 0)
              (context.copyPosition expansionIndex localColumn) = true := by
            intro hAncestor
            apply hFailure
            intro _
            exact hAncestor
          have hFirstFalse : isAncestor (array.expand expansionIndex).raw
              lowerRow (context.copyPosition expansionIndex 0)
              (context.copyPosition expansionIndex localColumn) = false := by
            cases hValue : isAncestor (array.expand expansionIndex).raw
                lowerRow (context.copyPosition expansionIndex 0)
                (context.copyPosition expansionIndex localColumn) with
            | false => rfl
            | true => exact (hFirstNotAncestor hValue).elim
          exact context.parent_in_good_or_same_copy_of_lower_first_not_ancestor
            hLower hLocal hLocalBound
            (fun {_ _} hMiddle hMiddleBound hLowerParent =>
              ih lowerRow hLower hMiddle hMiddleBound hLowerParent)
            hFirstFalse hParent
      · have hIndexZero : expansionIndex = 0 := by omega
        subst expansionIndex
        have hFoundLt := parent_some_lt hParent
        by_cases hGood : found < context.parentColumn
        · exact Or.inl hGood
        · right
          constructor
          · simp [copyStart]
            omega
          · simp [copyStart]
            simp [copyPosition, copyStart] at hFoundLt
            omega

/-- Hunter Lemma 2.5(i)，`G → B₀` 与 `G → Bₙ` 在所有行等价。 -/
theorem good_to_copy_all_rows {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat) :
    ∀ row {goodColumn localColumn},
      goodColumn < context.parentColumn →
      localColumn < context.blockLength →
      isAncestor (array.expand expansionIndex).raw row goodColumn
          (context.copyPosition 0 localColumn) =
        isAncestor (array.expand expansionIndex).raw row goodColumn
          (context.copyPosition expansionIndex localColumn) := by
  intro row
  induction row using Nat.strongRecOn with
  | ind row rowIH =>
      intro goodColumn localColumn hGood hLocal
      by_cases hTrimmedRow : row < trimHeight (expandRaw array.raw expansionIndex)
      · induction localColumn using Nat.strongRecOn with
        | ind localColumn localIH =>
            by_cases hLocalZero : localColumn = 0
            · subst localColumn
              exact context.good_to_first_copies_all_rows expansionIndex row hGood
            · have hLocalPositive : 0 < localColumn :=
                Nat.zero_lt_of_ne_zero hLocalZero
              cases hAscending : ascending array.raw context.maximalRow
                  context.parentColumn localColumn row with
              | true =>
                  have hAscendingRow : row < context.maximalRow := by
                    simp [ascending] at hAscending
                    exact hAscending.1
                  rcases (context.ascending_iff_first_nonstrict_ancestor_expand
                      expansionIndex hLocal hAscendingRow hTrimmedRow).mp
                      hAscending with hZero | hFirstZero
                  · omega
                  · have hFirstLast : isAncestor
                        (array.expand expansionIndex).raw row
                        (context.copyPosition expansionIndex 0)
                        (context.copyPosition expansionIndex localColumn) = true := by
                      rw [← context.inside_copy_all_rows expansionIndex row
                        context.blockLength_pos hLocal]
                      exact hFirstZero
                    have hGoodFirst := context.good_to_first_copies_all_rows
                      expansionIndex row hGood
                    apply Bool.eq_iff_iff.mpr
                    constructor
                    · intro hGoodTarget
                      have hGoodZeroFirst :=
                        (isAncestor_iff_of_intermediate
                          (array := (array.expand expansionIndex).raw)
                          (row := row)
                          (by simp only [copyPosition, copyStart]; omega)
                          hFirstZero).mp hGoodTarget
                      have hGoodLastFirst : isAncestor
                          (array.expand expansionIndex).raw row goodColumn
                          (context.copyPosition expansionIndex 0) = true := by
                        rw [← hGoodFirst]
                        exact hGoodZeroFirst
                      exact isAncestor_trans hGoodLastFirst hFirstLast
                    · intro hGoodTarget
                      have hGoodLastFirst :=
                        (isAncestor_iff_of_intermediate
                          (array := (array.expand expansionIndex).raw)
                          (row := row)
                          (by simp only [copyPosition, copyStart]; omega)
                          hFirstLast).mp hGoodTarget
                      have hGoodZeroFirst : isAncestor
                          (array.expand expansionIndex).raw row goodColumn
                          (context.copyPosition 0 0) = true := by
                        rw [hGoodFirst]
                        exact hGoodLastFirst
                      exact isAncestor_trans hGoodZeroFirst hFirstZero
              | false =>
                  have hParentShape :=
                    context.parent_copies_eq_or_internal_of_not_ascending
                      hTrimmedRow hLocalPositive hLocal hAscending
                      (fun {found} hParent =>
                        context.parent_locality_all_rows expansionIndex row
                          hLocalPositive hLocal hParent)
                      (fun lowerRow hLower candidate hCandidate =>
                        rowIH lowerRow hLower hCandidate hLocal)
                  rcases hParentShape with hParentsEqual |
                    ⟨parentLocal, hParentLocal, hZeroParent, hLastParent⟩
                  · exact isAncestor_congr_of_parent_eq hParentsEqual goodColumn
                  · have hParentBound : parentLocal < context.blockLength :=
                      Nat.lt_trans hParentLocal hLocal
                    have hGoodParents := localIH parentLocal hParentLocal
                      hParentBound
                    apply Bool.eq_iff_iff.mpr
                    constructor
                    · intro hGoodTarget
                      rcases (isAncestor_iff_of_parent_some hZeroParent).mp
                          hGoodTarget with hEqual | hGoodParent
                      · simp only [copyPosition, copyStart] at hEqual
                        omega
                      · apply (isAncestor_iff_of_parent_some hLastParent).mpr
                        right
                        rw [← hGoodParents]
                        exact hGoodParent
                    · intro hGoodTarget
                      rcases (isAncestor_iff_of_parent_some hLastParent).mp
                          hGoodTarget with hEqual | hGoodParent
                      · simp only [copyPosition, copyStart] at hEqual
                        omega
                      · apply (isAncestor_iff_of_parent_some hZeroParent).mpr
                        right
                        rw [hGoodParents]
                        exact hGoodParent
      · rw [isAncestor_expand_eq_false_of_le expansionIndex goodColumn
          (context.copyPosition 0 localColumn) (by omega)]
        rw [isAncestor_expand_eq_false_of_le expansionIndex goodColumn
          (context.copyPosition expansionIndex localColumn) (by omega)]

/-- `row < m₀` 时，大 expansion 中任意副本的内部 ancestry 都等同于第零副本。 -/
theorem inside_copy_eq_zero_of_lt_maximalRow
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row copyNumber leftLocal rightLocal : Nat}
    (hCopy : copyNumber ≤ expansionIndex)
    (hRow : row < context.maximalRow)
    (hLeft : leftLocal < context.blockLength)
    (hRight : rightLocal < context.blockLength) :
    isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition 0 leftLocal)
        (context.copyPosition 0 rightLocal) =
      isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition copyNumber leftLocal)
        (context.copyPosition copyNumber rightLocal) := by
  by_cases hCopyZero : copyNumber = 0
  · subst copyNumber
    rfl
  · have hCopyPositive : 0 < copyNumber := Nat.zero_lt_of_ne_zero hCopyZero
    have hInsideSmall := context.inside_copy_all_rows copyNumber row hLeft hRight
    have hZeroTargetSmall := context.copyPosition_lt_length
      (index := copyNumber) (copyNumber := 0) (Nat.zero_le _) hRight
    have hCopyTargetSmall := context.copyPosition_lt_length
      (index := copyNumber) (copyNumber := copyNumber) (Nat.le_refl _) hRight
    have hZeroPrefix := context.isAncestor_expand_indices_eq_of_lt_length
      (ancestor := context.copyPosition 0 leftLocal)
      hCopyPositive hCopy hZeroTargetSmall hRow
    have hCopyPrefix := context.isAncestor_expand_indices_eq_of_lt_length
      (ancestor := context.copyPosition copyNumber leftLocal)
      hCopyPositive hCopy hCopyTargetSmall hRow
    rw [← hZeroPrefix, ← hCopyPrefix]
    exact hInsideSmall

/-- 较早副本到较晚副本内部目标时，必先经过较晚副本的首列。 -/
theorem first_later_nonstrict_ancestor_of_earlier_ancestor
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row earlierCopy laterCopy leftLocal rightLocal : Nat}
    (hLeft : leftLocal < context.blockLength)
    (hRight : rightLocal < context.blockLength)
    (hCopies : earlierCopy < laterCopy)
    (hLater : laterCopy ≤ expansionIndex)
    (hAncestor : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition earlierCopy leftLocal)
      (context.copyPosition laterCopy rightLocal) = true) :
    rightLocal = 0 ∨
      isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition laterCopy 0)
        (context.copyPosition laterCopy rightLocal) = true := by
  by_cases hRightZero : rightLocal = 0
  · exact Or.inl hRightZero
  · right
    have hRightPositive : 0 < rightLocal := Nat.zero_lt_of_ne_zero hRightZero
    rcases ancestor_entries_lt hAncestor with
      ⟨ancestorValue, targetValue, hAncestorEntry, hTargetEntry, hValueLt⟩
    have hExpandedUniform := ValidArray.uniformHeight_expand
      (index := expansionIndex)
      (rectangular_iff_exists_uniformHeight.mp array.rectangular_eq).choose_spec
    have hLargerRow := row_lt_uniformHeight_of_entry?_eq_some
      hExpandedUniform hTargetEntry
    have hTargetSmall := context.copyPosition_lt_length
      (index := laterCopy) (copyNumber := laterCopy) (Nat.le_refl _) hRight
    have hRawLargerEntry : entry? (expandRaw array.raw expansionIndex)
        (context.copyPosition laterCopy rightLocal) row = some targetValue := by
      rw [← entry?_expand_of_lt expansionIndex _ row hLargerRow]
      exact hTargetEntry
    have hRawSmallerEntry : entry? (expandRaw array.raw laterCopy)
        (context.copyPosition laterCopy rightLocal) row = some targetValue := by
      rw [context.entry?_expandRaw_indices_eq_of_lt_length hLater hTargetSmall]
      exact hRawLargerEntry
    have hTargetNonzero : targetValue ≠ 0 := by omega
    have hSmallerRow := row_lt_trimHeight_of_entry?_eq_some_of_ne_zero
      hRawSmallerEntry hTargetNonzero
    have hAncestorSmall : isAncestor (array.expand laterCopy).raw row
        (context.copyPosition earlierCopy leftLocal)
        (context.copyPosition laterCopy rightLocal) = true := by
      rw [context.isAncestor_expand_indices_eq_of_rows hLater hTargetSmall
        hSmallerRow hLargerRow]
      exact hAncestor
    cases hFirstSmall : isAncestor (array.expand laterCopy).raw row
        (context.copyPosition laterCopy 0)
        (context.copyPosition laterCopy rightLocal) with
    | true =>
        rw [← context.isAncestor_expand_indices_eq_of_rows hLater hTargetSmall
          hSmallerRow hLargerRow]
        exact hFirstSmall
    | false =>
        have hRegion := context.ancestor_in_good_or_same_copy_of_first_not_ancestor
          hRightPositive hRight
          (fun {middleLocal parentColumn} hMiddle hMiddleBound hParent =>
            context.parent_locality_all_rows laterCopy row
              hMiddle hMiddleBound hParent)
          hFirstSmall hAncestorSmall
        rcases hRegion with hGood | hSameCopy
        · have hEarlierInCopy := context.copyPosition_in_block
              (copyNumber := earlierCopy) hLeft
          simp only [copyStart] at hEarlierInCopy
          omega
        · have hEarlierInCopy := context.copyPosition_in_block
              (copyNumber := earlierCopy) hLeft
          have hLaterInCopy := hSameCopy
          have hImpossible := context.column_lt_of_inCopy_of_lt_copy hCopies
            hEarlierInCopy hLaterInCopy
          omega

/-- 任意副本首列的 `m₀`-ancestors 在更大 expansion 中仍全部位于 `G`。 -/
theorem ancestor_first_copy_at_maximalRow_in_good
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex copyNumber ancestor : Nat}
    (hCopy : copyNumber ≤ expansionIndex)
    (hAncestor : isAncestor (array.expand expansionIndex).raw
      context.maximalRow ancestor (context.copyPosition copyNumber 0) = true) :
    ancestor < context.parentColumn := by
  rcases ancestor_entries_lt hAncestor with
    ⟨ancestorValue, targetValue, hAncestorEntry, hTargetEntry, hValueLt⟩
  have hExpandedUniform := ValidArray.uniformHeight_expand
    (index := expansionIndex)
    (rectangular_iff_exists_uniformHeight.mp array.rectangular_eq).choose_spec
  have hLargerRow := row_lt_uniformHeight_of_entry?_eq_some
    hExpandedUniform hTargetEntry
  have hTargetSmall := context.copyPosition_lt_length
    (index := copyNumber) (copyNumber := copyNumber) (Nat.le_refl _)
    context.blockLength_pos
  have hRawLargerEntry : entry? (expandRaw array.raw expansionIndex)
      (context.copyPosition copyNumber 0) context.maximalRow = some targetValue := by
    rw [← entry?_expand_of_lt expansionIndex _ context.maximalRow hLargerRow]
    exact hTargetEntry
  have hRawSmallerEntry : entry? (expandRaw array.raw copyNumber)
      (context.copyPosition copyNumber 0) context.maximalRow = some targetValue := by
    rw [context.entry?_expandRaw_indices_eq_of_lt_length hCopy hTargetSmall]
    exact hRawLargerEntry
  have hTargetNonzero : targetValue ≠ 0 := by omega
  have hSmallerRow := row_lt_trimHeight_of_entry?_eq_some_of_ne_zero
    hRawSmallerEntry hTargetNonzero
  have hAncestorSmall : isAncestor (array.expand copyNumber).raw
      context.maximalRow ancestor (context.copyPosition copyNumber 0) = true := by
    rw [context.isAncestor_expand_indices_eq_of_rows hCopy hTargetSmall
      hSmallerRow hLargerRow]
    exact hAncestor
  exact context.ancestor_first_last_at_maximalRow_in_good hAncestorSmall

/-- 从较早副本跨到较晚副本时，行号必小于 `m₀`，且链经过后者首列。 -/
theorem earlier_ancestor_later_first_of_ancestor
    {array : ValidArray} (context : ExpansionContext array)
    {expansionIndex row earlierCopy laterCopy leftLocal rightLocal : Nat}
    (hLeft : leftLocal < context.blockLength)
    (hRight : rightLocal < context.blockLength)
    (hCopies : earlierCopy < laterCopy)
    (hLater : laterCopy ≤ expansionIndex)
    (hAncestor : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition earlierCopy leftLocal)
      (context.copyPosition laterCopy rightLocal) = true) :
    row < context.maximalRow ∧
      isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition earlierCopy leftLocal)
        (context.copyPosition laterCopy 0) = true := by
  have hEarlierFirst : isAncestor (array.expand expansionIndex).raw row
      (context.copyPosition earlierCopy leftLocal)
      (context.copyPosition laterCopy 0) = true := by
    rcases context.first_later_nonstrict_ancestor_of_earlier_ancestor
        hLeft hRight hCopies hLater hAncestor with hRightZero | hFirstAncestor
    · subst rightLocal
      exact hAncestor
    · exact (isAncestor_iff_of_intermediate
        (array := (array.expand expansionIndex).raw) (row := row)
        (context.column_lt_of_inCopy_of_lt_copy hCopies
          (context.copyPosition_in_block hLeft)
          (context.copyPosition_in_block context.blockLength_pos))
        hFirstAncestor).mp hAncestor
  have hRow : row < context.maximalRow := by
    apply Nat.lt_of_not_ge
    intro hMaximalRow
    have hAtMaximalRow : isAncestor (array.expand expansionIndex).raw
        context.maximalRow (context.copyPosition earlierCopy leftLocal)
        (context.copyPosition laterCopy 0) = true := by
      rcases Nat.eq_or_lt_of_le hMaximalRow with hEqual | hStrict
      · rwa [hEqual]
      · exact isAncestor_of_lt_row hStrict hEarlierFirst
    have hGood := context.ancestor_first_copy_at_maximalRow_in_good
      hLater hAtMaximalRow
    have hEarlierInCopy := context.copyPosition_in_block
      (copyNumber := earlierCopy) hLeft
    simp only [copyStart] at hEarlierInCopy
    omega
  exact ⟨hRow, hEarlierFirst⟩

/-- Hunter Lemma 2.5(v)，较早副本到相邻两个后继目标副本的 ancestry 等价。 -/
theorem earlier_to_successive_all_rows
    {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex : Nat) : ∀ row
    {leftLocal rightLocal earlierCopy laterCopy},
      leftLocal < context.blockLength →
      rightLocal < context.blockLength →
      earlierCopy < laterCopy → laterCopy < expansionIndex →
      isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition earlierCopy leftLocal)
          (context.copyPosition laterCopy rightLocal) =
        isAncestor (array.expand expansionIndex).raw row
          (context.copyPosition earlierCopy leftLocal)
          (context.copyPosition (laterCopy + 1) rightLocal) := by
  intro row leftLocal rightLocal earlierCopy laterCopy
    hLeft hRight hEarlier hLater
  have hLaterLe : laterCopy ≤ expansionIndex := by omega
  have hNextLe : laterCopy + 1 ≤ expansionIndex := by omega
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hAncestor
    have hStructure := context.earlier_ancestor_later_first_of_ancestor
      hLeft hRight hEarlier hLaterLe hAncestor
    have hBoundary := context.first_copy_ancestor_next
      (expansionIndex := expansionIndex) (copyNumber := laterCopy)
      hLater hStructure.1
    have hEarlierNextFirst := isAncestor_trans hStructure.2 hBoundary
    by_cases hRightZero : rightLocal = 0
    · subst rightLocal
      exact hEarlierNextFirst
    · rcases context.first_later_nonstrict_ancestor_of_earlier_ancestor
          hLeft hRight hEarlier hLaterLe hAncestor with hImpossible | hFirstLater
      · exact (hRightZero hImpossible).elim
      · have hInsideLater := context.inside_copy_eq_zero_of_lt_maximalRow
            hLaterLe hStructure.1 context.blockLength_pos hRight
        have hInsideNext := context.inside_copy_eq_zero_of_lt_maximalRow
          hNextLe hStructure.1 context.blockLength_pos hRight
        have hFirstNext : isAncestor (array.expand expansionIndex).raw row
            (context.copyPosition (laterCopy + 1) 0)
            (context.copyPosition (laterCopy + 1) rightLocal) = true := by
          rw [← hInsideNext, hInsideLater]
          exact hFirstLater
        exact isAncestor_trans hEarlierNextFirst hFirstNext
  · intro hAncestor
    have hStructure := context.earlier_ancestor_later_first_of_ancestor
      hLeft hRight (by omega) hNextLe hAncestor
    have hBoundary := context.first_copy_ancestor_next
      (expansionIndex := expansionIndex) (copyNumber := laterCopy)
      hLater hStructure.1
    have hEarlierLaterFirst :=
      (isAncestor_iff_of_intermediate
        (array := (array.expand expansionIndex).raw) (row := row)
        (context.column_lt_of_inCopy_of_lt_copy hEarlier
          (context.copyPosition_in_block hLeft)
          (context.copyPosition_in_block context.blockLength_pos))
        hBoundary).mp hStructure.2
    by_cases hRightZero : rightLocal = 0
    · subst rightLocal
      exact hEarlierLaterFirst
    · rcases context.first_later_nonstrict_ancestor_of_earlier_ancestor
          hLeft hRight (by omega) hNextLe hAncestor with
          hImpossible | hFirstNext
      · exact (hRightZero hImpossible).elim
      · have hInsideNext := context.inside_copy_eq_zero_of_lt_maximalRow
            hNextLe hStructure.1 context.blockLength_pos hRight
        have hInsideLater := context.inside_copy_eq_zero_of_lt_maximalRow
          hLaterLe hStructure.1 context.blockLength_pos hRight
        have hFirstLater : isAncestor (array.expand expansionIndex).raw row
            (context.copyPosition laterCopy 0)
            (context.copyPosition laterCopy rightLocal) = true := by
          rw [← hInsideLater, hInsideNext]
          exact hFirstNext
        exact isAncestor_trans hEarlierLaterFirst hFirstLater

/-- Hunter Lemma 2.5 在任意固定行上的五个分句。 -/
theorem lemma25AtRow_all {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex row : Nat) :
    Lemma25AtRow context expansionIndex row := by
  constructor
  · intro goodColumn localColumn hGood hLocal
    exact context.good_to_copy_all_rows expansionIndex row hGood hLocal
  · intro leftLocal rightLocal hLeft hRight
    exact context.inside_copy_all_rows expansionIndex row hLeft hRight
  · intro hExpansionIndex hRow localColumn hLocal
    exact context.previous_to_next_all_rows hExpansionIndex row hRow hLocal
  · intro localColumn found hLocal hLocalBound hParent
    exact context.parent_locality_all_rows expansionIndex row
      hLocal hLocalBound hParent
  · intro leftLocal rightLocal earlierCopy laterCopy
      hLeft hRight hEarlier hLater
    exact context.earlier_to_successive_all_rows expansionIndex row
      hLeft hRight hEarlier hLater

/-- Hunter Lemma 2.5 的完整形式化。 -/
theorem lemma25_all {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat) :
    Lemma25 context expansionIndex := by
  intro row
  exact context.lemma25AtRow_all expansionIndex row

theorem lemma25AtRow_of_trimHeight_le {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex row : Nat)
    (hRow : trimHeight (expandRaw array.raw expansionIndex) ≤ row) :
    Lemma25AtRow context expansionIndex row := by
  constructor
  · intro goodColumn localColumn hGood hLocal
    rw [isAncestor_expand_eq_false_of_le expansionIndex goodColumn
      (context.copyPosition 0 localColumn) hRow]
    rw [isAncestor_expand_eq_false_of_le expansionIndex goodColumn
      (context.copyPosition expansionIndex localColumn) hRow]
  · intro leftLocal rightLocal hLeft hRight
    rw [isAncestor_expand_eq_false_of_le expansionIndex
      (context.copyPosition 0 leftLocal) (context.copyPosition 0 rightLocal) hRow]
    rw [isAncestor_expand_eq_false_of_le expansionIndex
      (context.copyPosition expansionIndex leftLocal)
      (context.copyPosition expansionIndex rightLocal) hRow]
  · intro hPositive hMaximal localColumn hLocal
    have hBound := context.maximalRow_le_trimHeight_expandRaw hPositive
    omega
  · intro localColumn found hPositive hLocal hParent
    rw [parent_expand_eq_none_of_le expansionIndex
      (context.copyPosition expansionIndex localColumn) hRow] at hParent
    simp at hParent
  · intro leftLocal rightLocal earlierCopy laterCopy hLeft hRight hEarlier hLater
    rw [isAncestor_expand_eq_false_of_le expansionIndex
      (context.copyPosition earlierCopy leftLocal)
      (context.copyPosition laterCopy rightLocal) hRow]
    rw [isAncestor_expand_eq_false_of_le expansionIndex
      (context.copyPosition earlierCopy leftLocal)
      (context.copyPosition (laterCopy + 1) rightLocal) hRow]

theorem lemma25_of_below_trimHeight {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat)
    (hRows : ∀ row, row < trimHeight (expandRaw array.raw expansionIndex) →
      Lemma25AtRow context expansionIndex row) :
    Lemma25 context expansionIndex := by
  intro row
  by_cases hRow : row < trimHeight (expandRaw array.raw expansionIndex)
  · exact hRows row hRow
  · exact context.lemma25AtRow_of_trimHeight_le expansionIndex row
      (by omega)

end ExpansionContext

end BMS
end YesMetaZFC
