import YesMetaZFC.BMS.ExpansionRepresentation

/-!
# expansion 标签族的组装

反射迭代自然分别给出 `G` 上的旧标签和每个 `Bᵢ` 上的新标签。本文件把
这些分块函数组装成 expansion 全部列上的单一函数，并证明两类坐标的
化简定理。
-/

namespace YesMetaZFC
namespace BMS

universe u

namespace StabilityFrame

/-- `G` 与各复制块的分块标签族。 -/
structure ExpansionLabelFamily {Label : Type u} {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat) where
  goodLabel : Fin context.parentColumn → Label
  copyLabel : Fin (expansionIndex + 1) → Fin context.blockLength → Label

namespace ExpansionLabelFamily

/-- 非 `G` 列的唯一复制块坐标。 -/
noncomputable def copyCoordinates {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat)
    (column : Fin (array.expand expansionIndex).raw.length)
    (hNotGood : context.parentColumn ≤ column.1) :
    Fin (expansionIndex + 1) × Fin context.blockLength := by
  let offset := column.1 - context.parentColumn
  have hOffset : offset < (expansionIndex + 1) * context.blockLength := by
    have hColumn : column.1 < context.parentColumn +
        (expansionIndex + 1) * context.blockLength := by
      simpa only [context.length_expand] using column.isLt
    dsimp only [offset]
    omega
  exact (
    ⟨offset / context.blockLength,
      (Nat.div_lt_iff_lt_mul context.blockLength_pos).2 hOffset⟩,
    ⟨offset % context.blockLength,
      Nat.mod_lt offset context.blockLength_pos⟩)

/-- 选出的坐标确实重建原列号。 -/
theorem copyPosition_copyCoordinates {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat)
    (column : Fin (array.expand expansionIndex).raw.length)
    (hNotGood : context.parentColumn ≤ column.1) :
    context.copyPosition
        (copyCoordinates context expansionIndex column hNotGood).1.1
        (copyCoordinates context expansionIndex column hNotGood).2.1 =
      column.1 := by
  classical
  simp only [copyCoordinates, ExpansionContext.copyPosition,
    ExpansionContext.copyStart]
  have hDecomposition := Nat.div_add_mod
    (column.1 - context.parentColumn) context.blockLength
  rw [Nat.mul_comm] at hDecomposition
  omega

/-- 把分块标签族组装成输出数组的标签函数。 -/
noncomputable def assembled {Label : Type u} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    (family : ExpansionLabelFamily (Label := Label) context expansionIndex) :
    Fin (array.expand expansionIndex).raw.length → Label := by
  classical
  intro column
  by_cases hGood : column.1 < context.parentColumn
  · exact family.goodLabel ⟨column.1, hGood⟩
  · let coordinates := copyCoordinates context expansionIndex column
      (Nat.le_of_not_gt hGood)
    exact family.copyLabel coordinates.1 coordinates.2

@[simp]
theorem assembled_good {Label : Type u} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    (family : ExpansionLabelFamily (Label := Label) context expansionIndex)
    (column : Fin context.parentColumn)
    (hColumn : column.1 < (array.expand expansionIndex).raw.length) :
    family.assembled ⟨column.1, hColumn⟩ = family.goodLabel column := by
  classical
  simp [assembled, column.isLt]

/-- 对输出列直接使用 `G` 范围证明的化简形式。 -/
theorem assembled_of_lt_parentColumn {Label : Type u} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    (family : ExpansionLabelFamily (Label := Label) context expansionIndex)
    (column : Fin (array.expand expansionIndex).raw.length)
    (hGood : column.1 < context.parentColumn) :
    family.assembled column = family.goodLabel ⟨column.1, hGood⟩ := by
  classical
  simp [assembled, hGood]

@[simp]
theorem assembled_copy {Label : Type u} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    (family : ExpansionLabelFamily (Label := Label) context expansionIndex)
    (copyNumber : Fin (expansionIndex + 1))
    (localColumn : Fin context.blockLength) :
    family.assembled
        ⟨context.copyPosition copyNumber.1 localColumn.1,
          context.copyPosition_lt_length
            (Nat.lt_succ_iff.mp copyNumber.isLt) localColumn.isLt⟩ =
      family.copyLabel copyNumber localColumn := by
  classical
  have hNotGood : ¬ context.copyPosition copyNumber.1 localColumn.1 <
      context.parentColumn := by
    simp only [ExpansionContext.copyPosition, ExpansionContext.copyStart]
    omega
  simp only [assembled, dif_neg hNotGood]
  let coordinates := copyCoordinates context expansionIndex
    ⟨context.copyPosition copyNumber.1 localColumn.1,
      context.copyPosition_lt_length
        (Nat.lt_succ_iff.mp copyNumber.isLt) localColumn.isLt⟩
    (Nat.le_of_not_gt hNotGood)
  have hPosition := copyPosition_copyCoordinates context expansionIndex
    ⟨context.copyPosition copyNumber.1 localColumn.1,
      context.copyPosition_lt_length
        (Nat.lt_succ_iff.mp copyNumber.isLt) localColumn.isLt⟩
    (Nat.le_of_not_gt hNotGood)
  have hCoordinates := context.copyPosition_injective
    coordinates.2.isLt localColumn.isLt hPosition
  have hCopy : coordinates.1 = copyNumber := Fin.ext hCoordinates.1
  have hLocal : coordinates.2 = localColumn := Fin.ext hCoordinates.2
  change family.copyLabel coordinates.1 coordinates.2 =
    family.copyLabel copyNumber localColumn
  rw [hCopy, hLocal]

end ExpansionLabelFamily

/--
分块标签族的局部关系证书。四个严格序字段与四个 ancestry 字段分别
对应 `G×G`、`G×Bᵢ`、`Bᵢ×Bᵢ` 和 `Bᵢ×Bⱼ`。
-/
structure ExpansionRegionCertificate {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    (context : ExpansionContext array) (expansionIndex : Nat) where
  family : ExpansionLabelFamily (Label := Label) context expansionIndex
  good_lt_good : ∀ {left right}, left < right →
    frame.lt (family.goodLabel left) (family.goodLabel right)
  good_lt_copy : ∀ goodColumn copyNumber localColumn,
    frame.lt (family.goodLabel goodColumn)
      (family.copyLabel copyNumber localColumn)
  inside_copy_lt : ∀ copyNumber {leftLocal rightLocal},
    leftLocal < rightLocal →
      frame.lt (family.copyLabel copyNumber leftLocal)
        (family.copyLabel copyNumber rightLocal)
  between_copies_lt : ∀ {leftCopy rightCopy}, leftCopy < rightCopy →
    ∀ leftLocal rightLocal,
      frame.lt (family.copyLabel leftCopy leftLocal)
        (family.copyLabel rightCopy rightLocal)
  preserves_good : ∀ {row} {left right : Fin context.parentColumn},
    isAncestor (array.expand expansionIndex).raw row left.1 right.1 = true →
      frame.stableLt row (family.goodLabel left) (family.goodLabel right)
  preserves_good_to_copy : ∀ {row} {left : Fin context.parentColumn}
      {copyNumber localColumn},
    isAncestor (array.expand expansionIndex).raw row left.1
        (context.copyPosition copyNumber.1 localColumn.1) = true →
      frame.stableLt row (family.goodLabel left)
        (family.copyLabel copyNumber localColumn)
  preserves_inside_copy : ∀ {row copyNumber leftLocal rightLocal},
    isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition copyNumber.1 leftLocal.1)
        (context.copyPosition copyNumber.1 rightLocal.1) = true →
      frame.stableLt row (family.copyLabel copyNumber leftLocal)
        (family.copyLabel copyNumber rightLocal)
  preserves_between_copies : ∀ {row leftCopy rightCopy leftLocal rightLocal},
    leftCopy < rightCopy →
    isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition leftCopy.1 leftLocal.1)
        (context.copyPosition rightCopy.1 rightLocal.1) = true →
      frame.stableLt row (family.copyLabel leftCopy leftLocal)
        (family.copyLabel rightCopy rightLocal)

namespace ExpansionRegionCertificate

/-- 局部分区证书组装为 `ExpansionLabeling`。 -/
noncomputable def labeling {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    {context : ExpansionContext array} {expansionIndex : Nat}
    (certificate : ExpansionRegionCertificate (frame := frame)
      context expansionIndex) :
    ExpansionLabeling (frame := frame) context expansionIndex where
  label := certificate.family.assembled
  strictlyIncreasing := by
    intro left right hOrder
    by_cases hRightGood : right.1 < context.parentColumn
    · have hLeftGood : left.1 < context.parentColumn :=
        Nat.lt_trans hOrder hRightGood
      rw [certificate.family.assembled_of_lt_parentColumn left hLeftGood,
        certificate.family.assembled_of_lt_parentColumn right hRightGood]
      exact certificate.good_lt_good
        (left := ⟨left.1, hLeftGood⟩)
        (right := ⟨right.1, hRightGood⟩) hOrder
    · let rightCoordinates := ExpansionLabelFamily.copyCoordinates
        context expansionIndex right (Nat.le_of_not_gt hRightGood)
      have hRightPosition := ExpansionLabelFamily.copyPosition_copyCoordinates
        context expansionIndex right (Nat.le_of_not_gt hRightGood)
      by_cases hLeftGood : left.1 < context.parentColumn
      · have hAssembledLeft : certificate.family.assembled left =
            certificate.family.goodLabel ⟨left.1, hLeftGood⟩ := by
          have hAssembled := certificate.family.assembled_good
            ⟨left.1, hLeftGood⟩ left.isLt
          have hColumn :
              (⟨left.1, left.isLt⟩ :
                Fin (array.expand expansionIndex).raw.length) = left :=
            Fin.ext rfl
          rw [hColumn] at hAssembled
          exact hAssembled
        have hAssembledRight : certificate.family.assembled right =
            certificate.family.copyLabel rightCoordinates.1
              rightCoordinates.2 := by
          let rightColumn : Fin (array.expand expansionIndex).raw.length :=
            ⟨context.copyPosition rightCoordinates.1.1
                rightCoordinates.2.1,
              context.copyPosition_lt_length
                (Nat.lt_succ_iff.mp rightCoordinates.1.isLt)
                rightCoordinates.2.isLt⟩
          have hRightEq : rightColumn = right := Fin.ext hRightPosition
          rw [← hRightEq]
          exact certificate.family.assembled_copy _ _
        rw [hAssembledLeft, hAssembledRight]
        exact certificate.good_lt_copy _ _ _
      · let leftCoordinates := ExpansionLabelFamily.copyCoordinates
          context expansionIndex left (Nat.le_of_not_gt hLeftGood)
        have hLeftPosition := ExpansionLabelFamily.copyPosition_copyCoordinates
          context expansionIndex left (Nat.le_of_not_gt hLeftGood)
        have hAssembledLeft : certificate.family.assembled left =
            certificate.family.copyLabel leftCoordinates.1
              leftCoordinates.2 := by
          let leftColumn : Fin (array.expand expansionIndex).raw.length :=
            ⟨context.copyPosition leftCoordinates.1.1
                leftCoordinates.2.1,
              context.copyPosition_lt_length
                (Nat.lt_succ_iff.mp leftCoordinates.1.isLt)
                leftCoordinates.2.isLt⟩
          have hLeftEq : leftColumn = left := Fin.ext hLeftPosition
          rw [← hLeftEq]
          exact certificate.family.assembled_copy _ _
        have hAssembledRight : certificate.family.assembled right =
            certificate.family.copyLabel rightCoordinates.1
              rightCoordinates.2 := by
          let rightColumn : Fin (array.expand expansionIndex).raw.length :=
            ⟨context.copyPosition rightCoordinates.1.1
                rightCoordinates.2.1,
              context.copyPosition_lt_length
                (Nat.lt_succ_iff.mp rightCoordinates.1.isLt)
                rightCoordinates.2.isLt⟩
          have hRightEq : rightColumn = right := Fin.ext hRightPosition
          rw [← hRightEq]
          exact certificate.family.assembled_copy _ _
        rw [hAssembledLeft, hAssembledRight]
        rcases Nat.lt_trichotomy leftCoordinates.1.1
            rightCoordinates.1.1 with hCopies | hCopies | hCopies
        · exact certificate.between_copies_lt hCopies _ _
        · have hCopyEq : leftCoordinates.1 = rightCoordinates.1 :=
            Fin.ext hCopies
          rw [← hCopyEq]
          apply certificate.inside_copy_lt
          have hPositionOrder : context.copyPosition leftCoordinates.1.1
              leftCoordinates.2.1 <
              context.copyPosition rightCoordinates.1.1
                rightCoordinates.2.1 := by
            change left.1 < right.1 at hOrder
            calc
              context.copyPosition leftCoordinates.1.1
                  leftCoordinates.2.1 = left.1 := hLeftPosition
              _ < right.1 := hOrder
              _ = context.copyPosition rightCoordinates.1.1
                  rightCoordinates.2.1 := hRightPosition.symm
          rw [hCopies] at hPositionOrder
          simp only [ExpansionContext.copyPosition,
            ExpansionContext.copyStart] at hPositionOrder
          omega
        · have hReverse := context.column_lt_of_inCopy_of_lt_copy hCopies
            (context.copyPosition_in_block rightCoordinates.2.isLt)
            (context.copyPosition_in_block leftCoordinates.2.isLt)
          rw [hLeftPosition, hRightPosition] at hReverse
          omega
  preserves_good := by
    intro row left right hRightGood hAncestor
    have hLeftGood : left.1 < context.parentColumn :=
      Nat.lt_trans (isAncestor_lt hAncestor) hRightGood
    rw [certificate.family.assembled_of_lt_parentColumn left hLeftGood,
      certificate.family.assembled_of_lt_parentColumn right hRightGood]
    exact certificate.preserves_good
      (left := ⟨left.1, hLeftGood⟩)
      (right := ⟨right.1, hRightGood⟩) hAncestor
  preserves_good_to_copy := by
    intro row left copyNumber localColumn hLeft hCopy hLocal hAncestor
    rw [certificate.family.assembled_of_lt_parentColumn left hLeft,
      certificate.family.assembled_copy
        ⟨copyNumber, Nat.lt_succ_iff.mpr hCopy⟩
        ⟨localColumn, hLocal⟩]
    exact certificate.preserves_good_to_copy
      (left := ⟨left.1, hLeft⟩)
      (copyNumber := ⟨copyNumber, Nat.lt_succ_iff.mpr hCopy⟩)
      (localColumn := ⟨localColumn, hLocal⟩) hAncestor
  preserves_inside_copy := by
    intro row copyNumber leftLocal rightLocal hCopy hLeft hRight hAncestor
    have hLeftValue := certificate.family.assembled_copy
      ⟨copyNumber, Nat.lt_succ_iff.mpr hCopy⟩ ⟨leftLocal, hLeft⟩
    have hRightValue := certificate.family.assembled_copy
      ⟨copyNumber, Nat.lt_succ_iff.mpr hCopy⟩ ⟨rightLocal, hRight⟩
    rw [hLeftValue, hRightValue]
    exact certificate.preserves_inside_copy
      (copyNumber := ⟨copyNumber, Nat.lt_succ_iff.mpr hCopy⟩)
      (leftLocal := ⟨leftLocal, hLeft⟩)
      (rightLocal := ⟨rightLocal, hRight⟩) hAncestor
  preserves_between_copies := by
    intro row leftCopy rightCopy leftLocal rightLocal hCopies hRightCopy
      hLeft hRight hAncestor
    have hLeftCopy : leftCopy < expansionIndex + 1 := by omega
    have hLeftValue := certificate.family.assembled_copy
      ⟨leftCopy, hLeftCopy⟩ ⟨leftLocal, hLeft⟩
    have hRightValue := certificate.family.assembled_copy
      ⟨rightCopy, Nat.lt_succ_iff.mpr hRightCopy⟩ ⟨rightLocal, hRight⟩
    rw [hLeftValue, hRightValue]
    exact certificate.preserves_between_copies
      (leftCopy := ⟨leftCopy, hLeftCopy⟩)
      (rightCopy := ⟨rightCopy, Nat.lt_succ_iff.mpr hRightCopy⟩)
      (leftLocal := ⟨leftLocal, hLeft⟩)
      (rightLocal := ⟨rightLocal, hRight⟩) hCopies hAncestor

end ExpansionRegionCertificate
end StabilityFrame
end BMS
end YesMetaZFC
