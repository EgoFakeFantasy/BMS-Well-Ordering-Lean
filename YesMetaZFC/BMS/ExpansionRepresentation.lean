import YesMetaZFC.BMS.BM4WellOrder

/-!
# expansion 标签的区域组装

一次非退化 expansion 的列唯一分成 `G` 与若干复制块。本文件证明：只要标签关系已在
`G×G`、`G×B_i`、`B_i×B_i` 和 `B_i×B_j (i<j)` 四个区域分别验证，就能组装成
整个 expansion 的稳定表示。后续 Lemma 2.5/2.6 适配层只需逐区填充这些字段。
-/

namespace YesMetaZFC
namespace BMS

universe u

namespace StabilityFrame

/-- 一次非退化 expansion 的分区标签证书。 -/
structure ExpansionLabeling {Label : Type u} {frame : StabilityFrame Label}
    {array : ValidArray} (context : ExpansionContext array)
    (expansionIndex : Nat) where
  label : Fin (array.expand expansionIndex).raw.length → Label
  strictlyIncreasing : ∀ {left right}, left < right →
    frame.lt (label left) (label right)
  preserves_good : ∀ {row} {left right : Fin (array.expand expansionIndex).raw.length},
    right.1 < context.parentColumn →
    isAncestor (array.expand expansionIndex).raw row left.1 right.1 = true →
      frame.stableLt row (label left) (label right)
  preserves_good_to_copy : ∀ {row}
      {left : Fin (array.expand expansionIndex).raw.length}
      {copyNumber localColumn},
    left.1 < context.parentColumn →
    (hCopy : copyNumber ≤ expansionIndex) →
    (hLocal : localColumn < context.blockLength) →
    isAncestor (array.expand expansionIndex).raw row left.1
        (context.copyPosition copyNumber localColumn) = true →
      frame.stableLt row (label left)
        (label ⟨context.copyPosition copyNumber localColumn,
          context.copyPosition_lt_length hCopy hLocal⟩)
  preserves_inside_copy : ∀ {row copyNumber leftLocal rightLocal},
    (hCopy : copyNumber ≤ expansionIndex) →
    (hLeft : leftLocal < context.blockLength) →
    (hRight : rightLocal < context.blockLength) →
    isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition copyNumber leftLocal)
        (context.copyPosition copyNumber rightLocal) = true →
      frame.stableLt row
        (label ⟨context.copyPosition copyNumber leftLocal,
          context.copyPosition_lt_length hCopy hLeft⟩)
        (label ⟨context.copyPosition copyNumber rightLocal,
          context.copyPosition_lt_length hCopy hRight⟩)
  preserves_between_copies : ∀ {row leftCopy rightCopy leftLocal rightLocal},
    (hCopies : leftCopy < rightCopy) →
    (hRightCopy : rightCopy ≤ expansionIndex) →
    (hLeft : leftLocal < context.blockLength) →
    (hRight : rightLocal < context.blockLength) →
    isAncestor (array.expand expansionIndex).raw row
        (context.copyPosition leftCopy leftLocal)
        (context.copyPosition rightCopy rightLocal) = true →
      frame.stableLt row
        (label ⟨context.copyPosition leftCopy leftLocal,
          context.copyPosition_lt_length (Nat.le_trans (Nat.le_of_lt
            hCopies) hRightCopy) hLeft⟩)
        (label ⟨context.copyPosition rightCopy rightLocal,
          context.copyPosition_lt_length hRightCopy hRight⟩)

namespace ExpansionLabeling

/-- 四个互斥列区域覆盖全部 ancestry 对。 -/
theorem preservesAncestor {Label : Type u} {frame : StabilityFrame Label}
    {array : ValidArray} {context : ExpansionContext array}
    {expansionIndex : Nat}
    (labeling : ExpansionLabeling (frame := frame) context expansionIndex) :
    ∀ {row} {left right : Fin (array.expand expansionIndex).raw.length},
      isAncestor (array.expand expansionIndex).raw row left.1 right.1 = true →
      frame.stableLt row (labeling.label left) (labeling.label right) := by
  intro row left right hAncestor
  have hOrder : left.1 < right.1 := isAncestor_lt hAncestor
  by_cases hRightGood : right.1 < context.parentColumn
  · exact labeling.preserves_good hRightGood hAncestor
  · have hRightNotGood : context.parentColumn ≤ right.1 := by omega
    rcases context.exists_copyPosition_of_not_good right.isLt hRightNotGood with
      ⟨rightCopy, rightLocal, hRightCopy, hRightLocal, hRightPosition⟩
    by_cases hLeftGood : left.1 < context.parentColumn
    · have hRightEq : right =
          ⟨context.copyPosition rightCopy rightLocal,
            context.copyPosition_lt_length hRightCopy hRightLocal⟩ :=
          Fin.ext hRightPosition
      rw [hRightEq] at hAncestor ⊢
      exact labeling.preserves_good_to_copy hLeftGood hRightCopy hRightLocal
        hAncestor
    · have hLeftNotGood : context.parentColumn ≤ left.1 := by omega
      rcases context.exists_copyPosition_of_not_good left.isLt hLeftNotGood with
        ⟨leftCopy, leftLocal, hLeftCopy, hLeftLocal, hLeftPosition⟩
      have hCopyOrder : leftCopy ≤ rightCopy := by
        apply Nat.le_of_not_gt
        intro hReverse
        have hReverseOrder := context.column_lt_of_inCopy_of_lt_copy
          hReverse (context.copyPosition_in_block hRightLocal)
          (context.copyPosition_in_block hLeftLocal)
        rw [← hRightPosition, ← hLeftPosition] at hReverseOrder
        omega
      rcases Nat.eq_or_lt_of_le hCopyOrder with hSameCopy | hEarlierCopy
      · subst rightCopy
        have hLeftEq : left =
            ⟨context.copyPosition leftCopy leftLocal,
              context.copyPosition_lt_length hLeftCopy hLeftLocal⟩ :=
          Fin.ext hLeftPosition
        have hRightEq : right =
            ⟨context.copyPosition leftCopy rightLocal,
              context.copyPosition_lt_length hRightCopy hRightLocal⟩ :=
          Fin.ext hRightPosition
        rw [hLeftEq, hRightEq] at hAncestor ⊢
        exact labeling.preserves_inside_copy hRightCopy hLeftLocal hRightLocal
          hAncestor
      · have hLeftLe : leftCopy ≤ expansionIndex :=
          Nat.le_trans (Nat.le_of_lt hEarlierCopy) hRightCopy
        have hLeftEq : left =
            ⟨context.copyPosition leftCopy leftLocal,
              context.copyPosition_lt_length hLeftLe hLeftLocal⟩ :=
          Fin.ext hLeftPosition
        have hRightEq : right =
            ⟨context.copyPosition rightCopy rightLocal,
              context.copyPosition_lt_length hRightCopy hRightLocal⟩ :=
          Fin.ext hRightPosition
        rw [hLeftEq, hRightEq] at hAncestor ⊢
        exact labeling.preserves_between_copies hEarlierCopy hRightCopy
          hLeftLocal hRightLocal hAncestor

/-- 分区标签证书组装为完整稳定表示。 -/
def representation {Label : Type u} {frame : StabilityFrame Label}
    {array : ValidArray} {context : ExpansionContext array}
    {expansionIndex : Nat}
    (labeling : ExpansionLabeling (frame := frame) context expansionIndex) :
    StableRepresentation frame (array.expand expansionIndex) where
  label := labeling.label
  strictlyIncreasing := labeling.strictlyIncreasing
  preservesAncestor := labeling.preservesAncestor

end ExpansionLabeling
end StabilityFrame
end BMS
end YesMetaZFC
