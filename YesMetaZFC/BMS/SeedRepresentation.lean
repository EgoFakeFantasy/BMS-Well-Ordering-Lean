import YesMetaZFC.BMS.WellFoundedness

/-!
# BM4 seed 的稳定表示

论文把 seed 的两列分别标为一对在所有相关行稳定的标签。本文件把这一步展开到
`Fin 2` 的全部边界情形，并同时携带严格上界，供 Stage 4 的下降系统使用。
-/

namespace YesMetaZFC
namespace BMS

universe u

namespace StabilityFrame

/-- 高度 `height` 的 seed 所需的三个标签。 -/
structure SeedStabilityData {Label : Type u} (frame : StabilityFrame Label)
    (height : Nat) where
  lower : Label
  upper : Label
  bound : Label
  lower_lt_upper : frame.lt lower upper
  upper_lt_bound : frame.lt upper bound
  lower_stableLt_upper : ∀ row, row < height →
    frame.stableLt row lower upper

namespace SeedStabilityData

/-- seed 两列的标签函数。 -/
def label {Label : Type u} {frame : StabilityFrame Label} {height : Nat}
    (data : SeedStabilityData frame height) :
    Fin (validSeed height).raw.length → Label :=
  fun column => if column.1 = 0 then data.lower else data.upper

/-- 高度为 `height` 的 seed 每列都恰有 `height` 个坐标。 -/
theorem uniformHeight_seed (height : Nat) :
    UniformHeight height (validSeed height).raw := by
  intro column hColumn
  simp [raw_validSeed, seed] at hColumn
  rcases hColumn with hColumn | hColumn
  · rw [hColumn]
    simp
  · rw [hColumn]
    simp

/-- seed 标签严格按列递增。 -/
theorem label_strictlyIncreasing {Label : Type u}
    {frame : StabilityFrame Label} {height : Nat}
    (data : SeedStabilityData frame height) :
    ∀ {left right : Fin (validSeed height).raw.length},
      left < right → frame.lt (data.label left) (data.label right) := by
  intro left right hOrder
  have hLeft : left.1 = 0 := by
    have hLeftBound := left.isLt
    have hRightBound := right.isLt
    have hLength : (validSeed height).raw.length = 2 := by
      simp [raw_validSeed, seed]
    omega
  have hRight : right.1 ≠ 0 := by omega
  simp [label, hLeft, hRight, data.lower_lt_upper]

/-- seed 的唯一可能严格 ancestor 对由给定稳定关系覆盖。 -/
theorem label_preservesAncestor {Label : Type u}
    {frame : StabilityFrame Label} {height : Nat}
    (data : SeedStabilityData frame height) :
    ∀ {row : Nat} {left right : Fin (validSeed height).raw.length},
      isAncestor (validSeed height).raw row left.1 right.1 = true →
      frame.stableLt row (data.label left) (data.label right) := by
  intro row left right hAncestor
  have hOrder := isAncestor_lt hAncestor
  have hLeft : left.1 = 0 := by
    have hLeftBound := left.isLt
    have hRightBound := right.isLt
    have hLength : (validSeed height).raw.length = 2 := by
      simp [raw_validSeed, seed]
    omega
  have hRight : right.1 ≠ 0 := by omega
  rcases ancestor_entries_lt hAncestor with
    ⟨leftValue, rightValue, hLeftEntry, _, _⟩
  have hRow : row < height :=
    row_lt_uniformHeight_of_entry?_eq_some (uniformHeight_seed height)
      hLeftEntry
  simpa [label, hLeft, hRight] using data.lower_stableLt_upper row hRow

/-- `SeedStabilityData` 产生完整稳定表示。 -/
def representation {Label : Type u} {frame : StabilityFrame Label}
    {height : Nat} (data : SeedStabilityData frame height) :
    StableRepresentation frame (validSeed height) where
  label := data.label
  strictlyIncreasing := data.label_strictlyIncreasing
  preservesAncestor := data.label_preservesAncestor

/-- seed 表示严格位于数据给出的上界以下。 -/
theorem representation_boundedBy {Label : Type u}
    {frame : StabilityFrame Label} {height : Nat}
    (data : SeedStabilityData frame height)
    (hTransitive : ∀ {first second third}, frame.lt first second →
      frame.lt second third → frame.lt first third) :
    data.representation.BoundedBy data.bound := by
  intro column
  by_cases hColumn : column.1 = 0
  · simp [representation, label, hColumn,
      hTransitive data.lower_lt_upper data.upper_lt_bound]
  · simp [representation, label, hColumn, data.upper_lt_bound]

end SeedStabilityData
end StabilityFrame
end BMS
end YesMetaZFC
