import YesMetaZFC.BMS.Lemma25

/-!
# BM4 稳定标签的抽象接口

论文使用序数上的普通严格序与一族稳定关系 `<ₘ`。本文件先冻结 Stage 3/4
共用的纯关系接口；具体的可构造层级实现在后续文件给出。
-/

namespace YesMetaZFC
namespace BMS

universe u

/-- 论文稳定表示所需的标签关系。 -/
structure StabilityFrame (Label : Type u) where
  /-- 标签的严格良序。 -/
  lt : Label → Label → Prop
  /-- 第 `level` 层稳定关系。 -/
  stableLt : Nat → Label → Label → Prop
  lt_wellFounded : WellFounded lt
  stableLt_lt : ∀ {level left right}, stableLt level left right → lt left right

namespace StabilityFrame

/-- 每对标签只在有限多个层级上可能稳定；这是论文对 `σ` 以下序数的关键性质。 -/
def FiniteLevelSupport {Label : Type u} (frame : StabilityFrame Label) : Prop :=
  ∀ left right, ∃ cutoff, ∀ level,
    frame.stableLt level left right → level < cutoff

/-- 稳定关系随层级向下单调。 -/
def LevelMonotone {Label : Type u} (frame : StabilityFrame Label) : Prop :=
  ∀ {lowerLevel upperLevel left right}, lowerLevel ≤ upperLevel →
    frame.stableLt upperLevel left right →
      frame.stableLt lowerLevel left right

/-- 标签区间中没有一对标签在所有有限层级上都稳定。 -/
def NoFullyStablePair {Label : Type u} (frame : StabilityFrame Label) : Prop :=
  ∀ left right, ¬ ∀ level, frame.stableLt level left right

/--
论文中 `σ` 的极小性的抽象形式：若稳定层级向下单调，
且 `σ` 以下不存在全层稳定对，则每对标签只有有限多个真稳定层。
-/
theorem finiteLevelSupport_of_noFullyStablePair
    {Label : Type u} {frame : StabilityFrame Label}
    (hMonotone : frame.LevelMonotone)
    (hNoFullyStable : frame.NoFullyStablePair) :
    frame.FiniteLevelSupport := by
  intro left right
  apply Classical.byContradiction
  intro hNoCutoff
  have hUnbounded : ∀ cutoff, ∃ level,
      frame.stableLt level left right ∧ cutoff ≤ level := by
    intro cutoff
    apply Classical.byContradiction
    intro hNoLevel
    apply hNoCutoff
    refine ⟨cutoff, ?_⟩
    intro level hStable
    apply Nat.lt_of_not_ge
    intro hCutoff
    exact hNoLevel ⟨level, hStable, hCutoff⟩
  apply hNoFullyStable left right
  intro level
  rcases hUnbounded (level + 1) with
    ⟨upperLevel, hStable, hLevel⟩
  exact hMonotone (by omega) hStable

/-- 成对有限标签族共享一个稳定层级上界。 -/
theorem exists_stabilityCutoff_fin_pairs {Label : Type u}
    {frame : StabilityFrame Label} (hFinite : FiniteLevelSupport frame)
    {leftCount rightCount : Nat} (left : Fin leftCount → Label)
    (right : Fin rightCount → Label) :
    ∃ cutoff, ∀ leftIndex rightIndex level,
      frame.stableLt level (left leftIndex) (right rightIndex) →
        level < cutoff := by
  have oneRight : ∀ (value : Label),
      ∃ cutoff, ∀ leftIndex level,
        frame.stableLt level (left leftIndex) value → level < cutoff := by
    intro value
    induction leftCount with
    | zero =>
        exact ⟨0, fun index => Fin.elim0 index⟩
    | succ count ih =>
        rcases ih (fun index => left index.castSucc) with
          ⟨priorCutoff, hPrior⟩
        rcases hFinite (left (Fin.last count)) value with
          ⟨lastCutoff, hLast⟩
        refine ⟨max priorCutoff lastCutoff, ?_⟩
        intro index
        refine Fin.lastCases ?_ (fun priorIndex => ?_) index
        · intro level hStable
          exact Nat.lt_of_lt_of_le (hLast level hStable)
            (Nat.le_max_right _ _)
        · intro level hStable
          exact Nat.lt_of_lt_of_le (hPrior priorIndex level hStable)
            (Nat.le_max_left _ _)
  induction rightCount with
  | zero =>
      exact ⟨0, fun _ rightIndex => Fin.elim0 rightIndex⟩
  | succ count ih =>
      rcases ih (fun index => right index.castSucc) with
        ⟨priorCutoff, hPrior⟩
      rcases oneRight (right (Fin.last count)) with
        ⟨lastCutoff, hLast⟩
      refine ⟨max priorCutoff lastCutoff, ?_⟩
      intro leftIndex rightIndex
      refine Fin.lastCases ?_ (fun priorIndex => ?_) rightIndex
      · intro level hStable
        exact Nat.lt_of_lt_of_le (hLast leftIndex level hStable)
          (Nat.le_max_right _ _)
      · intro level hStable
        exact Nat.lt_of_lt_of_le (hPrior leftIndex priorIndex level hStable)
          (Nat.le_max_left _ _)

/-- Lemma 2.6 的 `X×Y` 与 `Y×Y` 关系可同时由一个有限 cutoff 覆盖。 -/
theorem exists_reflectionStabilityCutoff {Label : Type u}
    {frame : StabilityFrame Label} (hFinite : FiniteLevelSupport frame)
    {lowerCount upperCount : Nat} (lower : Fin lowerCount → Label)
    (upper : Fin upperCount → Label) :
    ∃ cutoff,
      (∀ lowerIndex upperIndex level,
        frame.stableLt level (lower lowerIndex) (upper upperIndex) →
          level < cutoff) ∧
      (∀ left right level,
        frame.stableLt level (upper left) (upper right) →
          level < cutoff) := by
  rcases exists_stabilityCutoff_fin_pairs hFinite lower upper with
    ⟨lowerCutoff, hLower⟩
  rcases exists_stabilityCutoff_fin_pairs hFinite upper upper with
    ⟨upperCutoff, hUpper⟩
  refine ⟨max lowerCutoff upperCutoff, ?_, ?_⟩
  · intro lowerIndex upperIndex level hStable
    exact Nat.lt_of_lt_of_le (hLower lowerIndex upperIndex level hStable)
      (Nat.le_max_left _ _)
  · intro left right level hStable
    exact Nat.lt_of_lt_of_le (hUpper left right level hStable)
      (Nat.le_max_right _ _)

/-- 一个有限数组的稳定表示。 -/
structure StableRepresentation {Label : Type u} (frame : StabilityFrame Label)
    (array : ValidArray) where
  label : Fin array.raw.length → Label
  strictlyIncreasing :
    ∀ {left right : Fin array.raw.length}, left < right →
      frame.lt (label left) (label right)
  preservesAncestor :
    ∀ {row : Nat} {left right : Fin array.raw.length},
      isAncestor array.raw row left.1 right.1 = true →
      frame.stableLt row (label left) (label right)

/-- 表示的所有标签都严格低于同一上界。 -/
def StableRepresentation.BoundedBy {Label : Type u}
    {frame : StabilityFrame Label} {array : ValidArray}
    (representation : StableRepresentation frame array) (bound : Label) : Prop :=
  ∀ column, frame.lt (representation.label column) bound

end StabilityFrame

end BMS
end YesMetaZFC
