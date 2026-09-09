import YesMetaZFC.BMS.Stability

/-!
# Hunter Lemma 2.6 的有限关系图形式

原证明只向反射公式中放入给定有限 `X`、`Y` 上实际为真的原子关系。
因此用有限索引族而非集合编码规定输入，可以同时保留重复标签与见证函数的精确对应。
-/

namespace YesMetaZFC
namespace BMS

universe u

namespace StabilityFrame

/-- Lemma 2.6 一次有限反射的输入数据与边界条件。 -/
structure FiniteReflectionInput {Label : Type u} (frame : StabilityFrame Label)
    (lowerCount upperCount : Nat) where
  level : Nat
  stabilityCutoff : Nat
  lowerBound : Label
  upperBound : Label
  lower : Fin lowerCount → Label
  upper : Fin upperCount → Label
  lowerBound_stableLt_upperBound :
    frame.stableLt level lowerBound upperBound
  lower_lt_lowerBound : ∀ index, frame.lt (lower index) lowerBound
  lowerBound_le_upper : ∀ index,
    frame.lt lowerBound (upper index) ∨ lowerBound = upper index
  upper_lt_upperBound : ∀ index, frame.lt (upper index) upperBound
  lower_stableLt_below_cutoff : ∀ lowerIndex upperIndex stableLevel,
    frame.stableLt stableLevel (lower lowerIndex) (upper upperIndex) →
      stableLevel < stabilityCutoff
  upper_stableLt_below_cutoff : ∀ left right stableLevel,
    frame.stableLt stableLevel (upper left) (upper right) →
      stableLevel < stabilityCutoff

/-- Lemma 2.6 所要求的有限反射见证。 -/
structure FiniteReflectionWitness {Label : Type u}
    {frame : StabilityFrame Label} {lowerCount upperCount : Nat}
    (input : FiniteReflectionInput frame lowerCount upperCount) where
  image : Fin upperCount → Label
  lower_lt_image : ∀ lowerIndex upperIndex,
    frame.lt (input.lower lowerIndex) (image upperIndex)
  image_lt_lowerBound : ∀ upperIndex,
    frame.lt (image upperIndex) input.lowerBound
  preserves_lower_stableLt : ∀ {lowerIndex : Fin lowerCount}
      {upperIndex : Fin upperCount} {level : Nat},
    frame.stableLt level (input.lower lowerIndex) (input.upper upperIndex) →
    frame.stableLt level (input.lower lowerIndex) (image upperIndex)
  preserves_upper_lt : ∀ {left right : Fin upperCount},
    frame.lt (input.upper left) (input.upper right) →
    frame.lt (image left) (image right)
  preserves_upper_stableLt : ∀ {left right : Fin upperCount} {level : Nat},
    frame.stableLt level (input.upper left) (input.upper right) →
    frame.stableLt level (image left) (image right)
  reflects_to_lowerBound : ∀ {upperIndex : Fin upperCount}
      {reflectedLevel : Nat},
    reflectedLevel < input.level →
    frame.stableLt reflectedLevel (input.upper upperIndex) input.upperBound →
    frame.stableLt reflectedLevel (image upperIndex) input.lowerBound

/-- 一个稳定框架满足 Hunter 所需的全部有限反射实例。 -/
def FiniteReflectionPrinciple {Label : Type u}
    (frame : StabilityFrame Label) : Prop :=
  ∀ {lowerCount upperCount : Nat} (input :
      FiniteReflectionInput frame lowerCount upperCount),
    Nonempty (FiniteReflectionWitness input)

/-- 反射见证的图像是单射：这是论文中“唯一保序双射”的有限版。 -/
theorem FiniteReflectionWitness.image_injective
    {Label : Type u} {frame : StabilityFrame Label}
    {lowerCount upperCount : Nat}
    {input : FiniteReflectionInput frame lowerCount upperCount}
    (witness : FiniteReflectionWitness input)
    (hUpperLinear : ∀ {left right : Fin upperCount}, left < right →
      frame.lt (input.upper left) (input.upper right)) :
    Function.Injective witness.image := by
  have hIrrefl : ∀ label, ¬ frame.lt label label := by
    intro label hLoop
    induction frame.lt_wellFounded.apply label with
    | intro current _ ih =>
        exact ih current hLoop hLoop
  intro left right hEqual
  by_cases hSame : left = right
  · exact hSame
  · rcases Nat.lt_trichotomy left.1 right.1 with hLeft | hValueEqual | hRight
    · have hImageLt := witness.preserves_upper_lt (hUpperLinear hLeft)
      rw [hEqual] at hImageLt
      exact (hIrrefl _ hImageLt).elim
    · exact (hSame (Fin.ext hValueEqual)).elim
    · have hImageLt := witness.preserves_upper_lt (hUpperLinear hRight)
      rw [hEqual] at hImageLt
      exact (hIrrefl _ hImageLt).elim

end StabilityFrame

end BMS
end YesMetaZFC
