import BMSConstructibleBridge.StableBoundary
import BMSConstructibleBridge.StageElementarityReflection

/-!
# 不依赖全层稳定边界的有限图反射

将有限反射、任意边界限制及单点反射独立出来，供全层边界与有限层边界共享。
这些定理不构造任何稳定对，也不导入全公式同时反射。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open StabilityFrame

/-- 具体稳定公式给出全体序数上的 Hunter 有限反射原理。 -/
theorem globalFiniteReflection_l
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop)) :
    FiniteReflectionPrinciple
      (constructibleStabilityFrame : StabilityFrame Ordinal.{u}) :=
  finiteReflectionPrinciple_of_ordinalElementarity
    (ordinalElementarityReflection_l data)

/-- 全体序数上的有限反射限制到任意序数边界以下。 -/
theorem boundedFiniteReflection_l
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    (sigma : Ordinal.{u}) :
    FiniteReflectionPrinciple (boundedConstructibleStabilityFrame sigma) := by
  intro lowerCount upperCount input
  let globalInput : FiniteReflectionInput
      (constructibleStabilityFrame : StabilityFrame Ordinal.{u})
      lowerCount upperCount := {
    level := input.level
    stabilityCutoff := input.stabilityCutoff
    lowerBound := input.lowerBound.1
    upperBound := input.upperBound.1
    lower := fun index => (input.lower index).1
    upper := fun index => (input.upper index).1
    lowerBound_stableLt_upperBound := input.lowerBound_stableLt_upperBound
    lower_lt_lowerBound := input.lower_lt_lowerBound
    lowerBound_le_upper := by
      intro index
      rcases input.lowerBound_le_upper index with hOrder | hEqual
      · exact Or.inl hOrder
      · exact Or.inr (congrArg Subtype.val hEqual)
    upper_lt_upperBound := input.upper_lt_upperBound
    lower_stableLt_below_cutoff := input.lower_stableLt_below_cutoff
    upper_stableLt_below_cutoff := input.upper_stableLt_below_cutoff }
  rcases (globalFiniteReflection_l data) globalInput with ⟨globalWitness⟩
  let image : Fin upperCount → BoundedOrdinal sigma := fun index =>
    ⟨globalWitness.image index,
      lt_trans (globalWitness.image_lt_lowerBound index) input.lowerBound.2⟩
  refine ⟨{
    image := image
    lower_lt_image := ?_
    image_lt_lowerBound := ?_
    preserves_lower_stableLt := ?_
    preserves_upper_lt := ?_
    preserves_upper_stableLt := ?_
    reflects_to_lowerBound := ?_ }⟩
  · intro lowerIndex upperIndex
    exact globalWitness.lower_lt_image lowerIndex upperIndex
  · intro upperIndex
    exact globalWitness.image_lt_lowerBound upperIndex
  · intro lowerIndex upperIndex level hStable
    exact globalWitness.preserves_lower_stableLt hStable
  · intro left right hOrder
    exact globalWitness.preserves_upper_lt hOrder
  · intro left right level hStable
    exact globalWitness.preserves_upper_stableLt hStable
  · intro upperIndex reflectedLevel hLevel hStable
    exact globalWitness.reflects_to_lowerBound hLevel hStable

/--
把上方单点 `alpha` 反射到 `alpha` 以下，并置于给定有限下方参数族之上。
反射图同时把 `alpha <_m beta`（`m < level`）变成图像 `<_m alpha`。
-/
theorem exists_reflectedSingleton_l
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    {count level cutoff : Nat} {alpha beta : Ordinal.{u}}
    (lower : Fin count -> Ordinal.{u})
    (hAlphaBeta : stageStableLt level alpha beta)
    (hLower : forall index, lower index < alpha)
    (hCutoff : forall index stableLevel,
      stageStableLt stableLevel (lower index) alpha ->
        stableLevel < cutoff) :
    exists image,
      (forall index, lower index < image) /\ image < alpha /\
      (forall index stableLevel,
        stageStableLt stableLevel (lower index) alpha ->
          stageStableLt stableLevel (lower index) image) /\
      forall reflectedLevel, reflectedLevel < level ->
        stageStableLt reflectedLevel image alpha := by
  let input : FiniteReflectionInput
      (constructibleStabilityFrame : StabilityFrame Ordinal.{u}) count 1 := {
    level := level
    stabilityCutoff := cutoff
    lowerBound := alpha
    upperBound := beta
    lower := lower
    upper := fun _ => alpha
    lowerBound_stableLt_upperBound := hAlphaBeta
    lower_lt_lowerBound := hLower
    lowerBound_le_upper := by intro _; exact Or.inr rfl
    upper_lt_upperBound := by intro _; exact hAlphaBeta.2.1
    lower_stableLt_below_cutoff := by
      intro lowerIndex _ stableLevel hStable
      exact hCutoff lowerIndex stableLevel hStable
    upper_stableLt_below_cutoff := by
      intro left right stableLevel hStable
      exact (lt_irrefl alpha hStable.2.1).elim }
  let witness := Classical.choice ((globalFiniteReflection_l data) input)
  let image := witness.image (0 : Fin 1)
  refine ⟨image, ?_, witness.image_lt_lowerBound (0 : Fin 1), ?_, ?_⟩
  · intro index
    exact witness.lower_lt_image index (0 : Fin 1)
  · intro index stableLevel hStable
    exact witness.preserves_lower_stableLt
      (lowerIndex := index) (upperIndex := (0 : Fin 1)) hStable
  · intro reflectedLevel hReflected
    apply witness.reflects_to_lowerBound
      (upperIndex := (0 : Fin 1)) hReflected
    exact stageStableLt_levelMonotone (Nat.le_of_lt hReflected) hAlphaBeta

end ConstructibleBridge
end BMS
end YesMetaZFC
