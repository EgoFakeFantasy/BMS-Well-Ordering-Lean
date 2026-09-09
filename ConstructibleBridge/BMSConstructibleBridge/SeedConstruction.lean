import BMSConstructibleBridge.NativeStableBoundary
import BMSConstructibleBridge.StageElementarityReflection
import YesMetaZFC.BMS.SeedRepresentation

/-!
# 最小全稳定边界以下的规范 seed

从边界到一个全稳定后继的关系出发，连续三次反射只含一个上方标签的有限图。
第一次得到边界下的稳定下端点，第二次把它与边界之间插入稳定上端点，第三次
再插入严格上界。这样为每个有限高度直接产生 Stage 4 所需的三个标签。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open StabilityFrame

/-- 最小边界以下的任意固定序数对只有有限多个真稳定层。 -/
theorem exists_stageStableCutoff_below_boundary_l
    {sigma alpha beta : Ordinal.{u}}
    (hSigma : IsMinimalFullyStableBoundary sigma)
    (hAlpha : alpha < sigma) :
    exists cutoff, forall level,
      stageStableLt level alpha beta -> level < cutoff := by
  apply Classical.byContradiction
  intro hNoCutoff
  have hUnbounded : forall cutoff, exists level,
      stageStableLt level alpha beta /\ cutoff <= level := by
    intro cutoff
    apply Classical.byContradiction
    intro hNoLevel
    apply hNoCutoff
    refine ⟨cutoff, ?_⟩
    intro level hStable
    apply Nat.lt_of_not_ge
    intro hCutoff
    exact hNoLevel ⟨level, hStable, hCutoff⟩
  apply hSigma.2 alpha hAlpha
  refine ⟨beta, ?_⟩
  intro level
  rcases hUnbounded (level + 1) with
    ⟨upperLevel, hStable, hLevel⟩
  exact stageStableLt_levelMonotone (by omega) hStable

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

/-- 每个有限高度在最小全稳定边界以下都有规范 seed 数据。 -/
noncomputable def seedStabilityData_l
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
    (height : Nat) :
    SeedStabilityData
      (boundedConstructibleStabilityFrame
        (leastFullyStableBoundary_l : Ordinal.{u})) height := by
  let sigma : Ordinal.{u} := leastFullyStableBoundary_l
  have hSigma : IsMinimalFullyStableBoundary sigma :=
    leastFullyStableBoundary_isMinimal_l
  let beta : Ordinal.{u} := Classical.choose hSigma.1
  have hSigmaBeta : forall level, stageStableLt level sigma beta :=
    Classical.choose_spec hSigma.1
  have hFirst := exists_reflectedSingleton_l data
    (lower := fun index : Fin 0 => Fin.elim0 index)
    (cutoff := 0)
    (hAlphaBeta := hSigmaBeta (height + 3))
    (hLower := fun index => Fin.elim0 index)
    (hCutoff := fun index _ _ => Fin.elim0 index)
  let lower : Ordinal.{u} := Classical.choose hFirst
  have hFirstSpec := Classical.choose_spec hFirst
  have hLowerSigma : lower < sigma := hFirstSpec.2.1
  have hLowerStable := hFirstSpec.2.2.2
  have hLowerCutoffExists :=
    exists_stageStableCutoff_below_boundary_l hSigma hLowerSigma
      (beta := sigma)
  let lowerCutoff : Nat := Classical.choose hLowerCutoffExists
  have hLowerCutoff := Classical.choose_spec hLowerCutoffExists
  have hSecond := exists_reflectedSingleton_l data
    (lower := fun _ : Fin 1 => lower)
    (hAlphaBeta := hSigmaBeta (height + 2))
    (hLower := fun _ => hLowerSigma)
    (hCutoff := fun _ => hLowerCutoff)
  let upper : Ordinal.{u} := Classical.choose hSecond
  have hSecondSpec := Classical.choose_spec hSecond
  have hLowerUpper := hSecondSpec.1
  have hUpperSigma : upper < sigma := hSecondSpec.2.1
  have hLowerPreserved := hSecondSpec.2.2.1
  have hUpperCutoffExists :=
    exists_stageStableCutoff_below_boundary_l hSigma hUpperSigma
      (beta := sigma)
  let upperCutoff : Nat := Classical.choose hUpperCutoffExists
  have hUpperCutoff := Classical.choose_spec hUpperCutoffExists
  let combinedCutoff := max lowerCutoff upperCutoff
  have hThird := exists_reflectedSingleton_l data
    (lower := fun index : Fin 2 => if index.1 = 0 then lower else upper)
    (hAlphaBeta := hSigmaBeta (height + 1))
    (hLower := by
      intro index
      fin_cases index <;> simp [hLowerSigma, hUpperSigma])
    (cutoff := combinedCutoff)
    (hCutoff := by
      intro index stableLevel hStable
      fin_cases index
      · exact Nat.lt_of_lt_of_le (hLowerCutoff stableLevel (by simpa using hStable))
          (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (hUpperCutoff stableLevel (by simpa using hStable))
          (Nat.le_max_right _ _))
  let bound : Ordinal.{u} := Classical.choose hThird
  have hThirdSpec := Classical.choose_spec hThird
  have hBelowBound := hThirdSpec.1
  have hBoundSigma : bound < sigma := hThirdSpec.2.1
  refine {
    lower := ⟨lower, hLowerSigma⟩
    upper := ⟨upper, hUpperSigma⟩
    bound := ⟨bound, hBoundSigma⟩
    lower_lt_upper := hLowerUpper (0 : Fin 1)
    upper_lt_bound := ?_
    lower_stableLt_upper := ?_ }
  · exact hBelowBound (1 : Fin 2)
  · intro row hRow
    have hLowerSigmaRow : stageStableLt row lower sigma :=
      hLowerStable row (by omega)
    exact hLowerPreserved (0 : Fin 1) row hLowerSigmaRow

end ConstructibleBridge
end BMS
end YesMetaZFC
