import BMSConstructibleBridge.NativeStableBoundary
import BMSConstructibleBridge.FiniteStageReflection
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
