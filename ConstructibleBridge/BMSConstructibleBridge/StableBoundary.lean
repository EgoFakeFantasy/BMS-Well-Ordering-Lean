import BMSConstructibleBridge.StageElementarity

/-!
# 最小全层稳定边界以下的具体框架

论文不在全部序数上使用有限层支撑，而是在最小全层稳定序数 `σ` 以下工作。
本模块把这个限制落实为子类型，并从 `σ` 的极小性推出每一对标签只有有限多个
稳定层。这样不会误把全体序数框架声明为有限支撑。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open StabilityFrame
open Logic FirstOrder

/-- `σ` 严格下方的序数标签。 -/
abbrev BoundedOrdinal (σ : Ordinal.{u}) := {α : Ordinal.{u} // α < σ}

/-- `σ` 是存在共同高层见证的第一个全有限层稳定序数。 -/
def IsMinimalFullyStableBoundary (σ : Ordinal.{u}) : Prop :=
  (∃ β, ∀ level, stageStableLt level σ β) ∧
    ∀ α, α < σ → ¬ ∃ β, ∀ level, stageStableLt level α β

/-- 将可构造层稳定关系限制在 `σ` 以下。 -/
def boundedConstructibleStabilityFrame (σ : Ordinal.{u}) :
    StabilityFrame (BoundedOrdinal σ) where
  lt := fun α β => α.1 < β.1
  stableLt := fun level α β => stageStableLt level α.1 β.1
  lt_wellFounded := by
    exact Ordinal.lt_wf.onFun
  stableLt_lt := stageStableLt_lt

/-- 有限层稳定关系的传递性在边界限制后保持。 -/
theorem boundedConstructibleStabilityFrame_stableLt_trans
    {σ : Ordinal.{u}} {level : Nat}
    {α β γ : BoundedOrdinal σ}
    (hαβ : (boundedConstructibleStabilityFrame σ).stableLt level α β)
    (hβγ : (boundedConstructibleStabilityFrame σ).stableLt level β γ) :
    (boundedConstructibleStabilityFrame σ).stableLt level α γ :=
  stageStableLt_trans hαβ hβγ

/-- 边界限制后的稳定层级仍向下单调。 -/
theorem boundedConstructibleStabilityFrame_levelMonotone
    {σ : Ordinal.{u}} :
    (boundedConstructibleStabilityFrame σ).LevelMonotone := by
  intro lowerLevel upperLevel α β hLevels hStable
  exact stageStableLt_levelMonotone hLevels hStable

/-- `σ` 的极小性排除其下方的全层稳定标签对。 -/
theorem boundedConstructibleStabilityFrame_noFullyStablePair
    {σ : Ordinal.{u}} (hσ : IsMinimalFullyStableBoundary σ) :
    (boundedConstructibleStabilityFrame σ).NoFullyStablePair := by
  intro α β hAll
  exact hσ.2 α.1 α.2 ⟨β.1, hAll⟩

/-- 因而 `σ` 以下每一对标签只有有限多个真稳定层。 -/
theorem boundedConstructibleStabilityFrame_finiteLevelSupport
    {σ : Ordinal.{u}} (hσ : IsMinimalFullyStableBoundary σ) :
    (boundedConstructibleStabilityFrame σ).FiniteLevelSupport :=
  finiteLevelSupport_of_noFullyStablePair
    boundedConstructibleStabilityFrame_levelMonotone
    (boundedConstructibleStabilityFrame_noFullyStablePair hσ)

end ConstructibleBridge
end BMS
end YesMetaZFC
