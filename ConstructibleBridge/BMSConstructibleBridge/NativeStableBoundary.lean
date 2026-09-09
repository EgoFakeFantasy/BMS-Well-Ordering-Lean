import BMSConstructibleBridge.NativeStageReflection
import BMSConstructibleBridge.StableBoundary

/-!
# 原生最小全稳定边界

全反射层已经在 YesMetaZFC 自身的公式语法中对所有有限层初等。本模块使用
序数严格序的良基性，选出拥有全层稳定严格后继的最小序数，并把它直接包装为
`IsMinimalFullyStableBoundary`。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

/-- 原生稳定关系中拥有全层稳定严格后继的序数。 -/
def HasFullyStableSuccessor_l (alpha : Ordinal.{u}) : Prop :=
  exists beta, forall level, stageStableLt level alpha beta

/-- 原生全稳定下端点非空，且可在任意起点之上构造。 -/
theorem exists_fullyStableSuccessorAbove_l (start : Ordinal.{u}) :
    exists alpha, start <= alpha /\ HasFullyStableSuccessor_l alpha := by
  let base := stableReflectionStart_l start
  let alpha := fullReflectionOrdinal_l base
  exact ⟨alpha,
    (le_max_left start (Order.succ Ordinal.omega0)).trans
      (le_fullReflectionOrdinal_l base),
    nextFullReflectionOrdinal_l alpha,
    fullReflectionOrdinal_stageFullyStable_l start⟩

/-- 拥有原生全稳定后继的序数组成非空集合。 -/
theorem fullyStableSuccessor_nonempty_l :
    Set.Nonempty {alpha : Ordinal.{u} | HasFullyStableSuccessor_l alpha} := by
  rcases exists_fullyStableSuccessorAbove_l (0 : Ordinal.{u}) with
    ⟨alpha, _hAlpha, hStable⟩
  exact ⟨alpha, hStable⟩

/-- 最小的原生全稳定下端点。 -/
noncomputable def leastFullyStableBoundary_l : Ordinal.{u} :=
  Ordinal.lt_wf.min
    {alpha | HasFullyStableSuccessor_l alpha}
    fullyStableSuccessor_nonempty_l

/-- 最小原生全稳定边界拥有全层稳定严格后继。 -/
theorem leastFullyStableBoundary_hasSuccessor_l :
    HasFullyStableSuccessor_l (leastFullyStableBoundary_l : Ordinal.{u}) := by
  unfold leastFullyStableBoundary_l
  exact Ordinal.lt_wf.min_mem
    {alpha | HasFullyStableSuccessor_l alpha}
    fullyStableSuccessor_nonempty_l

/-- 最小原生全稳定边界以下不存在另一个全稳定下端点。 -/
theorem not_fullyStable_below_leastBoundary_l
    {alpha : Ordinal.{u}} (hAlpha : alpha < leastFullyStableBoundary_l) :
    ¬ HasFullyStableSuccessor_l alpha := by
  intro hStable
  unfold leastFullyStableBoundary_l at hAlpha
  exact (Ordinal.lt_wf.not_lt_min
    {gamma | HasFullyStableSuccessor_l gamma} hStable) hAlpha

/-- 规范选择的边界满足 Stage 3 所需的极小全稳定边界接口。 -/
theorem leastFullyStableBoundary_isMinimal_l :
    IsMinimalFullyStableBoundary
      (leastFullyStableBoundary_l : Ordinal.{u}) := by
  constructor
  · exact leastFullyStableBoundary_hasSuccessor_l
  · intro alpha hAlpha
    exact not_fullyStable_below_leastBoundary_l hAlpha

end ConstructibleBridge
end BMS
end YesMetaZFC
