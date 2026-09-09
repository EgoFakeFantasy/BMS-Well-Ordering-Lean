import BMSConstructibleBridge.ExternalFullReflection

/-!
# 外部全稳定边界的存在性

本模块先在 `lean-constructible-universe` 的公式语法上完成稳定序数存在性：
`alpha <_n beta` 表示严格层增长且 `L_alpha` 到 `L_beta` 对
`Sigma_(n+1)` 公式初等。全公式同时反射层立即给出对所有 `n` 同时稳定的
一对序数；序数良基性随后选出最小下端点。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

/-- 外部公式语法上的 Hunter 稳定关系。 -/
def externalStageStableLt_l
    (level : Nat) (alpha beta : Ordinal.{u}) : Prop :=
  alpha < beta /\ ExternalStageSigmaElementaryAt_l (level + 1) alpha beta

/-- 相继的全反射层在所有 Hunter 层级上同时稳定。 -/
theorem fullReflectionOrdinal_fullyStable_l (start : Ordinal.{u}) :
    forall level,
      externalStageStableLt_l level
        (fullReflectionOrdinal_l start)
        (nextFullReflectionOrdinal_l (fullReflectionOrdinal_l start)) := by
  intro level
  exact ⟨lt_nextFullReflectionOrdinal_l _,
    externalStageSigmaElementaryAt_fullReflection_l (level + 1) start⟩

/-- 一个序数拥有对所有有限层同时稳定的严格后继。 -/
def HasExternalFullyStableSuccessor_l (alpha : Ordinal.{u}) : Prop :=
  exists beta, forall level, externalStageStableLt_l level alpha beta

/-- 全稳定下端点非空，而且可在任意给定起点之上显式构造。 -/
theorem exists_externalFullyStableSuccessorAbove_l (start : Ordinal.{u}) :
    exists alpha, start <= alpha /\ HasExternalFullyStableSuccessor_l alpha := by
  let alpha := fullReflectionOrdinal_l start
  exact ⟨alpha, le_fullReflectionOrdinal_l start,
    nextFullReflectionOrdinal_l alpha,
    fullReflectionOrdinal_fullyStable_l start⟩

/-- 拥有全稳定后继的序数组成非空集合。 -/
theorem externalFullyStableSuccessor_nonempty_l :
    Set.Nonempty
      {alpha : Ordinal.{u} | HasExternalFullyStableSuccessor_l alpha} := by
  rcases exists_externalFullyStableSuccessorAbove_l
      (0 : Ordinal.{u}) with ⟨alpha, _hAlpha, hStable⟩
  exact ⟨alpha, hStable⟩

/-- 外部公式语法中最小的全稳定下端点。 -/
noncomputable def leastExternalFullyStableBoundary_l : Ordinal.{u} :=
  Ordinal.lt_wf.min
    {alpha | HasExternalFullyStableSuccessor_l alpha}
    externalFullyStableSuccessor_nonempty_l

/-- 最小外部全稳定边界确实拥有一个全稳定严格后继。 -/
theorem leastExternalFullyStableBoundary_hasSuccessor_l :
    HasExternalFullyStableSuccessor_l
      (leastExternalFullyStableBoundary_l : Ordinal.{u}) := by
  unfold leastExternalFullyStableBoundary_l
  exact Ordinal.lt_wf.min_mem
    {alpha | HasExternalFullyStableSuccessor_l alpha}
    externalFullyStableSuccessor_nonempty_l

/-- 最小外部全稳定边界以下不存在另一个全稳定下端点。 -/
theorem not_externalFullyStable_below_leastBoundary_l
    {alpha : Ordinal.{u}}
    (hAlpha : alpha < leastExternalFullyStableBoundary_l) :
    ¬ HasExternalFullyStableSuccessor_l alpha := by
  intro hStable
  unfold leastExternalFullyStableBoundary_l at hAlpha
  exact (Ordinal.lt_wf.not_lt_min
    {gamma | HasExternalFullyStableSuccessor_l gamma} hStable) hAlpha

/-- 外部最小边界的存在性与极小性合并后的接口。 -/
theorem leastExternalFullyStableBoundary_spec_l :
    HasExternalFullyStableSuccessor_l
        (leastExternalFullyStableBoundary_l : Ordinal.{u}) /\
      forall alpha,
        alpha < leastExternalFullyStableBoundary_l ->
          ¬ HasExternalFullyStableSuccessor_l alpha :=
  ⟨leastExternalFullyStableBoundary_hasSuccessor_l,
    fun _ hAlpha => not_externalFullyStable_below_leastBoundary_l hAlpha⟩

end ConstructibleBridge
end BMS
end YesMetaZFC
