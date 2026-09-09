import BMSConstructibleBridge.ExternalFullReflection
import BMSConstructibleBridge.StageElementarity

/-!
# 可构造层的同时有限层反射

YesMetaZFC 重构后，内在类型化公式与依赖库的 `FOFormula` 不再共享变量表示。
稳定序数的规范含义现已固定为依赖库自身的外部 Tarski 语义，因此本层直接复用
已经证明的全公式同时反射定理，不再经由旧的编号自由变量反向翻译。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

/-- 为全稳定反射同时越过调用者下界和内部阶段参数界的规范起点。 -/
noncomputable def stableReflectionStart_l (start : Ordinal.{u}) : Ordinal.{u} :=
  max start (Order.succ Ordinal.omega0)

/-- 相继全反射层在每个 Hunter 稳定级别上同时满足稳定关系。 -/
theorem fullReflectionOrdinal_stageFullyStable_l (start : Ordinal.{u}) :
    ∀ level,
      stageStableLt level
        (fullReflectionOrdinal_l (stableReflectionStart_l start))
        (nextFullReflectionOrdinal_l
          (fullReflectionOrdinal_l (stableReflectionStart_l start))) := by
  intro level
  refine ⟨?_, lt_nextFullReflectionOrdinal_l _,
    boundedExternalStageSigmaElementaryAt_fullReflection_l
      (stageStabilityLevyLevel_l level)
      (stableReflectionStart_l start),
    fullReflectionOrdinal_isSuccLimit_l (stableReflectionStart_l start),
    fullReflectionOrdinal_isSuccLimit_l
      (Order.succ (fullReflectionOrdinal_l (stableReflectionStart_l start)))⟩
  exact (show Ordinal.omega0 < stableReflectionStart_l start from
      (Order.lt_succ Ordinal.omega0).trans_le
        (le_max_right start (Order.succ Ordinal.omega0))).trans_le
    (le_fullReflectionOrdinal_l (stableReflectionStart_l start))

end ConstructibleBridge
end BMS
end YesMetaZFC
