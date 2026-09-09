import BMSConstructibleBridge.StageStableBetweenFormula
import BMSConstructibleBridge.StageStableToUniverseFormula
import BMSConstructibleBridge.StabilitySemantics

/-!
# 可构造稳定关系的公式数据

把二元具名层公式、ambient 真值公式、复杂度证书和精确语义装入有限反射所需
的统一数据结构。这里没有额外假设字段：全部内容都由前面已经证明的定理给出。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- `stageStableLt` 的无条件公式内部化数据。 -/
noncomputable def constructibleStabilityFormulaData_l :
    ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop) where
  stableBetweenFormula := stageStableBetweenFormula_l
  stableToUniverseFormula := fun level =>
    stageStableToUniverseFormulaAtLevel_l
      (stageStabilityLevyLevel_l level)
  stableBetween_isSigmaFinite := by
    intro reflectionLevel level
    simpa only [stageStableBetweenFormula_l, stageStableBetweenCore_l,
      stageStableBetweenFormulaAtLevel_l] using
      stageStableBetweenFormula_isSigmaFinite_reflection_l
        reflectionLevel level
  stableToUniverse_isSigmaFinite := by
    intro reflectionLevel level hLevel
    exact stageStableToUniverseFormula_isSigmaFinite_reflection_l hLevel
  satisfies_stableBetween_iff := by
    intro top hTop hOmega left right level hLeft hRight
    exact satisfies_stageStableBetweenFormula_iff_l
      hTop hOmega level hLeft hRight
  satisfies_stableToUniverse_iff := by
    intro top hTop hOmega value level hValue
    simpa only [stageStableLt] using
      (satisfies_stageStableToUniverseFormulaAtLevel_iff_l
        hTop hOmega (stageStabilityLevyLevel_l level) hValue)

end YesMetaZFC.BMS.ConstructibleBridge
