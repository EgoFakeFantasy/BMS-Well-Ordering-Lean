import BMSConstructibleBridge.SeedConstruction
import BMSConstructibleBridge.ConstructibleStabilityFormulaData
import YesMetaZFC.BMS.ReflectionWellOrderingModel

/-!
# 可构造层数据到 BM4 良序性的最终组装

本模块先保留“给定公式数据”的参数化装配接口，再把前序模块已经构造出的
可构造层公式数据代入，从而得到不带额外数据参数的 BM4 良序性结论。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open StabilityFrame

/-- 把具体可构造层数据组装为 Stage 4 所需的完整反射模型。 -/
noncomputable def reflectionDataOfFormulaData_l
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop)) :
    ReflectionWellOrderingData :=
  let σ : Ordinal.{u} := leastFullyStableBoundary_l
  let hσ : IsMinimalFullyStableBoundary σ :=
    leastFullyStableBoundary_isMinimal_l
  ReflectionWellOrderingData.ofFiniteReflection
    (BoundedOrdinal σ) (boundedConstructibleStabilityFrame σ)
    (fun hαβ hβγ => hαβ.trans hβγ)
    boundedConstructibleStabilityFrame_stableLt_trans
    (boundedConstructibleStabilityFrame_finiteLevelSupport hσ)
    (boundedFiniteReflection_l data σ)
    (seedStabilityData_l data)

/-- 具体 Stage 3 数据排除 BM4 的无限一步下降链。 -/
theorem bm4_no_infinite_descent_of_formulaData_l
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop)) :
    ¬ ∃ chain : Nat → GeneratedArray,
      ∀ index, GeneratedStep (chain (index + 1)) (chain index) :=
  (reflectionDataOfFormulaData_l data).bm4_no_infinite_descent

/-- 具体 Stage 3 数据给出生成 BM4 记号上的严格良序。 -/
theorem bm4_strictWellOrder_of_formulaData_l
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop)) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  (reflectionDataOfFormulaData_l data).bm4_strictWellOrder

/-- 可构造层级给出的无条件 Stage 4 反射模型。 -/
noncomputable def reflectionData_l : ReflectionWellOrderingData :=
  reflectionDataOfFormulaData_l constructibleStabilityFormulaData_l.{0}

/-- BM4 的生成数组不存在无限的一步下降链。 -/
theorem bm4_no_infinite_descent_l :
    ¬ ∃ chain : Nat → GeneratedArray,
      ∀ index, GeneratedStep (chain (index + 1)) (chain index) :=
  bm4_no_infinite_descent_of_formulaData_l
    constructibleStabilityFormulaData_l.{0}

/-- BM4 生成记号及其严格下降关系构成严格良序。 -/
theorem bm4_strictWellOrder_l :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  bm4_strictWellOrder_of_formulaData_l
    constructibleStabilityFormulaData_l.{0}

end ConstructibleBridge
end BMS
end YesMetaZFC
