import BMSConstructibleBridge.StageStructure
import BMSConstructibleBridge.ExternalBoundedLevyHierarchy
import BMSConstructibleBridge.StageStabilityComplexity

/-!
# 可构造层稳定关系的固定元数语义接口

上游公式语法已经改为由 bound/free 排序上下文内在索引。稳定关系本身仍先在
`lean-constructible-universe` 的固定元数成员公式中给出：具名层关系是二元公式，
到当前宇宙的关系是一元公式。有限反射编译器会先在这一固定元数语法中完成全部
重命名和存在闭包，最后只翻译一次；因此不再依赖已经删除的任意自由变量编号接口。

本模块只陈述两个公式应满足的复杂度和逐层语义，不包含 Lemma 2.6、seed 或 BM4
结论字段。Stage 3 的实质数学任务正是构造这一数据。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Constructible

/-- 由序数上的候选稳定关系得到标准的良序标签框架。 -/
def ordinalStabilityFrame
    (stable : Nat → Ordinal.{u} → Ordinal.{u} → Prop)
    (hStableLt : ∀ {level alpha beta}, stable level alpha beta → alpha < beta) :
    StabilityFrame Ordinal.{u} where
  lt := (· < ·)
  stableLt := stable
  lt_wellFounded := Ordinal.lt_wf
  stableLt_lt := hStableLt

/--
稳定公式内部化的最小证明包。二元公式在任意反射层都只需低复杂度，因为两端
都是具名集合；一元 ambient 公式仅在 `level < reflectionLevel` 时进入反射图。
-/
structure ConstructibleStabilityFormulaData
    (stable : Nat → Ordinal.{u} → Ordinal.{u} → Prop) where
  stableBetweenFormula : Nat → FOFormula 2
  stableToUniverseFormula : Nat → FOFormula 1
  stableBetween_isSigmaFinite : ∀ reflectionLevel level,
    ExternalBoundedIsSigmaFinite_l (stageStabilityLevyLevel_l reflectionLevel)
      (stableBetweenFormula level)
  stableToUniverse_isSigmaFinite : ∀ reflectionLevel level,
    level < reflectionLevel →
      ExternalBoundedIsSigmaFinite_l
        (stageStabilityLevyLevel_l reflectionLevel)
        (stableToUniverseFormula level)
  satisfies_stableBetween_iff : ∀
      {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
      (hOmega : Ordinal.omega0 < top)
      {left right : StageCarrier top} (level : Nat)
      (hLeft : left.1.IsOrdinal) (hRight : right.1.IsOrdinal),
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (stableBetweenFormula level) ![left, right] ↔
      stable level left.1.rank right.1.rank
  satisfies_stableToUniverse_iff : ∀
      {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
      (hOmega : Ordinal.omega0 < top)
      {value : StageCarrier top} (level : Nat)
      (hValue : value.1.IsOrdinal),
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (stableToUniverseFormula level) ![value] ↔
      stable level value.1.rank top

end ConstructibleBridge
end BMS
end YesMetaZFC
