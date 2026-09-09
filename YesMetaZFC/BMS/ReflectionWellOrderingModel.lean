import YesMetaZFC.BMS.ExpansionReflectionInput
import YesMetaZFC.BMS.OrdinalReflectionSyntax

/-!
# 从有限反射数据组装 BM4 良序模型

本文件是 Stage 3 与 Stage 4 的精确接口。Stage 3 只需提供标签良序、稳定关系的
有限支撑与 Lemma 2.6；Stage 4 已在 `expand_bounded` 中完成全部复制块迭代。
-/

namespace YesMetaZFC
namespace BMS

universe u

namespace StabilityFrame

/-- 具体反射模型必须向 BM4 组合层提供的数据。 -/
structure ReflectionWellOrderingData where
  Label : Type u
  frame : StabilityFrame Label
  lt_transitive : ∀ {first second third},
    frame.lt first second → frame.lt second third →
      frame.lt first third
  stableLt_transitive : ∀ {level first second third},
    frame.stableLt level first second →
    frame.stableLt level second third →
    frame.stableLt level first third
  finiteLevelSupport : frame.FiniteLevelSupport
  finiteReflection : FiniteReflectionPrinciple frame
  seed_stability : ∀ height, SeedStabilityData frame height

namespace ReflectionWellOrderingData

/-- 已经建立 Lemma 2.6 的有限反射原则时，直接组装 Stage 4 数据。 -/
def ofFiniteReflection
    (Label : Type u) (frame : StabilityFrame Label)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third)
    (hFinite : frame.FiniteLevelSupport)
    (hReflection : FiniteReflectionPrinciple frame)
    (hSeed : ∀ height, SeedStabilityData frame height) :
    ReflectionWellOrderingData where
  Label := Label
  frame := frame
  lt_transitive := hLtTransitive
  stableLt_transitive := hStableTransitive
  finiteLevelSupport := hFinite
  finiteReflection := hReflection
  seed_stability := hSeed

/-- 纯成员闭句的有限 Lévy 初等反射给出 Lemma 2.6，进而组装 Stage 4 数据。 -/
def ofOrdinalElementarity
    (Label : Type u) (frame : StabilityFrame Label)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
        frame.stableLt level first third)
    (hFinite : frame.FiniteLevelSupport)
    (hElementarity : OrdinalElementarityReflectionProperty frame)
    (hSeed : ∀ height, SeedStabilityData frame height) :
    ReflectionWellOrderingData where
  Label := Label
  frame := frame
  lt_transitive := hLtTransitive
  stableLt_transitive := hStableTransitive
  finiteLevelSupport := hFinite
  finiteReflection := finiteReflectionPrinciple_of_ordinalElementarity hElementarity
  seed_stability := hSeed

/--
当具体模型以 `σ` 的极小性给出“无全层稳定对”时，
有限层支撑可由单调性自动推出，无需重复作为模型字段提供。
-/
def ofMinimalStableBoundary
    (Label : Type u) (frame : StabilityFrame Label)
    (hLtTransitive : ∀ {first second third},
      frame.lt first second → frame.lt second third →
        frame.lt first third)
    (hStableTransitive : ∀ {level first second third},
      frame.stableLt level first second →
      frame.stableLt level second third →
      frame.stableLt level first third)
    (hLevelMonotone : frame.LevelMonotone)
    (hNoFullyStable : frame.NoFullyStablePair)
    (hReflection : FiniteReflectionPrinciple frame)
    (hSeed : ∀ height, SeedStabilityData frame height) :
    ReflectionWellOrderingData :=
  ofFiniteReflection Label frame hLtTransitive hStableTransitive
    (finiteLevelSupport_of_noFullyStablePair hLevelMonotone hNoFullyStable)
    hReflection hSeed

/-- Stage 4 的反射迭代把具体反射数据组装成最终模型。 -/
def wellOrderingModel (data : ReflectionWellOrderingData) :
    WellOrderingModel where
  Label := data.Label
  frame := data.frame
  lt_transitive := data.lt_transitive
  seed_stability := data.seed_stability
  expand_bounded := ExpansionReflectionState.expand_bounded data.finiteReflection
    data.finiteLevelSupport data.lt_transitive data.stableLt_transitive

/-- 具体反射数据直接给出 BM4 一步关系的良基性。 -/
theorem bm4_step_wellFounded (data : ReflectionWellOrderingData) :
    WellFounded GeneratedStep :=
  data.wellOrderingModel.bm4_step_wellFounded

/-- 具体反射数据排除 BM4 无限下降链。 -/
theorem bm4_no_infinite_descent (data : ReflectionWellOrderingData) :
    ¬ ∃ chain : Nat → GeneratedArray,
      ∀ index, GeneratedStep (chain (index + 1)) (chain index) :=
  data.wellOrderingModel.bm4_no_infinite_descent

/-- 具体反射数据给出生成 BM4 记号的 strict well-order。 -/
theorem bm4_strictWellOrder (data : ReflectionWellOrderingData) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  data.wellOrderingModel.bm4_strictWellOrder

end ReflectionWellOrderingData
end StabilityFrame
end BMS
end YesMetaZFC
