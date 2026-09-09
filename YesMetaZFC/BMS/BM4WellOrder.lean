import YesMetaZFC.BMS.SeedRepresentation

/-!
# BM4 良序定理的最终接口

本文件把 seed 表示与单步表示下降组装为 Stage 0 冻结的三个结论。
生成序可比性已由有限 expansion 路径和同胞 expansion 可比性在组合层内部推出；
具体序数/可构造层级模型不需再提供可比性公理。
-/

namespace YesMetaZFC
namespace BMS

universe u

namespace StabilityFrame

/-- Hunter 证明中由序数模型提供、由组合层消费的全部数据。 -/
structure WellOrderingModel where
  Label : Type u
  frame : StabilityFrame Label
  lt_transitive : ∀ {first second third},
    frame.lt first second → frame.lt second third → frame.lt first third
  seed_stability : ∀ height, SeedStabilityData frame height
  expand_bounded : ∀ {array : ValidArray} (index : Nat)
      {bound : Label} (representation : StableRepresentation frame array),
    representation.BoundedBy bound →
    array.expand index ≠ array →
      ∃ smallerBound,
        frame.lt smallerBound bound ∧
          ∃ expandedRepresentation :
              StableRepresentation frame (array.expand index),
            expandedRepresentation.BoundedBy smallerBound

namespace WellOrderingModel

/-- 最终模型给出的表示下降系统。 -/
theorem representationDescentSystem (model : WellOrderingModel) :
    RepresentationDescentSystem model.frame where
  seed_bounded := by
    intro height
    let data := model.seed_stability height
    exact ⟨data.bound, data.representation,
      data.representation_boundedBy model.lt_transitive⟩
  expand_bounded := model.expand_bounded

/-- Stage 0 接口一：BM4 的一步关系在生成数组上良基。 -/
theorem bm4_step_wellFounded (model : WellOrderingModel) :
    WellFounded GeneratedStep :=
  model.representationDescentSystem.step_wellFoundedOn_generated

/-- Stage 0 接口二：不存在无限 BM4 一步下降链。 -/
theorem bm4_no_infinite_descent (model : WellOrderingModel) :
    ¬ ∃ chain : Nat → GeneratedArray,
      ∀ index, GeneratedStep (chain (index + 1)) (chain index) := by
  simpa [GeneratedStep] using
    model.representationDescentSystem.no_infinite_step_chain

/-- Stage 0 接口三：非空有限 expansion 生成的关系是 strict well-order。 -/
theorem bm4_strictWellOrder (model : WellOrderingModel) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  model.representationDescentSystem.strictWellOrder_generated

end WellOrderingModel
end StabilityFrame
end BMS
end YesMetaZFC
