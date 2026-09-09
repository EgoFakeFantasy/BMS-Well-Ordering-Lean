import BMSConstructibleBridge.StageRelativization
import BMSConstructibleBridge.LocalStageFormula

/-!
# 外层中有界识别更低的可构造层

当 `α < β < top` 且 `L_β` 已作为一个集合参数给出时，把局部阶段公式的全部
量词限制到 `L_β`。所得三元公式是真正的 `Delta0`，并在 `L_top` 中精确断言
第三个坐标等于 `L_α`。这把稳定公式中“识别左端层”的复杂度彻底消去。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 三个坐标依次为外显界 `L_β`、序数码 `α` 与候选阶段。 -/
def relativizedLocalLStagePairDelta_l : Delta0Formula 3 :=
  stageRelativizedDelta_l localLStagePairFormula_l

/-- 内层局部阶段公式所需的二元载体赋值。 -/
noncomputable def localStageInnerAssignment_l
    {α β : Ordinal.{u}} (hαβ : α < β) (stage : StageCarrier β) :
    Tuple (StageCarrier β) 2 :=
  ![⟨α.toZFSet, ordinal_toZFSet_mem_LStageZF_of_lt hαβ⟩, stage]

/-- 二元载体赋值去掉子类型证明后恢复公开的序数码与候选阶段。 -/
theorem localStageInnerAssignment_value_l
    {α β : Ordinal.{u}} (hαβ : α < β) (stage : StageCarrier β) :
    Delta0Formula.val (localStageInnerAssignment_l hαβ stage) =
      ![α.toZFSet, stage.1] := by
  funext position
  fin_cases position <;> rfl

/--
在外层 `L_top` 中，以已命名的 `L_β` 为界识别 `L_α`，等价于候选集合确为
真实阶段。证明只组合通用层相对化和前序局部阶段正确性。
-/
theorem satisfiesIn_relativizedLocalLStagePairFormula_iff_l
    {top α β : Ordinal.{u}} (hβtop : β < top)
    (hβ : Order.IsSuccLimit β) (hω : Ordinal.omega0 < β)
    (hαβ : α < β) (stage : StageCarrier β) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        relativizedLocalLStagePairDelta_l.toFO
        (tupleCons (LStageZF β) ![α.toZFSet, stage.1]) ↔
      stage.1 = LStageZF α := by
  have hRelativized := satisfiesIn_stageRelativizedFormula_iff_l
    hβtop localLStagePairFormula_l
      (localStageInnerAssignment_l hαβ stage)
  rw [localStageInnerAssignment_value_l] at hRelativized
  exact hRelativized.trans
    (satisfiesIn_localLStagePairFormula_iff_l hβ hω hαβ stage)

/-- 三元有界阶段识别器翻译后是原生 `Delta0`。 -/
theorem translatedRelativizedLocalLStagePair_isDelta0_l :
    Logic.FirstOrder.Formula.IsDelta0 StabilityFrame.membershipLevyBound
      (translateExternalFormula relativizedLocalLStagePairDelta_l.toFO) :=
  translateExternalDelta0_isDelta0_l relativizedLocalLStagePairDelta_l

end YesMetaZFC.BMS.ConstructibleBridge
