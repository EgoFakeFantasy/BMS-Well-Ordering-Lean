import BMSConstructibleBridge.StageSuccLimitFormula
import BMSConstructibleBridge.RelativizedLocalStageFormula
import BMSConstructibleBridge.TextbookEStageLevelAgreementFormula

/-!
# 两个具名可构造层之间的稳定公式语法

本模块只构造公式，不引用稳定关系的语义定义，使复杂度重编号可以位于
`StageElementarity` 的依赖下方。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/--
五元布局为 `[left,right,L_left,L_right,omega]`。除三个具名集合的存在性外，
序数、顺序、后继极限与左层识别部分全部是有界公式。
-/
def stageStableBetweenCoreAtLevel_l (levyLevel : Nat) : FOFormula 5 :=
  .conj (Constructible.Model.omegaSetAt (4 : Fin 5)) <|
  .conj (.mem (4 : Fin 5) (0 : Fin 5)) <|
  .conj (.mem (0 : Fin 5) (1 : Fin 5)) <|
  .conj (stageIsSuccLimitDeltaAt_l (0 : Fin 5)).toFO <|
  .conj (stageIsSuccLimitDeltaAt_l (1 : Fin 5)).toFO <|
  .conj (.mem (2 : Fin 5) (3 : Fin 5)) <|
  .conj (FOFormula.rename ![1, 3] localLStagePairFormula_l) <|
  .conj
    (FOFormula.rename ![3, 0, 2]
      relativizedLocalLStagePairDelta_l.toFO)
    (FOFormula.rename ![2, 3]
      (textbookEStageLevelAgreementFormula_l levyLevel))

/-- 给定 Levy 层后，两个公开序数坐标上的具名层稳定关系公式。 -/
def stageStableBetweenFormulaAtLevel_l (levyLevel : Nat) : FOFormula 2 :=
  externalExistentialClosure_l 3
    (stageStableBetweenCoreAtLevel_l levyLevel)

end YesMetaZFC.BMS.ConstructibleBridge
