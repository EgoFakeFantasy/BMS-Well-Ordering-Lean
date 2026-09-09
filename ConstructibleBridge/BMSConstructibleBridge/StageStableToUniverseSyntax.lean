import BMSConstructibleBridge.TextbookEAmbientAgreementFormula
import BMSConstructibleBridge.TextbookAmbientTruthClassifierFormula
import BMSConstructibleBridge.StageSuccLimitFormula
import BMSConstructibleBridge.RelativizedLocalStageFormula

/-!
# 具名可构造层到当前层的稳定公式语法

本模块只构造 ambient 稳定公式，不引用稳定关系的语义定义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 三元布局为 `[value,L_value,omega]`。 -/
def stageStableToUniverseCoreAtLevel_l (levyLevel : Nat) : FOFormula 3 :=
  .conj (Constructible.Model.omegaSetAt (2 : Fin 3)) <|
  .conj (.mem (2 : Fin 3) (0 : Fin 3)) <|
  .conj (stageIsSuccLimitDeltaAt_l (0 : Fin 3)).toFO <|
  .conj
    (FOFormula.rename ![0, 1] localLStagePairFormula_l)
    (FOFormula.rename ![1]
      (textbookEAmbientLevelAgreementFormulaFor_l levyLevel
        (textbookAmbientTruthClassifierFormula_l levyLevel)))

/-- 给定 Levy 层后，一个公开序数坐标上的 ambient 稳定公式。 -/
def stageStableToUniverseFormulaAtLevel_l (levyLevel : Nat) : FOFormula 1 :=
  externalExistentialClosure_l 2
    (stageStableToUniverseCoreAtLevel_l levyLevel)

end YesMetaZFC.BMS.ConstructibleBridge
