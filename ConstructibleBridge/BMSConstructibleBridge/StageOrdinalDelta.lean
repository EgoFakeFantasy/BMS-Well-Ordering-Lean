import BMSConstructibleBridge.StageStructure

/-!
# 阶段序数的有界成员语言公式

把有限反射与后继极限公式共同使用的“是 von Neumann 序数”谓词放在不依赖
稳定关系的低层模块中，避免公式语法与稳定语义形成循环导入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 外部有界语法中的“是 von Neumann 序数”。 -/
def finiteReflectionIsOrdinalDelta_l : Delta0Formula 1 :=
  .conj
    (.boundedAll (0 : Fin 1)
      (.boundedAll (Fin.last 1)
        (.mem (Fin.last 2) (0 : Fin 3))))
    (.boundedAll (0 : Fin 1)
      (.boundedAll (Fin.last 1)
        (.boundedAll (Fin.last 2)
          (.mem (Fin.last 3) (1 : Fin 4)))))

@[simp]
theorem finiteReflectionIsOrdinalDelta_toFO_l :
    finiteReflectionIsOrdinalDelta_l.toFO = OrdinalFormula.isOrdinal := by
  rfl

end YesMetaZFC.BMS.ConstructibleBridge
