import BMSConstructibleBridge.TextbookLevyTraceGraph

/-!
# 有限证书的正反回归检查

只使用内核可归约的 `decide`，不引入外部原生计算证书。负例针对空元数、
前向引用、错误极性以及跨层合取；格式识别与推导有效性分别检查。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

/-- 零层的一元成员原子测试记录。 -/
private def sigmaAtom : TextbookLevyJudgment := ⟨true, 0, 1, 1⟩

/-- 相同原子也具有 Pi 极性。 -/
private def piAtom : TextbookLevyJudgment := ⟨false, 0, 1, 1⟩

/-- 原子单行记录通过检查。 -/
theorem textbookLevyTrace_accepts_atom_l :
    checkTextbookLevyTrace_l [sigmaAtom] = true := by decide

/-- 正元 Sigma 原子可以被存在量词关闭。 -/
theorem textbookLevyTrace_accepts_exists_l :
    checkTextbookLevyTrace_l [sigmaAtom, sigmaAtom.quantify] = true := by decide

/-- 否定把 Pi 原子变为 Sigma 记录。 -/
theorem textbookLevyTrace_accepts_negation_l :
    checkTextbookLevyTrace_l [piAtom, piAtom.negate] = true := by decide

/-- 前向引用不能借用稍后才出现的原子记录。 -/
theorem textbookLevyTrace_rejects_forwardReference_l :
    checkTextbookLevyTrace_l [piAtom.negate, piAtom] = false := by decide

/-- 零元数下不存在可使用的原子变量索引。 -/
theorem textbookLevyTrace_rejects_unscopedAtom_l :
    checkTextbookLevyTrace_l [⟨true, 0, 0, 1⟩] = false := by decide

/-- 原始分类系统不允许直接对 Pi 记录使用无界存在规则。 -/
theorem textbookLevyTrace_rejects_piExists_l :
    checkTextbookLevyTrace_l [piAtom, piAtom.quantify] = false := by decide

/-- 两个层级不一致的记录不能直接合取。 -/
theorem textbookLevyTrace_rejects_mixedLevelConjunction_l :
    checkTextbookLevyTrace_l
      [sigmaAtom, ⟨true, 1, 1, 5⟩, sigmaAtom.conjoin ⟨true, 1, 1, 5⟩] = false :=
    by decide

end YesMetaZFC.BMS.ConstructibleBridge
