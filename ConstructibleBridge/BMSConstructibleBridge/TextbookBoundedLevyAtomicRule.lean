import BMSConstructibleBridge.TextbookBoundedLevyTraceGraph
import BMSConstructibleBridge.TextbookDelta0ClassifierFormula

/-!
# 真正有界 Lévy 分类器的 `Delta0` 基底规则

基底分支忽略当前痕迹、位置、极性和层级，只把公开的元数与公式码交给
三元 `Delta0` 分类器。整个更高层分类器稍后统一相对化，因此此处仍保持
普通纯成员公式接口。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 七个局部字段上的 `Delta0` 基底分支。 -/
def textbookBoundedLevyAtomicRuleFormula_l : FOFormula 7 :=
  FOFormula.rename ![0, 5, 6] textbookDelta0ClassifierFormula_l

/-- 基底分支精确表示当前码具有真正的 `Delta0` 证书。 -/
theorem satisfies_textbookBoundedLevyAtomicRuleFormula_iff_l
    (graph position : ZFSet.{u})
    (entry : TextbookBoundedLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyAtomicRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), graph, position,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      TextbookIsDelta0Code_l entry.arity entry.code := by
  simp only [textbookBoundedLevyAtomicRuleFormula_l,
    FOFormula.satisfies_rename]
  have hAssignment :
      (fun index : Fin 3 =>
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), graph, position,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code]
          (![0, 5, 6] index)) =
        ![Ordinal.omega0.toZFSet, natCode entry.arity,
          natCode entry.code] := by
    funext index
    fin_cases index <;> rfl
  rw [hAssignment]
  exact satisfies_textbookDelta0ClassifierFormula_iff_l
    (⟨entry.arity, entry.code⟩ : TextbookDelta0Judgment)

end YesMetaZFC.BMS.ConstructibleBridge
