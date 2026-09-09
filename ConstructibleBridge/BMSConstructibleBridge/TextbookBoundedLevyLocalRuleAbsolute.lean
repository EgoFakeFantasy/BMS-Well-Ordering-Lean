import BMSConstructibleBridge.TextbookBoundedLevyAtomicRuleAbsolute
import BMSConstructibleBridge.TextbookBoundedLevyNegationRuleAbsolute
import BMSConstructibleBridge.TextbookBoundedLevyConjunctionRuleAbsolute
import BMSConstructibleBridge.TextbookBoundedLevyExistentialRuleAbsolute
import BMSConstructibleBridge.TextbookBoundedLevyRaiseRuleAbsolute
import BMSConstructibleBridge.TextbookBoundedLevyLocalRuleFormula

/-!
# 五分支局部分类器在可构造层中的语义

五条规则的层内精确性在这里汇合，得到逐行痕迹验证所需的统一接口。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

private theorem satisfiesIn_disj_localRule_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.disj left right) assignment ↔
      Model.SatisfiesIn M left assignment ∨
        Model.SatisfiesIn M right assignment := by
  classical
  simp only [FOFormula.disj, Model.SatisfiesIn]
  tauto

/-- 统一局部规则公式在规范痕迹图上精确对应有限索引规则。 -/
theorem satisfiesIn_textbookBoundedLevyLocalRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyLocalRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1,
          natCode (textbookBoundedLevyPolarityCode_l (trace.get index).isSigma),
          natCode (trace.get index).level, natCode (trace.get index).arity,
          natCode (trace.get index).code] ↔
      textbookBoundedLevyIndexedRule_l trace.get index := by
  simp only [textbookBoundedLevyLocalRuleFormula_l,
    satisfiesIn_disj_localRule_iff,
    satisfiesIn_textbookBoundedLevyAtomicRuleFormula_iff_l hθ hω
      (textbookBoundedLevyTraceGraphZF_l trace) (natCode index.1)
      (trace.get index)
      (LStageZF_mono (le_of_lt hω)
        (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace))
      (natCode_mem_stage_l hω _),
    satisfiesIn_textbookBoundedLevyNegationRuleFormula_iff_l
      hθ hω trace index (trace.get index),
    satisfiesIn_textbookBoundedLevyConjunctionRuleFormula_iff_l
      hθ hω trace index (trace.get index),
    satisfiesIn_textbookBoundedLevyExistentialRuleFormula_iff_l
      hθ hω trace index (trace.get index),
    satisfiesIn_textbookBoundedLevyRaiseRuleFormula_iff_l
      hω trace index (trace.get index)]
  rfl

/-- 统一局部规则在规范痕迹参数上对后继极限层绝对。 -/
theorem textbookBoundedLevyLocalRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyLocalRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1,
          natCode (textbookBoundedLevyPolarityCode_l (trace.get index).isSigma),
          natCode (trace.get index).level, natCode (trace.get index).arity,
          natCode (trace.get index).code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyLocalRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1,
          natCode (textbookBoundedLevyPolarityCode_l (trace.get index).isSigma),
          natCode (trace.get index).level, natCode (trace.get index).arity,
          natCode (trace.get index).code] :=
  (satisfiesIn_textbookBoundedLevyLocalRuleFormula_iff_l
    hθ hω trace index).trans
      (satisfies_textbookBoundedLevyLocalRuleFormula_iff_l trace index).symm

end YesMetaZFC.BMS.ConstructibleBridge
