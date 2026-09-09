import BMSConstructibleBridge.TextbookLevyAtomicRuleAbsolute
import BMSConstructibleBridge.TextbookLevyNegationRuleAbsolute
import BMSConstructibleBridge.TextbookLevyConjunctionRuleAbsolute
import BMSConstructibleBridge.TextbookLevyExistentialRuleAbsolute
import BMSConstructibleBridge.TextbookLevyRaiseRuleAbsolute
import BMSConstructibleBridge.TextbookLevyLocalRuleFormula

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
theorem satisfiesIn_textbookLevyLocalRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyLocalRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1,
          natCode (textbookLevyPolarityCode_l (trace.get index).isSigma),
          natCode (trace.get index).level, natCode (trace.get index).arity,
          natCode (trace.get index).code] ↔
      textbookLevyIndexedRule_l trace.get index := by
  simp only [textbookLevyLocalRuleFormula_l,
    satisfiesIn_disj_localRule_iff,
    satisfiesIn_textbookLevyAtomicRuleFormula_iff_l hθ hω
      (textbookLevyTraceGraphZF_l trace) (natCode index.1)
      (trace.get index)
      (LStageZF_mono (le_of_lt hω)
        (textbookLevyTraceGraphZF_mem_LStageOmega_l trace))
      (natCode_mem_stage_l hω _),
    satisfiesIn_textbookLevyNegationRuleFormula_iff_l
      hθ hω trace index (trace.get index),
    satisfiesIn_textbookLevyConjunctionRuleFormula_iff_l
      hθ hω trace index (trace.get index),
    satisfiesIn_textbookLevyExistentialRuleFormula_iff_l
      hθ hω trace index (trace.get index),
    satisfiesIn_textbookLevyRaiseRuleFormula_iff_l
      hω trace index (trace.get index)]
  rfl

/-- 统一局部规则在规范痕迹参数上对后继极限层绝对。 -/
theorem textbookLevyLocalRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyLocalRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1,
          natCode (textbookLevyPolarityCode_l (trace.get index).isSigma),
          natCode (trace.get index).level, natCode (trace.get index).arity,
          natCode (trace.get index).code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookLevyLocalRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1,
          natCode (textbookLevyPolarityCode_l (trace.get index).isSigma),
          natCode (trace.get index).level, natCode (trace.get index).arity,
          natCode (trace.get index).code] :=
  (satisfiesIn_textbookLevyLocalRuleFormula_iff_l
    hθ hω trace index).trans
      (satisfies_textbookLevyLocalRuleFormula_iff_l trace index).symm

end YesMetaZFC.BMS.ConstructibleBridge
