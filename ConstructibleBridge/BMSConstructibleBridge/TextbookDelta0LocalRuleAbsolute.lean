import BMSConstructibleBridge.TextbookDelta0AtomicRuleAbsolute
import BMSConstructibleBridge.TextbookDelta0NegationRuleAbsolute
import BMSConstructibleBridge.TextbookDelta0ConjunctionRuleAbsolute
import BMSConstructibleBridge.TextbookDelta0BoundedExistsRuleAbsolute
import BMSConstructibleBridge.TextbookDelta0LocalRuleFormula

/-!
# `Delta0` 四分支局部分类器在可构造层中的语义

四条构造规则的层内精确性在这里汇合，形成逐行验证规范痕迹的统一接口。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

private theorem satisfiesIn_disj_delta0LocalRule_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.disj left right) assignment ↔
      Model.SatisfiesIn M left assignment ∨
        Model.SatisfiesIn M right assignment := by
  classical
  simp only [FOFormula.disj, Model.SatisfiesIn]
  tauto

/-- 统一局部规则公式在规范痕迹图上精确对应有限索引规则。 -/
theorem satisfiesIn_textbookDelta0LocalRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0LocalRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode (trace.get index).arity,
          natCode (trace.get index).code] ↔
      textbookDelta0IndexedRule_l trace.get index := by
  simp only [textbookDelta0LocalRuleFormula_l,
    satisfiesIn_disj_delta0LocalRule_iff,
    satisfiesIn_textbookDelta0AtomicRuleFormula_iff_l hθ hω
      (textbookDelta0TraceGraphZF_l trace) (natCode index.1)
      (trace.get index)
      (LStageZF_mono (le_of_lt hω)
        (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace))
      (natCode_mem_stage_l hω _),
    satisfiesIn_textbookDelta0NegationRuleFormula_iff_l
      hθ hω trace index (trace.get index),
    satisfiesIn_textbookDelta0ConjunctionRuleFormula_iff_l
      hθ hω trace index (trace.get index),
    satisfiesIn_textbookDelta0BoundedExistsRuleFormula_iff_l
      hθ hω trace index (trace.get index)]
  rfl

/-- 统一局部规则在规范参数上对后继极限层绝对。 -/
theorem textbookDelta0LocalRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0LocalRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode (trace.get index).arity,
          natCode (trace.get index).code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0LocalRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode (trace.get index).arity,
          natCode (trace.get index).code] :=
  (satisfiesIn_textbookDelta0LocalRuleFormula_iff_l
    hθ hω trace index).trans
      (satisfies_textbookDelta0LocalRuleFormula_iff_l trace index).symm

end YesMetaZFC.BMS.ConstructibleBridge
