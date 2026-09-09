import BMSConstructibleBridge.TextbookAmbientTruthClassifierComplexity

/-!
# 环境真值逐行规则的复杂度

把低层分类器看成一个不透明参数后，四个升层叶只增加一次双侧层级；当前层的
其余规则均由固定辅助公式组成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 四个升层叶在低层分类器之上只增加一个共同层级。 -/
theorem textbookAmbientTruthLowerRule_isBiFinite_l
    {rank lowerLevel : Nat} {lowerClassifier : FOFormula 5}
    (hFixed : textbookAmbientTruthFixedRank_l ≤ rank)
    (hClassifier : ExternalBoundedIsBiFinite_l rank lowerClassifier) :
    ExternalBoundedIsBiFinite_l (rank + 1)
      (textbookAmbientTruthLowerRuleFormula_l
        lowerLevel lowerClassifier) := by
  have hLiteral (value : Nat) : ExternalBoundedIsBiFinite_l (rank + 1)
      (Delta0Formula.natLiteralDeltaAt value (4 : Fin 8)).toFO :=
    .delta0 _
  have hCall (polarity : Bool) :=
    textbookAmbientTruthFixedPolarityClassifier_isBiFinite_l
      hClassifier polarity
  have hClassification (polarity : Bool) :
      ExternalBoundedIsBiFinite_l (rank + 1)
        (textbookAmbientTruthLowerClassificationFormula_l
          lowerLevel polarity) :=
    (textbookAmbientTruthLowerClassification_isBiFinite_l
      lowerLevel polarity).mono (by omega)
  rw [textbookAmbientTruthLowerRuleFormula_l]
  exact (hLiteral 1).conj (hCall true) |>.disj <|
    ((hLiteral 1).conj
      ((hClassification false).conj (hCall false).neg)).disj <|
    (hLiteral 0).conj (hCall false) |>.disj <|
    (hLiteral 0).conj
      ((hClassification true).conj (hCall true).neg)

/-- 给定可选低层规则后，当前逐行规则继承其共同双侧上界。 -/
theorem textbookAmbientTruthLocalRuleAt_isBiFinite_l
    {rank level : Nat} {lowerRule : Option (FOFormula 8)}
    (hFixed : textbookAmbientTruthFixedRank_l ≤ rank)
    (hLower : ∀ formula, lowerRule = some formula →
      ExternalBoundedIsBiFinite_l rank formula) :
    ExternalBoundedIsBiFinite_l rank
      (textbookAmbientTruthLocalRuleFormulaAt_l level lowerRule) := by
  rw [textbookAmbientTruthLocalRuleFormulaAt_l.eq_def]
  apply (textbookAmbientTuple_isBiFinite_fixed_l.rename _).mono hFixed |>.conj
  apply (ExternalBoundedIsBiFinite_l.delta0 _).conj
  cases hOption : lowerRule with
  | none =>
      exact (textbookAmbientTruthCoreRule_isBiFinite_l level).mono hFixed
  | some formula =>
      exact ((textbookAmbientTruthCoreRule_isBiFinite_l level).mono hFixed).disj
        (hLower formula hOption)

end YesMetaZFC.BMS.ConstructibleBridge
