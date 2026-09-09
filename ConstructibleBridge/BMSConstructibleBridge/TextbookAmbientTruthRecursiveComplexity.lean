import BMSConstructibleBridge.TextbookAmbientTruthTraceComplexity

/-!
# 递归环境真值分类器的线性复杂度

逐层递归时，升层叶增加一层，有限迹包装增加四层。因此局部规则与最终分类器
分别具有 `fixed + 5*level` 和 `fixed + 5*level + 4` 的保守双侧上界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

set_option maxRecDepth 2000

/-- 递归分类器与逐行规则的线性共同复杂度上界。 -/
theorem textbookAmbientTruthFormulaBundle_isBiFinite_l (level : Nat) :
    ExternalBoundedIsBiFinite_l
        (textbookAmbientTruthFixedRank_l + 5 * level)
        (textbookAmbientTruthLocalRuleFormula_l level) ∧
      ExternalBoundedIsBiFinite_l
        (textbookAmbientTruthFixedRank_l + 5 * level + 4)
        (textbookAmbientTruthClassifierFormula_l level) := by
  induction level with
  | zero =>
      have hLocal : ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
          (textbookAmbientTruthLocalRuleFormula_l 0) := by
        rw [textbookAmbientTruthLocalRuleFormula_zero_l]
        exact textbookAmbientTruthLocalRuleAt_isBiFinite_l
          (level := 0) (lowerRule := none) (Nat.le_refl _) (by simp)
      constructor
      · exact hLocal.mono (by omega)
      · rw [textbookAmbientTruthClassifierFormula_zero_l]
        exact (textbookAmbientTruthClassifierFor_isBiFinite_l
          (rank := textbookAmbientTruthFixedRank_l) (level := 0)
          (Nat.le_refl _) hLocal).mono (by omega)
  | succ lowerLevel inductionHypothesis =>
      let lowerRank := textbookAmbientTruthFixedRank_l + 5 * lowerLevel + 4
      have hFixedLower : textbookAmbientTruthFixedRank_l ≤ lowerRank := by
        dsimp [lowerRank]
        omega
      have hLowerRule : ExternalBoundedIsBiFinite_l (lowerRank + 1)
          (textbookAmbientTruthLowerRuleFormula_l lowerLevel
            (textbookAmbientTruthClassifierFormula_l lowerLevel)) :=
        textbookAmbientTruthLowerRule_isBiFinite_l hFixedLower
          inductionHypothesis.2
      have hLocal : ExternalBoundedIsBiFinite_l (lowerRank + 1)
          (textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1)) := by
        rw [textbookAmbientTruthLocalRuleFormula_succ_l]
        exact textbookAmbientTruthLocalRuleAt_isBiFinite_l (by omega)
          (by
            intro formula hFormula
            simp only [Option.some.injEq] at hFormula
            subst formula
            exact hLowerRule)
      constructor
      · exact hLocal.mono (by
          dsimp [lowerRank]
          omega)
      · rw [textbookAmbientTruthClassifierFormula_succ_l]
        exact (textbookAmbientTruthClassifierFor_isBiFinite_l
          (by omega) hLocal).mono (by
            dsimp [lowerRank]
            omega)

/-- 公开分类器的 `Sigma` 复杂度证书。 -/
theorem textbookAmbientTruthClassifierFormula_isSigmaFinite_l (level : Nat) :
    ExternalBoundedIsSigmaFinite_l
      (textbookAmbientTruthFixedRank_l + 5 * level + 4)
      (textbookAmbientTruthClassifierFormula_l level) :=
  (textbookAmbientTruthFormulaBundle_isBiFinite_l level).2.1

/-- 公开分类器的 `Pi` 复杂度证书。 -/
theorem textbookAmbientTruthClassifierFormula_isPiFinite_l (level : Nat) :
    ExternalBoundedIsPiFinite_l
      (textbookAmbientTruthFixedRank_l + 5 * level + 4)
      (textbookAmbientTruthClassifierFormula_l level) :=
  (textbookAmbientTruthFormulaBundle_isBiFinite_l level).2.2

end YesMetaZFC.BMS.ConstructibleBridge
