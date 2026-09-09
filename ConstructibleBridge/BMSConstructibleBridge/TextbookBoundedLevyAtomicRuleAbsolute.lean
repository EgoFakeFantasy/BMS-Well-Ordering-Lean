import BMSConstructibleBridge.TextbookBoundedLevyAtomicRule
import BMSConstructibleBridge.TextbookBoundedLevyTraceBounds
import BMSConstructibleBridge.TextbookDelta0ClassifierAbsolute

/-!
# 真正有界 Lévy 基底规则的层内绝对性

基底规则只是把公开的元数与公式码交给已经完成层内规范化的三元
`Delta0` 分类器。因而这里不再重做证书解码，只证明七元赋值经重命名后
恰好化为三元分类器的规范赋值。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 基底规则在每个越过 `omega` 的后继极限层中精确识别真正的 `Delta0` 码。 -/
theorem satisfiesIn_textbookBoundedLevyAtomicRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (graph position : ZFSet.{u}) (entry : TextbookBoundedLevyJudgment)
    (_hGraph : graph ∈ LStageZF θ) (_hPosition : position ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyAtomicRuleFormula_l
        ![Ordinal.omega0.toZFSet, graph, position,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      TextbookIsDelta0Code_l entry.arity entry.code := by
  simp only [textbookBoundedLevyAtomicRuleFormula_l,
    Model.satisfiesIn_rename]
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
  exact satisfiesIn_textbookDelta0ClassifierFormula_iff_l
    hθ hω (⟨entry.arity, entry.code⟩ : TextbookDelta0Judgment)

/-- 基底规则的层内语义与全宇宙语义一致。 -/
theorem textbookBoundedLevyAtomicRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (graph position : ZFSet.{u}) (entry : TextbookBoundedLevyJudgment)
    (hGraph : graph ∈ LStageZF θ) (hPosition : position ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyAtomicRuleFormula_l
        ![Ordinal.omega0.toZFSet, graph, position,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyAtomicRuleFormula_l
        ![Ordinal.omega0.toZFSet, graph, position,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookBoundedLevyAtomicRuleFormula_iff_l
    hθ hω graph position entry hGraph hPosition).trans
      (satisfies_textbookBoundedLevyAtomicRuleFormula_iff_l
        graph position entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
