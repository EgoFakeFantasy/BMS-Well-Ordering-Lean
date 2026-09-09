import BMSConstructibleBridge.StageStableToUniverseSyntax
import BMSConstructibleBridge.StageStableBetweenSyntax
import BMSConstructibleBridge.ExternalBoundedFormulaRank

/-!
# 稳定公式的有限复杂度预算与重编号

二元稳定公式只有固定的无界骨架；其中的等级自然数仍由有界公式表示，所以
存在一个与标签无关的共同 `Sigma` 上界。ambient 稳定公式则随所检查的 Levy
等级增长。这里在 Lean 元层固定各个巨型辅助公式已有的有限证书，再递归定义
严格递增的稳定等级。

所有选择都来自公式结构的有限秩证书，不向对象理论加入新公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 二元稳定公式中四个固定非有界子式的共同等级。 -/
private noncomputable def stageStableBetweenFixedLevel_l : Nat :=
  max
    (externalBoundedBiLevel_l
      (Constructible.Model.omegaSetAt (2 : Fin 5))) <|
  max
    (externalBoundedBiLevel_l textbookEStageLevelAgreementBody_l) <|
  max
    (externalBoundedBiLevel_l
      (Constructible.Model.omegaSetAt (4 : Fin 5)))
    (externalBoundedBiLevel_l localLStagePairFormula_l)

private theorem omegaSetTwo_isBiFinite_stability_l :
    ExternalBoundedIsBiFinite_l stageStableBetweenFixedLevel_l
      (Constructible.Model.omegaSetAt (2 : Fin 5)) := by
  apply (externalBoundedBiLevel_spec_l
    (Constructible.Model.omegaSetAt (2 : Fin 5))).mono
  unfold stageStableBetweenFixedLevel_l
  exact Nat.le_max_left _ _

private theorem agreementBody_isBiFinite_stability_l :
    ExternalBoundedIsBiFinite_l stageStableBetweenFixedLevel_l
      textbookEStageLevelAgreementBody_l := by
  apply (externalBoundedBiLevel_spec_l
    textbookEStageLevelAgreementBody_l).mono
  unfold stageStableBetweenFixedLevel_l
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

private theorem omegaSetFour_isBiFinite_stability_l :
    ExternalBoundedIsBiFinite_l stageStableBetweenFixedLevel_l
      (Constructible.Model.omegaSetAt (4 : Fin 5)) := by
  apply (externalBoundedBiLevel_spec_l
    (Constructible.Model.omegaSetAt (4 : Fin 5))).mono
  unfold stageStableBetweenFixedLevel_l
  exact (Nat.le_max_left _ _).trans <|
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

private theorem localLStagePair_isBiFinite_stability_l :
    ExternalBoundedIsBiFinite_l stageStableBetweenFixedLevel_l
      localLStagePairFormula_l := by
  apply (externalBoundedBiLevel_spec_l localLStagePairFormula_l).mono
  unfold stageStableBetweenFixedLevel_l
  exact (Nat.le_max_right _ _).trans <|
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

/-- 两个具名层的统一 E 等价公式具有与编码等级无关的固定上界。 -/
theorem textbookEStageLevelAgreementFormula_isSigmaFinite_stability_l
    (levyLevel : Nat) :
    ExternalBoundedIsSigmaFinite_l (stageStableBetweenFixedLevel_l + 2)
      (textbookEStageLevelAgreementFormula_l levyLevel) := by
  have hAll : ExternalBoundedIsBiFinite_l
      (stageStableBetweenFixedLevel_l + 2)
      (FOFormula.all (FOFormula.all textbookEStageLevelAgreementBody_l)) :=
    agreementBody_isBiFinite_stability_l.all.all
  have hCore : ExternalBoundedIsSigmaFinite_l
      (stageStableBetweenFixedLevel_l + 2)
      (textbookEStageLevelAgreementCore_l levyLevel) := by
    rw [textbookEStageLevelAgreementCore_l]
    exact (omegaSetTwo_isBiFinite_stability_l.1.mono (by omega)).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := stageStableBetweenFixedLevel_l + 2)
        (Delta0Formula.natLiteralDeltaAt 1 (3 : Fin 5))).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := stageStableBetweenFixedLevel_l + 2)
        (Delta0Formula.natLiteralDeltaAt levyLevel (4 : Fin 5))).conj hAll.1
  rw [textbookEStageLevelAgreementFormula_l]
  exact .ex (.ex (.ex hCore))

/-- 二元稳定公式的复杂度与稳定标签无关。 -/
theorem stageStableBetweenFormulaAtLevel_isSigmaFinite_stability_l
    (levyLevel : Nat) :
    ExternalBoundedIsSigmaFinite_l (stageStableBetweenFixedLevel_l + 2)
      (stageStableBetweenFormulaAtLevel_l levyLevel) := by
  have hCore : ExternalBoundedIsSigmaFinite_l
      (stageStableBetweenFixedLevel_l + 2)
      (stageStableBetweenCoreAtLevel_l levyLevel) := by
    rw [stageStableBetweenCoreAtLevel_l]
    exact (omegaSetFour_isBiFinite_stability_l.1.mono (by omega)).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := stageStableBetweenFixedLevel_l + 2)
        (Delta0Formula.mem (4 : Fin 5) (0 : Fin 5))).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := stageStableBetweenFixedLevel_l + 2)
        (Delta0Formula.mem (0 : Fin 5) (1 : Fin 5))).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := stageStableBetweenFixedLevel_l + 2)
        (stageIsSuccLimitDeltaAt_l (0 : Fin 5))).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := stageStableBetweenFixedLevel_l + 2)
        (stageIsSuccLimitDeltaAt_l (1 : Fin 5))).conj <|
      (ExternalBoundedIsSigmaFinite_l.delta0
        (level := stageStableBetweenFixedLevel_l + 2)
        (Delta0Formula.mem (2 : Fin 5) (3 : Fin 5))).conj <|
      (localLStagePair_isBiFinite_stability_l.1.rename ![(1 : Fin 5), 3]
        |>.mono (by omega)).conj <|
      ((ExternalBoundedIsSigmaFinite_l.delta0
        (level := stageStableBetweenFixedLevel_l + 2)
        relativizedLocalLStagePairDelta_l).rename ![(3 : Fin 5), 0, 2]).conj
          ((textbookEStageLevelAgreementFormula_isSigmaFinite_stability_l
            levyLevel).rename ![(2 : Fin 5), 3])
  rw [stageStableBetweenFormulaAtLevel_l]
  exact externalExistentialClosure_isSigmaFinite_l 3 _ hCore

/--
稳定标签实际使用的 Levy 等级。零级先容纳全部二元稳定公式；后继项严格超过
前项，并吸收在前项 Levy 等级上构造的 ambient 稳定公式。
-/
noncomputable def stageStabilityLevyLevel_l : Nat → Nat
  | 0 => stageStableBetweenFixedLevel_l + 2
  | level + 1 =>
      max (stageStabilityLevyLevel_l level + 1)
        (externalBoundedSigmaLevel_l
          (stageStableToUniverseFormulaAtLevel_l
            (stageStabilityLevyLevel_l level)))

/-- 稳定标签的 Levy 重编号严格逐级增长。 -/
theorem stageStabilityLevyLevel_lt_succ_l (level : Nat) :
    stageStabilityLevyLevel_l level <
      stageStabilityLevyLevel_l (level + 1) := by
  rw [stageStabilityLevyLevel_l]
  exact (Nat.lt_succ_self _).trans_le (Nat.le_max_left _ _)

/-- 稳定标签的 Levy 重编号单调。 -/
theorem stageStabilityLevyLevel_mono_l {lowerLevel upperLevel : Nat}
    (hLevels : lowerLevel ≤ upperLevel) :
    stageStabilityLevyLevel_l lowerLevel ≤
      stageStabilityLevyLevel_l upperLevel := by
  induction hLevels with
  | refl => exact Nat.le_refl _
  | @step upperLevel hLevels inductionHypothesis =>
      exact inductionHypothesis.trans
        (stageStabilityLevyLevel_lt_succ_l upperLevel).le

/-- 本级 ambient 稳定公式的复杂度被下一稳定等级吸收。 -/
theorem stageStableToUniverseFormula_isSigmaFinite_succ_l (level : Nat) :
    ExternalBoundedIsSigmaFinite_l
      (stageStabilityLevyLevel_l (level + 1))
      (stageStableToUniverseFormulaAtLevel_l
        (stageStabilityLevyLevel_l level)) := by
  apply (externalBoundedSigmaLevel_spec_l
    (stageStableToUniverseFormulaAtLevel_l
      (stageStabilityLevyLevel_l level))).mono
  rw [stageStabilityLevyLevel_l]
  exact Nat.le_max_right _ _

/-- 若 `level < reflectionLevel`，其 ambient 稳定公式落在反射等级预算内。 -/
theorem stageStableToUniverseFormula_isSigmaFinite_reflection_l
    {level reflectionLevel : Nat} (hLevel : level < reflectionLevel) :
    ExternalBoundedIsSigmaFinite_l
      (stageStabilityLevyLevel_l reflectionLevel)
      (stageStableToUniverseFormulaAtLevel_l
        (stageStabilityLevyLevel_l level)) :=
  (stageStableToUniverseFormula_isSigmaFinite_succ_l level).mono
    (stageStabilityLevyLevel_mono_l (Nat.succ_le_iff.mpr hLevel))

/-- 二元稳定公式落在每个反射标签的 Levy 等级内。 -/
theorem stageStableBetweenFormula_isSigmaFinite_reflection_l
    (reflectionLevel level : Nat) :
    ExternalBoundedIsSigmaFinite_l
      (stageStabilityLevyLevel_l reflectionLevel)
      (stageStableBetweenFormulaAtLevel_l
        (stageStabilityLevyLevel_l level)) := by
  apply (stageStableBetweenFormulaAtLevel_isSigmaFinite_stability_l
    (stageStabilityLevyLevel_l level)).mono
  change stageStabilityLevyLevel_l 0 ≤
    stageStabilityLevyLevel_l reflectionLevel
  exact stageStabilityLevyLevel_mono_l (Nat.zero_le _)

end YesMetaZFC.BMS.ConstructibleBridge
