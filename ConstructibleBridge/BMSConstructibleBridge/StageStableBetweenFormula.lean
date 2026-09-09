import BMSConstructibleBridge.StageStableBetweenSyntax
import BMSConstructibleBridge.StageElementarity
import BMSConstructibleBridge.TextbookEStageElementarity

/-!
# 两个具名可构造层之间的稳定公式

本文件构造 Hunter 反射论证中的 `phi_1`。公开坐标是两个序数码；三个存在见证
依次是 `L_left`、`L_right` 与标准 `omega`。右层由局部 bare-stage 求值器识别，
左层在右层中由有界相对化公式识别，最后统一 textbook E 公式比较两个具名层。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

set_option maxHeartbeats 800000

/-- 第 `level` 个稳定标签使用重编号后的 Levy 等级。 -/
noncomputable def stageStableBetweenCore_l (level : Nat) : FOFormula 5 :=
  stageStableBetweenCoreAtLevel_l (stageStabilityLevyLevel_l level)

/-- 两个公开序数坐标上的具名层稳定关系公式。 -/
noncomputable def stageStableBetweenFormula_l (level : Nat) : FOFormula 2 :=
  externalExistentialClosure_l 3 (stageStableBetweenCore_l level)

/-- 五元原始赋值对应的层载体赋值。 -/
noncomputable def stageStableBetweenStageAssignment_l
    {top : Ordinal.{u}} {left right firstStage secondStage omegaValue : ZFSet.{u}}
    (hLeft : left ∈ LStageZF top) (hRight : right ∈ LStageZF top)
    (hFirst : firstStage ∈ LStageZF top)
    (hSecond : secondStage ∈ LStageZF top)
    (hOmega : omegaValue ∈ LStageZF top) :
    Tuple (StageCarrier top) 5 :=
  ![⟨left, hLeft⟩, ⟨right, hRight⟩, ⟨firstStage, hFirst⟩,
    ⟨secondStage, hSecond⟩, ⟨omegaValue, hOmega⟩]

/-- 去掉子类型证明后恢复原始五元赋值。 -/
@[simp]
theorem stageStableBetweenStageAssignment_value_l
    {top : Ordinal.{u}} {left right firstStage secondStage omegaValue : ZFSet.{u}}
    (hLeft : left ∈ LStageZF top) (hRight : right ∈ LStageZF top)
    (hFirst : firstStage ∈ LStageZF top)
    (hSecond : secondStage ∈ LStageZF top)
    (hOmega : omegaValue ∈ LStageZF top) :
    Delta0Formula.val
        (stageStableBetweenStageAssignment_l hLeft hRight hFirst hSecond hOmega) =
      ![left, right, firstStage, secondStage, omegaValue] := by
  funext position
  fin_cases position <;> rfl

/-- `phi_1` 在任意合适的外层中精确表达 `stageStableLt`。 -/
theorem satisfies_stageStableBetweenFormula_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmegaTop : Ordinal.omega0 < top)
    {left right : StageCarrier top} (level : Nat)
    (hLeftOrdinal : left.1.IsOrdinal) (hRightOrdinal : right.1.IsOrdinal) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (stageStableBetweenFormula_l level) ![left, right] ↔
      stageStableLt level left.1.rank right.1.rank := by
  rw [Constructible.Model.satisfies_stageCarrier_iff_satisfiesIn]
  rw [stageStableBetweenFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 3,
      (∀ index, witnesses index ∈ LStageZF top) ∧
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (stageStableBetweenCore_l level)
        (Fin.append ![left.1, right.1] witnesses)) ↔ _
  constructor
  · rintro ⟨witnesses, hWitnesses, hCore⟩
    let firstStage := witnesses (0 : Fin 3)
    let secondStage := witnesses (1 : Fin 3)
    let omegaValue := witnesses (2 : Fin 3)
    have hAssignment :
        Fin.append ![left.1, right.1] witnesses =
          ![left.1, right.1, firstStage, secondStage, omegaValue] := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignment] at hCore
    have hFirstTop : firstStage ∈ LStageZF top := hWitnesses 0
    have hSecondTop : secondStage ∈ LStageZF top := hWitnesses 1
    have hOmegaValueTop : omegaValue ∈ LStageZF top := hWitnesses 2
    have hFullAssignment : ∀ position : Fin 5,
        ![left.1, right.1, firstStage, secondStage, omegaValue] position ∈
          LStageZF top := by
      intro position
      fin_cases position
      · exact left.2
      · exact right.2
      · exact hFirstTop
      · exact hSecondTop
      · exact hOmegaValueTop
    simp only [stageStableBetweenCore_l, Model.SatisfiesIn] at hCore
    rcases hCore with
      ⟨hOmegaFormula, hOmegaLeft, hLeftRight, hLeftLimit, hRightLimit,
        hFirstSecond, hSecondLocal, hFirstLocal, hAgreement⟩
    have hOmegaValue : omegaValue = Ordinal.omega0.toZFSet :=
      (Constructible.Model.satisfiesIn_omegaSetAt_iff
        hTop hOmegaTop (4 : Fin 5)
        ![left.1, right.1, firstStage, secondStage, omegaValue]
        hFullAssignment).mp hOmegaFormula
    rw [hOmegaValue] at hOmegaLeft
    rw [hOmegaValue] at hLeftLimit
    rw [hOmegaValue] at hRightLimit
    rw [hOmegaValue] at hSecondLocal
    rw [hOmegaValue] at hFirstLocal
    rw [hOmegaValue] at hAgreement
    rw [hOmegaValue] at hFirstSecond
    have hFullAssignmentStandard : ∀ position : Fin 5,
        ![left.1, right.1, firstStage, secondStage,
          Ordinal.omega0.toZFSet] position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact left.2
      · exact right.2
      · exact hFirstTop
      · exact hSecondTop
      · exact omega_toZFSet_mem_stage_l hOmegaTop
    change Ordinal.omega0.toZFSet ∈ left.1 at hOmegaLeft
    have hOmegaLeftRank : Ordinal.omega0 < left.1.rank := by
      have hCodes := Ordinal.toZFSet_mem_toZFSet_iff
        (a := Ordinal.omega0) (b := left.1.rank)
      apply hCodes.mp
      simpa only [hLeftOrdinal.toZFSet_rank_eq] using hOmegaLeft
    have hLeftRightRank : left.1.rank < right.1.rank :=
      (stageOrdinal_mem_iff_rank_lt_l left right
        hLeftOrdinal hRightOrdinal).mp hLeftRight
    have hLeftLimitRank : Order.IsSuccLimit left.1.rank := by
      apply (satisfiesIn_stageIsSuccLimitDeltaAt_iff_rank_raw_l
        (0 : Fin 5)
        ![left.1, right.1, firstStage, secondStage,
          Ordinal.omega0.toZFSet] hFullAssignmentStandard hLeftOrdinal).mp
      exact hLeftLimit
    have hRightLimitRank : Order.IsSuccLimit right.1.rank := by
      apply (satisfiesIn_stageIsSuccLimitDeltaAt_iff_rank_raw_l
        (1 : Fin 5)
        ![left.1, right.1, firstStage, secondStage,
          Ordinal.omega0.toZFSet] hFullAssignmentStandard hRightOrdinal).mp
      exact hRightLimit
    let secondCarrier : StageCarrier top := ⟨secondStage, hSecondTop⟩
    have hSecondLocalRaw :
        Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          localLStagePairFormula_l ![right.1, secondStage] := by
      rw [Model.satisfiesIn_rename] at hSecondLocal
      have hRename :
          (fun position =>
            ![left.1, right.1, firstStage, secondStage,
              Ordinal.omega0.toZFSet] (![1, 3] position)) =
            ![right.1, secondStage] := by
        funext position
        fin_cases position <;> rfl
      rw [hRename] at hSecondLocal
      exact hSecondLocal
    have hSecondValue : secondStage = LStageZF right.1.rank := by
      apply (satisfiesIn_localLStagePairFormula_iff_l
        hTop hOmegaTop (stageOrdinal_rank_lt_l right hRightOrdinal)
        secondCarrier).mp
      simpa only [hRightOrdinal.toZFSet_rank_eq] using hSecondLocalRaw
    have hFirstInSecond : firstStage ∈ LStageZF right.1.rank := by
      change firstStage ∈ secondStage at hFirstSecond
      simpa only [hSecondValue] using hFirstSecond
    let firstCarrier : StageCarrier right.1.rank :=
      ⟨firstStage, hFirstInSecond⟩
    have hFirstLocalRaw :
        Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          relativizedLocalLStagePairDelta_l.toFO
          ![secondStage, left.1, firstStage] := by
      rw [Model.satisfiesIn_rename] at hFirstLocal
      have hRename :
          (fun position =>
            ![left.1, right.1, firstStage, secondStage,
              Ordinal.omega0.toZFSet] (![3, 0, 2] position)) =
            ![secondStage, left.1, firstStage] := by
        funext position
        fin_cases position <;> rfl
      rw [hRename] at hFirstLocal
      exact hFirstLocal
    have hFirstValue : firstStage = LStageZF left.1.rank := by
      apply (satisfiesIn_relativizedLocalLStagePairFormula_iff_l
        (stageOrdinal_rank_lt_l right hRightOrdinal)
        hRightLimitRank (hOmegaLeftRank.trans hLeftRightRank)
        hLeftRightRank firstCarrier).mp
      have hTuple :
          tupleCons (LStageZF right.1.rank) ![left.1.rank.toZFSet,
            firstCarrier.1] =
            ![secondStage, left.1, firstStage] := by
        funext position
        fin_cases position
        · exact hSecondValue.symm
        · exact hLeftOrdinal.toZFSet_rank_eq
        · rfl
      rw [hTuple]
      exact hFirstLocalRaw
    have hAgreementRaw :
        Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          (textbookEStageLevelAgreementFormula_l
            (stageStabilityLevyLevel_l level))
          ![firstStage, secondStage] := by
      rw [Model.satisfiesIn_rename] at hAgreement
      have hRename :
          (fun position =>
            ![left.1, right.1, firstStage, secondStage,
              Ordinal.omega0.toZFSet] (![2, 3] position)) =
            ![firstStage, secondStage] := by
        funext position
        fin_cases position <;> rfl
      rw [hRename] at hAgreement
      exact hAgreement
    have hElementary :
        BoundedExternalStageSigmaElementaryAt_l
          (stageStabilityLevyLevel_l level)
          left.1.rank right.1.rank := by
      apply (satisfiesIn_textbookEStageLevelAgreementFormula_stage_iff_boundedExternal_l
        hTop hOmegaTop (stageOrdinal_rank_lt_l left hLeftOrdinal)
        (stageOrdinal_rank_lt_l right hRightOrdinal) hLeftRightRank.le
        hLeftLimitRank hRightLimitRank hOmegaLeftRank
        (hOmegaLeftRank.trans hLeftRightRank)
        (stageStabilityLevyLevel_l level)).mp
      simpa only [hFirstValue, hSecondValue] using hAgreementRaw
    exact ⟨hOmegaLeftRank, hLeftRightRank, hElementary,
      hLeftLimitRank, hRightLimitRank⟩
  · rintro ⟨hOmegaLeftRank, hLeftRightRank, hElementary,
      hLeftLimitRank, hRightLimitRank⟩
    let firstStage : ZFSet.{u} := LStageZF left.1.rank
    let secondStage : ZFSet.{u} := LStageZF right.1.rank
    let omegaValue : ZFSet.{u} := Ordinal.omega0.toZFSet
    have hLeftTop := stageOrdinal_rank_lt_l left hLeftOrdinal
    have hRightTop := stageOrdinal_rank_lt_l right hRightOrdinal
    have hFirstTop : firstStage ∈ LStageZF top := LStageZF_mem_of_lt hLeftTop
    have hSecondTop : secondStage ∈ LStageZF top := LStageZF_mem_of_lt hRightTop
    have hOmegaValueTop : omegaValue ∈ LStageZF top :=
      omega_toZFSet_mem_stage_l hOmegaTop
    refine ⟨![firstStage, secondStage, omegaValue], ?_, ?_⟩
    · intro position
      fin_cases position
      · exact hFirstTop
      · exact hSecondTop
      · exact hOmegaValueTop
    · have hAssignment :
          Fin.append ![left.1, right.1]
              ![firstStage, secondStage, omegaValue] =
            ![left.1, right.1, firstStage, secondStage, omegaValue] := by
        funext position
        fin_cases position <;> rfl
      rw [hAssignment]
      simp only [stageStableBetweenCore_l, Model.SatisfiesIn]
      have hFullAssignment : ∀ position : Fin 5,
          ![left.1, right.1, firstStage, secondStage, omegaValue] position ∈
            LStageZF top := by
        intro position
        fin_cases position
        · exact left.2
        · exact right.2
        · exact hFirstTop
        · exact hSecondTop
        · exact hOmegaValueTop
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Constructible.Model.satisfiesIn_omegaSetAt_iff
          hTop hOmegaTop (4 : Fin 5) _ hFullAssignment).mpr rfl
      · have hCodes := Ordinal.toZFSet_mem_toZFSet_iff
          (a := Ordinal.omega0) (b := left.1.rank)
        change Ordinal.omega0.toZFSet ∈ left.1
        simpa only [hLeftOrdinal.toZFSet_rank_eq] using
          hCodes.mpr hOmegaLeftRank
      · exact (stageOrdinal_mem_iff_rank_lt_l left right
          hLeftOrdinal hRightOrdinal).mpr hLeftRightRank
      · exact (satisfiesIn_stageIsSuccLimitDeltaAt_iff_rank_raw_l
          (0 : Fin 5) _ hFullAssignment hLeftOrdinal).mpr hLeftLimitRank
      · exact (satisfiesIn_stageIsSuccLimitDeltaAt_iff_rank_raw_l
          (1 : Fin 5) _ hFullAssignment hRightOrdinal).mpr hRightLimitRank
      · exact LStageZF_mem_of_lt hLeftRightRank
      · refine (Model.satisfiesIn_rename
          (LStageZF top : Set ZFSet.{u})
          localLStagePairFormula_l ![1, 3]
          ![left.1, right.1, firstStage, secondStage, omegaValue]).mpr ?_
        have hRename :
            (fun position =>
              ![left.1, right.1, firstStage, secondStage, omegaValue]
                (![1, 3] position)) = ![right.1, secondStage] := by
          funext position
          fin_cases position <;> rfl
        rw [hRename]
        have hLocal := (satisfiesIn_localLStagePairFormula_iff_l
          hTop hOmegaTop hRightTop ⟨secondStage, hSecondTop⟩).mpr rfl
        simpa only [secondStage, hRightOrdinal.toZFSet_rank_eq] using hLocal
      · refine (Model.satisfiesIn_rename
          (LStageZF top : Set ZFSet.{u})
          relativizedLocalLStagePairDelta_l.toFO ![3, 0, 2]
          ![left.1, right.1, firstStage, secondStage, omegaValue]).mpr ?_
        have hRename :
            (fun position =>
              ![left.1, right.1, firstStage, secondStage, omegaValue]
                (![3, 0, 2] position)) =
              ![secondStage, left.1, firstStage] := by
          funext position
          fin_cases position <;> rfl
        rw [hRename]
        let firstCarrier : StageCarrier right.1.rank :=
          ⟨firstStage, by exact LStageZF_mem_of_lt hLeftRightRank⟩
        have hRelativized := (satisfiesIn_relativizedLocalLStagePairFormula_iff_l
          hRightTop hRightLimitRank (hOmegaLeftRank.trans hLeftRightRank)
          hLeftRightRank firstCarrier).mpr rfl
        have hTuple :
            tupleCons (LStageZF right.1.rank)
                ![left.1.rank.toZFSet, firstCarrier.1] =
              ![secondStage, left.1, firstStage] := by
          funext position
          fin_cases position
          · rfl
          · exact hLeftOrdinal.toZFSet_rank_eq
          · rfl
        rw [hTuple] at hRelativized
        exact hRelativized
      · refine (Model.satisfiesIn_rename
          (LStageZF top : Set ZFSet.{u})
          (textbookEStageLevelAgreementFormula_l
            (stageStabilityLevyLevel_l level)) ![2, 3]
          ![left.1, right.1, firstStage, secondStage, omegaValue]).mpr ?_
        have hRename :
            (fun position =>
              ![left.1, right.1, firstStage, secondStage, omegaValue]
                (![2, 3] position)) = ![firstStage, secondStage] := by
          funext position
          fin_cases position <;> rfl
        rw [hRename]
        have hAgreement :=
          (satisfiesIn_textbookEStageLevelAgreementFormula_stage_iff_boundedExternal_l
          hTop hOmegaTop hLeftTop hRightTop hLeftRightRank.le
          hLeftLimitRank hRightLimitRank hOmegaLeftRank
          (hOmegaLeftRank.trans hLeftRightRank)
          (stageStabilityLevyLevel_l level)).mpr hElementary
        simpa only [firstStage, secondStage] using hAgreement

end YesMetaZFC.BMS.ConstructibleBridge
