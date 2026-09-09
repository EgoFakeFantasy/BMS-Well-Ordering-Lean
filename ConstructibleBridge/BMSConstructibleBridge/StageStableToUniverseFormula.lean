import BMSConstructibleBridge.StageStableToUniverseSyntax
import BMSConstructibleBridge.TextbookEAmbientElementarity

/-!
# 具名可构造层到当前层的稳定公式

本文件构造 Hunter 反射论证中的 ambient 原子。公开坐标是序数码；两个存在
见证依次是对应的 `L` 层和标准 `omega`。最后调用有限真值轨迹分类器，表达该
具名层到当前求值层的有限 `Sigma` 初等性。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

set_option maxHeartbeats 800000

/-- ambient 稳定公式精确表达具名层到当前层的有限初等性。 -/
theorem satisfies_stageStableToUniverseFormulaAtLevel_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmegaTop : Ordinal.omega0 < top)
    {value : StageCarrier top} (levyLevel : Nat)
    (hValueOrdinal : value.1.IsOrdinal) :
    FOFormula.Satisfies
        (fun first second : StageCarrier top => first.1 ∈ second.1)
        (stageStableToUniverseFormulaAtLevel_l levyLevel) ![value] ↔
      Ordinal.omega0 < value.1.rank ∧
        value.1.rank < top ∧
        BoundedExternalStageSigmaElementaryAt_l levyLevel value.1.rank top ∧
        Order.IsSuccLimit value.1.rank ∧ Order.IsSuccLimit top := by
  rw [Constructible.Model.satisfies_stageCarrier_iff_satisfiesIn]
  rw [stageStableToUniverseFormulaAtLevel_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 2,
      (∀ position, witnesses position ∈ LStageZF top) ∧
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (stageStableToUniverseCoreAtLevel_l levyLevel)
        (Fin.append ![value.1] witnesses)) ↔ _
  constructor
  · rintro ⟨witnesses, hWitnesses, hCore⟩
    let stageValue := witnesses (0 : Fin 2)
    let omegaValue := witnesses (1 : Fin 2)
    have hAppend : Fin.append ![value.1] witnesses =
        ![value.1, stageValue, omegaValue] := by
      funext position
      fin_cases position <;> rfl
    rw [hAppend] at hCore
    have hFull : ∀ position : Fin 3,
        ![value.1, stageValue, omegaValue] position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact value.2
      · exact hWitnesses 0
      · exact hWitnesses 1
    simp only [stageStableToUniverseCoreAtLevel_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename] at hCore
    rcases hCore with
      ⟨hOmegaFormula, hOmegaValueMem, hLimit, hLocal, hAgreement⟩
    have hOmegaValue : omegaValue = Ordinal.omega0.toZFSet :=
      (Constructible.Model.satisfiesIn_omegaSetAt_iff
        hTop hOmegaTop (2 : Fin 3)
        ![value.1, stageValue, omegaValue] hFull).mp hOmegaFormula
    have hCanonical : ![value.1, stageValue, omegaValue] =
        ![value.1, stageValue, Ordinal.omega0.toZFSet] := by
      funext position
      fin_cases position
      · rfl
      · rfl
      · exact hOmegaValue
    rw [hCanonical] at hOmegaValueMem hLimit hLocal hAgreement
    change Ordinal.omega0.toZFSet ∈ value.1 at hOmegaValueMem
    have hOmegaValueRank : Ordinal.omega0 < value.1.rank := by
      apply (Ordinal.toZFSet_mem_toZFSet_iff
        (a := Ordinal.omega0) (b := value.1.rank)).mp
      simpa only [hValueOrdinal.toZFSet_rank_eq] using hOmegaValueMem
    have hValueTop : value.1.rank < top :=
      stageOrdinal_rank_lt_l value hValueOrdinal
    have hValueLimit : Order.IsSuccLimit value.1.rank := by
      exact (satisfiesIn_stageIsSuccLimitDeltaAt_iff_rank_raw_l
        (0 : Fin 3) ![value.1, stageValue, Ordinal.omega0.toZFSet]
        (by
          intro position
          fin_cases position
          · exact value.2
          · exact hWitnesses 0
          · exact omega_toZFSet_mem_stage_l hOmegaTop)
        hValueOrdinal).mp hLimit
    have hLocalRaw : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        localLStagePairFormula_l ![value.1, stageValue] := by
      have hSelected :
          (fun position =>
            ![value.1, stageValue, Ordinal.omega0.toZFSet]
              (![(0 : Fin 3), 1] position)) =
            ![value.1, stageValue] := by
        funext position
        fin_cases position <;> rfl
      rw [hSelected] at hLocal
      exact hLocal
    have hStageValue : stageValue = LStageZF value.1.rank := by
      apply (satisfiesIn_localLStagePairFormula_iff_l
        hTop hOmegaTop hValueTop ⟨stageValue, hWitnesses 0⟩).mp
      simpa only [hValueOrdinal.toZFSet_rank_eq] using hLocalRaw
    have hAgreementRaw :
        Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          (textbookEAmbientLevelAgreementFormulaFor_l levyLevel
            (textbookAmbientTruthClassifierFormula_l levyLevel))
          ![stageValue] := by
      have hSelected :
          (fun position =>
            ![value.1, stageValue, Ordinal.omega0.toZFSet]
              (![1] position)) = ![stageValue] := by
        funext position
        fin_cases position <;> rfl
      rw [hSelected] at hAgreement
      exact hAgreement
    have hElementary :=
      (satisfiesIn_textbookEAmbientLevelAgreementFormula_iff_l
        hTop hOmegaTop hValueTop hValueLimit hOmegaValueRank levyLevel
        (hWitnesses 0) hStageValue).mp hAgreementRaw
    exact ⟨hOmegaValueRank, hValueTop, hElementary, hValueLimit, hTop⟩
  · rintro ⟨hOmegaValueRank, hValueTop, hElementary, hValueLimit, _⟩
    let stageValue : ZFSet.{u} := LStageZF value.1.rank
    let omegaValue : ZFSet.{u} := Ordinal.omega0.toZFSet
    have hStageTop : stageValue ∈ LStageZF top :=
      LStageZF_mem_of_lt hValueTop
    have hOmegaStage : omegaValue ∈ LStageZF top :=
      omega_toZFSet_mem_stage_l hOmegaTop
    refine ⟨![stageValue, omegaValue], ?_, ?_⟩
    · intro position
      fin_cases position
      · exact hStageTop
      · exact hOmegaStage
    · have hAppend : Fin.append ![value.1] ![stageValue, omegaValue] =
          ![value.1, stageValue, omegaValue] := by
        funext position
        fin_cases position <;> rfl
      rw [hAppend]
      simp only [stageStableToUniverseCoreAtLevel_l, Model.SatisfiesIn,
        Model.satisfiesIn_rename]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (Constructible.Model.satisfiesIn_omegaSetAt_iff
          hTop hOmegaTop (2 : Fin 3) _
          (by
            intro position
            fin_cases position
            · exact value.2
            · exact hStageTop
            · exact hOmegaStage)).mpr rfl
      · change Ordinal.omega0.toZFSet ∈ value.1
        apply (Ordinal.toZFSet_mem_toZFSet_iff
          (a := Ordinal.omega0) (b := value.1.rank)).mpr at hOmegaValueRank
        simpa only [hValueOrdinal.toZFSet_rank_eq] using hOmegaValueRank
      · exact (satisfiesIn_stageIsSuccLimitDeltaAt_iff_rank_raw_l
          (0 : Fin 3) ![value.1, stageValue, omegaValue]
          (by
            intro position
            fin_cases position
            · exact value.2
            · exact hStageTop
            · exact hOmegaStage)
          hValueOrdinal).mpr hValueLimit
      · have hSelected :
            (fun position => ![value.1, stageValue, omegaValue]
              (![(0 : Fin 3), 1] position)) = ![value.1, stageValue] := by
          funext position
          fin_cases position <;> rfl
        rw [hSelected]
        have hLocal := (satisfiesIn_localLStagePairFormula_iff_l
          hTop hOmegaTop hValueTop ⟨stageValue, hStageTop⟩).mpr rfl
        simpa only [stageValue, hValueOrdinal.toZFSet_rank_eq] using hLocal
      · have hSelected :
            (fun position => ![value.1, stageValue, omegaValue]
              (![1] position)) = ![stageValue] := by
          funext position
          fin_cases position <;> rfl
        rw [hSelected]
        exact (satisfiesIn_textbookEAmbientLevelAgreementFormula_iff_l
          hTop hOmegaTop hValueTop hValueLimit hOmegaValueRank levyLevel
          hStageTop rfl).mpr hElementary

end YesMetaZFC.BMS.ConstructibleBridge
