import BMSConstructibleBridge.FiniteReflectionFormula

/-!
# 从稳定层包含取得 Hunter 有限反射

本模块把固定元数的六块关系图送入 `stageStableLt` 自带的
`Sigma_(level+1)` 层初等性。目标层中的原上方有限族充当存在见证；反射回源层
后，逐坐标 rank 构成 Hunter Lemma 2.6 所需图像。全部参数都保存在内在 bound
环境中，不再使用上游已删除的任意自由变量编号。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Logic FirstOrder
open StabilityFrame
open Constructible

/-- 映射规范 bound 环境后重新读出的元组就是逐点层包含。 -/
theorem externalBoundTuple_mapEnv_externalEnvOfTuple_l
    {source target : Ordinal.{u}}
    (sourceNonempty : Nonempty (StageCarrier source))
    (targetNonempty : Nonempty (StageCarrier target))
    (hSourceTarget : source ≤ target) {arity : Nat}
    (tuple : Tuple (StageCarrier source) arity) :
    externalBoundTuple
        ((lStageLevyEmbedding sourceNonempty targetNonempty hSourceTarget).mapEnv
          (externalEnvOfTuple sourceNonempty tuple)) =
      externalStageTuple_l hSourceTarget tuple := by
  funext index
  change lStageInclusion hSourceTarget
      (externalBoundTuple (externalEnvOfTuple sourceNonempty tuple) index) =
    lStageInclusion hSourceTarget (tuple index)
  rw [externalBoundTuple_externalEnvOfTuple]

/-- 上方族为空时，Hunter 的有限图条件全部真空成立。 -/
def emptyFiniteReflectionWitness_l
    {lowerCount : Nat}
    (input : FiniteReflectionInput constructibleStabilityFrame lowerCount 0) :
    FiniteReflectionWitness input where
  image := Fin.elim0
  lower_lt_image := fun _ upperIndex => Fin.elim0 upperIndex
  image_lt_lowerBound := fun upperIndex => Fin.elim0 upperIndex
  preserves_lower_stableLt := by
    intro lowerIndex upperIndex
    exact Fin.elim0 upperIndex
  preserves_upper_lt := by
    intro left
    exact Fin.elim0 left
  preserves_upper_stableLt := by
    intro left
    exact Fin.elim0 left
  reflects_to_lowerBound := by
    intro upperIndex
    exact Fin.elim0 upperIndex

/-- `stageStableLt` 自带的层初等性统一产生全部 Hunter 有限反射实例。 -/
theorem ordinalElementarityReflection_l
    (data : ConstructibleStabilityFormulaData.{u}
      (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop)) :
    OrdinalElementarityReflectionProperty
      (constructibleStabilityFrame : StabilityFrame Ordinal.{u}) := by
  intro lowerCount upperCount input
  rcases stageStableLt_elementary
      input.lowerBound_stableLt_upperBound with
    ⟨sourceNonempty, targetNonempty, hSourceTarget, hElementary⟩
  let embedding :=
    lStageLevyEmbedding sourceNonempty targetNonempty hSourceTarget
  by_cases hUpper : 0 < upperCount
  · let lowerTuple : Tuple (StageCarrier input.lowerBound) lowerCount :=
      fun index => encodeStageOrdinal_l input.lowerBound (input.lower index)
        (input.lower_lt_lowerBound index)
    let upperTuple : Tuple (StageCarrier input.upperBound) upperCount :=
      fun index => encodeStageOrdinal_l input.upperBound (input.upper index)
        (input.upper_lt_upperBound index)
    let sourceEnv := externalEnvOfTuple sourceNonempty lowerTuple
    let externalFormula := finiteReflectionFormula_l (input := input) data hUpper
    let formula := translateExternalFormula externalFormula
    have hTargetLowerOrdinal : ∀ lowerIndex,
        ((Fin.append (externalStageTuple_l hSourceTarget lowerTuple) upperTuple)
          (finiteReflectionLowerCoordinate_l lowerIndex)).1.IsOrdinal := by
      intro lowerIndex
      rw [finiteReflectionLowerCoordinate_l, Fin.append_left]
      change
        (lStageInclusion hSourceTarget (lowerTuple lowerIndex)).1.IsOrdinal
      exact encodeStageOrdinal_isOrdinal_l input.lowerBound
        (input.lower lowerIndex) (input.lower_lt_lowerBound lowerIndex)
    have hTargetFacts : FiniteReflectionMatrixFacts_l input input.upperBound
        (Fin.append (externalStageTuple_l hSourceTarget lowerTuple) upperTuple) := by
      refine {
        image_isOrdinal := ?_
        lower_mem_image := ?_
        preserves_lower_stableLt := ?_
        preserves_upper_lt := ?_
        preserves_upper_stableLt := ?_
        reflects_to_top := ?_ }
      · intro upperIndex
        rw [finiteReflectionImageCoordinate_l, Fin.append_right]
        exact encodeStageOrdinal_isOrdinal_l input.upperBound
          (input.upper upperIndex) (input.upper_lt_upperBound upperIndex)
      · intro lowerIndex upperIndex
        rw [finiteReflectionLowerCoordinate_l, finiteReflectionImageCoordinate_l,
          Fin.append_left, Fin.append_right]
        have hLowerUpper : input.lower lowerIndex < input.upper upperIndex :=
          (input.lower_lt_lowerBound lowerIndex).trans_le
            ((input.lowerBound_le_upper upperIndex).elim
              (fun h => h.le) (fun h => h.le))
        change (input.lower lowerIndex).toZFSet ∈
          (input.upper upperIndex).toZFSet
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hLowerUpper
      · intro lowerIndex upperIndex level hStable
        simpa [finiteReflectionLowerCoordinate_l,
          finiteReflectionImageCoordinate_l, Fin.append_left, Fin.append_right,
          externalStageTuple_l, lowerTuple, upperTuple, lStageInclusion,
          encodeStageOrdinal_l, encodeStageOrdinal_rank_l] using hStable
      · intro left right hOrder
        rw [finiteReflectionImageCoordinate_l, Fin.append_right,
          finiteReflectionImageCoordinate_l, Fin.append_right]
        change (input.upper left).toZFSet ∈ (input.upper right).toZFSet
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hOrder
      · intro left right level hStable
        simpa [finiteReflectionImageCoordinate_l, Fin.append_right,
          upperTuple, encodeStageOrdinal_l, encodeStageOrdinal_rank_l] using hStable
      · intro upperIndex level hStable
        simpa [finiteReflectionImageCoordinate_l, Fin.append_right,
          upperTuple, encodeStageOrdinal_l, encodeStageOrdinal_rank_l] using hStable
    have hTargetMatrix : FOFormula.Satisfies
        (fun first second : StageCarrier input.upperBound => first.1 ∈ second.1)
        (finiteReflectionMatrix_l (input := input) data hUpper)
        (Fin.append (externalStageTuple_l hSourceTarget lowerTuple)
          upperTuple) := by
      apply (satisfies_finiteReflectionMatrix_iff_l
        (stageStableLt_right_isSuccLimit
          input.lowerBound_stableLt_upperBound)
        (stageStableLt_omega_lt_right
          input.lowerBound_stableLt_upperBound)
        data hUpper _ hTargetLowerOrdinal).mpr
      exact hTargetFacts
    refine ⟨{
      source := lStageStructure input.lowerBound sourceNonempty
      target := lStageStructure input.upperBound targetNonempty
      embedding := embedding
      boundContext := externalBoundContext lowerCount
      freeContext := []
      formula := formula
      sourceEnv := sourceEnv
      formulaLevel := stageStabilityLevyLevel_l input.level
      formula_isSigma := finiteReflectionFormula_isSigmaFinite_l data hUpper
      target_satisfies := ?_
      reflects_formula := ?_
      extract := ?_ }⟩
    · apply (satisfies_translateExternalFormula_iff
        externalFormula (embedding.mapEnv sourceEnv)).mpr
      rw [externalBoundTuple_mapEnv_externalEnvOfTuple_l]
      apply (satisfies_externalExistentialClosure_l
        (fun first second : StageCarrier input.upperBound => first.1 ∈ second.1)
        upperCount (finiteReflectionMatrix_l (input := input) data hUpper)
        (externalStageTuple_l hSourceTarget lowerTuple)).mpr
      exact ⟨upperTuple, hTargetMatrix⟩
    · intro hTarget
      apply (satisfies_translateExternalFormula_iff
        externalFormula sourceEnv).mpr
      rw [externalBoundTuple_externalEnvOfTuple]
      apply (hElementary
        (finiteReflectionFormula_external_isSigmaFinite_l data hUpper)
        lowerTuple).mpr
      have hTargetExternal :=
        (satisfies_translateExternalFormula_iff
          externalFormula (embedding.mapEnv sourceEnv)).mp hTarget
      rw [externalBoundTuple_mapEnv_externalEnvOfTuple_l] at hTargetExternal
      exact hTargetExternal
    · intro hSource
      have hSourceExternal :=
        (satisfies_translateExternalFormula_iff externalFormula sourceEnv).mp
          hSource
      rw [externalBoundTuple_externalEnvOfTuple] at hSourceExternal
      rcases (satisfies_externalExistentialClosure_l
          (fun first second : StageCarrier input.lowerBound =>
            first.1 ∈ second.1)
          upperCount (finiteReflectionMatrix_l (input := input) data hUpper)
          lowerTuple).mp hSourceExternal with
        ⟨imageTuple, hSourceMatrix⟩
      have hSourceLowerOrdinal : ∀ lowerIndex,
          ((Fin.append lowerTuple imageTuple)
            (finiteReflectionLowerCoordinate_l lowerIndex)).1.IsOrdinal := by
        intro lowerIndex
        rw [finiteReflectionLowerCoordinate_l, Fin.append_left]
        exact encodeStageOrdinal_isOrdinal_l input.lowerBound
          (input.lower lowerIndex) (input.lower_lt_lowerBound lowerIndex)
      have hSourceFacts := (satisfies_finiteReflectionMatrix_iff_l
        (stageStableLt_left_isSuccLimit
          input.lowerBound_stableLt_upperBound)
        (stageStableLt_omega_lt_left
          input.lowerBound_stableLt_upperBound)
        data hUpper _ hSourceLowerOrdinal).mp hSourceMatrix
      let image : Fin upperCount → Ordinal.{u} :=
        fun index => (imageTuple index).1.rank
      refine ⟨{
        image := image
        lower_lt_image := ?_
        image_lt_lowerBound := ?_
        preserves_lower_stableLt := ?_
        preserves_upper_lt := ?_
        preserves_upper_stableLt := ?_
        reflects_to_lowerBound := ?_ }⟩
      · intro lowerIndex upperIndex
        have hMembership := hSourceFacts.lower_mem_image lowerIndex upperIndex
        have hOrder := (stageOrdinal_mem_iff_rank_lt_l
          ((Fin.append lowerTuple imageTuple)
            (finiteReflectionLowerCoordinate_l lowerIndex))
          ((Fin.append lowerTuple imageTuple)
            (finiteReflectionImageCoordinate_l upperIndex))
          (hSourceLowerOrdinal lowerIndex)
          (hSourceFacts.image_isOrdinal upperIndex)).mp hMembership
        simpa [constructibleStabilityFrame, image,
          finiteReflectionLowerCoordinate_l,
          finiteReflectionImageCoordinate_l, Fin.append_left, Fin.append_right,
          lowerTuple, encodeStageOrdinal_l, encodeStageOrdinal_rank_l] using hOrder
      · intro upperIndex
        exact stageOrdinal_rank_lt_l (imageTuple upperIndex)
          (by simpa [finiteReflectionImageCoordinate_l, Fin.append_right] using
            hSourceFacts.image_isOrdinal upperIndex)
      · intro lowerIndex upperIndex level hStable
        have hCutoff := input.lower_stableLt_below_cutoff
          lowerIndex upperIndex level hStable
        have hPreserved := hSourceFacts.preserves_lower_stableLt
          lowerIndex upperIndex ⟨level, hCutoff⟩ hStable
        simpa [constructibleStabilityFrame, image,
          finiteReflectionLowerCoordinate_l,
          finiteReflectionImageCoordinate_l, Fin.append_left, Fin.append_right,
          lowerTuple, encodeStageOrdinal_l, encodeStageOrdinal_rank_l]
          using hPreserved
      · intro left right hOrder
        have hMembership := hSourceFacts.preserves_upper_lt left right hOrder
        have hRankOrder := (stageOrdinal_mem_iff_rank_lt_l
          (imageTuple left) (imageTuple right)
          (by simpa [finiteReflectionImageCoordinate_l, Fin.append_right] using
            hSourceFacts.image_isOrdinal left)
          (by simpa [finiteReflectionImageCoordinate_l, Fin.append_right] using
            hSourceFacts.image_isOrdinal right)).mp
          (by simpa [finiteReflectionImageCoordinate_l, Fin.append_right] using
            hMembership)
        exact hRankOrder
      · intro left right level hStable
        have hCutoff := input.upper_stableLt_below_cutoff
          left right level hStable
        have hPreserved := hSourceFacts.preserves_upper_stableLt
          left right ⟨level, hCutoff⟩ hStable
        simpa [constructibleStabilityFrame, image,
          finiteReflectionImageCoordinate_l, Fin.append_right]
          using hPreserved
      · intro upperIndex reflectedLevel hLevel hStable
        have hReflected := hSourceFacts.reflects_to_top
          upperIndex ⟨reflectedLevel, hLevel⟩ hStable
        simpa [constructibleStabilityFrame, image,
          finiteReflectionImageCoordinate_l, Fin.append_right]
          using hReflected
  · have hZero : upperCount = 0 := Nat.eq_zero_of_not_pos hUpper
    subst upperCount
    let sourceEnv : FirstOrder.Env
        (lStageStructure input.lowerBound sourceNonempty) [] [] :=
      FirstOrder.Env.empty
    refine ⟨{
      source := lStageStructure input.lowerBound sourceNonempty
      target := lStageStructure input.upperBound targetNonempty
      embedding := embedding
      boundContext := []
      freeContext := []
      formula := .truth
      sourceEnv := sourceEnv
      formulaLevel := 0
      formula_isSigma := .delta0 .truth
      target_satisfies := by simp [Formula.satisfies]
      reflects_formula := fun _ => by simp [Formula.satisfies]
      extract := fun _ => ⟨emptyFiniteReflectionWitness_l input⟩ }⟩

end ConstructibleBridge
end BMS
end YesMetaZFC
