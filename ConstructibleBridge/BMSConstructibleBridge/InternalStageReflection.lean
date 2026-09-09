import BMSConstructibleBridge.InternalStageFormula
import BMSConstructibleBridge.ExternalFullReflection

/-!
# 内部阶段公式在反射层中的精确语义

`L` 类载体上的正确性与集合大小层上的正确性分开陈述。先在显式的满足关系
绝对性条件下传递二元阶段公式，再应用已经构造的全反射层。该结果没有宣称
单凭 `omega < theta` 就能得到阶段求值历史的局部存在性。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 在对 `L` 全初等的层中，内部阶段公式精确识别外部 `L_alpha`。 -/
theorem satisfiesIn_internalLStagePairFormula_stage_iff_l
    {θ α : Ordinal.{u}}
    (hAbsolute : SatisfactionAbsolute (LStageZF θ : Set ZFSet.{u}) L)
    (hα : α < θ) (stage : StageCarrier θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        internalLStagePairFormula_l ![α.toZFSet, stage.1] ↔
      stage.1 = LStageZF α := by
  have hAssignment : ∀ position : Fin 2,
      (![α.toZFSet, stage.1] position) ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact ordinal_toZFSet_mem_LStageZF_of_lt hα
    · exact stage.2
  rw [hAbsolute internalLStagePairFormula_l _ hAssignment]
  exact satisfiesIn_internalLStagePairFormula_L_iff_l α
    ⟨stage.1, mem_L_iff.mpr ⟨θ, stage.2⟩⟩

/-- 全反射层中的内部阶段公式具有无额外数学前提的精确语义。 -/
theorem satisfiesIn_internalLStagePairFormula_fullReflection_iff_l
    (start : Ordinal.{u}) {α : Ordinal.{u}}
    (hα : α < fullReflectionOrdinal_l start)
    (stage : StageCarrier (fullReflectionOrdinal_l start)) :
    Model.SatisfiesIn
        (LStageZF (fullReflectionOrdinal_l start) : Set ZFSet.{u})
        internalLStagePairFormula_l ![α.toZFSet, stage.1] ↔
      stage.1 = LStageZF α :=
  satisfiesIn_internalLStagePairFormula_stage_iff_l
    (fullReflectionOrdinal_satisfactionAbsolute_l start) hα stage

/-- 全初等层中，每个低于层界的序数都有内部阶段公式的实际见证。 -/
theorem exists_internalLStagePairFormula_stage_l
    {θ α : Ordinal.{u}}
    (hAbsolute : SatisfactionAbsolute (LStageZF θ : Set ZFSet.{u}) L)
    (hα : α < θ) :
    ∃ stage : StageCarrier θ,
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        internalLStagePairFormula_l ![α.toZFSet, stage.1] := by
  have hUniverse : Model.SatisfiesIn L
      (.ex internalLStagePairFormula_l) ![α.toZFSet] := by
    refine ⟨LStageZF α, (Model.stageLCarrier α).2, ?_⟩
    have hTuple : snoc ![α.toZFSet] (LStageZF α) =
        ![α.toZFSet, LStageZF α] := by
      funext position
      fin_cases position <;> rfl
    rw [hTuple]
    exact (satisfiesIn_internalLStagePairFormula_L_iff_l α
      (Model.stageLCarrier α)).mpr rfl
  have hSmall := (hAbsolute (.ex internalLStagePairFormula_l)
    ![α.toZFSet] (by
      intro position
      have hPosition : position = 0 := Fin.eq_zero position
      subst position
      exact ordinal_toZFSet_mem_LStageZF_of_lt hα)).mpr hUniverse
  rcases hSmall with ⟨stage, hStage, hFormula⟩
  refine ⟨⟨stage, hStage⟩, ?_⟩
  have hTuple : snoc ![α.toZFSet] stage = ![α.toZFSet, stage] := by
    funext position
    fin_cases position <;> rfl
  rwa [hTuple] at hFormula

/-- 层初等性把外部 `L_alpha` 本身反射为当前层内的集合。 -/
theorem lStageZF_mem_of_satisfactionAbsolute_l
    {θ α : Ordinal.{u}}
    (hAbsolute : SatisfactionAbsolute (LStageZF θ : Set ZFSet.{u}) L)
    (hα : α < θ) : LStageZF α ∈ LStageZF θ := by
  rcases exists_internalLStagePairFormula_stage_l hAbsolute hα with
    ⟨stage, hStage⟩
  have hValue := (satisfiesIn_internalLStagePairFormula_stage_iff_l
    hAbsolute hα stage).mp hStage
  rw [← hValue]
  exact stage.2

end YesMetaZFC.BMS.ConstructibleBridge
