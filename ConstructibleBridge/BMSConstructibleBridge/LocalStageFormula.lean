import BMSConstructibleBridge.InternalStageFormula
import ConstructibleUniverse.SetTheory.ZFC.Constructible.StandardCondensation

/-!
# 后继极限层中的局部可构造阶段公式

`internalLStagePairFormula_l` 依靠全宇宙 `L` 的求值历史。本模块改用上游的
`bareStageAtFormula`，并接入已经完成的规范历史界与 Gödel 求值器绝对性证明。
结果是在每个严格高于 `omega` 的后继极限层 `L_theta` 中，都有一个真正的
二元成员语言公式精确识别 `(alpha, L_alpha)`，不再需要全初等反射假设。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 二个公开坐标与十三个局部规范参数组成的十五元赋值。 -/
def localStagePublicAssignment_l
    (index stage : ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13) :
    Tuple ZFSet.{u} 15 :=
  Fin.append ![index, stage] fixed

/-- 参数重排读取公开赋值末尾的十三元组。 -/
theorem localStagePublicAssignment_fixed_l
    (index stage : ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13) :
    (fun position => localStagePublicAssignment_l index stage fixed
      (internalStageFixedRename_l position)) = fixed := by
  funext position
  simp [localStagePublicAssignment_l, internalStageFixedRename_l, Fin.append]

/-- 阶段重排把公开布局恢复为 `(fixed13,index,stage)`。 -/
theorem localStagePublicAssignment_core_l
    (index stage : ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13) :
    (fun position => localStagePublicAssignment_l index stage fixed
      (internalStageCoreRename_l position)) =
      snoc (snoc fixed index) stage := by
  funext position
  fin_cases position <;> rfl

/-- 同时固定规范参数并断言局部 bare-stage 关系的核心公式。 -/
def localStageCoreFormula_l : FOFormula 15 :=
  .conj
    (FOFormula.rename internalStageFixedRename_l
      Constructible.Model.canonicalStageParametersFormula)
    (FOFormula.rename internalStageCoreRename_l
      Constructible.Model.bareStageAtFormula)

/-- 上游的全局历史界给出任意合适局部层中的精确 bare-stage 语义。 -/
theorem bareStageCorrectAt_of_isSuccLimit_omega_lt_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) :
    MostowskiCollapse.BareStageCondensation.BareStageCorrectAt θ :=
  MostowskiCollapse.BareStageCondensation.bareStageCorrectAt_of_evaluator_and_history_bounds
      hθ hω
      (Constructible.Godel.RudimentaryTerm.bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
        hθ hω)
      Constructible.Model.canonicalBareHistory_mem_LStageZF_add_omega

/-- 核心公式在局部层中唯一固定参数并识别真实的 `L_alpha`。 -/
theorem satisfiesIn_localStageCoreFormula_iff_l
    {θ α : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (hα : α < θ)
    (stage : StageCarrier θ) (fixed : Tuple ZFSet.{u} 13)
    (hfixed : ∀ index, fixed index ∈ LStageZF θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        localStageCoreFormula_l
        (localStagePublicAssignment_l α.toZFSet stage.1 fixed) ↔
      fixed = Constructible.Model.stageHistoryFixedParametersRaw ∧
        stage.1 = LStageZF α := by
  have hindex : α.toZFSet ∈ LStageZF θ :=
    ordinal_toZFSet_mem_LStageZF_of_lt hα
  have hcorrect := bareStageCorrectAt_of_isSuccLimit_omega_lt_l hθ hω
  simp only [localStageCoreFormula_l, Constructible.Model.SatisfiesIn]
  rw [Constructible.Model.satisfiesIn_rename,
    Constructible.Model.satisfiesIn_rename,
    localStagePublicAssignment_fixed_l,
    localStagePublicAssignment_core_l]
  constructor
  · rintro ⟨hparameters, hstage⟩
    have hfixedEq :
        fixed = Constructible.Model.stageHistoryFixedParametersRaw :=
      (Constructible.Model.satisfiesIn_canonicalStageParametersFormula_iff
        hθ hω fixed hfixed).mp hparameters
    subst fixed
    refine ⟨rfl, ?_⟩
    change Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      Constructible.Model.bareStageAtFormula
      (MostowskiCollapse.BareStageCondensation.bareStageAssignment
        α.toZFSet stage.1) at hstage
    exact (hcorrect α stage.1 hindex stage.2).mp hstage
  · rintro ⟨rfl, hstageEq⟩
    refine ⟨?_, ?_⟩
    · exact (Constructible.Model.satisfiesIn_canonicalStageParametersFormula_iff
        hθ hω _ hfixed).mpr rfl
    · have hstage := (hcorrect α stage.1 hindex stage.2).mpr hstageEq
      change Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        Constructible.Model.bareStageAtFormula
        (snoc (snoc Constructible.Model.stageHistoryFixedParametersRaw
          α.toZFSet) stage.1) at hstage
      exact hstage

/-- 存在闭包规范参数后得到适用于局部后继极限层的二元阶段公式。 -/
def localLStagePairFormula_l : FOFormula 2 :=
  externalExistentialClosure_l 13 localStageCoreFormula_l

/--
二元局部阶段公式的精确语义。它只要求环境层是严格高于 `omega` 的后继极限，
这正是稳定层构造将要保证的自然定义域。
-/
theorem satisfiesIn_localLStagePairFormula_iff_l
    {θ α : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (hα : α < θ)
    (stage : StageCarrier θ) :
    Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        localLStagePairFormula_l ![α.toZFSet, stage.1] ↔
      stage.1 = LStageZF α := by
  rw [localLStagePairFormula_l, satisfiesIn_externalExistentialClosure_l]
  change (∃ fixed : Tuple ZFSet.{u} 13,
      (∀ index, fixed index ∈ LStageZF θ) ∧
      Constructible.Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        localStageCoreFormula_l
        (localStagePublicAssignment_l α.toZFSet stage.1 fixed)) ↔ _
  constructor
  · rintro ⟨fixed, hfixed, hformula⟩
    exact (satisfiesIn_localStageCoreFormula_iff_l
      hθ hω hα stage fixed hfixed).mp hformula |>.2
  · intro hstage
    let fixed : Tuple ZFSet.{u} 13 :=
      Constructible.Model.stageHistoryFixedParametersRaw
    have hfixed : ∀ index, fixed index ∈ LStageZF θ := by
      intro index
      simpa only [fixed, Constructible.Model.stageHistoryFixedParametersRaw]
        using Constructible.Model.stageHistoryFixedParameters_mem_LStageZF_of_omega_lt
          hω index
    refine ⟨fixed, hfixed, ?_⟩
    exact (satisfiesIn_localStageCoreFormula_iff_l
      hθ hω hα stage fixed hfixed).mpr ⟨rfl, hstage⟩

end YesMetaZFC.BMS.ConstructibleBridge
