import BMSConstructibleBridge.TextbookLevyClassifierAbsolute
import BMSConstructibleBridge.ExternalDelta0Translation

/-!
# 以可构造层为界的有限 Lévy 分类器

旧外部公式把所有量词写成无界量词，因此它的表面交替秩高于分类关系真正需要的
复杂度。本文件使用上游 `Delta0Formula.relativize`，把每个量词统一限制到一个
显式给定的可构造层。只要该层严格高于 `omega`，前序局部绝对性定理就说明这
个真正有界的公式仍精确识别同一份有限分类证书。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/--
六个坐标依次为量词界、标准 `omega`、极性、层级、元数和公式码。
所有原分类器量词现在都是真正的集合有界量词。
-/
def boundedTextbookLevyClassifierDelta_l : Delta0Formula 6 :=
  Delta0Formula.relativize textbookLevyClassifierFormula_l

/-- 后继极限层中用于解释有界分类器的五个规范参数。 -/
noncomputable def textbookLevyClassifierStageAssignment_l
    (θ : Ordinal.{u}) (hω : Ordinal.omega0 < θ)
    (entry : TextbookLevyJudgment) : Tuple (StageCarrier θ) 5 :=
  ![⟨Ordinal.omega0.toZFSet, omega_toZFSet_mem_stage_l hω⟩,
    ⟨natCode (textbookLevyPolarityCode_l entry.isSigma),
      natCode_mem_stage_l hω _⟩,
    ⟨natCode entry.level, natCode_mem_stage_l hω _⟩,
    ⟨natCode entry.arity, natCode_mem_stage_l hω _⟩,
    ⟨natCode entry.code, natCode_mem_stage_l hω _⟩]

/-- 规范阶段赋值去掉子类型证明后恢复分类器的五个公开参数。 -/
theorem textbookLevyClassifierStageAssignment_value_l
    (θ : Ordinal.{u}) (hω : Ordinal.omega0 < θ)
    (entry : TextbookLevyJudgment) :
    Delta0Formula.val (textbookLevyClassifierStageAssignment_l θ hω entry) =
      ![Ordinal.omega0.toZFSet,
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] := by
  funext position
  fin_cases position <;> rfl

/--
以 `L_θ` 为统一量词界的有界分类器精确刻画有限 Lévy 分类证书。
这是后续稳定关系公式把公式码分类保留在原生 `Delta0` 层的入口。
-/
theorem satisfies_boundedTextbookLevyClassifierDelta_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (entry : TextbookLevyJudgment) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        boundedTextbookLevyClassifierDelta_l
        (tupleCons (LStageZF θ)
          (Delta0Formula.val
            (textbookLevyClassifierStageAssignment_l θ hω entry))) ↔
      entry.Certified := by
  rw [boundedTextbookLevyClassifierDelta_l,
    Delta0Formula.satisfies_relativize]
  change FOFormula.Satisfies
      (fun left right : StageCarrier θ => left.1 ∈ right.1)
      textbookLevyClassifierFormula_l
      (textbookLevyClassifierStageAssignment_l θ hω entry) ↔ _
  rw [Constructible.Model.satisfies_stageCarrier_iff_satisfiesIn]
  change Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookLevyClassifierFormula_l
      (Delta0Formula.val
        (textbookLevyClassifierStageAssignment_l θ hω entry)) ↔ _
  rw [textbookLevyClassifierStageAssignment_value_l]
  exact satisfiesIn_textbookLevyClassifierFormula_iff_l hθ hω entry

/-- 有界分类器翻译成 YesMetaZFC 成员语言后是原生 `Delta0`。 -/
theorem translatedBoundedTextbookLevyClassifier_isDelta0_l :
    Logic.FirstOrder.Formula.IsDelta0 StabilityFrame.membershipLevyBound
      (translateExternalFormula boundedTextbookLevyClassifierDelta_l.toFO) :=
  translateExternalDelta0_isDelta0_l boundedTextbookLevyClassifierDelta_l

/-- 把内层 `L_θ` 及分类器参数一同放入外层 `L_top`。 -/
noncomputable def boundedTextbookLevyClassifierOuterAssignment_l
    (top θ : Ordinal.{u}) (hθtop : θ < top)
    (hω : Ordinal.omega0 < θ) (entry : TextbookLevyJudgment) :
    Tuple (StageCarrier top) 6 :=
  ![⟨LStageZF θ, LStageZF_mem_of_lt hθtop⟩,
    ⟨Ordinal.omega0.toZFSet,
      omega_toZFSet_mem_stage_l (hω.trans hθtop)⟩,
    ⟨natCode (textbookLevyPolarityCode_l entry.isSigma),
      natCode_mem_stage_l (hω.trans hθtop) _⟩,
    ⟨natCode entry.level, natCode_mem_stage_l (hω.trans hθtop) _⟩,
    ⟨natCode entry.arity, natCode_mem_stage_l (hω.trans hθtop) _⟩,
    ⟨natCode entry.code, natCode_mem_stage_l (hω.trans hθtop) _⟩]

/-- 外层赋值的底层六元组就是 `L_θ` 与五个规范分类参数。 -/
theorem boundedTextbookLevyClassifierOuterAssignment_value_l
    (top θ : Ordinal.{u}) (hθtop : θ < top)
    (hω : Ordinal.omega0 < θ) (entry : TextbookLevyJudgment) :
    Delta0Formula.val
        (boundedTextbookLevyClassifierOuterAssignment_l
          top θ hθtop hω entry) =
      tupleCons (LStageZF θ)
        (Delta0Formula.val
          (textbookLevyClassifierStageAssignment_l θ hω entry)) := by
  funext position
  fin_cases position <;> rfl

/--
真正有界的分类器在任意更高可构造层中仍精确：有界公式的传递绝对性把外层
求值降到全宇宙，而相对化定理再把它还原为内层 `L_θ` 的旧分类器。
-/
theorem satisfiesIn_boundedTextbookLevyClassifier_iff_l
    {top θ : Ordinal.{u}} (hθtop : θ < top)
    (hθ : Order.IsSuccLimit θ) (hω : Ordinal.omega0 < θ)
    (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        boundedTextbookLevyClassifierDelta_l.toFO
        (tupleCons (LStageZF θ)
          (Delta0Formula.val
            (textbookLevyClassifierStageAssignment_l θ hω entry))) ↔
      entry.Certified := by
  let assignment : Tuple (StageCarrier top) 6 :=
    boundedTextbookLevyClassifierOuterAssignment_l
      top θ hθtop hω entry
  have hSubtype := Constructible.Model.satisfies_stageCarrier_iff_satisfiesIn
    boundedTextbookLevyClassifierDelta_l.toFO assignment
  rw [Delta0Formula.satisfies_toFO] at hSubtype
  have hAbsolute := Delta0Formula.satisfies_absolute
    (LStageZF_isTransitive top)
    boundedTextbookLevyClassifierDelta_l assignment
  rw [boundedTextbookLevyClassifierOuterAssignment_value_l] at hAbsolute
  exact hSubtype.symm.trans <| hAbsolute.trans
    (satisfies_boundedTextbookLevyClassifierDelta_iff_l hθ hω entry)

end YesMetaZFC.BMS.ConstructibleBridge
