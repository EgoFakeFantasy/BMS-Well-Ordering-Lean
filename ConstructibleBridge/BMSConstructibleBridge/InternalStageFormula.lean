import BMSConstructibleBridge.StageStructure
import BMSConstructibleBridge.ExternalExistentialClosure
import ConstructibleUniverse.SetTheory.ZFC.Constructible.VEqualsL

/-!
# 无参数的内部可构造层公式

外部库的 `internalLStageAtFormula` 把十三个规范求值器常量作为显式参数。本模块
先把布局重排为 `(index, stage, fixed13)`，再存在闭包最后十三个坐标，得到真正
只有两个自由坐标的成员语言公式。这里先证明 `L` 类载体上的精确语义；后续
稳定公式将在 `omega` 以上的集合大小层中使用同一封装。
-/

universe u

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Constructible

/-- 将规范求值器参数从十三元布局放到二元公开参数之后。 -/
def internalStageFixedRename_l : Fin 13 → Fin 15 :=
  fun index => Fin.natAdd 2 index

/--
把 `(fixed13, index, stage)` 布局重排为 `(index, stage, fixed13)`。
-/
def internalStageCoreRename_l : Fin 15 → Fin 15 :=
  fun index => Fin.lastCases
    (1 : Fin 15)
    (fun prior => Fin.lastCases
      (0 : Fin 15)
      (fun fixedIndex => Fin.natAdd 2 fixedIndex)
      prior)
    index

/-- 二个公开坐标与十三个内部参数组成的规范十五元赋值。 -/
def internalStagePublicAssignment_l
    (index stage : Constructible.Model.LCarrier.{u})
    (fixed : Tuple Constructible.Model.LCarrier.{u} 13) :
    Tuple Constructible.Model.LCarrier.{u} 15 :=
  Fin.append ![index, stage] fixed

/-- 重排后的参数公式恰好读取赋值末尾的十三元组。 -/
theorem internalStagePublicAssignment_fixed_l
    (index stage : Constructible.Model.LCarrier.{u})
    (fixed : Tuple Constructible.Model.LCarrier.{u} 13) :
    (fun position => internalStagePublicAssignment_l index stage fixed
      (internalStageFixedRename_l position)) = fixed := by
  funext position
  simp [internalStagePublicAssignment_l, internalStageFixedRename_l,
    Fin.append]

/-- 重排后的阶段公式恢复外部库的原始十五元赋值。 -/
theorem internalStagePublicAssignment_core_l
    (index stage : Constructible.Model.LCarrier.{u})
    (fixed : Tuple Constructible.Model.LCarrier.{u} 13) :
    (fun position => internalStagePublicAssignment_l index stage fixed
      (internalStageCoreRename_l position)) =
      snoc (snoc fixed index) stage := by
  funext position
  fin_cases position <;>
    rfl

/-- 带公开 `(index, stage)` 与隐藏规范参数的内部阶段核心公式。 -/
def internalStageCoreFormula_l : FOFormula 15 :=
  .conj
    (FOFormula.rename internalStageFixedRename_l
      Constructible.Model.canonicalStageParametersFormula)
    (FOFormula.rename internalStageCoreRename_l
      Constructible.Model.internalLStageAtFormula)

/-- 核心公式的语义同时固定参数并识别指定内部层。 -/
theorem satisfies_internalStageCoreFormula_l
    (index stage : Constructible.Model.LCarrier.{u})
    (fixed : Tuple Constructible.Model.LCarrier.{u} 13) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem internalStageCoreFormula_l
        (internalStagePublicAssignment_l index stage fixed) ↔
      fixed = Constructible.Model.stageHistoryFixedParameters ∧
        Constructible.Model.InternalLStageAt index stage := by
  simp only [internalStageCoreFormula_l, FOFormula.Satisfies]
  rw [FOFormula.satisfies_rename, FOFormula.satisfies_rename,
    internalStagePublicAssignment_fixed_l,
    internalStagePublicAssignment_core_l,
    Constructible.Model.satisfies_canonicalStageParametersFormula]
  constructor
  · rintro ⟨rfl, hStage⟩
    exact ⟨rfl,
      (Constructible.Model.satisfies_internalLStageAtFormula
        index stage).mp hStage⟩
  · rintro ⟨rfl, hStage⟩
    exact ⟨rfl,
      (Constructible.Model.satisfies_internalLStageAtFormula
        index stage).mpr hStage⟩

/--
存在闭包十三个规范参数后得到真正的二元内部 `L`-阶段公式。
坐标顺序为 `(index, stage)`。
-/
def internalLStagePairFormula_l : FOFormula 2 :=
  externalExistentialClosure_l 13 internalStageCoreFormula_l

/-- 二元公式在可构造宇宙中精确识别内部阶段。 -/
theorem satisfies_internalLStagePairFormula_l
    (index stage : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
        internalLStagePairFormula_l ![index, stage] ↔
      Constructible.Model.InternalLStageAt index stage := by
  rw [internalLStagePairFormula_l, satisfies_externalExistentialClosure_l]
  change (∃ fixed, FOFormula.Satisfies Constructible.Model.lCarrierMem
      internalStageCoreFormula_l
      (internalStagePublicAssignment_l index stage fixed)) ↔ _
  simp only [satisfies_internalStageCoreFormula_l, exists_eq_left]

/-- 在规范序数码处，二元公式的唯一输出正是外部的可构造层。 -/
theorem satisfies_internalLStagePairFormula_ordinal_iff_l
    (α : Ordinal.{u}) (stage : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
        internalLStagePairFormula_l
        ![Constructible.Model.ordinalLCarrier α, stage] ↔
      stage = Constructible.Model.stageLCarrier α := by
  rw [satisfies_internalLStagePairFormula_l,
    Constructible.Model.internalLStageAt_ordinal_iff]

/-- 类域满足关系的版本直接识别底层 `ZFSet` 阶段集合。 -/
theorem satisfiesIn_internalLStagePairFormula_L_iff_l
    (α : Ordinal.{u}) (stage : Constructible.Model.LCarrier.{u}) :
    Constructible.Model.SatisfiesIn Constructible.L
        internalLStagePairFormula_l ![α.toZFSet, stage.1] ↔
      stage.1 = Constructible.LStageZF α := by
  have hSemantics := Constructible.Model.satisfies_lCarrier_iff_satisfiesIn_L
    internalLStagePairFormula_l
    ![Constructible.Model.ordinalLCarrier α, stage]
  have hAssignment :
      (fun position =>
        (![Constructible.Model.ordinalLCarrier α, stage] position).1) =
      ![α.toZFSet, stage.1] := by
    funext position
    fin_cases position <;> rfl
  rw [hAssignment] at hSemantics
  rw [← hSemantics, satisfies_internalLStagePairFormula_ordinal_iff_l]
  constructor
  · intro hStage
    exact congrArg Subtype.val hStage
  · intro hStage
    exact Subtype.ext hStage

end ConstructibleBridge
end BMS
end YesMetaZFC
