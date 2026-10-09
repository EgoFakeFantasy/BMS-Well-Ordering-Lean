import BMSConstructibleBridge.PowerlessRelativeClassParameterBounds
import BMSConstructibleBridge.SecondOrderOrdinalLimitDerives
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage

/-! # 有限实际 Class 参数的非零极限共同母层

只处理源语法的外部有限自由上下文，不收集内部参数族。先用已有共同层界
容纳全部实际 Class 参数，再由原 Z₂ 的序数上方极限存在取得严格较高的
非零极限层，逐成员提升原界。不要求起点或参数在 Class 内可数，故也
适用于位于首不可数截断层上方的统一 Def 图及预算母界。

本文件是后续预算实际存在证明的语义辅助。输出为 Prop 中的实际原商
层见证；不抽取 Type 选择函数，不调用源 Collection，不替代最终 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLimitParameterBounds

open Logic FirstOrder
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (X : type_l hℳ B) :
    ∃ δ C, PowerlessRelativeHierarchySemantics.limit_l hℳ δ ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ B δ C ∧ mem_l hℳ X.val C ∧
      ∀ (s : SetTheory.SetSort) (v : Variable Δ s), mem_l hℳ (η.freeVal v).val C := by
  obtain ⟨a, c, hc, hXc, hParams⟩ := PowerlessRelativeClassParameterBounds.exists_l η X
  obtain ⟨δ, hδ, haδ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ a
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hc)
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hδ
  have hcC := PowerlessRelativeLevelClosure.members_l hℳ hBase haδ hc hC
  have hLift x (hx : mem_l hℳ x c) :=
    PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC c hcC x hx
  exact ⟨δ, C, ⟨⟨a, haδ⟩, hNoMax⟩, hC, hLift X.val hXc,
    fun s v => hLift (η.freeVal v).val (hParams s v)⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLimitParameterBounds
