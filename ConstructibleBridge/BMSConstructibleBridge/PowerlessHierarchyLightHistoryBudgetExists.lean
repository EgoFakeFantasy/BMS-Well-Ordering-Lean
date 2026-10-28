import BMSConstructibleBridge.PowerlessRelativeOrdinalBudgetReading
import BMSConstructibleBridge.PowerlessRelativeClassLimitParameterBounds
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryBudgetProvider

/-! # 原内部长前史的实际预算起点与函数装配

背景为原 Z₂ 的实际图商。B、给定 Class 对象 D、实际层 W 和任意序数
指标母集 A 先进入一个真正非零极限共同层。该层指标的原数码图经有效根
清理后，全部根仍内部良基且底部对象保持原指标；没有加入参数可数性、
Class 递归、Collection 或 Type 层代表选择。

本模块的预算只用于原公式集合归纳；预算函数本身允许 raw，不能被暗作
Class Δ₀分离参数，也不代替最终对象 Derives 或 BMS 良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryBudgetExists

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 清理真正共同层指标的根码，并保留全部固定参数的实际层成员界。 -/
theorem start_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (K : source_coding_l hℳ)
    {B Ω W A : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (D : PowerlessRelativeClassStructure.type_l hℳ B)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hA : SetTheory.Structure.IsOrdinal (SecondOrderOrdinalBudgetOrder.quotient_l hℳ) A) :
    ∃ S : SecondOrderModel.set_l ℳ, ∃ r : SecondOrderModel.num_l ℳ,
      ∃ hS : ∀ n, SecondOrderDomain.wf_l S n, ∃ C : type_l hℳ,
        SetTheory.Structure.IsOrdinal (SecondOrderOrdinalBudgetOrder.quotient_l hℳ)
          (SecondOrderOrdinalBudgetOrder.base_l hℳ hS r) ∧
        PowerlessRelativeHierarchySemantics.limit_l hℳ
          (SecondOrderOrdinalBudgetOrder.base_l hℳ hS r) ∧
        PowerlessRelativeHierarchySemantics.level_l hℳ B
          (SecondOrderOrdinalBudgetOrder.base_l hℳ hS r) C ∧
        mem_l hℳ B C ∧ mem_l hℳ D.val C ∧ mem_l hℳ W C ∧ mem_l hℳ A C := by
  let B₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let W₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨W, PowerlessRelativeLevelClosure.class_l hℳ hBase hW⟩
  let A₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨A, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hA⟩
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] [.set, .set, .set] :=
    Env.empty |>.pushFree D |>.pushFree W₀ |>.pushFree A₀
  obtain ⟨ξ, C, hLimit, hC, hBC, hParams⟩ :=
    PowerlessRelativeClassLimitParameterBounds.exists_l η B₀
  have hDC : mem_l hℳ D.val C := hParams .set (.there (.there .here))
  have hWC : mem_l hℳ W C := hParams .set (.there .here)
  have hAC : mem_l hℳ A C := hParams .set .here
  have hξ := PowerlessRelativeLevelClosure.ordinal_l hℳ hC
  obtain ⟨Ξ, hΞ⟩ := SecondOrderQuotient.surj_l hℳ ξ
  obtain ⟨S, hSGraph⟩ := SecondOrderValidRootGraph.exists_l hℳ Ξ.real
  have hS (n : SecondOrderModel.num_l ℳ) : SecondOrderDomain.wf_l S n :=
    SecondOrderValidRootGraph.wf_l hSGraph n
  have hBaseEq : SecondOrderOrdinalBudgetOrder.base_l hℳ hS Ξ.root = ξ :=
    ((SecondOrderQuotient.eq_iff_l hℳ Ξ ⟨S, Ξ.root, hS Ξ.root⟩).mpr
      (SecondOrderValidRootGraph.agrees_l hℳ hSGraph Ξ.root Ξ.wf)).symm.trans hΞ
  exact ⟨S, Ξ.root, hS, C, hBaseEq.symm ▸ hξ, hBaseEq.symm ▸ hLimit,
    hBaseEq.symm ▸ hC, hBC, hDC, hWC, hAC⟩

/-- 真正构造预算图并消去条件式预算前提；参数共同母界也由原接口实际取得。 -/
theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (K : source_coding_l hℳ)
    {B Ω W A : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (D : PowerlessRelativeClassStructure.type_l hℳ B)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hA : SetTheory.Structure.IsOrdinal (SecondOrderOrdinalBudgetOrder.quotient_l hℳ) A) :
    ∃ Q : type_l hℳ,
      PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B D.val W A Q := by
  obtain ⟨S, r, hS, C, _hξ, hLimit, hStart, hBStart, hDStart, hWStart, hAStart⟩ :=
    start_l hℳ K hBase D hW hA
  obtain ⟨Acode, hAcode⟩ := SecondOrderQuotient.surj_l hℳ A
  have hOrdinalCode : SetTheory.Structure.IsOrdinal
      (SecondOrderOrdinalBudgetOrder.quotient_l hℳ) (mk_l hℳ Acode) := by
    simpa only [hAcode] using hA
  have hCodeStart : mem_l hℳ (mk_l hℳ Acode) C := by
    simpa only [hAcode] using hAStart
  let two : SecondOrderModel.num_l ℳ :=
    SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))
  obtain ⟨Qnum, N, R, G, hQnum, hN, hRel, hG, _Y, F, _hMap, hReadF⟩ :=
    SecondOrderOrdinalBudgetFunction.exists_l hℳ S r hS Acode two
  have hBudget := PowerlessHierarchyLightHistoryBudgetProvider.budget_of_tail_l hℳ hBase
    Acode hOrdinalCode hS hQnum hN hRel hG rfl hLimit hStart
    hBStart hDStart hWStart hCodeStart hReadF
  refine ⟨F, ?_⟩
  simpa only [hAcode] using hBudget

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryBudgetExists
