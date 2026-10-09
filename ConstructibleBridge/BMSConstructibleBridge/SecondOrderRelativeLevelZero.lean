import BMSConstructibleBridge.SecondOrderRelativeClass

/-! # 零阶段的值及基对象进入相对类

空序数没有规范前驱；任意历史证书的零阶段因而等于指定基对象。商相等
传输覆盖任意根编码，不要求输入空序数采用固定实数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelZero

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem value_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {α C : SecondOrderGraph.code_l ℳ}
    (hα : ∀ X, ¬SecondOrderGraph.mem_l X α)
    (hC : SecondOrderRelativeLevel.spec_l hℳ B hB α C) :
    SecondOrderGraph.eq_l C ⟨B, zero_l ℳ, hB⟩ := by
  obtain ⟨A, _, Q, D, R, S, n, W, hP, hS, hn, hαn, hWn, hCW⟩ := hC
  have hαN : SecondOrderGraph.eq_l α (SecondOrderRootCorrespondence.member_code_l hℳ A hP n hn) := hαn
  have hMin : SecondOrderRelativeHierarchyStep.minimal_l R n := by
    intro i hi
    have hid := ((hP.predecessors i n).mp hi).1
    let I := SecondOrderRootCorrespondence.member_code_l hℳ A hP i hid
    have hIN := (SecondOrderRootCorrespondence.edge_iff_l hℳ A hP hid hn).mp hi
    exact hα I ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ I) hαN).mpr hIN)
  have hWB : W = B := by
    rcases hS.history n W hWn with ⟨_, hWB⟩ | ⟨k, _, hk, _, _⟩ | ⟨hLimit, _⟩
    · exact hWB
    · exact False.elim (hMin k hk.1)
    · exact False.elim (hLimit.1 hMin)
  subst W
  exact hCW

theorem base_object_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩) :
    SecondOrderRelativeClass.member_l hℳ B hB ⟨B, zero_l ℳ, hB⟩ := by
  obtain ⟨α, hα, hEmpty⟩ := SecondOrderOrdinalSuccessor.empty_exists_l hℳ
  obtain ⟨C, hC⟩ := SecondOrderRelativeLevel.exists_l hℳ B hB hBase α hα
  exact (SecondOrderRelativeClass.congr_l hℳ (value_l hℳ hEmpty hC)).mp
    (SecondOrderRelativeClass.level_l hℳ B hB hBase α C hα hC)

#print axioms value_l
#print axioms base_object_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelZero
