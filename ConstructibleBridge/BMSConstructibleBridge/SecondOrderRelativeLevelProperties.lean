import BMSConstructibleBridge.SecondOrderRelativeLevelTheorem

/-! # 相对层值的传递性与基集保持

从任意实际历史证书传输性质到任意输出根编码；不选择规范实数作为全局层值。
本文件的语义辅助随后用于相对类的对象定义与闭包句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelProperties

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem transitive_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {α C : SecondOrderGraph.code_l ℳ}
    (hC : SecondOrderRelativeLevel.spec_l hℳ B hB α C) : SecondOrderTransitiveSuperset.transitive_l C := by
  obtain ⟨_, _, _, _, _, S, n, W, _, hS, _, _, hW, hCW⟩ := hC
  let V : SecondOrderGraph.code_l ℳ := ⟨W, zero_l ℳ, hS.wellFounded n W hW⟩
  have hEq : SecondOrderGraph.eq_l C V := hCW
  intro X Y hX hY
  have hXV := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ X) hEq).mp hX
  have hYV := hS.transitive n W hW V.wf X Y hXV hY
  exact (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ Y) hEq).mpr hYV

theorem base_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {α C : SecondOrderGraph.code_l ℳ}
    (hC : SecondOrderRelativeLevel.spec_l hℳ B hB α C) :
    SecondOrderGraphSubsetFormula.subset_l ⟨B, zero_l ℳ, hB⟩ C := by
  obtain ⟨_, _, _, _, _, S, n, W, _, hS, _, _, hW, hCW⟩ := hC
  let V : SecondOrderGraph.code_l ℳ := ⟨W, zero_l ℳ, hS.wellFounded n W hW⟩
  have hEq : SecondOrderGraph.eq_l C V := hCW
  intro X hX
  exact (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ X) hEq).mpr
    (hS.base n W hW V.wf X hX)

#print axioms transitive_l
#print axioms base_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelProperties
