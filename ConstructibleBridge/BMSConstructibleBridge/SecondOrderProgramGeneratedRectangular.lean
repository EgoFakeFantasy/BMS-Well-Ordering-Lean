import BMSConstructibleBridge.SecondOrderProgramSeedRectangular
import BMSConstructibleBridge.SecondOrderProgramRunRectangular
import BMSConstructibleBridge.SecondOrderProgramGeneratedDecode

/-!
# 原生成解码器的内部矩形性

对同一原输入码运行原seed和原run，得到真实矩形数组。共同列长受输入码中的种子
高度约束；这不意味着种子高度受最终当前行数界约束，也不限制内部轨迹长度或宽度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedRectangular

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramSeed (seed_m)
open SecondOrderProgramRun (run_m)
open SecondOrderProgramGeneratedDecode (decode_m decode_rel_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 每个内部输入的原解码输出均矩形，实际共同列高不超过原种子参数。 -/
theorem decode_rectangular_l (hℳ : Theory.Models ℳ theory_m) {D L E : set_l ℳ}
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {c y : num_l ℳ}
    (hy : relation_l D c y) :
    letI := order_l hℳ
    ∃ n h, rectangular_l L E y n h ∧ h ≤ (SecondOrderUnpairing.value_l hℳ c).1 := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ seed_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ run_m
  obtain ⟨a, ha, hr⟩ := (decode_rel_l hℳ hD hS hR c y).mp hy
  exact SecondOrderProgramRunRectangular.run_rectangular_l hℳ hR hL hE
    (SecondOrderProgramSeedRectangular.seed_rectangular_l hℳ hS hL hE ha) hr

#print axioms decode_rectangular_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedRectangular
