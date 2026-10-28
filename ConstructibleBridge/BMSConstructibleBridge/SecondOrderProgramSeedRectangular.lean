import BMSConstructibleBridge.SecondOrderProgramSeedSpecification
import BMSConstructibleBridge.SecondOrderProgramRectangular

/-!
# 原任意内部高度种子的矩形性

两列都由原replicate生成，长度恰为输入高度。等长列集合经理解取得，再依次接入
第二列和第一列；零高度也保留原两列，不能误删为空数组。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSeedRectangular

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l length_set_l rectangular_iff_all_l)
open SecondOrderProgramListAll (all_zero_l all_cons_l)
open SecondOrderProgramSeed (seed_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同一原种子输出的真实宽度为二，全部有效列的实际高度等于任意内部输入n。 -/
theorem seed_rectangular_l (hℳ : Theory.Models ℳ theory_m) {S L E : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {n y : num_l ℳ}
    (hy : relation_l S n y) : rectangular_l L E y (succ_l (succ_l (zero_l ℳ))) n := by
  obtain ⟨T, hT⟩ := length_set_l hℳ L n
  obtain ⟨a, b, he, ha, _, hb, _⟩ := SecondOrderProgramSeedSpecification.columns_l hℳ hS hL hE hy
  apply (rectangular_iff_all_l hT).mpr
  refine ⟨SecondOrderProgramSeedSpecification.width_l hℳ hS hL hy, ?_⟩
  rw [he]
  exact all_cons_l hℳ hE ((hT a).mpr ha)
    (all_cons_l hℳ hE ((hT b).mpr hb) (all_zero_l hℳ E T (zero_l ℳ)))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSeedRectangular
