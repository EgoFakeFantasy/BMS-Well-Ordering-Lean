import BMSConstructibleBridge.SecondOrderProgramNormalized
import BMSConstructibleBridge.SecondOrderProgramExpansionRectangular
import BMSConstructibleBridge.SecondOrderProgramTrimNormalized

/-!
# 原完整展开输出的当前高度规范化

所有实际raw分支保持矩形性，最后的原裁剪保持支撑高度并产生准确共同列长。
输入只要求矩形，不假定其尾部已经规范化；展开指标可以是任意内部数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionNormalized

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramNormalized (normalized_l)
open SecondOrderProgramExpansion (raw_m expand_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 任意矩形输入的原完整展开，其共同列长等于输出自身的实际当前高度。 -/
theorem expand_normalized_l (hℳ : Theory.Models ℳ theory_m) {X H L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n h k y : num_l ℳ}
    (hx : rectangular_l L E x n h) (hy : relation_l X (value_l x k) y) :
    normalized_l H L E y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ raw_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ SecondOrderProgramTrimArray.trim_m
  obtain ⟨v, hv, ht⟩ :=
    (SecondOrderProgramExpansionFallback.expand_rel_l hℳ hX hR hT x k y).mp hy
  obtain ⟨m, hvr⟩ := SecondOrderProgramExpansionRectangular.raw_rectangular_l hℳ hR hL hE hx hv
  have hHf := SecondOrderProgramArithmetic.function_of_semantics_l hℳ
    SecondOrderProgramTrimHeight.trim_m hH
  obtain ⟨z, hz, _⟩ := hHf v
  obtain ⟨g, hg, _⟩ := hHf y
  have hgz := SecondOrderProgramTrimNormalized.height_eq_l hℳ hT hH hL hE hvr hz ht hg
  rw [hgz] at hg
  exact ⟨m, z, SecondOrderProgramTrimNormalized.rectangular_l hℳ hT hH hL hE hvr hz ht, hg⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionNormalized
