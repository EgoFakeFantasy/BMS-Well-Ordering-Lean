import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessRectangular
import BMSConstructibleBridge.SecondOrderProgramExpansionSelected
import BMSConstructibleBridge.SecondOrderProgramTrimRectangular

/-!
# 原完整展开保持矩形性且共同列高不增

按实际最大父行结果分支：无父时取原前缀，有父时拼接好块与所有同高副本。
最后执行原裁剪。空数组和任意内部展开指标均被覆盖，不给外部父表或标准性假设。
这里的高度是实际共同列长；不能把结论替换为种子高度受当前目标行数界约束。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionRectangular

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramRectangularSelection (take_rectangular_l)
open SecondOrderProgramExpansion (raw_m expand_m fallback_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramExpansionSuccess (success_m bad_m)
open SecondOrderProgramExpansionFallback (raw_none_l fallback_rel_l index_rel_l expand_rel_l)
open SecondOrderProgramExpansionSuccessRectangular (bad_rectangular_l success_rectangular_l)
open SecondOrderProgramListTake (take_m)
open SecondOrderProgramListCode (pred_m pred_succ_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原raw的所有真实分支保留共同列高，输出实际宽度由程序决定。 -/
theorem raw_rectangular_l (hℳ : Theory.Models ℳ theory_m) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m raw_m) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n h k y : num_l ℳ}
    (hx : rectangular_l L E x n h) (hy : relation_l R (value_l x k) y) :
    ∃ m, rectangular_l L E y m h := by
  letI := order_l hℳ
  obtain ⟨M, hMf, hM⟩ := graph_total_l hℳ maximal_m
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ last_index_m
  obtain ⟨z, hz, _⟩ := hMf x
  rcases predecessor_l hℳ z with rfl | ⟨r, rfl⟩
  · obtain ⟨F, _, hF⟩ := graph_total_l hℳ fallback_m
    obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
    have hf := (raw_none_l hℳ hR hM hF hz k y).mp hy
    obtain ⟨j, _, hk⟩ := (fallback_rel_l hℳ hF hJ hK x k y).mp hf
    exact ⟨min n j, take_rectangular_l hℳ hK hL hE hx hk⟩
  · obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
    obtain ⟨S, _, hS⟩ := graph_total_l hℳ success_m
    obtain ⟨B, hBf, hB⟩ := graph_total_l hℳ bad_m
    obtain ⟨D, hDf, hD⟩ := graph_total_l hℳ sub_m
    obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ pred_m
    obtain ⟨j, p, hn, hp, hpj⟩ :=
      SecondOrderProgramMaximalParentSelection.width_parent_l hℳ hM hP hL hz
    have he : n = succ_l j := function_value_unique_l (function_of_semantics_l hℳ length_m hL) hx.1 hn
    have hxr : rectangular_l L E x (succ_l j) h := by
      rw [← he]
      exact hx
    have hj := (index_rel_l hℳ hJ hL hQ hn j).mpr ((pred_succ_l hℳ hQ j j).mpr rfl)
    have hys := (SecondOrderProgramExpansionSelected.raw_some_l hℳ hR hM hP hJ hS hz hj hp k y).mp hy
    obtain ⟨d, hd, _⟩ := hDf (value_l j p)
    obtain ⟨b, hb, _⟩ := hBf (value_l x (value_l k (value_l r p)))
    have hbr := bad_rectangular_l hℳ hB hL hE hD hxr (Or.inr hpj) hd hb
    exact ⟨_, success_rectangular_l hℳ hS hB hL hE hxr hb hbr hys⟩

/-- 任意真实完整展开都仍为矩形数组，并有不超过原共同列高的实际共同列长。 -/
theorem expand_rectangular_l (hℳ : Theory.Models ℳ theory_m) {X L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n h k y : num_l ℳ}
    (hx : rectangular_l L E x n h) (hy : relation_l X (value_l x k) y) :
    letI := order_l hℳ
    ∃ m g, rectangular_l L E y m g ∧ g ≤ h := by
  letI := order_l hℳ
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ raw_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ SecondOrderProgramTrimArray.trim_m
  obtain ⟨H, hHf, hH⟩ := graph_total_l hℳ SecondOrderProgramTrimHeight.trim_m
  obtain ⟨v, hv, ht⟩ := (expand_rel_l hℳ hX hR hT x k y).mp hy
  obtain ⟨m, hvr⟩ := raw_rectangular_l hℳ hR hL hE hx hv
  obtain ⟨z, hz, _⟩ := hHf v
  exact ⟨m, min h z, SecondOrderProgramTrimRectangular.trim_rectangular_l hℳ hT hH hL hE hvr hz ht,
    min_le_left h z⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionRectangular
