import BMSConstructibleBridge.SecondOrderProgramExpansionNormalized
import BMSConstructibleBridge.SecondOrderProgramRunClosedSet
import BMSConstructibleBridge.SecondOrderProgramSeedRectangular
import BMSConstructibleBridge.SecondOrderProgramGeneratedDecode

/-!
# 原生成解码器的当前高度规范化

原种子的支撑高度精确等于列长；原完整展开保持规范化内部集合。
原run的实际公式归纳因此覆盖任意内部轨迹，最终得到每个原解码输出的准确当前高度。
最后只使用当前数组的零尾部界，不限制种子高度、轨迹长度或数组宽度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedNormalized

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramNormalized (normalized_l normalized_set_l)
open SecondOrderProgramSeed (seed_m)
open SecondOrderProgramRun (run_m)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramGeneratedDecode (decode_m decode_rel_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramZeroRows (zero_rows_l trim_bound_iff_zero_rows_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原种子在任意内部输入高度下均已规范化。 -/
theorem seed_normalized_l (hℳ : Theory.Models ℳ theory_m) {S H L E : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {n y : num_l ℳ}
    (hy : relation_l S n y) : normalized_l H L E y := by
  obtain ⟨h, hh, _⟩ := function_of_semantics_l hℳ SecondOrderProgramTrimHeight.trim_m hH y
  have he := SecondOrderProgramSeedSpecification.height_l hℳ hS hH hy hh
  rw [he] at hh
  exact ⟨_, n, SecondOrderProgramSeedRectangular.seed_rectangular_l hℳ hS hL hE hy, hh⟩

/-- 对真实规范化集合使用原run内部归纳，不把任意外部不变量直接套到非标准轨迹。 -/
theorem run_normalized_l (hℳ : Theory.Models ℳ theory_m) {R H L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {t v y : num_l ℳ}
    (hv : normalized_l H L E v) (hy : relation_l R (value_l t v) y) : normalized_l H L E y := by
  obtain ⟨X, _, hX⟩ := graph_total_l hℳ expand_m
  obtain ⟨S, hS⟩ := normalized_set_l hℳ H L E
  have hclosed (v i w : num_l ℳ) (hv : mem_l v S) (hw : relation_l X (value_l v i) w) : mem_l w S := by
    obtain ⟨n, h, hvr, _⟩ := (hS v).mp hv
    exact (hS w).mpr (SecondOrderProgramExpansionNormalized.expand_normalized_l hℳ hX hH hL hE hvr hw)
  exact (hS y).mp (SecondOrderProgramRunClosedSet.run_mem_l hℳ hR hX hclosed ((hS v).mpr hv) hy)

/-- 所有内部输入码的原解码输出都具有等于当前高度的准确共同列长。 -/
theorem decode_normalized_l (hℳ : Theory.Models ℳ theory_m) {D H L E : set_l ℳ}
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {c y : num_l ℳ}
    (hy : relation_l D c y) : normalized_l H L E y := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ seed_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ run_m
  obtain ⟨a, ha, hr⟩ := (decode_rel_l hℳ hD hS hR c y).mp hy
  exact run_normalized_l hℳ hR hH hL hE (seed_normalized_l hℳ hS hH hL hE ha) hr

/-- 当前零尾部界约束实际共同列长；该界不被偷换为原输入中的种子高度界。 -/
theorem decode_bounded_l (hℳ : Theory.Models ℳ theory_m) {D H L E : set_l ℳ}
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {c y b : num_l ℳ}
    (hy : relation_l D c y) (hb : zero_rows_l E y b) :
    letI := order_l hℳ
    ∃ n h, rectangular_l L E y n h ∧ relation_l H y h ∧ h ≤ b := by
  obtain ⟨n, h, hyr, hh⟩ := decode_normalized_l hℳ hD hH hL hE hy
  exact ⟨n, h, hyr, hh, (trim_bound_iff_zero_rows_l hℳ hH hE hh b).mpr hb⟩

#print axioms seed_normalized_l
#print axioms run_normalized_l
#print axioms decode_normalized_l
#print axioms decode_bounded_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedNormalized
