import BMSConstructibleBridge.SecondOrderProgramTrimEntryBelow
import BMSConstructibleBridge.SecondOrderProgramUniformParentPrefix
import BMSConstructibleBridge.SecondOrderProgramParentHeightBound

/-!
# 原零行裁剪保持统一父关系及祖先关系

保留行的可选entry一致；删去的全零尾行在两侧都无父节点。复用真实prefix公式
做内部行归纳，再由同宽数组的越界规格补齐全部列。行号无需外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimParent

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramTrimArray (trim_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramUniformParentPrefix (prefix_m prefix_language_m prefix_syntax_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 对矩形输入，原裁剪保留全部内部行、列上的原统一父查询。 -/
theorem parent_l (hℳ : Theory.Models ℳ theory_m) {T P L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h : num_l ℳ}
    (hx : rectangular_l L E x n h) (hy : relation_l T x y) (r t q : num_l ℳ) :
    relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l y r) t) q := by
  letI := order_l hℳ
  obtain ⟨H, hHf, hH⟩ := graph_total_l hℳ SecondOrderProgramTrimHeight.trim_m
  obtain ⟨z, hz, _⟩ := hHf x
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ SecondOrderProgramEntry.entry_m
  have hyr := SecondOrderProgramTrimNormalized.rectangular_l hℳ hT hH hL hE hx hz hy
  have hxzero := (SecondOrderProgramZeroRows.trim_bound_iff_zero_rows_l hℳ hH hE hz z).mp (le_refl z)
  have hyzero := SecondOrderProgramRectangularHeight.zero_rows_l hℳ hL hE hyr
  have hPf := function_of_semantics_l hℳ parent_m hP
  have hnone : ∀ r, z ≤ r → ∀ t q,
      relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l y r) t) q := by
    intro r hr t q
    have hp := SecondOrderProgramParentHeightBound.parent_none_l hℳ hP hE hxzero hr t
    have hp' := SecondOrderProgramParentHeightBound.parent_none_l hℳ hP hE hyzero hr t
    constructor
    · intro hq
      rw [← function_value_unique_l hPf hp hq]
      exact hp'
    · intro hq
      rw [← function_value_unique_l hPf hp' hq]
      exact hp
  have hprefix : ∀ r t, t < n → ∀ q,
      relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l y r) t) q := by
    intro r
    apply induct_l hℳ prefix_m prefix_language_m
      (((((Env.empty (M := ℳ)).pushFree P).pushFree n).pushFree y).pushFree x)
      (fun r => ∀ t, SecondOrderOrder.lt_l t n → ∀ q,
        relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l y r) t) q)
      (prefix_syntax_l P x y n) ?_ ?_ r
    · intro t ht q
      by_cases hr : zero_l ℳ < z
      · exact SecondOrderProgramParentPrefixStep.zero_congr_l hℳ hP hL hJ hx.1 hyr.1
          (Or.inl rfl) (Or.inl rfl)
          (fun j hj v => SecondOrderProgramTrimEntryBelow.entry_l hℳ hT hH hJ hL hE hx hz hy hj hr v) ht q
      · exact hnone (zero_l ℳ) (le_of_not_gt hr) t q
    · intro r ih t ht q
      by_cases hr : succ_l r < z
      · exact SecondOrderProgramParentPrefixStep.succ_congr_l hℳ hP hL hJ hx.1 hyr.1
          (Or.inl rfl) (Or.inl rfl) r
          (fun j hj v => SecondOrderProgramTrimEntryBelow.entry_l hℳ hT hH hJ hL hE hx hz hy hj hr v) ih ht q
      · exact hnone (succ_l r) (le_of_not_gt hr) t q
  by_cases ht : t < n
  · exact hprefix r t ht q
  · exact (SecondOrderProgramUniformParentState.parent_past_end_l hℳ hP hL hx.1 r t q
      (le_of_not_gt ht)).trans
      (SecondOrderProgramUniformParentState.parent_past_end_l hℳ hP hL hyr.1 r t q
        (le_of_not_gt ht)).symm

/-- 逐父查询保持传至原祖先成员程序，包括零行及越界列。 -/
theorem member_l (hℳ : Theory.Models ℳ theory_m) {T M L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h : num_l ℳ}
    (hx : rectangular_l L E x n h) (hy : relation_l T x y) (r t i q : num_l ℳ) :
    relation_l M (value_l (value_l (value_l x r) t) i) q ↔
      relation_l M (value_l (value_l (value_l y r) t) i) q := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorCongruence.member_congr_l hℳ parent_m parent_m hP hP hM hM
    (value_l x r) (value_l y r) (parent_l hℳ hT hP hL hE hx hy r) t i q

#print axioms parent_l
#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimParent
