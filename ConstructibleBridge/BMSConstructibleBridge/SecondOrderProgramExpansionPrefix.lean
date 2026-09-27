import BMSConstructibleBridge.SecondOrderProgramSuccessPrefix
import BMSConstructibleBridge.SecondOrderProgramExpansionFallbackPrefix
import BMSConstructibleBridge.SecondOrderProgramExpansionRectangular

/-!
# 完整原展开保留除末列外的原父关系和祖先关系

按实际最大父行图分支，成功时消费好块加零号副本的整个前缀保持，失败时消费
去末列前缀保持。两支均保留实际trim步骤；没有额外的父行选择或展开正确性假设。
本结论不约束新增副本之间的祖先关系，也不是严格良序下降。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionPrefix

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramExpansion (raw_m expand_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramListCode (pred_m pred_succ_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 真实expand在所有原非末列上保持任意内部行的原统一父查询，覆盖全部分支。 -/
theorem parent_l (hℳ : Theory.Models ℳ theory_m) {X P L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y j h k t : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) h) (hy : relation_l X (value_l x k) y)
    (ht : SecondOrderOrder.lt_l t j) (u q : num_l ℳ) :
    relation_l P (value_l (value_l x u) t) q ↔ relation_l P (value_l (value_l y u) t) q := by
  obtain ⟨M, hMf, hM⟩ := graph_total_l hℳ maximal_m
  obtain ⟨z, hz, _⟩ := hMf x
  rcases predecessor_l hℳ z with rfl | ⟨r, rfl⟩
  · exact SecondOrderProgramExpansionFallbackPrefix.parent_l hℳ hX hM hP hL hE hx hz hy ht u q
  · obtain ⟨J, _, hJ⟩ := graph_total_l hℳ last_index_m
    obtain ⟨D, _, hD⟩ := graph_total_l hℳ pred_m
    have hj : relation_l J x j :=
      (SecondOrderProgramExpansionFallback.index_rel_l hℳ hJ hL hD hx.1 j).mpr
        ((pred_succ_l hℳ hD j j).mpr rfl)
    obtain ⟨j', p, hj', hp, hpj⟩ := SecondOrderProgramMaximalParentSelection.parent_some_l hℳ hM hP hJ hz
    have he := function_value_unique_l (function_of_semantics_l hℳ last_index_m hJ) hj' hj
    subst j'
    obtain ⟨S, _, hS⟩ := graph_total_l hℳ SecondOrderProgramExpansionSuccess.success_m
    obtain ⟨T, _, hT⟩ := graph_total_l hℳ SecondOrderProgramTrimArray.trim_m
    obtain ⟨R, _, hR⟩ := graph_total_l hℳ raw_m
    obtain ⟨v, hs, hv⟩ :=
      (SecondOrderProgramExpansionSelected.expand_some_l hℳ hX hM hP hJ hS hT hz hj hp k y).mp hy
    have hr := (SecondOrderProgramExpansionSelected.raw_some_l hℳ hR hM hP hJ hS hz hj hp k v).mpr hs
    obtain ⟨n, hvr⟩ := SecondOrderProgramExpansionRectangular.raw_rectangular_l hℳ hR hL hE hx hr
    exact (SecondOrderProgramSuccessPrefix.parent_l hℳ hS hP hL hx.1 (Or.inr hpj) hs ht u q).trans
      (SecondOrderProgramTrimParent.parent_l hℳ hT hP hL hE hvr hv u t q)

/-- 原非末列的整个祖先成员查询在真实完整展开前后相同，保留原内部搜索预算。 -/
theorem member_l (hℳ : Theory.Models ℳ theory_m) {X M L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y j h k t : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) h) (hy : relation_l X (value_l x k) y)
    (ht : SecondOrderOrder.lt_l t j) (u i q : num_l ℳ) :
    relation_l M (value_l (value_l (value_l x u) t) i) q ↔
      relation_l M (value_l (value_l (value_l y u) t) i) q := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorPrefixCongruence.member_congr_l hℳ parent_m parent_m hP hP hM hM
    (value_l x u) (value_l y u) j
    (fun _ _ hp => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp)
    (fun t ht q => parent_l hℳ hX hP hL hE hx hy (t := t) ht u q) ht i q

#print axioms parent_l
#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionPrefix
