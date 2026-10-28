import BMSConstructibleBridge.SecondOrderProgramTrimParent
import BMSConstructibleBridge.SecondOrderProgramPrefixPreservation
import BMSConstructibleBridge.SecondOrderProgramExpansionFallback
import BMSConstructibleBridge.SecondOrderProgramRectangularSelection

/-!
# 原无父展开在剩余列上保持父关系和祖先关系

非空输入的真实fallback取去末列前缀，再执行原零行裁剪。
本结论与已验有父分支的好块保持互补；内部宽度及查询行号均不假定标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionFallbackPrefix

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListTake (take_m)
open SecondOrderProgramExpansion (raw_m expand_m fallback_m)
open SecondOrderProgramMaximalParentRow (maximal_m)
open SecondOrderProgramExpansionFallback (expand_rel_l raw_none_l fallback_succ_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 无最大父行的完整展开，在删末列后的每列上保持全部原父查询。 -/
theorem parent_l (hℳ : Theory.Models ℳ theory_m) {X M P L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h k t : num_l ℳ}
    (hx : rectangular_l L E x (succ_l n) h) (hm : relation_l M x (zero_l ℳ))
    (hy : relation_l X (value_l x k) y) (ht : SecondOrderOrder.lt_l t n) (r q : num_l ℳ) :
    relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l y r) t) q := by
  letI := order_l hℳ
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ raw_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ SecondOrderProgramTrimArray.trim_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ fallback_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  obtain ⟨v, hv, hty⟩ := (expand_rel_l hℳ hX hR hT x k y).mp hy
  have hk := (fallback_succ_l hℳ hF hL hK hx.1 k v).mp
    ((raw_none_l hℳ hR hM hF hm k v).mp hv)
  have hns : n ≤ succ_l n := Or.inr ⟨zero_l ℳ, by rw [add_succ_l hℳ, add_zero_l hℳ]⟩
  have htm : t < min (succ_l n) n := by rw [min_eq_right hns]; exact ht
  exact (SecondOrderProgramPrefixPreservation.take_parent_l hℳ hK hP hL hx.1 hk htm r q).trans
    (SecondOrderProgramTrimParent.parent_l hℳ hT hP hL hE
      (SecondOrderProgramRectangularSelection.take_rectangular_l hℳ hK hL hE hx hk) hty r t q)

/-- 同一无父展开在每个保留列上保持原祖先成员程序的全部输出。 -/
theorem member_l (hℳ : Theory.Models ℳ theory_m) {X M A L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hA : graph_semantics_l (graph_m (member_m parent_m)) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h k t : num_l ℳ}
    (hx : rectangular_l L E x (succ_l n) h) (hm : relation_l M x (zero_l ℳ))
    (hy : relation_l X (value_l x k) y) (ht : SecondOrderOrder.lt_l t n) (r i q : num_l ℳ) :
    relation_l A (value_l (value_l (value_l x r) t) i) q ↔
      relation_l A (value_l (value_l (value_l y r) t) i) q := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorPrefixCongruence.member_congr_l hℳ parent_m parent_m hP hP hA hA
    (value_l x r) (value_l y r) n
    (fun _ _ hp => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp)
    (fun j hj q => parent_l hℳ hX hM hP hL hE hx hm hy (t := j) hj r q) ht i q

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionFallbackPrefix
