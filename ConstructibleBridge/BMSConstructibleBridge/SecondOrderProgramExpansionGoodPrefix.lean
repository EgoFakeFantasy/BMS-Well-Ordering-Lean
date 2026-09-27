import BMSConstructibleBridge.SecondOrderProgramTrimParent
import BMSConstructibleBridge.SecondOrderProgramPrefixPreservation
import BMSConstructibleBridge.SecondOrderProgramExpansionRectangular

/-!
# 原完整展开保留好块的父关系和祖先关系

先沿原成功正文的take与append保留好块，再沿真实trim保留所有父查询。
最大父行、末列及所选父列均来自原程序图，未用抽象展开替换实际expand。
本文件不处理坏块副本，也不声称已建立稳定表示或良序下降。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodPrefix

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListTake (take_m take_length_min_l)
open SecondOrderProgramListAppend (append_m)
open SecondOrderProgramExpansionSuccess (success_m good_m copied_m success_rel_l)
open SecondOrderProgramExpansionSuccessShape (good_rel_l)
open SecondOrderProgramExpansion (raw_m expand_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原成功正文在保留的好块列上不改变任意行的统一父查询。 -/
theorem success_parent_l (hℳ : Theory.Models ℳ theory_m) {S P L : set_l ℳ}
    (hS : graph_semantics_l (graph_m success_m) S)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L) {x y n k r p t : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l S (value_l x (value_l k (value_l r p))) y) :
    letI := order_l hℳ
    t < min n p → ∀ u q,
      relation_l P (value_l (value_l x u) t) q ↔ relation_l P (value_l (value_l y u) t) q := by
  letI := order_l hℳ
  intro ht u q
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ good_m
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ copied_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ append_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  obtain ⟨g, c, hg, _, ha⟩ := (success_rel_l hℳ hS hG hC hA _ y).mp hy
  have hk := (good_rel_l hℳ hG hK x k r p g).mp hg
  exact (SecondOrderProgramPrefixPreservation.take_parent_l hℳ hK hP hL hx hk ht u q).trans
    (SecondOrderProgramPrefixPreservation.append_parent_l hℳ hA hP hL
      (take_length_min_l hℳ hK hL hx hk) ha ht u q)

/-- 原成功正文保留好块列的完整祖先成员输出，允许任意内部行和复制次数。 -/
theorem success_member_l (hℳ : Theory.Models ℳ theory_m) {S M L : set_l ℳ}
    (hS : graph_semantics_l (graph_m success_m) S)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L) {x y n k r p t : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l S (value_l x (value_l k (value_l r p))) y) :
    letI := order_l hℳ
    t < min n p → ∀ u i q,
      relation_l M (value_l (value_l (value_l x u) t) i) q ↔
        relation_l M (value_l (value_l (value_l y u) t) i) q := by
  letI := order_l hℳ
  intro ht u i q
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorPrefixCongruence.member_congr_l hℳ parent_m parent_m hP hP hM hM
    (value_l x u) (value_l y u) (min n p)
    (fun _ _ hp => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp)
    (fun j hj q => success_parent_l hℳ hS hP hL hx hy (t := j) hj u q) ht i q

/-- 实际最大父行成功分支的完整expand，在裁剪后仍保持好块上的所有父查询。 -/
theorem expand_parent_l (hℳ : Theory.Models ℳ theory_m) {X M P J L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hJ : graph_semantics_l (graph_m last_index_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h k r j p t : num_l ℳ}
    (hx : rectangular_l L E x n h) (hm : relation_l M x (succ_l r)) (hj : relation_l J x j)
    (hp : relation_l P (value_l (value_l x r) j) (succ_l p))
    (hy : relation_l X (value_l x k) y) :
    letI := order_l hℳ
    t < min n p → ∀ u q,
      relation_l P (value_l (value_l x u) t) q ↔ relation_l P (value_l (value_l y u) t) q := by
  letI := order_l hℳ
  intro ht u q
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ success_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ SecondOrderProgramTrimArray.trim_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ raw_m
  obtain ⟨v, hs, hv⟩ :=
    (SecondOrderProgramExpansionSelected.expand_some_l hℳ hX hM hP hJ hS hT hm hj hp k y).mp hy
  have hr := (SecondOrderProgramExpansionSelected.raw_some_l hℳ hR hM hP hJ hS hm hj hp k v).mpr hs
  obtain ⟨m, hvr⟩ := SecondOrderProgramExpansionRectangular.raw_rectangular_l hℳ hR hL hE hx hr
  exact (success_parent_l hℳ hS hP hL hx.1 hs ht u q).trans
    (SecondOrderProgramTrimParent.parent_l hℳ hT hP hL hE hvr hv u t q)

/-- 在同一实际成功展开上，好块列的原祖先成员程序逐输出保持。 -/
theorem expand_member_l (hℳ : Theory.Models ℳ theory_m) {X M P J A L E : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hJ : graph_semantics_l (graph_m last_index_m) J)
    (hA : graph_semantics_l (graph_m (member_m parent_m)) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h k r j p t : num_l ℳ}
    (hx : rectangular_l L E x n h) (hm : relation_l M x (succ_l r)) (hj : relation_l J x j)
    (hp : relation_l P (value_l (value_l x r) j) (succ_l p))
    (hy : relation_l X (value_l x k) y) :
    letI := order_l hℳ
    t < min n p → ∀ u i q,
      relation_l A (value_l (value_l (value_l x u) t) i) q ↔
        relation_l A (value_l (value_l (value_l y u) t) i) q := by
  letI := order_l hℳ
  intro ht u i q
  exact SecondOrderProgramAncestorPrefixCongruence.member_congr_l hℳ parent_m parent_m hP hP hA hA
    (value_l x u) (value_l y u) (min n p)
    (fun _ _ hp => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp)
    (fun t ht q => expand_parent_l hℳ hX hM hP hJ hL hE hx hm hj hp hy (t := t) ht u q) ht i q

#print axioms success_parent_l
#print axioms success_member_l
#print axioms expand_parent_l
#print axioms expand_member_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodPrefix
