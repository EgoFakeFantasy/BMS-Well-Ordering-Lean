import BMSConstructibleBridge.SecondOrderProgramUniformParentPrefix
import BMSConstructibleBridge.SecondOrderProgramPrefixEntry
import BMSConstructibleBridge.SecondOrderProgramListAppend

/-!
# 原取前缀与拼接保留原父关系及祖先关系

原take在保留列上不改父查询和祖先成员；原append不会改变左段已有列的查询。
全部列界、行号与数组宽度均在模型内部，不给任意抽象前缀额外正确性假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramPrefixPreservation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListTake (take_m take_length_min_l)
open SecondOrderProgramListAppend (append_m append_length_l append_left_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原take保留的每列，在任意内部行的原统一父查询完全不变。 -/
theorem take_parent_l (hℳ : Theory.Models ℳ theory_m) {K P L : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L) {x y n k t : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l K (value_l x k) y) :
    letI := order_l hℳ
    t < min n k → ∀ r q,
      relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l y r) t) q := by
  letI := order_l hℳ
  intro ht r q
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ entry_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  exact SecondOrderProgramUniformParentPrefix.parent_congr_l hℳ hP hL hJ hx
    (take_length_min_l hℳ hK hL hx hy) (min_le_left n k) (Or.inl rfl)
    (fun j hj => SecondOrderProgramPrefixEntry.take_entry_l hℳ hK hJ hL hE hx hy hj) r t ht q

/-- 原take保留列的实际祖先成员输出不变，不仅保持某个抽象祖先集合。 -/
theorem take_member_l (hℳ : Theory.Models ℳ theory_m) {K M L : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L) {x y n k t : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l K (value_l x k) y) :
    letI := order_l hℳ
    t < min n k → ∀ r i q,
      relation_l M (value_l (value_l (value_l x r) t) i) q ↔
        relation_l M (value_l (value_l (value_l y r) t) i) q := by
  letI := order_l hℳ
  intro ht r i q
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ entry_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  exact SecondOrderProgramUniformParentPrefix.member_congr_l hℳ hM hL hJ hx
    (take_length_min_l hℳ hK hL hx hy) (min_le_left n k) (Or.inl rfl)
    (fun j hj => SecondOrderProgramPrefixEntry.take_entry_l hℳ hK hJ hL hE hx hy hj) r ht i q

/-- 向右拼接任意内部数组，不改变原左段任一有效列的可选entry。 -/
theorem append_entry_l (hℳ : Theory.Models ℳ theory_m) {A J L E : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y z n m t : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l L y m) (hz : relation_l A (value_l x y) z)
    (ht : SecondOrderOrder.lt_l t n) (r q : num_l ℳ) :
    relation_l J (value_l x (value_l t r)) q ↔ relation_l J (value_l z (value_l t r)) q := by
  letI := order_l hℳ
  have hnm : n ≤ add_l n m := (le_iff_l hℳ n (add_l n m)).mpr ⟨m, rfl⟩
  exact SecondOrderProgramPrefixEntry.entry_congr_l hℳ hJ hL hE hx
    (append_length_l hℳ hA hL hx hy hz) ht (lt_of_lt_of_le ht hnm)
    (fun s => (append_left_l hℳ hA hL hE hx hy hz ht s).symm) r q

/-- 原append不改变左段列的原父查询，右段长度和值均不受限制。 -/
theorem append_parent_l (hℳ : Theory.Models ℳ theory_m) {A P L : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L) {x y z n t : num_l ℳ}
    (hx : relation_l L x n) (hz : relation_l A (value_l x y) z)
    (ht : SecondOrderOrder.lt_l t n) (r q : num_l ℳ) :
    relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l z r) t) q := by
  obtain ⟨m, hy, _⟩ := function_of_semantics_l hℳ length_m hL y
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ entry_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  exact SecondOrderProgramUniformParentPrefix.parent_congr_l hℳ hP hL hJ hx
    (append_length_l hℳ hA hL hx hy hz) (Or.inl rfl)
    ((le_iff_l hℳ n (add_l n m)).mpr ⟨m, rfl⟩)
    (fun j hj => append_entry_l hℳ hA hJ hL hE hx hy hz hj) r t ht q

/-- 原append保留左段列的全部实际祖先成员输出，允许内部非标准宽度。 -/
theorem append_member_l (hℳ : Theory.Models ℳ theory_m) {A M L : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L) {x y z n t : num_l ℳ}
    (hx : relation_l L x n) (hz : relation_l A (value_l x y) z)
    (ht : SecondOrderOrder.lt_l t n) (r i q : num_l ℳ) :
    relation_l M (value_l (value_l (value_l x r) t) i) q ↔
      relation_l M (value_l (value_l (value_l z r) t) i) q := by
  obtain ⟨m, hy, _⟩ := function_of_semantics_l hℳ length_m hL y
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ entry_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  exact SecondOrderProgramUniformParentPrefix.member_congr_l hℳ hM hL hJ hx
    (append_length_l hℳ hA hL hx hy hz) (Or.inl rfl)
    ((le_iff_l hℳ n (add_l n m)).mpr ⟨m, rfl⟩)
    (fun j hj => append_entry_l hℳ hA hJ hL hE hx hy hz hj) r ht i q

#print axioms take_parent_l
#print axioms take_member_l
#print axioms append_entry_l
#print axioms append_parent_l
#print axioms append_member_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramPrefixPreservation
