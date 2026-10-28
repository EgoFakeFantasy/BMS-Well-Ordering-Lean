import BMSConstructibleBridge.SecondOrderProgramListReverseIndices
import BMSConstructibleBridge.SecondOrderProgramListEntryBound
import BMSConstructibleBridge.SecondOrderProgramListExtensionality

/-!
# 原反转的内部条目界与可逆性

有效内部下标都有逆序位置见证；结合已验证的原反转下标规格可传递全部有效条目的
数值界，再由真实长度和列表码外延性证明两次反转得到同一原码。不作外部列表解码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramReverseConsequences

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramListReverse (reverse_m reverse_step_m)
open SecondOrderProgramListReverseEntries (reverse_length_l)
open SecondOrderProgramListReverseIndices (reverse_indices_l)
open SecondOrderProgramListEntryBound (below_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListFold (fold_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 逆序下标方程对交换两个下标保持成立，含模型内部非标准下标。 -/
theorem index_symm_l (hℳ : Theory.Models ℳ theory_m) {j k n : num_l ℳ}
    (hjk : add_l (succ_l j) k = n) : add_l (succ_l k) j = n := by
  rw [SecondOrderNumbers.succ_add_l hℳ] at hjk ⊢
  rwa [SecondOrderNumbers.add_comm_l hℳ k j]

/-- 每个界内位置都有同一长度内的逆序位置，不要求长度标准。 -/
theorem index_exists_l (hℳ : Theory.Models ℳ theory_m) {j n : num_l ℳ}
    (hj : SecondOrderOrder.lt_l j n) :
    ∃ k, add_l (succ_l j) k = n ∧ SecondOrderOrder.lt_l k n := by
  obtain ⟨k, hk⟩ := hj
  have hidx : add_l (succ_l j) k = n := by
    rw [SecondOrderNumbers.succ_add_l hℳ, ← add_succ_l hℳ]
    exact hk
  exact ⟨k, hidx, j, (SecondOrderNumbers.add_comm_l hℳ k (succ_l j)).trans hidx⟩

/-- 反转逐下标规格，辅助折叠与迭代图由原总性在内部取得。 -/
theorem lookup_l (hℳ : Theory.Models ℳ theory_m) {T L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n j k : num_l ℳ}
    (hy : relation_l T x y) (hn : relation_l L x n) (hjk : add_l (succ_l j) k = n) (w : num_l ℳ) :
    relation_l E (value_l y j) w ↔ relation_l E (value_l x k) w := by
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  exact reverse_indices_l hℳ hT hF hL hE hI x y n j k w hy hn hjk

/-- 原反转保持全部有效位置的严格数值界，越界补零不作为成员参与。 -/
theorem below_reverse_l (hℳ : Theory.Models ℳ theory_m) {T L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n b : num_l ℳ}
    (hy : relation_l T x y) (hn : relation_l L x n) (hb : below_l E x n b) : below_l E y n b := by
  intro j hj w hw
  obtain ⟨k, hjk, hk⟩ := index_exists_l hℳ hj
  exact hb k hk w ((lookup_l hℳ hT hL hE hy hn hjk w).mp hw)

/-- 两次原反转恰好恢复同一个原码；长度约束不可省略。 -/
theorem involution_l (hℳ : Theory.Models ℳ theory_m) {T : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T) {x y z : num_l ℳ}
    (hxy : relation_l T x y) (hyz : relation_l T y z) : z = x := by
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨n, hn, _⟩ := hLf x
  have hyn := reverse_length_l hℳ hT hF hL hI x y n hxy hn
  have hzn := reverse_length_l hℳ hT hF hL hI y z n hyz hyn
  apply SecondOrderProgramListExtensionality.extensionality_l hℳ hL hE hzn hn
  intro j hj w hw
  obtain ⟨k, hjk, _⟩ := index_exists_l hℳ hj
  exact (lookup_l hℳ hT hL hE hxy hn (index_symm_l hℳ hjk) w).mp
    ((lookup_l hℳ hT hL hE hyz hyn hjk w).mp hw)

/-- 原反转关系是对称的，来自程序总性和两次反转的码相等。 -/
theorem symmetric_l (hℳ : Theory.Models ℳ theory_m) {T : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T) {x y : num_l ℳ}
    (hxy : relation_l T x y) : relation_l T y x := by
  obtain ⟨z, hyz, _⟩ := function_of_semantics_l hℳ reverse_m hT y
  exact (involution_l hℳ hT hxy hyz) ▸ hyz

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramReverseConsequences
