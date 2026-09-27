import BMSConstructibleBridge.SecondOrderProgramOffsetParentAncestor
import BMSConstructibleBridge.SecondOrderProgramPrefixEntry
import BMSConstructibleBridge.SecondOrderProgramListAppend

/-!
# 拼接右段的祖先偏移对应

若 `z = x ++ y` 且左段宽度为 `n`，则右段局部列 `i` 在 `z` 中位于 `n+i`。
原拼接的逐列读取定理与任意偏移父链接口给出全部内部行上的祖先等价。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAppendRightAncestor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramListAppend (append_m append_length_l append_right_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 拼接输出右段的祖先查询与右输入的局部祖先查询逐值一致。 -/
theorem member_l (hℳ : Theory.Models ℳ theory_m) {A L E J M : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x y z n m : num_l ℳ} (hx : relation_l L x n) (hy : relation_l L y m)
    (hz : relation_l A (value_l x y) z) (r j q : num_l ℳ)
    (hj : SecondOrderOrder.lt_l j m) :
    ¬relation_l M (value_l (value_l (value_l z r) (add_l n j)) (add_l n q)) (zero_l ℳ) ↔
      ¬relation_l M (value_l (value_l (value_l y r) j) q) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  have hzlen := append_length_l hℳ hA hL hx hy hz
  have hbound (t : num_l ℳ) (ht : t < m) : add_l n t < add_l n m :=
    SecondOrderProgramParentRelocation.lt_add_left_l hℳ ht
  have hentry (s t e : num_l ℳ) (ht : t < m) :
      relation_l J (value_l z (value_l (add_l n t) s)) e ↔
        relation_l J (value_l y (value_l t s)) e := by
    exact SecondOrderProgramPrefixEntry.entry_index_congr_l hℳ hJ hL hE hzlen hy
      (hbound t ht) ht (fun a => append_right_l hℳ hA hL hE hx hy hz ht a) s e
  exact SecondOrderProgramOffsetParentAncestor.ancestor_l
    hℳ hL hE hJ hP hM hzlen hy hbound hentry r j q hj

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAppendRightAncestor
