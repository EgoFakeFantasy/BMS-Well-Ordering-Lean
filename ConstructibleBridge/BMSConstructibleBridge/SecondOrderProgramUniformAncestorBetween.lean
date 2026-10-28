import BMSConstructibleBridge.SecondOrderProgramUniformAncestorRecord

/-!
# 低行持续性给出的中间祖先

若第 `r` 行上 `i` 是 `b` 的真实祖先，且中间列 `j` 在每个更低行都是 `b` 的
真实祖先，那么 `i` 在第 `r` 行也是 `j` 的真实祖先。第零行由零行记录判据处理；
后继行把低行的两条祖先链用可比性拼合，再使用后继行记录判据。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorBetween

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 当前行祖先与全部低行的中间祖先共同推出当前行的中间祖先。 -/
theorem member_between_l (hℳ : Theory.Models ℳ theory_m) {M J L : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L) {x n r b i j d : num_l ℳ}
    (hn : relation_l L x n) (hbn : SecondOrderOrder.lt_l b n)
    (hi : ¬relation_l M (value_l (value_l (value_l x r) b) i) (zero_l ℳ))
    (hij : SecondOrderOrder.lt_l i j) (hjb : SecondOrderOrder.lt_l j b)
    (hje : relation_l J (value_l x (value_l j r)) (succ_l d))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s r →
      ¬relation_l M (value_l (value_l (value_l x s) b) j) (zero_l ℳ)) :
    ¬relation_l M (value_l (value_l (value_l x r) j) i) (zero_l ℳ) := by
  letI := SecondOrderAlgebra.order_l hℳ
  have hjn : SecondOrderOrder.lt_l j n := SecondOrderOrder.trans_l hℳ hjb hbn
  rcases predecessor_l hℳ r with rfl | ⟨s, rfl⟩
  · obtain ⟨a, _, hie, _, _⟩ :=
      SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hi
    apply (SecondOrderProgramUniformAncestorRecord.member_iff_record_zero_l
      hℳ hM hJ hL hn hjn hie hje).mpr
    refine ⟨hij, ?_, ?_⟩
    · exact SecondOrderProgramUniformAncestorRecord.entry_lt_zero_l
        hℳ hM hJ hL hn hbn hi hij hjb hie hje
    · intro t e hit htj hte
      exact SecondOrderProgramUniformAncestorRecord.entry_lt_zero_l
        hℳ hM hJ hL hn hbn hi hit (SecondOrderOrder.trans_l hℳ htj hjb) hie hte
  · have hilow := SecondOrderProgramUniformAncestorStructure.row_succ_l hℳ hM hi
    have hjlow := hbelow s (lt_own_succ_l hℳ s)
    have hijlow := SecondOrderProgramUniformAncestorStructure.comparable_l
      hℳ hM hilow hjlow hij
    obtain ⟨a, _, hie, _, _⟩ :=
      SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hi
    apply (SecondOrderProgramUniformAncestorRecord.member_iff_record_l
      hℳ hM hJ hL hn hjn hie hje).mpr
    refine ⟨hij, hijlow, ?_, ?_⟩
    · exact SecondOrderProgramUniformAncestorRecord.entry_lt_l
        hℳ hM hJ hi hjlow hij hie hje
    · intro t e hit _ htlow hte
      have htB := SecondOrderProgramUniformAncestorStructure.trans_l hℳ hM hjlow htlow
      exact SecondOrderProgramUniformAncestorRecord.entry_lt_l
        hℳ hM hJ hi htB hit hie hte

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorBetween
