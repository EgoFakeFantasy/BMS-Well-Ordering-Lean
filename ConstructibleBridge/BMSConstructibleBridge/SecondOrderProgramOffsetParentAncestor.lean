import BMSConstructibleBridge.SecondOrderProgramOffsetParentZero
import BMSConstructibleBridge.SecondOrderProgramCopiesBlockParentShift
import BMSConstructibleBridge.SecondOrderProgramParentRelocationAncestorExit
import BMSConstructibleBridge.SecondOrderProgramParentRelocation
import BMSConstructibleBridge.SecondOrderProgramUniformParentState
import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification

/-!
# 任意偏移段的父边与祖先对应

若局部块第 `i` 列与原数组第 `K+i` 列在全部内部行上具有相同条目，且偏移段保持在
原数组宽度内，则两侧统一父程序的段内后继输出逐行对应。实际二阶归纳公式继而把
对应闭合到全部内部行；出段后的祖先链由通用出段同步定理处理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramOffsetParentAncestor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramCopiesBlockParentShift
  (reloc_ge_m reloc_ge_language_m reloc_ge_syntax_l)
open SecondOrderProgramParentRelocationAncestorExit (ancestor_exit_sync_l)
open SecondOrderProgramParentRelocation (parent_some_offset_congr_l)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramUniformParentState (parent_past_end_l)
open SecondOrderProgramUniformParentSpecification (eligible_l parent_succ_some_l)
open SecondOrderProgramUniformParentLookup (parent_zero_l)
open SecondOrderProgramParentZero (parent_zero_m parent_zero_some_l)
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorChain (chain_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramListReverse (reverse_m)
open SecondOrderProgramIteration (repeat_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev Δ : SortContext signature_m := [.set, .num, .num, .num, .num]

private def env_slots_l (P : set_l ℳ) (x blk K w : num_l ℳ) : Env ℳ [] Δ :=
  let η₀ := Env.pushFree (Env.empty (M := ℳ)) w
  let η₁ := Env.pushFree η₀ K
  let η₂ := Env.pushFree η₁ blk
  let η₃ := Env.pushFree η₂ x
  Env.pushFree η₃ P

private theorem parent_descends_l (hℳ : Theory.Models ℳ theory_m)
    {P P0 L M J : set_l ℳ} (hP : graph_semantics_l (graph_m parent_m) P)
    (hP0 : graph_semantics_l (graph_m parent_zero_m) P0)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x n r : num_l ℳ} (hn : relation_l L x n) (k p : num_l ℳ)
    (hp : relation_l P (value_l (value_l x r) k) (succ_l p)) :
    SecondOrderOrder.lt_l p k := by
  letI := order_l hℳ
  have hkn : SecondOrderOrder.lt_l k n := by
    by_contra hkt
    exact absurd ((parent_past_end_l hℳ hP hL hn r k (succ_l p) (le_of_not_gt hkt)).mp hp)
      ((nonzero_l hℳ p).symm)
  rcases predecessor_l hℳ r with rfl | ⟨r', rfl⟩
  · rw [parent_zero_l hℳ hP hP0 hL x n k (succ_l p) hn hkn,
      parent_zero_some_l hℳ hP0 hL hJ hn k p] at hp
    exact hp.2.1
  · exact ((parent_succ_some_l hℳ hP hL hM hJ hn r' k p).mp hp).2.1

/-- 已知本行段内父边对应时，任意段内目标的祖先成员关系与局部块同步。 -/
theorem ancestor_sync_l (hℳ : Theory.Models ℳ theory_m)
    {L E J P M : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x n blk K w r j : num_l ℳ} (hx : relation_l L x n) (hb : relation_l L blk w)
    (hj : SecondOrderOrder.lt_l j w)
    (hpp : ∀ t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l x r) (add_l K t)) (succ_l (add_l K q)) ↔
        relation_l P (value_l (value_l blk r) t) (succ_l q))
    (q : num_l ℳ) :
    ¬relation_l M (value_l (value_l (value_l x r) (add_l K j)) (add_l K q)) (zero_l ℳ) ↔
      ¬relation_l M (value_l (value_l (value_l blk r) j) q) (zero_l ℳ) := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (step_m parent_m))
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ (chain_m parent_m)
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨P0, _, hP0⟩ := graph_total_l hℳ parent_zero_m
  exact ancestor_exit_sync_l hℳ parent_m parent_m hP hP hR hR hL hE hA hA hT hM hM
    (value_l x r) (value_l blk r) K w j hj
    (parent_descends_l hℳ hP hP0 hL hM hJ hx)
    (parent_descends_l hℳ hP hP0 hL hM hJ hb)
    (fun t q ht => hpp t ht q) q

private theorem eligible_agree_l (hℳ : Theory.Models ℳ theory_m)
    {L E J P M : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x n blk K w r j q : num_l ℳ} (hx : relation_l L x n) (hb : relation_l L blk w)
    (hj : SecondOrderOrder.lt_l j w) (hq : SecondOrderOrder.lt_l q j)
    (hentry : ∀ s e, SecondOrderOrder.lt_l s w →
      (relation_l J (value_l x (value_l (add_l K s) (succ_l r))) e ↔
        relation_l J (value_l blk (value_l s (succ_l r))) e))
    (hpp : ∀ t, SecondOrderOrder.lt_l t w → ∀ a,
      relation_l P (value_l (value_l x r) (add_l K t)) (succ_l (add_l K a)) ↔
        relation_l P (value_l (value_l blk r) t) (succ_l a)) :
    eligible_l M J x r (add_l K j) (add_l K q) ↔ eligible_l M J blk r j q := by
  have hqw : SecondOrderOrder.lt_l q w := SecondOrderOrder.trans_l hℳ hq hj
  refine and_congr (ancestor_sync_l hℳ hL hE hJ hP hM hx hb hj hpp q) ?_
  constructor
  · rintro ⟨a, b, hqa, hjb, hab⟩
    exact ⟨a, b, (hentry q (succ_l a) hqw).mp hqa,
      (hentry j (succ_l b) hj).mp hjb, hab⟩
  · rintro ⟨a, b, hqa, hjb, hab⟩
    exact ⟨a, b, (hentry q (succ_l a) hqw).mpr hqa,
      (hentry j (succ_l b) hj).mpr hjb, hab⟩

private theorem reloc_ge_succ_l (hℳ : Theory.Models ℳ theory_m)
    {L E J P M : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x n blk K w : num_l ℳ} (hx : relation_l L x n) (hb : relation_l L blk w)
    (hbound : ∀ t, SecondOrderOrder.lt_l t w → SecondOrderOrder.lt_l (add_l K t) n)
    (hentry : ∀ r t e, SecondOrderOrder.lt_l t w →
      (relation_l J (value_l x (value_l (add_l K t) r)) e ↔
        relation_l J (value_l blk (value_l t r)) e))
    (r : num_l ℳ)
    (hpp : ∀ t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l x r) (add_l K t)) (succ_l (add_l K q)) ↔
        relation_l P (value_l (value_l blk r) t) (succ_l q)) :
    ∀ t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l x (succ_l r)) (add_l K t)) (succ_l (add_l K q)) ↔
        relation_l P (value_l (value_l blk (succ_l r)) t) (succ_l q) := by
  intro t ht q
  exact parent_some_offset_congr_l hℳ hP hL hM hJ hb hx ht (hbound t ht)
    (fun s hs => eligible_agree_l hℳ hL hE hJ hP hM hx hb ht hs
      (hentry (succ_l r)) hpp) q

/-- 任意内部行上的段内父后继输出对应。 -/
theorem reloc_ge_rows_l (hℳ : Theory.Models ℳ theory_m)
    {L E J P M : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x n blk K w : num_l ℳ} (hx : relation_l L x n) (hb : relation_l L blk w)
    (hbound : ∀ t, SecondOrderOrder.lt_l t w → SecondOrderOrder.lt_l (add_l K t) n)
    (hentry : ∀ r t e, SecondOrderOrder.lt_l t w →
      (relation_l J (value_l x (value_l (add_l K t) r)) e ↔
        relation_l J (value_l blk (value_l t r)) e)) :
    ∀ r t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l x r) (add_l K t)) (succ_l (add_l K q)) ↔
        relation_l P (value_l (value_l blk r) t) (succ_l q) := by
  intro r
  obtain ⟨P0, _, hP0⟩ := graph_total_l hℳ parent_zero_m
  refine induct_l hℳ reloc_ge_m reloc_ge_language_m
    (env_slots_l P x blk K w)
    (fun s => ∀ t, SecondOrderOrder.lt_l t w → ∀ q,
      relation_l P (value_l (value_l x s) (add_l K t)) (succ_l (add_l K q)) ↔
        relation_l P (value_l (value_l blk s) t) (succ_l q))
    (reloc_ge_syntax_l P x blk K w) ?_ ?_ r
  · intro t ht q
    exact SecondOrderProgramOffsetParentZero.reloc_ge_zero_l
      hℳ hP hP0 hL hJ hx hb hbound (hentry (zero_l ℳ)) ht
  · intro s hs t ht q
    exact reloc_ge_succ_l hℳ hL hE hJ hP hM hx hb hbound hentry s hs t ht q

/-- 对应偏移段与局部块的祖先成员关系在全部内部行上逐值一致。 -/
theorem ancestor_l (hℳ : Theory.Models ℳ theory_m)
    {L E J P M : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x n blk K w : num_l ℳ} (hx : relation_l L x n) (hb : relation_l L blk w)
    (hbound : ∀ t, SecondOrderOrder.lt_l t w → SecondOrderOrder.lt_l (add_l K t) n)
    (hentry : ∀ r t e, SecondOrderOrder.lt_l t w →
      (relation_l J (value_l x (value_l (add_l K t) r)) e ↔
        relation_l J (value_l blk (value_l t r)) e))
    (r j q : num_l ℳ) (hj : SecondOrderOrder.lt_l j w) :
    ¬relation_l M (value_l (value_l (value_l x r) (add_l K j)) (add_l K q)) (zero_l ℳ) ↔
      ¬relation_l M (value_l (value_l (value_l blk r) j) q) (zero_l ℳ) := by
  exact ancestor_sync_l hℳ hL hE hJ hP hM hx hb hj
    (reloc_ge_rows_l hℳ hL hE hJ hP hM hx hb hbound hentry r) q

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramOffsetParentAncestor
