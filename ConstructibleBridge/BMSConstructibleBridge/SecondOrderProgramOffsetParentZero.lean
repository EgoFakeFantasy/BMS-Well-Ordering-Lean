import BMSConstructibleBridge.SecondOrderProgramParentZero
import BMSConstructibleBridge.SecondOrderProgramUniformParent
import BMSConstructibleBridge.SecondOrderProgramUniformParentLookup
import BMSConstructibleBridge.SecondOrderProgramParentRelocation
import BMSConstructibleBridge.SecondOrderProgramEntry
import BMSConstructibleBridge.SecondOrderProgramLength

/-!
# 任意偏移段的零行父边对应

把副本段专用的零行父搬运抽象为任意内部偏移 `K`。接口只要求偏移段仍在原数组
长度内，以及原数组 `K+i` 与局部块 `i` 的真实条目逐值一致。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramOffsetParentZero

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramParentZero (parent_zero_m parent_zero_some_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramUniformParentLookup (parent_zero_l)
open SecondOrderProgramParentRelocation (lt_add_left_l lt_of_add_lt_add_left_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 第零行候选合格性只由对应两列的条目严格序决定。 -/
theorem zero_eligible_agree_l {J : set_l ℳ}
    {x blk K w i t : num_l ℳ}
    (hi : SecondOrderOrder.lt_l i w) (ht : SecondOrderOrder.lt_l t w)
    (hentry : ∀ j e, SecondOrderOrder.lt_l j w →
      (relation_l J (value_l x (value_l (add_l K j) (zero_l ℳ))) e ↔
        relation_l J (value_l blk (value_l j (zero_l ℳ))) e)) :
    SecondOrderProgramParentZero.eligible_l J x (add_l K t) (add_l K i) ↔
      SecondOrderProgramParentZero.eligible_l J blk t i := by
  refine ⟨fun ⟨a, b, ha, hb, hab⟩ => ⟨a, b, ?_, ?_, hab⟩,
    fun ⟨a, b, ha, hb, hab⟩ => ⟨a, b, ?_, ?_, hab⟩⟩
  · exact (hentry i (succ_l a) hi).mp ha
  · exact (hentry t (succ_l b) ht).mp hb
  · exact (hentry i (succ_l a) hi).mpr ha
  · exact (hentry t (succ_l b) ht).mpr hb

/-- 在任意偏移段上，第零行的段内后继父输出与局部块逐值对应。 -/
theorem reloc_ge_zero_l (hℳ : Theory.Models ℳ theory_m)
    {J P P0 L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hP0 : graph_semantics_l (graph_m parent_zero_m) P0)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x n blk K w j p : num_l ℳ} (hx : relation_l L x n) (hb : relation_l L blk w)
    (hbound : ∀ t, SecondOrderOrder.lt_l t w → SecondOrderOrder.lt_l (add_l K t) n)
    (hentry : ∀ t e, SecondOrderOrder.lt_l t w →
      (relation_l J (value_l x (value_l (add_l K t) (zero_l ℳ))) e ↔
        relation_l J (value_l blk (value_l t (zero_l ℳ))) e))
    (hj : SecondOrderOrder.lt_l j w) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    relation_l P (value_l (value_l x (zero_l ℳ)) (add_l K j)) (succ_l (add_l K p)) ↔
      relation_l P (value_l (value_l blk (zero_l ℳ)) j) (succ_l p) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hKj := hbound j hj
  have hel (i t : num_l ℳ) (hi : i < w) (ht : t < w) :
      SecondOrderProgramParentZero.eligible_l J x (add_l K t) (add_l K i) ↔
        SecondOrderProgramParentZero.eligible_l J blk t i :=
    zero_eligible_agree_l hi ht hentry
  rw [parent_zero_l hℳ hP hP0 hL x n (add_l K j) (succ_l (add_l K p)) hx hKj,
    parent_zero_l hℳ hP hP0 hL blk w j (succ_l p) hb hj,
    parent_zero_some_l hℳ hP0 hL hJ hx (add_l K j) (add_l K p),
    parent_zero_some_l hℳ hP0 hL hJ hb j p]
  constructor
  · rintro ⟨_, hKpj, ho, hmax⟩
    have hpj : p < j := lt_of_add_lt_add_left_l hℳ hKpj
    refine ⟨hj, hpj, (hel p j (lt_trans hpj hj) hj).mp ho, ?_⟩
    intro q hpq hqj
    exact (hel q j (lt_trans hqj hj) hj).not.mp
      (hmax (add_l K q) (lt_add_left_l hℳ hpq) (lt_add_left_l hℳ hqj))
  · rintro ⟨_, hpj, hb', hmax⟩
    refine ⟨hKj, lt_add_left_l hℳ hpj, (hel p j (lt_trans hpj hj) hj).mpr hb', ?_⟩
    intro c hKpc hcKj
    have hKle : K ≤ add_l K p := (le_iff_l hℳ _ _).mpr ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := (le_iff_l hℳ K c).mp (le_of_lt (lt_of_le_of_lt hKle hKpc))
    subst hq
    have hpq : p < q := lt_of_add_lt_add_left_l hℳ hKpc
    have hqj : q < j := lt_of_add_lt_add_left_l hℳ hcKj
    intro hc
    exact (hmax q hpq hqj) ((hel q j (lt_trans hqj hj) hj).mp hc)

#print axioms zero_eligible_agree_l
#print axioms reloc_ge_zero_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramOffsetParentZero
