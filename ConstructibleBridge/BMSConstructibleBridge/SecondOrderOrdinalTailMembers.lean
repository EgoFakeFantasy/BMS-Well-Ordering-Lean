import BMSConstructibleBridge.SecondOrderOrdinalTailGraph

/-! # ω 尾节点的精确成员与后继方程

用实际标签双模拟对齐基础图；内部数的前驱公理给出后继处的精确截段。
没有对原模型数作宿主归纳，也不预设新增节点已经是序数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailMembers

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem lt_succ_l (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) :
    SecondOrderOrder.lt_l m (succ_l n) ↔ SecondOrderOrder.lt_l m n ∨ m = n := by
  constructor
  · rintro ⟨k, hk⟩
    have hAdd : add_l m k = n := injective_l hℳ ((add_succ_l hℳ m k).symm.trans hk)
    rcases predecessor_l hℳ k with rfl | ⟨j, rfl⟩
    · exact Or.inr ((add_zero_l hℳ m).symm.trans hAdd)
    · exact Or.inl ⟨j, hAdd⟩
  · rintro (⟨k, hk⟩ | rfl)
    · exact ⟨succ_l k, (add_succ_l hℳ m (succ_l k)).trans (congrArg succ_l hk)⟩
    · exact ⟨zero_l ℳ, (add_succ_l hℳ m (zero_l ℳ)).trans (congrArg succ_l (add_zero_l hℳ m))⟩

variable (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
  (hG : SecondOrderOrdinalTailGraph.spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a)

theorem members_l (n : num_l ℳ) (X : SecondOrderGraph.code_l ℳ) :
    SecondOrderGraph.mem_l X (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n) ↔
      SecondOrderGraph.mem_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
        SecondOrderGraph.eq_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
          ∃ m, SecondOrderOrder.lt_l m n ∧
            SecondOrderGraph.eq_l X (SecondOrderOrdinalTailGraph.code_l hℳ hG hS m) := by
  have hOld (a : num_l ℳ) : SecondOrderBisimulation.eq_l S G a (value_l (zero_l ℳ) a) :=
    SecondOrderPairSet.tag_eq_l hℳ _ S G (SecondOrderOrdinalTailGraph.fiber_l hℳ hG) a
  constructor
  · rintro ⟨x, hx, hX⟩
    rcases (SecondOrderOrdinalTailGraph.tail_edge_l hℳ hG x n).mp hx with
      ⟨a, ha, hAr⟩ | ⟨m, hm, hmn⟩
    · have hXa := SecondOrderBisimulation.trans_l hℳ X.real G S X.root _ a
        (ha.symm ▸ hX) (SecondOrderBisimulation.symm_l hℳ S G a _ (hOld a))
      rcases hAr with hAr | hAr
      · exact Or.inl ⟨a, hAr, hXa⟩
      · exact Or.inr (Or.inl (hAr ▸ hXa))
    · have hXm : SecondOrderGraph.eq_l X (SecondOrderOrdinalTailGraph.code_l hℳ hG hS m) := by
        change SecondOrderBisimulation.eq_l X.real G X.root (value_l (succ_l (zero_l ℳ)) m)
        rw [hm]
        exact hX
      exact Or.inr (Or.inr ⟨m, hmn, hXm⟩)
  · rintro (⟨a, ha, hXa⟩ | hXr | ⟨m, hmn, hXm⟩)
    · exact ⟨value_l (zero_l ℳ) a,
        (SecondOrderOrdinalTailGraph.tail_edge_l hℳ hG _ n).mpr (Or.inl ⟨a, rfl, Or.inl ha⟩),
        SecondOrderBisimulation.trans_l hℳ X.real S G X.root a _ hXa (hOld a)⟩
    · exact ⟨value_l (zero_l ℳ) r,
        (SecondOrderOrdinalTailGraph.tail_edge_l hℳ hG _ n).mpr (Or.inl ⟨r, rfl, Or.inr rfl⟩),
        SecondOrderBisimulation.trans_l hℳ X.real S G X.root r _ hXr (hOld r)⟩
    · exact ⟨value_l (succ_l (zero_l ℳ)) m,
        (SecondOrderOrdinalTailGraph.tail_edge_l hℳ hG _ n).mpr (Or.inr ⟨m, rfl, hmn⟩), hXm⟩

theorem successor_l (n : num_l ℳ) (X : SecondOrderGraph.code_l ℳ) :
    SecondOrderGraph.mem_l X (SecondOrderOrdinalTailGraph.code_l hℳ hG hS (succ_l n)) ↔
      SecondOrderGraph.mem_l X (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n) ∨
        SecondOrderGraph.eq_l X (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n) := by
  rw [members_l hℳ hG hS]
  constructor
  · rintro (hX | hX | ⟨m, hm, hXm⟩)
    · exact Or.inl ((members_l hℳ hG hS n X).mpr (Or.inl hX))
    · exact Or.inl ((members_l hℳ hG hS n X).mpr (Or.inr (Or.inl hX)))
    · rcases (lt_succ_l hℳ m n).mp hm with hm | rfl
      · exact Or.inl ((members_l hℳ hG hS n X).mpr (Or.inr (Or.inr ⟨m, hm, hXm⟩)))
      · exact Or.inr hXm
  · rintro (hX | hX)
    · rcases (members_l hℳ hG hS n X).mp hX with hX | hX | ⟨m, hm, hXm⟩
      · exact Or.inl hX
      · exact Or.inr (Or.inl hX)
      · exact Or.inr (Or.inr ⟨m, (lt_succ_l hℳ m n).mpr (Or.inl hm), hXm⟩)
    · exact Or.inr (Or.inr ⟨n, (lt_succ_l hℳ n n).mpr (Or.inr rfl), hX⟩)

#print axioms members_l
#print axioms successor_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailMembers
