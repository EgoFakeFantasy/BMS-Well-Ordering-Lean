import BMSConstructibleBridge.SecondOrderOrdinalDoubleTailGraph

/-! # 内部 ω² 尾节点的精确成员

基础图由同一标签双模拟保持，新增成员恰为字典序严格较早的尾节点。
这里不预设尾节点为序数，也不使用模型数的外部良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalDoubleTailMembers

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderOrdinalDoubleTailGraph

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem members_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a)
    (n m : num_l ℳ) (X : SecondOrderGraph.code_l ℳ) :
    SecondOrderGraph.mem_l X (code_l hℳ hG hS n m) ↔
      SecondOrderGraph.mem_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
        SecondOrderGraph.eq_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
          ∃ i j, lex_l i j n m ∧ SecondOrderGraph.eq_l X (code_l hℳ hG hS i j) := by
  have hOld (a : num_l ℳ) : SecondOrderBisimulation.eq_l S G a (value_l (zero_l ℳ) a) :=
    SecondOrderPairSet.tag_eq_l hℳ _ S G (fiber_l hℳ hG) a
  constructor
  · rintro ⟨x, hx, hX⟩
    rcases (tail_edge_l hℳ hG x n m).mp hx with
      ⟨a, ha, hAr⟩ | ⟨i, j, hij, hOrder⟩
    · have hXa := SecondOrderBisimulation.trans_l hℳ X.real G S X.root _ a
        (ha.symm ▸ hX) (SecondOrderBisimulation.symm_l hℳ S G a _ (hOld a))
      rcases hAr with hAr | hAr
      · exact Or.inl ⟨a, hAr, hXa⟩
      · exact Or.inr (Or.inl (hAr ▸ hXa))
    · have hXij : SecondOrderGraph.eq_l X (code_l hℳ hG hS i j) := by
        change SecondOrderBisimulation.eq_l X.real G X.root (root_l i j)
        rw [hij]
        exact hX
      exact Or.inr (Or.inr ⟨i, j, hOrder, hXij⟩)
  · rintro (⟨a, ha, hXa⟩ | hXr | ⟨i, j, hOrder, hXij⟩)
    · exact ⟨value_l (zero_l ℳ) a,
        (tail_edge_l hℳ hG _ n m).mpr (Or.inl ⟨a, rfl, Or.inl ha⟩),
        SecondOrderBisimulation.trans_l hℳ X.real S G X.root a _ hXa (hOld a)⟩
    · exact ⟨value_l (zero_l ℳ) r,
        (tail_edge_l hℳ hG _ n m).mpr (Or.inl ⟨r, rfl, Or.inr rfl⟩),
        SecondOrderBisimulation.trans_l hℳ X.real S G X.root r _ hXr (hOld r)⟩
    · exact ⟨root_l i j, (tail_edge_l hℳ hG _ n m).mpr (Or.inr ⟨i, j, rfl, hOrder⟩), hXij⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalDoubleTailMembers
