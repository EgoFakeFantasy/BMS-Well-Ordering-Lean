import BMSConstructibleBridge.SecondOrderOrdinalBudgetGraph
import BMSConstructibleBridge.SecondOrderOrdinalSuccessor

/-! # 规范序数前驱图上的预算成员与序数性

预算图的构造本身允许任意内部良基指标图。本模块在实际指标域 D 上消费
传递性、线性和坐标界；这些性质由原 RootOrdinalRelation 的规范最小数
代表图真实提供，不是宿主层的外部序数良基假设。预算尾的全部成员恰为
起点 ξ 的成员与字典序较早的尾根。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalBudgetOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderOrdinalBudgetGraph
open SecondOrderOrdinalDoubleTailGraph (root_l)
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

abbrev quotient_l (hℳ : Theory.Models ℳ theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem lex_trans_l {R : set_l ℳ}
    (hTrans : ∀ i j k, SecondOrderPairing.relation_l R i j →
      SecondOrderPairing.relation_l R j k → SecondOrderPairing.relation_l R i k)
    (hℳ : Theory.Models ℳ theory_m) {i j k l n m : num_l ℳ}
    (h₁ : lex_l R i j k l) (h₂ : lex_l R k l n m) : lex_l R i j n m := by
  rcases h₁ with h₁ | ⟨rfl, h₁⟩
  · rcases h₂ with h₂ | ⟨rfl, _⟩
    · exact Or.inl (hTrans i k n h₁ h₂)
    · exact Or.inl h₁
  · rcases h₂ with h₂ | ⟨rfl, h₂⟩
    · exact Or.inl h₂
    · exact Or.inr ⟨rfl, SecondOrderOrder.trans_l hℳ h₁ h₂⟩

theorem lex_compare_l (hℳ : Theory.Models ℳ theory_m) {R D : set_l ℳ}
    (hCompare : ∀ n i, SecondOrderModel.mem_l n D → SecondOrderModel.mem_l i D →
      SecondOrderPairing.relation_l R n i ∨ n = i ∨ SecondOrderPairing.relation_l R i n)
    (n m i j : num_l ℳ) (hn : SecondOrderModel.mem_l n D) (hi : SecondOrderModel.mem_l i D) :
    lex_l R n m i j ∨ (n = i ∧ m = j) ∨ lex_l R i j n m := by
  rcases hCompare n i hn hi with h | rfl | h
  · exact Or.inl (Or.inl h)
  · rcases SecondOrderOrder.trichotomy_l hℳ m j with h | rfl | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inl h))

variable (hℳ : Theory.Models ℳ theory_m) {S R G : set_l ℳ} {r : num_l ℳ}
  (hG : spec_l S r R G) (hS : ∀ a, SecondOrderDomain.wf_l S a)
  (hR : ∀ a, SecondOrderDomain.wf_l R a)

noncomputable abbrev base_l (r : num_l ℳ) : type_l hℳ := mk_l hℳ ⟨S, r, hS r⟩

noncomputable abbrev tail_l (n m : num_l ℳ) : type_l hℳ :=
  mk_l hℳ (code_l hℳ hG hS n (hR n) m)

theorem members_l (n m : num_l ℳ) (X : SecondOrderGraph.code_l ℳ) :
    SecondOrderGraph.mem_l X (code_l hℳ hG hS n (hR n) m) ↔
      SecondOrderGraph.mem_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
        ∃ i j, lex_l R i j n m ∧
          SecondOrderGraph.eq_l X (code_l hℳ hG hS i (hR i) j) := by
  have hOld (a : num_l ℳ) : SecondOrderBisimulation.eq_l S G a
      (SecondOrderPairing.value_l (zero_l ℳ) a) :=
    SecondOrderPairSet.tag_eq_l hℳ _ S G (fiber_l hℳ hG) a
  constructor
  · rintro ⟨x, hx, hX⟩
    rcases (tail_edge_l hℳ hG x n m).mp hx with
      ⟨a, ha, hAr⟩ | ⟨i, j, hij, hOrder⟩
    · exact Or.inl ⟨a, hAr,
        SecondOrderBisimulation.trans_l hℳ X.real G S X.root _ a
          (ha.symm ▸ hX) (SecondOrderBisimulation.symm_l hℳ S G a _ (hOld a))⟩
    · exact Or.inr ⟨i, j, hOrder, by
        change SecondOrderBisimulation.eq_l X.real G X.root (root_l i j)
        rw [hij]
        exact hX⟩
  · rintro (⟨a, ha, hXa⟩ | ⟨i, j, hOrder, hXij⟩)
    · exact ⟨SecondOrderPairing.value_l (zero_l ℳ) a,
        (tail_edge_l hℳ hG _ n m).mpr (Or.inl ⟨a, rfl, ha⟩),
        SecondOrderBisimulation.trans_l hℳ X.real S G X.root a _ hXa (hOld a)⟩
    · exact ⟨root_l i j,
        (tail_edge_l hℳ hG _ n m).mpr (Or.inr ⟨i, j, rfl, hOrder⟩), hXij⟩

theorem reading_l (n m : num_l ℳ) (x : type_l hℳ) :
    mem_l hℳ x (tail_l hℳ hG hS hR n m) ↔
      mem_l hℳ x (base_l hℳ hS r) ∨
        ∃ i j, lex_l R i j n m ∧ x = tail_l hℳ hG hS hR i j := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact (members_l hℳ hG hS hR n m X).trans
    (or_congr Iff.rfl (exists_congr (fun _ => exists_congr (fun _ =>
      and_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ _ _).symm))))

/-- 指标严格较早时，该块的每个内部有限尾都低于较后块的零根。 -/
theorem earlier_l {i n : num_l ℳ} (hin : SecondOrderPairing.relation_l R i n)
    (j m : num_l ℳ) :
    mem_l hℳ (tail_l hℳ hG hS hR i j) (tail_l hℳ hG hS hR n m) :=
  (reading_l hℳ hG hS hR n m _).mpr (Or.inr ⟨i, j, Or.inl hin, rfl⟩)

variable (hξ : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (base_l hℳ hS r))
  (hTrans : ∀ i j k, SecondOrderPairing.relation_l R i j →
    SecondOrderPairing.relation_l R j k → SecondOrderPairing.relation_l R i k)

include hξ hTrans

theorem transitive_l (n m : num_l ℳ) (x : type_l hℳ)
    (hx : mem_l hℳ x (tail_l hℳ hG hS hR n m))
    (y : type_l hℳ) (hy : mem_l hℳ y x) : mem_l hℳ y (tail_l hℳ hG hS hR n m) := by
  apply (reading_l hℳ hG hS hR n m y).mpr
  rcases (reading_l hℳ hG hS hR n m x).mp hx with hx | ⟨i, j, hij, rfl⟩
  · exact Or.inl (hξ.transitive x hx y hy)
  · rcases (reading_l hℳ hG hS hR i j y).mp hy with hy | ⟨k, l, hkl, hy⟩
    · exact Or.inl hy
    · exact Or.inr ⟨k, l, lex_trans_l hTrans hℳ hkl hij, hy⟩

variable {D : set_l ℳ}
  (hEnds : ∀ i n, SecondOrderPairing.relation_l R i n →
    SecondOrderModel.mem_l i D ∧ SecondOrderModel.mem_l n D)
  (hCompare : ∀ n i, SecondOrderModel.mem_l n D → SecondOrderModel.mem_l i D →
    SecondOrderPairing.relation_l R n i ∨ n = i ∨ SecondOrderPairing.relation_l R i n)

include hCompare

theorem linear_l (C : type_l hℳ)
    (hTypes : ∀ x, mem_l hℳ x C → mem_l hℳ x (base_l hℳ hS r) ∨
      ∃ n m, SecondOrderModel.mem_l n D ∧ x = tail_l hℳ hG hS hR n m) :
    SetTheory.Structure.MembershipLinearOrder (quotient_l hℳ) C := by
  constructor
  · intro x _ hx
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact SecondOrderFoundation.irrefl_l hℳ X hx
  · intro x _ y _ z hz hxy hyz
    rcases hTypes z hz with hz | ⟨n, m, _, rfl⟩
    · have hZ : SetTheory.Structure.IsOrdinal (quotient_l hℳ) z := by
        apply SetTheory.Structure.IsOrdinal.mem hξ
        exact hz
      exact hZ.transitive y hyz x hxy
    · exact transitive_l hℳ hG hS hR hξ hTrans n m y hyz x hxy
  · intro x hx y hy
    rcases hTypes x hx with hx | ⟨n, m, hn, rfl⟩
    · rcases hTypes y hy with hy | ⟨i, j, hi, rfl⟩
      · exact hξ.wellOrder.linear.compare x hx y hy
      · exact Or.inr (Or.inl ((reading_l hℳ hG hS hR i j x).mpr (Or.inl hx)))
    · rcases hTypes y hy with hy | ⟨i, j, hi, rfl⟩
      · exact Or.inr (Or.inr ((reading_l hℳ hG hS hR n m y).mpr (Or.inl hy)))
      · rcases lex_compare_l hℳ hCompare n m i j hn hi with h | ⟨rfl, rfl⟩ | h
        · exact Or.inr (Or.inl ((reading_l hℳ hG hS hR i j _).mpr (Or.inr ⟨n, m, h, rfl⟩)))
        · exact Or.inl (fun _ => Iff.rfl)
        · exact Or.inr (Or.inr ((reading_l hℳ hG hS hR n m _).mpr (Or.inr ⟨i, j, h, rfl⟩)))

include hEnds

theorem ordinal_l (n m : num_l ℳ) (hn : SecondOrderModel.mem_l n D) :
    SetTheory.Structure.IsOrdinal (quotient_l hℳ) (tail_l hℳ hG hS hR n m) := by
  apply SecondOrderOrdinalSuccessor.ordinal_of_linear_l hℳ (code_l hℳ hG hS n (hR n) m)
  · exact fun X Y hX hY => transitive_l hℳ hG hS hR hξ hTrans n m
      (mk_l hℳ X) hX (mk_l hℳ Y) hY
  · apply linear_l hℳ hG hS hR hξ hTrans hCompare
    intro x hx
    rcases (reading_l hℳ hG hS hR n m x).mp hx with hx | ⟨i, j, hij, hx⟩
    · exact Or.inl hx
    · refine Or.inr ⟨i, j, ?_, hx⟩
      rcases hij with hi | ⟨rfl, _⟩
      · exact (hEnds i n hi).1
      · exact hn

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalBudgetOrder
