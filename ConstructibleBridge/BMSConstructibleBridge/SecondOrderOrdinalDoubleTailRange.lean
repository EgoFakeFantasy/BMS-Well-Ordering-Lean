import BMSConstructibleBridge.SecondOrderOrdinalDoubleTailMembers

/-! # ω² 尾图的实际集合包络

一次原理解选出基础成员、基础根与全部双指标尾节点，再用内部有效图拼接。
不能只收集每块的起点，否则所得集合不具有所需传递性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalDoubleTailRange

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderOrdinalDoubleTailGraph

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  .app (σ := signature_m) .zero .nil

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a) :
    ∃ C : SecondOrderGraph.code_l ℳ, ∀ X : SecondOrderGraph.code_l ℳ,
      SecondOrderGraph.mem_l X C ↔
        SecondOrderGraph.mem_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
          SecondOrderGraph.eq_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
            ∃ n m, SecondOrderGraph.eq_l X (code_l hℳ hG hS n m) := by
  let φ : Formula signature_m [] [.num, .set, .num] := .disj
    (.existsE .num (.conj (PrimitiveFormulas.pair_m zero_m (.bvar .here) (.fvar .here))
      (.disj (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar .here) (.fvar (.there (.there .here))))
        (.equal (.bvar .here) (.fvar (.there (.there .here)))))))
    (.existsE .num (.existsE .num (root_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))))
  have hPure : language_m φ = true := by
    change (true && _) = true
    exact root_language_m _ _ _ rfl rfl rfl
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ hPure
    (((Env.empty (M := ℳ)).pushFree r).pushFree S)
  have hRead (x : num_l ℳ) : mem_l x P ↔
      (∃ a, value_l (zero_l ℳ) a = x ∧ (relation_l S a r ∨ a = r)) ∨
        ∃ n m, root_l n m = x := by
    refine (hP x).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l,
      root_formula_l, zero_m, Term.eval]
    rfl
  obtain ⟨C, hC⟩ := SecondOrderGraftSemantics.exists_l hℳ G P
    (fun x _ => wf_l hℳ hG hS x)
  have hOld (a : num_l ℳ) : SecondOrderBisimulation.eq_l S G a (value_l (zero_l ℳ) a) :=
    SecondOrderPairSet.tag_eq_l hℳ _ S G (fiber_l hℳ hG) a
  refine ⟨C, fun X => (hC X).trans ?_⟩
  constructor
  · rintro ⟨x, hx, hX⟩
    rcases (hRead x).mp hx with ⟨a, ha, hAr⟩ | ⟨n, m, hnm⟩
    · have hXa := SecondOrderBisimulation.trans_l hℳ X.real G S X.root _ a
        (ha.symm ▸ hX) (SecondOrderBisimulation.symm_l hℳ S G a _ (hOld a))
      rcases hAr with hAr | hAr
      · exact Or.inl ⟨a, hAr, hXa⟩
      · exact Or.inr (Or.inl (hAr ▸ hXa))
    · have hXnm : SecondOrderGraph.eq_l X (code_l hℳ hG hS n m) := by
        change SecondOrderBisimulation.eq_l X.real G X.root (root_l n m)
        rw [hnm]
        exact hX
      exact Or.inr (Or.inr ⟨n, m, hXnm⟩)
  · rintro (⟨a, ha, hXa⟩ | hXr | ⟨n, m, hXnm⟩)
    · exact ⟨value_l (zero_l ℳ) a, (hRead _).mpr (Or.inl ⟨a, rfl, Or.inl ha⟩),
        SecondOrderBisimulation.trans_l hℳ X.real S G X.root a _ hXa (hOld a)⟩
    · exact ⟨value_l (zero_l ℳ) r, (hRead _).mpr (Or.inl ⟨r, rfl, Or.inr rfl⟩),
        SecondOrderBisimulation.trans_l hℳ X.real S G X.root r _ hXr (hOld r)⟩
    · exact ⟨root_l n m, (hRead _).mpr (Or.inr ⟨n, m, rfl⟩), hXnm⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalDoubleTailRange
