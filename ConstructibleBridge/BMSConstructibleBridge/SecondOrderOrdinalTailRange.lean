import BMSConstructibleBridge.SecondOrderOrdinalTailMembers

/-! # 基础序数与全部内部尾节点的实际集合包络

理解得到全部指定根的实数，再拼接已证明内部无下降链的图。
精确成员包括基础根及其成员，不能只收集尾节点后误称所得集合传递。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailRange

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  .app (σ := signature_m) .zero .nil
private def one_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  .app (σ := signature_m) .succ (.cons zero_m .nil)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : SecondOrderOrdinalTailGraph.spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a) :
    ∃ C : SecondOrderGraph.code_l ℳ, ∀ X : SecondOrderGraph.code_l ℳ,
      SecondOrderGraph.mem_l X C ↔
        SecondOrderGraph.mem_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
          SecondOrderGraph.eq_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
            ∃ m, SecondOrderGraph.eq_l X (SecondOrderOrdinalTailGraph.code_l hℳ hG hS m) := by
  let φ : Formula signature_m [] [.num, .set, .num] := .disj
    (.existsE .num (.conj (PrimitiveFormulas.pair_m zero_m (.bvar .here) (.fvar .here))
      (.disj (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar .here) (.fvar (.there (.there .here))))
        (.equal (.bvar .here) (.fvar (.there (.there .here)))))))
    (.existsE .num (PrimitiveFormulas.pair_m one_m (.bvar .here) (.fvar .here)))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree r).pushFree S)
  have hRead (x : num_l ℳ) : mem_l x P ↔
      (∃ a, value_l (zero_l ℳ) a = x ∧ (relation_l S a r ∨ a = r)) ∨
        ∃ m, value_l (succ_l (zero_l ℳ)) m = x := by
    refine (hP x).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l,
      one_m, zero_m, Term.eval]
    rfl
  obtain ⟨C, hC⟩ := SecondOrderGraftSemantics.exists_l hℳ G P
    (fun x _ => SecondOrderOrdinalTailGraph.wf_l hℳ hG hS x)
  have hOld (a : num_l ℳ) : SecondOrderBisimulation.eq_l S G a (value_l (zero_l ℳ) a) :=
    SecondOrderPairSet.tag_eq_l hℳ _ S G (SecondOrderOrdinalTailGraph.fiber_l hℳ hG) a
  refine ⟨C, fun X => (hC X).trans ?_⟩
  constructor
  · rintro ⟨x, hx, hX⟩
    rcases (hRead x).mp hx with ⟨a, ha, hAr⟩ | ⟨m, hm⟩
    · have hXa := SecondOrderBisimulation.trans_l hℳ X.real G S X.root _ a
        (ha.symm ▸ hX) (SecondOrderBisimulation.symm_l hℳ S G a _ (hOld a))
      rcases hAr with hAr | hAr
      · exact Or.inl ⟨a, hAr, hXa⟩
      · exact Or.inr (Or.inl (hAr ▸ hXa))
    · have hXm : SecondOrderGraph.eq_l X (SecondOrderOrdinalTailGraph.code_l hℳ hG hS m) := by
        change SecondOrderBisimulation.eq_l X.real G X.root (value_l (succ_l (zero_l ℳ)) m)
        rw [hm]
        exact hX
      exact Or.inr (Or.inr ⟨m, hXm⟩)
  · rintro (⟨a, ha, hXa⟩ | hXr | ⟨m, hXm⟩)
    · exact ⟨value_l (zero_l ℳ) a, (hRead _).mpr (Or.inl ⟨a, rfl, Or.inl ha⟩),
        SecondOrderBisimulation.trans_l hℳ X.real S G X.root a _ hXa (hOld a)⟩
    · exact ⟨value_l (zero_l ℳ) r, (hRead _).mpr (Or.inl ⟨r, rfl, Or.inr rfl⟩),
        SecondOrderBisimulation.trans_l hℳ X.real S G X.root r _ hXr (hOld r)⟩
    · exact ⟨value_l (succ_l (zero_l ℳ)) m, (hRead _).mpr (Or.inr ⟨m, rfl⟩), hXm⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailRange
