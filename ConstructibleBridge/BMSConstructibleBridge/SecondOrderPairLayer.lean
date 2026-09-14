import BMSConstructibleBridge.SecondOrderPairSet
import BMSConstructibleBridge.SecondOrderDomainClosure

/-!
# 同一内部关系的统一配对层

旧节点带零标签；每对旧根对应一个一标签新根，其子节点恰为两旧根的副本。
整层由一条实际理解公式产生，不为各对分别选择关系实数后假定能收集其族。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairLayer

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

noncomputable def old_l (a : num_l ℳ) : num_l ℳ := value_l (zero_l ℳ) a

noncomputable def pair_l (a b : num_l ℳ) : num_l ℳ := value_l (succ_l (zero_l ℳ)) (value_l a b)

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def one {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons zero .nil)

/-- 自由槽位为子节点、母节点、原关系。 -/
def formula_m : Formula signature_m [] [.num, .num, .set] :=
  .disj
    (.existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m zero (.bvar (.there .here)) (.fvar .here))
      (.conj (PrimitiveFormulas.pair_m zero (.bvar .here) (.fvar (.there .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))))))
    (.existsE .num (.existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
      (.conj (PrimitiveFormulas.pair_m one (.bvar .here) (.fvar (.there .here)))
        (.disj (PrimitiveFormulas.pair_m zero (.bvar (.there (.there .here))) (.fvar .here))
          (PrimitiveFormulas.pair_m zero (.bvar (.there .here)) (.fvar .here))))))))

structure spec_l (R G : set_l ℳ) : Prop where
  base : SecondOrderTaggedGraph.fiber_l (zero_l ℳ) R G
  pair : ∀ a b c, relation_l G c (pair_l a b) ↔ c = old_l a ∨ c = old_l b

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) : ∃ G, spec_l R G := by
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ formula_m (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree R)
  have h : ∀ c d, relation_l G c d ↔
      (∃ a b, old_l a = c ∧ old_l b = d ∧ relation_l R a b) ∨
      (∃ a b p, value_l a b = p ∧ value_l (succ_l (zero_l ℳ)) p = d ∧
        (old_l a = c ∨ old_l b = c)) := by
    intro c d
    refine (hG c d).trans ?_
    simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l]
    rfl
  refine ⟨G, ?_, ?_⟩
  · intro c k
    rw [h]
    constructor
    · rintro (⟨a, b, hc, hd, hR⟩ | ⟨a, b, p, _, hd, _⟩)
      · have h₁ := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).2
        subst b
        exact ⟨a, hc.symm, hR⟩
      · exact False.elim (nonzero_l hℳ (zero_l ℳ)
          (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).1)
    · rintro ⟨a, rfl, hR⟩
      exact Or.inl ⟨a, k, rfl, rfl, hR⟩
  · intro a b c
    rw [h]
    constructor
    · rintro (⟨d, e, _, h₁, _⟩ | ⟨d, e, p, hp, h₁, h₂⟩)
      · exact False.elim (nonzero_l hℳ (zero_l ℳ)
          (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ h₁).1.symm)
      · have h₃ := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ h₁).2
        have h₄ := SecondOrderPairingBounds.injective_l hℳ _ _ _ _ (hp.trans h₃)
        obtain ⟨rfl, rfl⟩ := h₄
        exact h₂.imp Eq.symm Eq.symm
    · intro h₁
      exact Or.inr ⟨a, b, value_l a b, rfl, rfl, h₁.imp Eq.symm Eq.symm⟩

theorem old_wf_l (hℳ : Theory.Models ℳ theory_m) (R G : set_l ℳ) (hG : spec_l R G)
    (a : num_l ℳ) (ha : SecondOrderDomain.wf_l R a) : SecondOrderDomain.wf_l G (old_l a) :=
  SecondOrderTaggedDomain.wf_l hℳ (zero_l ℳ) R G hG.base a ha

theorem pair_wf_l (hℳ : Theory.Models ℳ theory_m) (R G : set_l ℳ) (hG : spec_l R G)
    (a b : num_l ℳ) (ha : SecondOrderDomain.wf_l R a) (hb : SecondOrderDomain.wf_l R b) :
    SecondOrderDomain.wf_l G (pair_l a b) := by
  apply SecondOrderDomainClosure.intro_l hℳ
  intro c hc
  rcases (hG.pair a b c).mp hc with rfl | rfl
  · exact old_wf_l hℳ R G hG a ha
  · exact old_wf_l hℳ R G hG b hb

noncomputable def code_l (hℳ : Theory.Models ℳ theory_m) (R G : set_l ℳ) (hG : spec_l R G)
    (a b : num_l ℳ) (ha : SecondOrderDomain.wf_l R a) (hb : SecondOrderDomain.wf_l R b) :
    SecondOrderGraph.code_l ℳ := ⟨G, pair_l a b, pair_wf_l hℳ R G hG a b ha hb⟩

/-- 原根到副本的内部双模拟与根参数一致。 -/
theorem old_eq_l (hℳ : Theory.Models ℳ theory_m) (R G : set_l ℳ) (hG : spec_l R G)
    (a : num_l ℳ) : SecondOrderBisimulation.eq_l R G a (old_l a) :=
  SecondOrderPairSet.tag_eq_l hℳ (zero_l ℳ) R G hG.base a

theorem mem_l (hℳ : Theory.Models ℳ theory_m) (R G : set_l ℳ) (hG : spec_l R G)
    (a b : num_l ℳ) (ha : SecondOrderDomain.wf_l R a) (hb : SecondOrderDomain.wf_l R b)
    (D : SecondOrderGraph.code_l ℳ) :
    SecondOrderGraph.mem_l D (code_l hℳ R G hG a b ha hb) ↔
      SecondOrderGraph.eq_l D ⟨R, a, ha⟩ ∨ SecondOrderGraph.eq_l D ⟨R, b, hb⟩ := by
  constructor
  · rintro ⟨c, hc, h⟩
    rcases (hG.pair a b c).mp hc with rfl | rfl
    · exact Or.inl (SecondOrderBisimulation.trans_l hℳ D.real G R D.root _ a h
        (SecondOrderBisimulation.symm_l hℳ R G a _ (old_eq_l hℳ R G hG a)))
    · exact Or.inr (SecondOrderBisimulation.trans_l hℳ D.real G R D.root _ b h
        (SecondOrderBisimulation.symm_l hℳ R G b _ (old_eq_l hℳ R G hG b)))
  · rintro (h | h)
    · exact ⟨old_l a, (hG.pair a b _).mpr (Or.inl rfl),
        SecondOrderBisimulation.trans_l hℳ D.real R G D.root a _ h (old_eq_l hℳ R G hG a)⟩
    · exact ⟨old_l b, (hG.pair a b _).mpr (Or.inr rfl),
        SecondOrderBisimulation.trans_l hℳ D.real R G D.root b _ h (old_eq_l hℳ R G hG b)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairLayer
