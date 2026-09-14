import BMSConstructibleBridge.SecondOrderPairLayer

/-!
# 同一内部图上的统一子集层

每个内部索引对应一个新根，其子节点由同一内部关系 F 的该行选出。
所有新根只指向母根的旧子节点副本，不对集合族使用选择或收集公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetLayer

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderPairLayer (old_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

noncomputable def root_l (i : num_l ℳ) : num_l ℳ := value_l (succ_l (zero_l ℳ)) i

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def one {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons zero .nil)

def formula_m : Formula signature_m [] [.num, .num, .set, .set, .num] :=
  .disj
    (.existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m zero (.bvar (.there .here)) (.fvar .here))
      (.conj (PrimitiveFormulas.pair_m zero (.bvar .here) (.fvar (.there .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))))))
    (.existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m zero (.bvar (.there .here)) (.fvar .here))
      (.conj (PrimitiveFormulas.pair_m one (.bvar .here) (.fvar (.there .here)))
        (.conj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here))
          (.fvar (.there (.there (.there (.there .here))))))
          (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.bvar .here) (.bvar (.there .here))))))))

structure spec_l (R F : set_l ℳ) (r : num_l ℳ) (G : set_l ℳ) : Prop where
  base : SecondOrderTaggedGraph.fiber_l (zero_l ℳ) R G
  slice : ∀ i c, relation_l G c (root_l i) ↔ ∃ a, c = old_l a ∧ relation_l R a r ∧ relation_l F i a

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R F : set_l ℳ) (r : num_l ℳ) : ∃ G, spec_l R F r G := by
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ formula_m (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree r).pushFree F).pushFree R)
  have h (c d : num_l ℳ) : relation_l G c d ↔
      (∃ a b, old_l a = c ∧ old_l b = d ∧ relation_l R a b) ∨
        (∃ a i, old_l a = c ∧ root_l i = d ∧ relation_l R a r ∧ relation_l F i a) := by
    refine (hG c d).trans ?_
    simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l]
    rfl
  refine ⟨G, ?_, ?_⟩
  · intro c b
    rw [h]
    constructor
    · rintro (⟨a, d, hc, hd, hR⟩ | ⟨a, i, _, hd, _⟩)
      · have h₀ := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).2
        subst d
        exact ⟨a, hc.symm, hR⟩
      · exact False.elim (nonzero_l hℳ (zero_l ℳ) (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).1)
    · rintro ⟨a, rfl, hR⟩
      exact Or.inl ⟨a, b, rfl, rfl, hR⟩
  · intro i c
    rw [h]
    constructor
    · rintro (⟨a, b, _, hb, _⟩ | ⟨a, j, ha, hj, hR, hF⟩)
      · exact False.elim (nonzero_l hℳ (zero_l ℳ) (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hb).1.symm)
      · have h₀ := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hj).2
        subst j
        exact ⟨a, ha.symm, hR, hF⟩
    · rintro ⟨a, rfl, hR, hF⟩
      exact Or.inr ⟨a, i, rfl, rfl, hR, hF⟩

theorem wf_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) (F G : set_l ℳ)
    (hG : spec_l A.real F A.root G) (i : num_l ℳ) : SecondOrderDomain.wf_l G (root_l i) := by
  apply SecondOrderDomainClosure.intro_l hℳ
  intro c hc
  obtain ⟨a, rfl, ha, _⟩ := (hG.slice i c).mp hc
  exact SecondOrderTaggedDomain.wf_l hℳ (zero_l ℳ) A.real G hG.base a
    (SecondOrderDomain.child_l hℳ A.real A.root a A.wf ha)

noncomputable def code_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) (F G : set_l ℳ)
    (hG : spec_l A.real F A.root G) (i : num_l ℳ) : SecondOrderGraph.code_l ℳ :=
  ⟨G, root_l i, wf_l hℳ A F G hG i⟩

theorem mem_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) (F G : set_l ℳ)
    (hG : spec_l A.real F A.root G) (i : num_l ℳ) (B : SecondOrderGraph.code_l ℳ) :
    SecondOrderGraph.mem_l B (code_l hℳ A F G hG i) ↔ ∃ a,
      relation_l A.real a A.root ∧ relation_l F i a ∧ SecondOrderBisimulation.eq_l B.real A.real B.root a := by
  have h (a : num_l ℳ) : SecondOrderBisimulation.eq_l A.real G a (old_l a) :=
    SecondOrderPairSet.tag_eq_l hℳ (zero_l ℳ) A.real G hG.base a
  constructor
  · rintro ⟨c, hc, hB⟩
    obtain ⟨a, rfl, ha, hF⟩ := (hG.slice i c).mp hc
    exact ⟨a, ha, hF, SecondOrderBisimulation.trans_l hℳ B.real G A.real B.root _ a hB
      (SecondOrderBisimulation.symm_l hℳ A.real G a _ (h a))⟩
  · rintro ⟨a, ha, hF, hB⟩
    exact ⟨old_l a, (hG.slice i _).mpr ⟨a, rfl, ha, hF⟩,
      SecondOrderBisimulation.trans_l hℳ B.real A.real G B.root a _ hB (h a)⟩

theorem subset_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) (F G : set_l ℳ)
    (hG : spec_l A.real F A.root G) (i : num_l ℳ) (B : SecondOrderGraph.code_l ℳ)
    (hB : SecondOrderGraph.mem_l B (code_l hℳ A F G hG i)) : SecondOrderGraph.mem_l B A := by
  obtain ⟨a, ha, _, h⟩ := (mem_l hℳ A F G hG i B).mp hB
  exact ⟨a, ha, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetLayer
