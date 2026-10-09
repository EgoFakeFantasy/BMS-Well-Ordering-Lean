import BMSConstructibleBridge.SecondOrderSubsetLayer

/-! # 子集层图的完整边规格与实数唯一性

原子集层接口只约束旧纤维和切片根。递归要求确定整个实数，故这里还约束
其余所有节点的边；不能仅由商对象外延性宣称原实数编码唯一。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalSubsetLayer

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderPairLayer (old_l)
open SecondOrderSubsetLayer (root_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def edge_l (R F : set_l ℳ) (r c d : num_l ℳ) : Prop :=
  (∃ a b, old_l a = c ∧ old_l b = d ∧ relation_l R a b) ∨
    (∃ a i, old_l a = c ∧ root_l i = d ∧ relation_l R a r ∧ relation_l F i a)

def spec_l (R F : set_l ℳ) (r : num_l ℳ) (G : set_l ℳ) : Prop :=
  ∀ c d, relation_l G c d ↔ edge_l R F r c d

theorem formula_l (R F : set_l ℳ) (r c d : num_l ℳ) :
    SecondOrderSubsetLayer.formula_m.satisfies
      ((((((Env.empty (M := ℳ)).pushFree r).pushFree F).pushFree R).pushFree d).pushFree c) ↔
      edge_l R F r c d := by
  simp only [SecondOrderSubsetLayer.formula_m, Formula.satisfies,
    SecondOrderPairing.formula_l, SecondOrderPairing.edge_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R F : set_l ℳ) (r : num_l ℳ) :
    ∃! G, spec_l R F r G := by
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ SecondOrderSubsetLayer.formula_m
    (pure_language_m _ rfl) ((((Env.empty (M := ℳ)).pushFree r).pushFree F).pushFree R)
  have h : spec_l R F r G := fun c d => (hG c d).trans (formula_l R F r c d)
  exact ⟨G, h, fun H hH => SecondOrderRelations.ext_l hℳ H G
    (fun c d => (hH c d).trans (h c d).symm)⟩

theorem layer_l (hℳ : Theory.Models ℳ theory_m) {R F G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l R F r G) : SecondOrderSubsetLayer.spec_l R F r G := by
  refine ⟨?_, ?_⟩
  · intro c b
    rw [hG]
    constructor
    · rintro (⟨a, d, hc, hd, hR⟩ | ⟨a, i, _, hd, _⟩)
      · have h₀ := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).2
        subst d
        exact ⟨a, hc.symm, hR⟩
      · exact False.elim (nonzero_l hℳ (zero_l ℳ)
          (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).1)
    · rintro ⟨a, rfl, hR⟩
      exact Or.inl ⟨a, b, rfl, rfl, hR⟩
  · intro i c
    rw [hG]
    constructor
    · rintro (⟨a, b, _, hb, _⟩ | ⟨a, j, ha, hj, hR, hF⟩)
      · exact False.elim (nonzero_l hℳ (zero_l ℳ)
          (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hb).1.symm)
      · have h₀ := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hj).2
        subst j
        exact ⟨a, ha.symm, hR, hF⟩
    · rintro ⟨a, rfl, hR, hF⟩
      exact Or.inr ⟨a, i, rfl, rfl, hR, hF⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {R F G H : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l R F r G) (hH : spec_l R F r H) : G = H :=
  SecondOrderRelations.ext_l hℳ G H (fun c d => (hG c d).trans (hH c d).symm)

#print axioms exists_l
#print axioms layer_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalSubsetLayer
