import BMSConstructibleBridge.SecondOrderRelations

/-!
# 内部图的互不相交带标号副本

使用模型内已证的实际配对图，把两张关系分别放在标签零和一的节点中。
纤维规格量化任意子节点，排除来自其他标签的边，而非仅核验同标签节点。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTaggedGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def fiber_l (k : num_l ℳ) (R G : set_l ℳ) : Prop :=
  ∀ c b, relation_l G c (value_l k b) ↔ ∃ a, c = value_l k a ∧ relation_l R a b

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def one {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons zero .nil)

private def branch (k : Term signature_m [.num, .num] [.num, .num, .set, .set] .num)
    (R : Term signature_m [.num, .num] [.num, .num, .set, .set] .set) :
    Formula signature_m [] [.num, .num, .set, .set] :=
  .existsE .num <| .existsE .num <| .conj
    (PrimitiveFormulas.pair_m k (.bvar (.there .here)) (.fvar .here))
    (.conj (PrimitiveFormulas.pair_m k (.bvar .here) (.fvar (.there .here)))
      (GraphSyntax.edge_m R (.bvar (.there .here)) (.bvar .here)))

def formula_m : Formula signature_m [] [.num, .num, .set, .set] :=
  .disj (branch zero (.fvar (.there (.there .here))))
    (branch one (.fvar (.there (.there (.there .here)))))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (R S : set_l ℳ) (c d : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree S).pushFree R).pushFree d).pushFree c)
      formula_m ↔
      (∃ a b, value_l (zero_l ℳ) a = c ∧ value_l (zero_l ℳ) b = d ∧ relation_l R a b) ∨
      (∃ a b, value_l (succ_l (zero_l ℳ)) a = c ∧
        value_l (succ_l (zero_l ℳ)) b = d ∧ relation_l S a b) := by
  simp only [formula_m, branch, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R S : set_l ℳ) :
    ∃ G : set_l ℳ, fiber_l (zero_l ℳ) R G ∧ fiber_l (succ_l (zero_l ℳ)) S G := by
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    (((Env.empty (M := ℳ)).pushFree S).pushFree R)
  simp_rw [formula_l] at hG
  refine ⟨G, ?_, ?_⟩
  · intro c b
    rw [hG]
    constructor
    · rintro (⟨a, d, ha, hd, h⟩ | ⟨a, d, _, hd, _⟩)
      · obtain rfl := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).2
        exact ⟨a, ha.symm, h⟩
      · exact False.elim (nonzero_l hℳ (zero_l ℳ)
          (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).1)
    · rintro ⟨a, rfl, h⟩
      exact Or.inl ⟨a, b, rfl, rfl, h⟩
  · intro c b
    rw [hG]
    constructor
    · rintro (⟨a, d, _, hd, _⟩ | ⟨a, d, ha, hd, h⟩)
      · exact False.elim (nonzero_l hℳ (zero_l ℳ)
          (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).1.symm)
      · obtain rfl := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).2
        exact ⟨a, ha.symm, h⟩
    · rintro ⟨a, rfl, h⟩
      exact Or.inr ⟨a, b, rfl, rfl, h⟩

theorem edge_l (hℳ : Theory.Models ℳ theory_m) (k : num_l ℳ) (R G : set_l ℳ)
    (h : fiber_l k R G) (a b : num_l ℳ) :
    relation_l G (value_l k a) (value_l k b) ↔ relation_l R a b := by
  rw [h]
  constructor
  · rintro ⟨c, h₁, h₂⟩
    exact (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ h₁).2 ▸ h₂
  · exact fun h₁ => ⟨a, rfl, h₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTaggedGraph
