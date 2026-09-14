import BMSConstructibleBridge.SecondOrderRelations

/-!
# 内部图的新根拼接

旧节点统一移到后继位置，零作为新根；其子节点由内部选择集合指定。
实际关系理解构造同一模型内的实数，并给出所有模型节点的完整边规格。
本文件只构造图，内部根域保持由后续链变换证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraft

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons t .nil)

/-- 输入槽位是子节点、母节点、旧关系实数、选根集合。 -/
def formula_m : Formula signature_m [] [.num, .num, .set, .set] :=
  .existsE .num (.conj (.equal (.fvar .here) (succ (.bvar .here)))
    (.disj (.conj (.equal (.fvar (.there .here)) zero)
      (.rel .mem (.cons (.bvar .here) (.cons (.fvar (.there (.there (.there .here)))) .nil))))
      (.existsE .num (.conj (.equal (.fvar (.there .here)) (succ (.bvar .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))))))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (R P : set_l ℳ) (c d : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree P).pushFree R).pushFree d).pushFree c)
      formula_m ↔ ∃ a, c = succ_l a ∧
        ((d = zero_l ℳ ∧ mem_l a P) ∨ ∃ b, d = succ_l b ∧ relation_l R a b) := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

/-- 完整拼接规格；后续域证明只消费这些已由理解实现的等式。 -/
structure spec_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (R P G : set_l ℳ) : Prop where
  zero : ∀ b, ¬relation_l G (zero_l ℳ) b
  root : ∀ a, relation_l G (succ_l a) (zero_l ℳ) ↔ mem_l a P
  shift : ∀ a b, relation_l G (succ_l a) (succ_l b) ↔ relation_l R a b

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (R P : set_l ℳ) : ∃ G, spec_l R P G := by
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    (((Env.empty (M := ℳ)).pushFree P).pushFree R)
  simp_rw [formula_l] at hG
  refine ⟨G, ?_, ?_, ?_⟩
  · intro b h
    obtain ⟨a, h, _⟩ := (hG (zero_l ℳ) b).mp h
    exact nonzero_l hℳ a h.symm
  · intro a
    rw [hG]
    constructor
    · rintro ⟨c, h, h₁⟩
      obtain rfl := SecondOrderModel.injective_l hℳ h
      rcases h₁ with ⟨_, h₁⟩ | ⟨b, h₁, _⟩
      · exact h₁
      · exact False.elim (nonzero_l hℳ b h₁.symm)
    · intro h
      exact ⟨a, rfl, Or.inl ⟨rfl, h⟩⟩
  · intro a b
    rw [hG]
    constructor
    · rintro ⟨c, h, h₁⟩
      obtain rfl := SecondOrderModel.injective_l hℳ h
      rcases h₁ with ⟨h₁, _⟩ | ⟨d, h₁, h₂⟩
      · exact False.elim (nonzero_l hℳ b h₁)
      · exact (SecondOrderModel.injective_l hℳ h₁) ▸ h₂
    · intro h
      exact ⟨a, rfl, Or.inr ⟨b, rfl, h⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraft
