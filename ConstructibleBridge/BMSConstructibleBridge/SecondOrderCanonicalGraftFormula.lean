import BMSConstructibleBridge.SecondOrderCanonicalGraft

/-! # 完整拼接规格与原图公式的双向对应

规格覆盖零及所有后继节点。公式解释的唯一性来自同一模型的实际关系
理解和实数外延性，不从商对象等价擅自取得原实数相等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalGraftFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (R P G : set_l ℳ) : Prop := ∀ c d, relation_l G c d ↔ ∃ a, c = succ_l a ∧
  ((d = zero_l ℳ ∧ mem_l a P) ∨ ∃ b, d = succ_l b ∧ relation_l R a b)

theorem graft_l (hℳ : Theory.Models ℳ theory_m) {R P G : set_l ℳ}
    (hG : spec_l R P G) : SecondOrderGraft.spec_l R P G := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, _⟩ := (hG _ b).mp hb
    exact nonzero_l hℳ a ha.symm
  · intro a
    rw [hG]
    constructor
    · rintro ⟨c, hc, h⟩
      obtain rfl := injective_l hℳ hc
      rcases h with ⟨_, h⟩ | ⟨b, hb, _⟩
      · exact h
      · exact False.elim (nonzero_l hℳ b hb.symm)
    · intro h
      exact ⟨a, rfl, Or.inl ⟨rfl, h⟩⟩
  · intro a b
    rw [hG]
    constructor
    · rintro ⟨c, hc, h⟩
      obtain rfl := injective_l hℳ hc
      rcases h with ⟨hb, _⟩ | ⟨d, hd, hR⟩
      · exact False.elim (nonzero_l hℳ b hb)
      · exact (injective_l hℳ hd) ▸ hR
    · intro h
      exact ⟨a, rfl, Or.inr ⟨b, rfl, h⟩⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R P : set_l ℳ) : ∃ G, spec_l R P G := by
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ SecondOrderGraft.formula_m
    SecondOrderGraft.pure_m (((Env.empty (M := ℳ)).pushFree P).pushFree R)
  exact ⟨G, fun c d => (hG c d).trans (SecondOrderGraft.formula_l R P c d)⟩

theorem iff_l (hℳ : Theory.Models ℳ theory_m) (R P G : set_l ℳ) :
    spec_l R P G ↔ SecondOrderGraft.spec_l R P G := by
  refine ⟨graft_l hℳ, fun hG => ?_⟩
  obtain ⟨H, hH⟩ := exists_l hℳ R P
  have hEq := SecondOrderCanonicalGraft.unique_l hℳ hG (graft_l hℳ hH)
  exact hEq ▸ hH

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalGraftFormula
