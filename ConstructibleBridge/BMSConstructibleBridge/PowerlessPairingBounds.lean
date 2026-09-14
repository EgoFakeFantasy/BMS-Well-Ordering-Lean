import BMSConstructibleBridge.PowerlessPairingCode

/-! # 内部配对数支配两个坐标 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPairingBounds

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural PowerlessTriangular

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def growth_bound_m : Formula ℒ [] [.set, .set] := .forallE .set (.imp
  (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
  (.disj (SecondOrderObjectSyntax.member_m (.fvar .here) (.bvar .here)) (.equal (.fvar .here) (.bvar .here))))

theorem growth_bound_formula_l (η : Env ℳ [] [.set, .set]) : growth_bound_m.satisfies η ↔
    ∀ y, value_l (η.freeVal (.there .here)) (η.freeVal .here) y →
      member_l ℳ (η.freeVal .here) y ∨ η.freeVal .here = y := by
  simp only [growth_bound_m, Formula.satisfies, value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem growth_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω f : carrier_l ℳ} (hω : omega_l ω) (hf : map_l f ω ω)
    (h : ∀ n m x y, member_l ℳ n ω → successor_l n m → value_l f n x → value_l f m y → member_l ℳ x y) :
    ∀ n y, value_l f n y → member_l ℳ n y ∨ n = y := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => f, free := fun _ => ω }
  have h₀ : ∀ n, growth_bound_m.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ y, value_l f n y → member_l ℳ n y ∨ n = y := fun n => growth_bound_formula_l _
  have h₁ := PowerlessNatural.induction_l hℳ growth_bound_m η hω
    (fun e he => (h₀ e).mpr (fun y hy => PowerlessNaturalCompare.zero_le_l hℳ hω he y
      (PowerlessFunction.value_mem_l hℳ hf hy).2))
    (fun n m hn hm h₂ => (h₀ m).mpr (by
      intro y hy
      obtain ⟨x, hx, _⟩ := hf.2 n hn
      have h₃ := h n m x y hn hm hx.2 hy
      have hy₀ := (PowerlessFunction.value_mem_l hℳ hf hy).2
      have h₄ : member_l ℳ n y := by
        rcases (h₀ n).mp h₂ x hx.2 with h₄ | h₄
        · exact PowerlessNaturalOrder.member_transitive_l hℳ hω y hy₀ x n h₃ h₄
        · exact h₄.symm ▸ h₃
      exact PowerlessNaturalStep.bound_l hℳ hω y hy₀ n m h₄ hm))
  exact fun n y hy => (h₀ n).mp (h₁ n (PowerlessFunction.value_mem_l hℳ hf hy).1) y hy

theorem trans_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω a b c : carrier_l ℳ} (hω : omega_l ω) (hc : member_l ℳ c ω)
    (hab : member_l ℳ a b ∨ a = b) (hbc : member_l ℳ b c ∨ b = c) : member_l ℳ a c ∨ a = c := by
  rcases hbc with hbc | hbc
  · rcases hab with hab | hab
    · exact Or.inl (PowerlessNaturalOrder.member_transitive_l hℳ hω c hc b a hbc hab)
    · exact Or.inl (hab.symm ▸ hbc)
  · exact hbc ▸ hab

theorem coordinates_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T a b c : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) (h : PowerlessPairingCode.code_l ω e T a b c) :
    (member_l ℳ a c ∨ a = c) ∧ (member_l ℳ b c ∨ b = c) := by
  obtain ⟨s, t, hs, ht, hc⟩ := h
  have ht₀ := (PowerlessFunction.value_mem_l hℳ hT.1 ht).2
  have hc₀ := PowerlessAdditionBounds.output_l hℳ hω he ht₀ hc
  have h₀ := growth_l hℳ hω hT.1
    (fun _ _ _ _ hn hm hx hy => PowerlessTriangular.growth_l hℳ hω he hT hn hm hx hy) s t ht
  have h₁ := trans_l hℳ hω hc₀ h₀ (PowerlessAdditionBounds.lower_l hℳ hω he ht₀ hc)
  exact ⟨trans_l hℳ hω hc₀ (PowerlessAdditionBounds.lower_l hℳ hω he ha hs) h₁,
    trans_l hℳ hω hc₀ (PowerlessAdditionBounds.lower_l hℳ hω he hb
      ((PowerlessAdditionCommutativity.comm_l hℳ hω he ha hb s).mp hs)) h₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPairingBounds
