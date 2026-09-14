import BMSConstructibleBridge.PowerlessNaturalEmbedding

/-! # 传递值域上的内部严格增长函数 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalGrowth

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural PowerlessNaturalEmbedding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω f B : carrier_l ℳ} (hω : omega_l ω) (hf : map_l f ω B)
    (hB : ∀ y, member_l ℳ y B → PowerlessNaturalOrder.transitive_l y)
    (h : ∀ n m x y, member_l ℳ n ω → successor_l n m → value_l f n x → value_l f m y → member_l ℳ x y) :
    ∀ n, member_l ℳ n ω → ∀ k x y, member_l ℳ k n → value_l f k x → value_l f n y → member_l ℳ x y := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => f, free := fun _ => ω }
  have h₀ : ∀ n, prefix_m.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ k x y, member_l ℳ k n → value_l f k x → value_l f n y → member_l ℳ x y :=
    fun n => prefix_formula_l _
  have h₁ := PowerlessNatural.induction_l hℳ prefix_m η hω
    (fun e he => (h₀ e).mpr (fun k _ _ hk _ _ => (he k hk).elim))
    (fun n m hn hm h₂ => (h₀ m).mpr (by
      intro k x y hk hx hy
      obtain ⟨z, hz, _⟩ := hf.2 n hn
      have h₃ := h n m z y hn hm hz.2 hy
      rcases (hm k).mp hk with hk | hk
      · exact hB y (PowerlessFunction.value_mem_l hℳ hf hy).2 z x h₃ ((h₀ n).mp h₂ k x z hk hx hz.2)
      · subst k
        exact (PowerlessFunction.value_unique_l hℳ hf hx hz.2).symm ▸ h₃))
  exact fun n hn => (h₀ n).mp (h₁ n hn)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalGrowth
