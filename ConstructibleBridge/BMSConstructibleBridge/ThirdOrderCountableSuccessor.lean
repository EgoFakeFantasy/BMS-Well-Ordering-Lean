import BMSConstructibleBridge.ThirdOrderCountableImage
import BMSConstructibleBridge.PowerlessAddition
import BMSConstructibleBridge.PowerlessOmegaOrdinal

/-! # 可数集合的后继仍可数，首个不可数序数为极限 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCountableSuccessor

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessNatural

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem omega_mem_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω κ : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ) : member_l ℳ ω κ := by
  obtain ⟨f, hf, hF, _⟩ := PowerlessIdentity.exists_l hℳ ω
  have h : countable_l ω ω := ⟨f, hf, hF⟩
  have h₀ := PowerlessOmegaOrdinal.ordinal_l hℳ hω
  rcases PowerlessOrdinalOrder.trichotomy_l hℳ h₀ hκ.1 with h₁ | h₁ | h₁
  · exact h₁
  · exact (hκ.2.1 (h₁ ▸ h)).elim
  · exact (hκ.2.1 (ThirdOrderCountableImage.subset_l hℳ h
      (fun x hx => PowerlessOrdinal.transitive_l h₀ κ x h₁ hx))).elim

theorem shift_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) :
    ∃ f, map_l f ω ω ∧ injective_l f ∧ ∀ n m, value_l f n m → successor_l n m := by
  obtain ⟨f, B, hf, _, h₀⟩ := PowerlessMapping.exists_l hℳ PowerlessAddition.step_m (PowerlessAddition.env_l ω) ω
    (fun n _ => (successor_exists_l hℳ n).imp fun m hm => (PowerlessAddition.step_formula_l ω n m).mpr hm)
    (fun n _ m k hm hk => successor_unique_l hℳ
      ((PowerlessAddition.step_formula_l ω n m).mp hm) ((PowerlessAddition.step_formula_l ω n k).mp hk))
  have h : ∀ n m, value_l f n m → successor_l n m := fun n m hm =>
    (PowerlessAddition.step_formula_l ω n m).mp ((h₀ n (PowerlessFunction.value_mem_l hℳ hf hm).1 m).mp hm)
  exact ⟨f, PowerlessFunction.range_l hℳ hf (fun n m hm =>
      successor_mem_l hℳ hω (PowerlessFunction.value_mem_l hℳ hf hm).1 (h n m hm)),
    fun n k m hn hk => successor_injective_l hℳ (h n m hn) (h k m hk), h⟩

theorem successor_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A B : carrier_l ℳ} (hω : omega_l ω) (hA : countable_l ω A)
    (hB : PowerlessNatural.successor_l A B) : countable_l ω B := by
  obtain ⟨f, hf, hF⟩ := hA
  obtain ⟨g, hg, hG, h₀⟩ := shift_l hℳ hω
  obtain ⟨k, hk, h₁⟩ := PowerlessComposition.exists_l hℳ hf hg
  have hK := PowerlessComposition.injective_l hF hG h₁
  obtain ⟨e, he⟩ := PowerlessBasic.empty_l hℳ
  have h₂ : ∀ x, ¬value_l k x e := by
    intro x hx
    obtain ⟨n, _, hn⟩ := (h₁ x e).mp hx
    exact he n ((h₀ n e hn n).mpr (Or.inr rfl))
  obtain ⟨l, D, hl, h₃⟩ := PowerlessExtension.exists_l (d := e) hℳ hk (fun h => asymmetry_l hℳ h h) hB
  refine ⟨l, PowerlessFunction.range_l hℳ hl ?_, ?_⟩
  · intro x y hy
    rcases (h₃ x y).mp hy with hy | ⟨_, hy⟩
    · exact (PowerlessFunction.value_mem_l hℳ hk hy).2
    · exact hy.symm ▸ zero_mem_l hℳ hω he
  · intro x y z hx hy
    rcases (h₃ x z).mp hx with hx | ⟨hx, hz⟩
    · rcases (h₃ y z).mp hy with hy | ⟨_, hz⟩
      · exact hK x y z hx hy
      · exact (h₂ x (hz ▸ hx)).elim
    · rcases (h₃ y z).mp hy with hy | ⟨hy, _⟩
      · exact (h₂ y (hz ▸ hy)).elim
      · exact hx.trans hy.symm

theorem limit_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω κ a b : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ha : member_l ℳ a κ) (hb : PowerlessNatural.successor_l a b) : member_l ℳ b κ := by
  have h₀ := successor_l hℳ hω (hκ.2.2 a ha) hb
  have h₁ := PowerlessOrdinalOrder.successor_l hℳ (PowerlessOrdinal.mem_l hκ.1 ha) hb
  rcases PowerlessOrdinalOrder.trichotomy_l hℳ h₁ hκ.1 with h₂ | h₂ | h₂
  · exact h₂
  · exact (hκ.2.1 (h₂ ▸ h₀)).elim
  · exact (hκ.2.1 (ThirdOrderCountableImage.subset_l hℳ h₀
      (fun x hx => PowerlessOrdinal.transitive_l h₁ κ x h₂ hx))).elim

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCountableSuccessor
