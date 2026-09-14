import BMSConstructibleBridge.PowerlessFunction
import BMSConstructibleBridge.PowerlessNaturalCompare

/-!
# 保持集合后继的内部 ω 函数严格递增

递增性用实际初段取值公式归纳，适用于模型的全部内部自然数。
单射性再由内部自然数可比性和 Foundation 得出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalEmbedding

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def prefix_m : Formula ℒ [] [.set, .set] :=
  .forallE .set (.forallE .set (.forallE .set (.imp
    (SecondOrderObjectSyntax.member_m (.bvar (.there (.there .here))) (.fvar .here))
    (.imp (SecondOrderObjectSyntax.value_m (.fvar (.there .here))
      (.bvar (.there (.there .here))) (.bvar (.there .here)))
      (.imp (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
        (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here)))))))

theorem prefix_formula_l (η : Env ℳ [] [.set, .set]) : prefix_m.satisfies η ↔
    ∀ k x y, member_l ℳ k (η.freeVal .here) → value_l (η.freeVal (.there .here)) k x →
      value_l (η.freeVal (.there .here)) (η.freeVal .here) y → member_l ℳ x y := by
  simp only [prefix_m, Formula.satisfies, value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω f B : carrier_l ℳ} (hω : omega_l ω) (hf : map_l f ω B)
    (h : ∀ n m x y, member_l ℳ n ω → successor_l n m → value_l f n x → value_l f m y → successor_l x y) :
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
      apply (h₃ x).mpr
      rcases (hm k).mp hk with hk | hk
      · exact Or.inl ((h₀ n).mp h₂ k x z hk hx hz.2)
      · subst k
        exact Or.inr (PowerlessFunction.value_unique_l hℳ hf hx hz.2)))
  exact fun n hn => (h₀ n).mp (h₁ n hn)

theorem injective_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω f B : carrier_l ℳ} (hω : omega_l ω) (hf : map_l f ω B)
    (h : ∀ n m x y, member_l ℳ n ω → successor_l n m → value_l f n x → value_l f m y → successor_l x y) :
    ThirdOrderSemantics.injective_l f := by
  intro n m x hn hm
  have hn₀ := (PowerlessFunction.value_mem_l hℳ hf hn).1
  have hm₀ := (PowerlessFunction.value_mem_l hℳ hf hm).1
  rcases PowerlessNaturalCompare.compare_l hℳ hω n hn₀ m hm₀ with h₀ | h₀ | h₀
  · have h₁ := monotone_l hℳ hω hf h m hm₀ n x x h₀ hn hm
    exact (asymmetry_l hℳ h₁ h₁).elim
  · exact h₀
  · have h₁ := monotone_l hℳ hω hf h n hn₀ m x x h₀ hm hn
    exact (asymmetry_l hℳ h₁ h₁).elim

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalEmbedding
