import BMSConstructibleBridge.ThirdOrderSelection
import BMSConstructibleBridge.ThirdOrderOmegaOne
import BMSConstructibleBridge.PowerlessIdentity

/-! # 内部可数性的子集与像集传递 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCountableImage

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem subset_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A B : carrier_l ℳ} (hB : countable_l ω B) (hAB : ThirdOrderSemantics.subset_l A B) : countable_l ω A := by
  obtain ⟨f, hf, hF⟩ := PowerlessIdentity.inclusion_l hℳ hAB
  obtain ⟨g, hg, hG⟩ := hB
  obtain ⟨k, hk, h₀⟩ := PowerlessComposition.exists_l hℳ hf hg
  exact ⟨k, hk, PowerlessComposition.injective_l hF hG h₀⟩

theorem surjective_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω f A B : carrier_l ℳ} (hf : map_l f A B) (hA : countable_l ω A)
    (h : ∀ b, member_l ℳ b B → ∃ a, value_l f a b) : countable_l ω B := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => f, free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  have h₁ : ∀ b a, φ.satisfies (((PowerlessComprehension.env_l η).pushFree b).pushFree a) ↔ value_l f a b := by
    intro b a
    dsimp only [φ]
    rw [value_formula_l]
    rfl
  obtain ⟨g, C, hg, h₂⟩ := ThirdOrderSelection.exists_l hℳ φ η B
    (fun b hb => (h b hb).imp fun a ha => (h₁ b a).mpr ha)
  have h₃ : ∀ b a, value_l g b a → value_l f a b := fun b a ha => (h₁ b a).mp (h₂ b a ha)
  have hG : injective_l g := fun b c a hb hc => PowerlessFunction.value_unique_l h₀ hf (h₃ b a hb) (h₃ c a hc)
  have hg₀ : map_l g B A := PowerlessFunction.range_l h₀ hg
    (fun b a ha => (PowerlessFunction.value_mem_l h₀ hf (h₃ b a ha)).1)
  obtain ⟨i, hi, hI⟩ := hA
  obtain ⟨k, hk, h₄⟩ := PowerlessComposition.exists_l h₀ hg₀ hi
  exact ⟨k, hk, PowerlessComposition.injective_l hG hI h₄⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCountableImage
