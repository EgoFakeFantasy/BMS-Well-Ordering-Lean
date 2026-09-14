import BMSConstructibleBridge.PowerlessFunction

/-! # 内部集合函数的复合及单射性 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessComposition

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A B C f g : carrier_l ℳ} (hf : map_l f A B) (hg : map_l g B C) :
    ∃ h, map_l h A C ∧ ∀ x z, value_l h x z ↔ ∃ y, value_l f x y ∧ value_l g y z := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => g), free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set, .set, .set] :=
    .existsE .set (.conj
      (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.value_m (.fvar (.there (.there (.there .here)))) (.bvar .here) (.fvar .here)))
  have h : ∀ x z, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree z) ↔
      ∃ y, value_l f x y ∧ value_l g y z := by
    intro x z
    simp only [φ, Formula.satisfies, value_formula_l]
    rfl
  obtain ⟨k, D, hk, _, hV⟩ := PowerlessMapping.exists_l hℳ φ η A
    (fun x hx => by
      obtain ⟨y, hy, _⟩ := hf.2 x hx
      obtain ⟨z, hz, _⟩ := hg.2 y hy.1
      exact ⟨z, (h x z).mpr ⟨y, hy.2, hz.2⟩⟩)
    (fun x _ z w hz hw => by
      obtain ⟨y, hy, hz⟩ := (h x z).mp hz
      obtain ⟨v, hv, hw⟩ := (h x w).mp hw
      have h₀ := PowerlessFunction.value_unique_l hℳ hf hy hv
      subst v
      exact PowerlessFunction.value_unique_l hℳ hg hz hw)
  have h₀ : ∀ x z, value_l k x z ↔ ∃ y, value_l f x y ∧ value_l g y z := by
    intro x z
    constructor
    · intro hz
      exact (h x z).mp ((hV x (PowerlessFunction.value_mem_l hℳ hk hz).1 z).mp hz)
    · rintro ⟨y, hy, hz⟩
      exact (hV x (PowerlessFunction.value_mem_l hℳ hf hy).1 z).mpr ((h x z).mpr ⟨y, hy, hz⟩)
  refine ⟨k, PowerlessFunction.range_l hℳ hk ?_, h₀⟩
  intro x z hz
  obtain ⟨y, _, hy⟩ := (h₀ x z).mp hz
  exact (PowerlessFunction.value_mem_l hℳ hg hy).2

theorem injective_l {f g k : carrier_l ℳ} (hf : ThirdOrderSemantics.injective_l f)
    (hg : ThirdOrderSemantics.injective_l g)
    (h : ∀ x z, value_l k x z ↔ ∃ y, value_l f x y ∧ value_l g y z) :
    ThirdOrderSemantics.injective_l k := by
  intro x y z hx hy
  obtain ⟨a, ha, h₀⟩ := (h x z).mp hx
  obtain ⟨b, hb, h₁⟩ := (h y z).mp hy
  have h₂ := hg a b z h₀ h₁
  subst b
  exact hf x y a ha hb

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessComposition
