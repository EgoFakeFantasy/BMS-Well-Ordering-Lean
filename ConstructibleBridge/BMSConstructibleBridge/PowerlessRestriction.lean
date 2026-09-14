import BMSConstructibleBridge.PowerlessFunction

/-! # 内部集合函数的精确限制 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRestriction

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f A B C : carrier_l ℳ} (hf : map_l f A B) (hC : subset_l C A) :
    ∃ g, map_l g C B ∧ ∀ x y, value_l g x y ↔ member_l ℳ x C ∧ value_l f x y := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => f, free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  have h : ∀ x y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ↔
      value_l f x y := by
    intro x y
    dsimp only [φ]
    rw [value_formula_l]
    rfl
  obtain ⟨g, D, hg, _, hV⟩ := PowerlessMapping.exists_l hℳ φ η C
    (fun x hx => by
      obtain ⟨y, hy, _⟩ := hf.2 x (hC x hx)
      exact ⟨y, (h x y).mpr hy.2⟩)
    (fun x _ y z hy hz => PowerlessFunction.value_unique_l hℳ hf ((h x y).mp hy) ((h x z).mp hz))
  have h₀ : ∀ x y, value_l g x y ↔ member_l ℳ x C ∧ value_l f x y := by
    intro x y
    constructor
    · intro h₁
      have hx := (PowerlessFunction.value_mem_l hℳ hg h₁).1
      exact ⟨hx, (h x y).mp ((hV x hx y).mp h₁)⟩
    · rintro ⟨hx, h₁⟩
      exact (hV x hx y).mpr ((h x y).mpr h₁)
  refine ⟨g, PowerlessFunction.range_l hℳ hg ?_, h₀⟩
  intro x y h₁
  exact (PowerlessFunction.value_mem_l hℳ hf ((h₀ x y).mp h₁).2).2

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f g h A B C : carrier_l ℳ} (hg : map_l g C A) (hh : map_l h C B)
    (h₀ : ∀ x y, value_l g x y ↔ member_l ℳ x C ∧ value_l f x y)
    (h₁ : ∀ x y, value_l h x y ↔ member_l ℳ x C ∧ value_l f x y) : g = h :=
  PowerlessFunction.ext_l hℳ hg hh (fun x _ y => (h₀ x y).trans (h₁ x y).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRestriction
