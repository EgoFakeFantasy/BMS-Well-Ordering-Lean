import BMSConstructibleBridge.PowerlessFunction

/-! # 实际恒等图与集合包含单射 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessIdentity

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (A : carrier_l ℳ) :
    ∃ f, map_l f A A ∧ injective_l f ∧ ∀ x y, value_l f x y ↔ member_l ℳ x A ∧ y = x := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 0 :=
    { bound := Fin.elim0, free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set] := .equal (.fvar .here) (.fvar (.there .here))
  have h : ∀ x y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ↔ y = x :=
    fun _ _ => Iff.rfl
  obtain ⟨f, B, hf, _, hV⟩ := PowerlessMapping.exists_l hℳ φ η A
    (fun x _ => ⟨x, (h x x).mpr rfl⟩)
    (fun x _ y z hy hz => ((h x y).mp hy).trans ((h x z).mp hz).symm)
  have h₀ : ∀ x y, value_l f x y ↔ member_l ℳ x A ∧ y = x := by
    intro x y
    constructor
    · intro hy
      have hx := (PowerlessFunction.value_mem_l hℳ hf hy).1
      exact ⟨hx, (h x y).mp ((hV x hx y).mp hy)⟩
    · rintro ⟨hx, hy⟩
      exact (hV x hx y).mpr ((h x y).mpr hy)
  refine ⟨f, PowerlessFunction.range_l hℳ hf ?_, ?_, h₀⟩
  · intro x y hy
    obtain ⟨hx, hy⟩ := (h₀ x y).mp hy
    exact hy.symm ▸ hx
  · intro x y z hx hy
    exact ((h₀ x z).mp hx).2.symm.trans ((h₀ y z).mp hy).2

theorem inclusion_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A B : carrier_l ℳ} (h : subset_l A B) : ∃ f, map_l f A B ∧ injective_l f := by
  obtain ⟨f, hf, h₀, h₁⟩ := exists_l hℳ A
  exact ⟨f, PowerlessFunction.range_l hℳ hf (fun x y hy => by
    obtain ⟨hx, hy⟩ := (h₁ x y).mp hy
    exact hy.symm ▸ h x hx), h₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessIdentity
