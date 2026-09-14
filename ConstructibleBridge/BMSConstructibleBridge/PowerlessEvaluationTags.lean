import BMSConstructibleBridge.PowerlessFormulaConstructor

/-!
# 四个求值构造子的实际数码标签

标签依次为模型内部 0、1、2、3，由空集和集合后继构造。
其互异性是基础背景中的定理，不作为语法额外公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationTags

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def tags_l (e t₁ t₂ t₃ : carrier_l ℳ) : Prop :=
  zero_l e ∧ successor_l e t₁ ∧ successor_l t₁ t₂ ∧ successor_l t₂ t₃

def tags_m {Γ Δ : SortContext ℒ} (e t₁ t₂ t₃ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (e.weakenBound SetTheory.SetSort.set))))
    (.conj (PowerlessNaturalStep.successor_m e t₁)
      (.conj (PowerlessNaturalStep.successor_m t₁ t₂) (PowerlessNaturalStep.successor_m t₂ t₃)))

theorem tags_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (e t₁ t₂ t₃ : Term ℒ Γ Δ .set) :
    (tags_m e t₁ t₂ t₃).satisfies η ↔ tags_l (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) := by
  simp only [tags_m, tags_l, zero_l, Formula.satisfies, PowerlessNaturalStep.successor_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {e : carrier_l ℳ} (he : zero_l e) : ∃ t₁ t₂ t₃, tags_l e t₁ t₂ t₃ := by
  obtain ⟨t₁, h₁⟩ := successor_exists_l hℳ e
  obtain ⟨t₂, h₂⟩ := successor_exists_l hℳ t₁
  obtain ⟨t₃, h₃⟩ := successor_exists_l hℳ t₂
  exact ⟨t₁, t₂, t₃, he, h₁, h₂, h₃⟩

theorem natural_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω) (h : tags_l e t₁ t₂ t₃) :
    member_l ℳ e ω ∧ member_l ℳ t₁ ω ∧ member_l ℳ t₂ ω ∧ member_l ℳ t₃ ω := by
  have he := zero_mem_l hℳ hω h.1
  have h₁ := successor_mem_l hℳ hω he h.2.1
  have h₂ := successor_mem_l hℳ hω h₁ h.2.2.1
  exact ⟨he, h₁, h₂, successor_mem_l hℳ hω h₂ h.2.2.2⟩

theorem distinct_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {e t₁ t₂ t₃ : carrier_l ℳ} (h : tags_l e t₁ t₂ t₃) :
    e ≠ t₁ ∧ e ≠ t₂ ∧ e ≠ t₃ ∧ t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ := by
  have h₀ : ∀ a b : carrier_l ℳ, member_l ℳ a b → a ≠ b := by
    intro a b hab h₁
    subst b
    exact asymmetry_l hℳ hab hab
  have h₁ := (h.2.1 e).mpr (Or.inr rfl)
  have h₂ := (h.2.2.1 t₁).mpr (Or.inr rfl)
  have h₃ := (h.2.2.2 t₂).mpr (Or.inr rfl)
  have h₄ := (h.2.2.1 e).mpr (Or.inl h₁)
  exact ⟨h₀ _ _ h₁, h₀ _ _ h₄, h₀ _ _ ((h.2.2.2 e).mpr (Or.inl h₄)),
    h₀ _ _ h₂, h₀ _ _ ((h.2.2.2 t₁).mpr (Or.inl h₂)), h₀ _ _ h₃⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationTags
