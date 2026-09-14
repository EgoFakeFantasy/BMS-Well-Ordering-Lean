import BMSConstructibleBridge.PowerlessWitnessClosure
import BMSConstructibleBridge.PowerlessHierarchyStage

/-! # 严格增大的层次见证步骤及其纯公式 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSkolemStep

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage PowerlessWitnessClosure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def step_l (ω e T t₁ t₂ t₃ κ U F α β : carrier_l ℳ) : Prop :=
  member_l ℳ α β ∧ member_l ℳ β κ ∧ ∃ A B,
    stage_l ω e T t₁ t₂ t₃ α A ∧ stage_l ω e T t₁ t₂ t₃ β B ∧ closure_l ω U F A B

def step_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ κ U F α β : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.member_m α β) (.conj (SecondOrderObjectSyntax.member_m β κ)
    (.existsE .set (.existsE .set (.conj
      (stage_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w α) (.bvar (.there .here))) (.conj
        (stage_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w β) (.bvar .here))
        (closure_m (w ω) (w U) (w F) (.bvar (.there .here)) (.bvar .here)))))))

theorem step_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ κ U F α β : Term ℒ Γ Δ .set) :
    (step_m ω e T t₁ t₂ t₃ κ U F α β).satisfies η ↔ step_l (ω.eval η) (e.eval η) (T.eval η)
      (t₁.eval η) (t₂.eval η) (t₃.eval η) (κ.eval η) (U.eval η) (F.eval η) (α.eval η) (β.eval η) := by
  simp only [step_m, step_l, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval,
    stage_formula_l hℳ, closure_formula_l, Term.eval_weakenBound]
  rfl

theorem closure_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α β A B : carrier_l ℳ} (hω : omega_l ω)
    (h : step_l ω e T t₁ t₂ t₃ κ U F α β)
    (hA : stage_l ω e T t₁ t₂ t₃ α A) (hB : stage_l ω e T t₁ t₂ t₃ β B) :
    PowerlessWitnessClosure.closure_l ω U F A B := by
  obtain ⟨_, _, C, D, hC, hD, h⟩ := h
  have h₀ := PowerlessHierarchyStage.unique_l hℳ hω hC hA
  have h₁ := PowerlessHierarchyStage.unique_l hℳ hω hD hB
  exact h₀ ▸ h₁ ▸ h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSkolemStep
