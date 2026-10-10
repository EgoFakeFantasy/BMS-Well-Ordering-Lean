import BMSConstructibleBridge.PowerlessOrdinalCollection
import BMSConstructibleBridge.PowerlessStageStructure

/-!
# 固定源公式的无预设上端点见证步骤

在明确的公式见证覆盖前提下，按原公式收集见证的层号，得到严格超过任意
给定序数的一层，包含全部有定义请求的某个见证。没有预设稳定对、κ、
全公式真值集或可数选择。只要求该公式的见证落入层次，不要求全域覆盖。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitnessBound

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def binding_m {Γ : SortContext ℒ} :
    Substitution ℒ [] (.set :: .set :: Γ) [.set, .set] (.set :: .set :: Γ) :=
  .map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (fun {s} (v : Variable (.set :: .set :: Γ) s) => match v with
    | .here => .bvar .here
    | .there v => .fvar (.there v))

theorem binding_formula_l {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Γ)) (η : Env ℳ [] Γ) (x α U y : carrier_l ℳ) :
    (φ.substitute binding_m).satisfies ((((η.pushFree x).pushFree α).pushBound U).pushBound y) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
  rw [Formula.satisfies_substitute]
  apply Iff.of_eq
  congr 1
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v <;> rfl

def rank_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) : Formula ℒ [] (.set :: .set :: Γ) :=
  let q (s : Term ℒ [] Γ .set) : Term ℒ [.set] (.set :: .set :: Γ) .set :=
    ((s.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.conj
    (stage_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (.fvar .here) (.bvar .here))
    (.existsE .set (.conj
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (φ.substitute binding_m))))

theorem rank_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : Env ℳ [] Γ) (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (x α : carrier_l ℳ) :
    (rank_m φ ω e T t₁ t₂ t₃).satisfies ((η.pushFree x).pushFree α) ↔
      ∃ U, stage_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) α U ∧
        ∃ y, member_l ℳ y U ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  simp only [rank_m, Formula.satisfies, stage_formula_l hℳ,
    binding_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval_weakenBound, Term.eval_weakenFree]
  rfl

/-- 覆盖是明确的数学前提，不是新加的公理，也不是稳定对存在性的别名。 -/
theorem bound_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Γ .set) (A α : carrier_l ℳ)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (hα : PowerlessOrdinal.ordinal_l α)
    (hC : ∀ x y,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) → ∃ γ U,
      stage_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
        (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
        (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) γ U ∧
      member_l ℳ y U) :
    ∃ β B, member_l ℳ α β ∧
      stage_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
        (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
        (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) β B ∧
      ∀ x, member_l ℳ x A →
        (∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y)) →
        ∃ y, member_l ℳ y B ∧
          φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) := by
  let ρ := PowerlessComprehension.env_l η
  obtain ⟨γ, hγ, h₀⟩ := PowerlessOrdinalCollection.witnesses_l hℳ
    (rank_m φ ω e T t₁ t₂ t₃) η A (fun x _ δ h => by
      obtain ⟨U, hU, _⟩ := (rank_formula_l hℳ φ ρ ω e T t₁ t₂ t₃ x δ).mp h
      exact hU.1)
  obtain ⟨D, hD⟩ := PowerlessBasic.pairing_l hℳ α γ
  obtain ⟨β, hβ, h₁⟩ := PowerlessOrdinalCollection.bound_l hℳ (A := D)
    (fun δ hδ => by
      rcases (hD δ).mp hδ with rfl | rfl
      · exact hα
      · exact hγ)
  have hαβ := h₁ α ((hD α).mpr (Or.inl rfl))
  have hγβ := h₁ γ ((hD γ).mpr (Or.inr rfl))
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω hβ
    (e.eval ρ) (T.eval ρ) (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ)
  refine ⟨β, B, hαβ, hB, fun x hx h => ?_⟩
  have h₂ : ∃ δ, (rank_m φ ω e T t₁ t₂ t₃).satisfies ((ρ.pushFree x).pushFree δ) := by
    obtain ⟨y, hy⟩ := h
    obtain ⟨δ, U, hU, hyU⟩ := hC x y hy
    exact ⟨δ, (rank_formula_l hℳ φ ρ ω e T t₁ t₂ t₃ x δ).mpr ⟨U, hU, y, hyU, hy⟩⟩
  obtain ⟨δ, hδ, h₃⟩ := h₀ x hx h₂
  obtain ⟨U, hU, y, hyU, hy⟩ := (rank_formula_l hℳ φ ρ ω e T t₁ t₂ t₃ x δ).mp h₃
  exact ⟨y, PowerlessStageStructure.subset_l hℳ hω hU hB
    (PowerlessOrdinal.transitive_l hβ γ δ hγβ hδ) y hyU, hy⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceWitnessBound
