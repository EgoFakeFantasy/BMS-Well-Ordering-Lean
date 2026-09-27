import BMSConstructibleBridge.PowerlessSourceReflectionFamily
import BMSConstructibleBridge.PowerlessClassCore

/-!
# 同时满足有限核心并保留指定原公式反射的实际层

把有限核心的合取闭句加入反射列表。所得同一层既满足核心，
又对任意层内绑定参数保留原列表的双向反射；不先假设小层模型。
自由参数仍固定，环境仍为完整 PowerlessTheory。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceReflectionSupport

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

def sentence_m {Γ Δ : SortContext ℒ} (φ : Sentence ℒ) : Formula ℒ Γ Δ :=
  φ.substitute (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v))

theorem sentence_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (φ : Sentence ℒ) (η : Env ℳ Γ Δ) :
    (sentence_m φ).satisfies η ↔ φ.TrueIn ℳ := by
  rw [sentence_m, Formula.satisfies_substitute]
  have h : η.pullback (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
      (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)) = Env.empty := by
    apply Env.ext <;> intro s v <;> nomatch v
  rw [h]
  rfl

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (Φ : List (Formula ℒ Γ Δ))
    (Ξ : List (Sentence ℒ)) (hΞ : ∀ φ ∈ Ξ, PowerlessTheory.theory_m φ)
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Δ.length)
    (ω e T t₁ t₂ t₃ : Term ℒ [] Δ .set) (α : carrier_l ℳ)
    (hω : omega_l (ω.eval (PowerlessComprehension.env_l η)))
    (ht : PowerlessEvaluationTags.tags_l (e.eval (PowerlessComprehension.env_l η))
      (t₁.eval (PowerlessComprehension.env_l η)) (t₂.eval (PowerlessComprehension.env_l η))
      (t₃.eval (PowerlessComprehension.env_l η)))
    (hT : PowerlessTriangular.triangular_l (ω.eval (PowerlessComprehension.env_l η))
      (e.eval (PowerlessComprehension.env_l η)) (T.eval (PowerlessComprehension.env_l η)))
    (hα : PowerlessOrdinal.ordinal_l α)
    (hη : ∀ v : Variable Δ .set, PowerlessSourceWitnessDomain.domain_l
      (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
      (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
      (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η))
      ((PowerlessComprehension.env_l η).freeVal v)) :
    ∃ δ U, ∃ hU₀ : ∃ x, member_l ℳ x U,
      PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧
      stage_l (ω.eval (PowerlessComprehension.env_l η)) (e.eval (PowerlessComprehension.env_l η))
        (T.eval (PowerlessComprehension.env_l η)) (t₁.eval (PowerlessComprehension.env_l η))
        (t₂.eval (PowerlessComprehension.env_l η)) (t₃.eval (PowerlessComprehension.env_l η)) δ U ∧
      Theory.Models (PowerlessMemberStructure.structure_l U hU₀) (Theory.ofList Ξ) ∧
      (∀ v : Variable Δ .set, member_l ℳ ((PowerlessComprehension.env_l η).freeVal v) U) ∧
      ∀ φ ∈ Φ, ∀ θ : Env ℳ Γ Δ, PowerlessSourceClass.free_l θ = PowerlessComprehension.env_l η →
        ∀ hθ : ∀ t : Term ℒ Γ Δ .set, member_l ℳ (t.eval θ) U,
          (PowerlessSourceClass.form_m (PowerlessHierarchyClass.domain_m ω e T t₁ t₂ t₃) φ).satisfies θ ↔
            φ.satisfies (PowerlessHierarchyClass.lift_l hU₀ θ hθ) := by
  let ρ := PowerlessComprehension.env_l η
  let ψ : Formula ℒ Γ Δ := sentence_m (Formula.conjunctionList Ξ)
  obtain ⟨δ, U, hU₀, hδ, hαδ, hU, h₀, h₁⟩ :=
    PowerlessSourceReflectionFamily.exists_l hℳ (ψ :: Φ) η ω e T t₁ t₂ t₃ α hω ht hT hα hη
  have hρ : ∀ t : Term ℒ [] Δ .set, member_l ℳ (t.eval ρ) U := by
    intro t
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact h₀ v
    | .app f _ => nomatch f
  let θ : Env ℳ Γ Δ := {
    boundVal := fun {s} _ => by cases s; exact ω.eval ρ
    freeVal := ρ.freeVal }
  have hθ : ∀ t : Term ℒ Γ Δ .set, member_l ℳ (t.eval θ) U := by
    intro t
    match t with
    | .bvar _ => exact hρ ω
    | .fvar v => exact h₀ v
    | .app f _ => nomatch f
  have hP := PowerlessHierarchyClass.nonempty_l hℳ hω ht hT
  have h₂ : ∀ t : Term ℒ Γ Δ .set, PowerlessSourceWitnessDomain.domain_l
      (ω.eval ρ) (e.eval ρ) (T.eval ρ) (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ) (t.eval θ) :=
    fun t => ⟨δ, U, hU, hθ t⟩
  have h₃ : ψ.satisfies (PowerlessHierarchyClass.lift_l hP θ h₂) := by
    apply (sentence_formula_l _ _).mpr
    apply (Formula.satisfies_conjunctionList_iff Env.empty Ξ).mpr
    exact fun φ hφ => PowerlessClassCore.models_l hℳ hω ht hT φ (hΞ φ hφ)
  have h₄ := (PowerlessHierarchyClass.formula_l hℳ ψ θ ω e T t₁ t₂ t₃ hω ht hT h₂).mpr h₃
  have h₅ := (h₁ ψ (List.mem_cons_self) θ rfl hθ).mp h₄
  have h₆ := (sentence_formula_l (Formula.conjunctionList Ξ) _).mp h₅
  have h₇ := (Formula.satisfies_conjunctionList_iff Env.empty Ξ).mp h₆
  refine ⟨δ, U, hU₀, hδ, hαδ, hU, ?_, h₀, ?_⟩
  · rw [← PowerlessClassSeparation.structure_l U hU₀]
    exact h₇
  · intro φ hφ
    exact h₁ φ (List.mem_cons_of_mem _ hφ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceReflectionSupport
