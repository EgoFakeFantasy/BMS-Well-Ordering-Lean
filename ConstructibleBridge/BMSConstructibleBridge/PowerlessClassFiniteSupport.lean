import BMSConstructibleBridge.PowerlessClassCore

/-!
# 任意有限核心支持都有实际层模型

完整类模型满足给定有限核心列表；将其原合取闭句在真实层次类中
反射到更高真极限层，再回到既有成员结构。不存在稳定对或小层
满足支持的未证前提；环境核心及指定列表属于核心仍显式保留。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassFiniteSupport

open Logic FirstOrder ThirdOrderSemantics PowerlessSourceWitnessDomain PowerlessSourcePadding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessSourceClass.structure_l
  PowerlessSourceClass.type_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (Φ : List (Sentence ℒ)) (hΦ : ∀ φ ∈ Φ, PowerlessTheory.theory_m φ)
    (α : carrier_l ℳ) (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U, ∃ hU₀ : ∃ x, member_l ℳ x U,
      PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ δ U ∧
      Theory.Models (PowerlessMemberStructure.structure_l U hU₀) (Theory.ofList Φ) := by
  let P := domain_l ω e T t₁ t₂ t₃
  have hP := PowerlessHierarchyClass.nonempty_l hℳ hω ht hT
  have q := PowerlessClassBasic.parameters_l hℳ hω ht hT
  let a : PowerlessSourceClass.type_l P := ⟨ω, q.1⟩
  let b : PowerlessSourceClass.type_l P := ⟨e, q.2.1⟩
  let c : PowerlessSourceClass.type_l P := ⟨T, q.2.2.1⟩
  let d : PowerlessSourceClass.type_l P := ⟨t₁, q.2.2.2.1⟩
  let f : PowerlessSourceClass.type_l P := ⟨t₂, q.2.2.2.2.1⟩
  let g : PowerlessSourceClass.type_l P := ⟨t₃, q.2.2.2.2.2⟩
  let ξ := env_l (Env.empty (M := PowerlessSourceClass.structure_l P hP)) a b c d f g b
  let ψ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    Formula.fromSentence (Formula.conjunctionList Φ)
  let D := PowerlessHierarchyClass.domain_m (omega_m (Δ := [])) zero_m triangle_m tag₁_m tag₂_m tag₃_m
  obtain ⟨ζ, hζ⟩ := PowerlessSourceParameters.env_exists_l (PowerlessSourceClass.env_l ξ)
  have hω₀ : omega_l (omega_m.eval (PowerlessComprehension.env_l ζ)) := by rw [hζ]; exact hω
  have ht₀ : PowerlessEvaluationTags.tags_l (zero_m.eval (PowerlessComprehension.env_l ζ))
      (tag₁_m.eval (PowerlessComprehension.env_l ζ)) (tag₂_m.eval (PowerlessComprehension.env_l ζ))
      (tag₃_m.eval (PowerlessComprehension.env_l ζ)) := by rw [hζ]; exact ht
  have hT₀ : PowerlessTriangular.triangular_l (omega_m.eval (PowerlessComprehension.env_l ζ))
      (zero_m.eval (PowerlessComprehension.env_l ζ)) (triangle_m.eval (PowerlessComprehension.env_l ζ)) := by
    rw [hζ]; exact hT
  have h₀ : Theory.Models (PowerlessSourceClass.structure_l P hP) (Theory.ofList Φ) :=
    fun φ hφ => PowerlessClassCore.models_l hℳ hω ht hT φ (hΦ φ hφ)
  have h₁ := (Formula.satisfies_conjunctionList_iff Env.empty Φ).mpr h₀
  have h₂ : ψ.satisfies ξ := (Formula.satisfies_fromSentence ξ (Formula.conjunctionList Φ)).mpr h₁
  have h₃ : (PowerlessSourceClass.form_m D ψ).satisfies (PowerlessComprehension.env_l ζ) := by
    rw [hζ]
    exact (PowerlessSourceClass.formula_l D ψ ξ (fun y =>
      PowerlessHierarchyClass.domain_formula_l hℳ _ omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m y)).mpr h₂
  obtain ⟨δ, U, hU₀, hδ, hαδ, hU, h₄, h₅⟩ := PowerlessSourceReflection.exists_l hℳ ψ ζ
    omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m α hω₀ ht₀ hT₀ hα (by
      intro v
      rw [hζ]
      exact (ξ.freeVal v).property)
  have hρ : ∀ t : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set,
      member_l ℳ (t.eval (PowerlessComprehension.env_l ζ)) U := by
    intro t
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact h₄ v
    | .app f _ => nomatch f
  have h₆ := (h₅ (PowerlessComprehension.env_l ζ) rfl hρ).mp h₃
  have h₇ := (Formula.satisfies_fromSentence
    (PowerlessHierarchyClass.lift_l hU₀ (PowerlessComprehension.env_l ζ) hρ)
    (Formula.conjunctionList Φ)).mp h₆
  have h₈ := (Formula.satisfies_conjunctionList_iff Env.empty Φ).mp h₇
  rw [hζ] at hU
  refine ⟨δ, U, hU₀, hδ, hαδ, hU, ?_⟩
  rw [← PowerlessClassSeparation.structure_l U hU₀]
  exact h₈

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassFiniteSupport

