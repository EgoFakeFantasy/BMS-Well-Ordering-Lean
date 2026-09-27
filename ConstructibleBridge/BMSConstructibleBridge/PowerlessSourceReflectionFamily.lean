import BMSConstructibleBridge.PowerlessSourceReflection

/-!
# 原公式有限列表的共同反射层

合并每个原公式的实际子公式请求，构造一个共同真极限层。
自由参数固定而绑定参数遍历该层；不预设层间稳定性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceReflectionFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (Φ : List (Formula ℒ Γ Δ))
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
      (∀ v : Variable Δ .set, member_l ℳ ((PowerlessComprehension.env_l η).freeVal v) U) ∧
      ∀ φ ∈ Φ, ∀ θ : Env ℳ Γ Δ, PowerlessSourceClass.free_l θ = PowerlessComprehension.env_l η →
        ∀ hθ : ∀ t : Term ℒ Γ Δ .set, member_l ℳ (t.eval θ) U,
          (PowerlessSourceClass.form_m (PowerlessHierarchyClass.domain_m ω e T t₁ t₂ t₃) φ).satisfies θ ↔
            φ.satisfies (PowerlessHierarchyClass.lift_l hU₀ θ hθ) := by
  let ρ := PowerlessComprehension.env_l η
  let D := PowerlessHierarchyClass.domain_m ω e T t₁ t₂ t₃
  let P := PowerlessSourceWitnessDomain.domain_l
    (ω.eval ρ) (e.eval ρ) (T.eval ρ) (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ)
  obtain ⟨β, B, hαβ, hB, h₀⟩ := PowerlessSourceReflection.parameters_l hℳ hω α hα Δ ρ.freeVal hη
  obtain ⟨δ, U, hδ, hβδ, hU, h₁⟩ := PowerlessSourceFamily.exists_l hℳ
    (Φ.flatMap (PowerlessSourceRequests.requests_m D)) η ω e T t₁ t₂ t₃ β hω ht hT hB.1
  have hU₀ : ∃ x, member_l ℳ x U :=
    ⟨e.eval ρ, PowerlessStageClosure.empty_l hℳ hω hU hδ ht hT ht.1⟩
  refine ⟨δ, U, hU₀, hδ, PowerlessOrdinal.transitive_l hδ.1 β α hβδ hαβ, hU,
    fun v => PowerlessStageStructure.subset_l hℳ hω hB hU hβδ _ (h₀ v), ?_⟩
  intro φ hφ θ hθρ hθ
  have h₂ : ∀ x, member_l ℳ x U → P x := fun x hx => ⟨δ, U, hU, hx⟩
  have h₃ := PowerlessSourceRequests.reflection_l P h₂ D φ
    (PowerlessHierarchyClass.lift_l hU₀ θ hθ) (by
      intro x
      rw [PowerlessHierarchyClass.env_l, hθρ]
      exact PowerlessHierarchyClass.domain_formula_l hℳ ρ ω e T t₁ t₂ t₃ x) (by
      rw [PowerlessHierarchyClass.env_l, hθρ]
      exact PowerlessSourceRequests.subset_l
        (fun p hp => List.mem_flatMap.mpr ⟨φ, hφ, hp⟩) h₁)
  rw [PowerlessHierarchyClass.env_l] at h₃
  exact h₃

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceReflectionFamily

