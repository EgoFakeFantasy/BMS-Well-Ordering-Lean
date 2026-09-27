import BMSConstructibleBridge.PowerlessSourceRequests
import BMSConstructibleBridge.PowerlessHierarchyClass

/-!
# 实际层次类的有限参数反射

先将实际有限参数放入同一层，再在更高极限层关闭原子公式请求。
层的存在性由既有原公式收集构造给出，不预设稳定对或类满足核心理论。
反射结论明确返回自由参数包含性，不以空环境条件掩盖参数缺失。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceReflection

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 每个实际有限参数族在类内时，有严格高于给定序数的共同容纳层。 -/
theorem parameters_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (α : carrier_l ℳ) (hα : PowerlessOrdinal.ordinal_l α)
    (Γ : SortContext ℒ) (a : Variable Γ .set → carrier_l ℳ)
    (ha : ∀ v, PowerlessSourceWitnessDomain.domain_l ω e T t₁ t₂ t₃ (a v)) :
    ∃ β B, member_l ℳ α β ∧ stage_l ω e T t₁ t₂ t₃ β B ∧
      ∀ v, member_l ℳ (a v) B := by
  induction Γ with
  | nil =>
    obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ α
    obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω
      (PowerlessOrdinalOrder.successor_l hℳ hα hβ) e T t₁ t₂ t₃
    exact ⟨β, B, (hβ α).mpr (Or.inr rfl), hB, fun v => nomatch v⟩
  | cons s Γ ih =>
    cases s
    obtain ⟨β, B, hαβ, hB, h₀⟩ := ih (fun v => a (.there v)) (fun v => ha (.there v))
    obtain ⟨γ, C, hC, h₁⟩ := ha .here
    obtain ⟨Q, hQ⟩ := PowerlessBasic.pairing_l hℳ β γ
    obtain ⟨δ, hδ, h₂⟩ := PowerlessOrdinalCollection.bound_l hℳ (A := Q) (by
      intro ξ hξ
      rcases (hQ ξ).mp hξ with rfl | rfl
      · exact hB.1
      · exact hC.1)
    have hβδ := h₂ β ((hQ β).mpr (Or.inl rfl))
    have hγδ := h₂ γ ((hQ γ).mpr (Or.inr rfl))
    obtain ⟨U, hU⟩ := PowerlessHierarchyStage.exists_l hℳ hω hδ e T t₁ t₂ t₃
    refine ⟨δ, U, PowerlessOrdinal.transitive_l hδ β α hβδ hαβ, hU, ?_⟩
    intro v
    cases v with
    | here => exact PowerlessStageStructure.subset_l hℳ hω hC hU hγδ _ h₁
    | there v => exact PowerlessStageStructure.subset_l hℳ hω hB hU hβδ _ (h₀ v)

/-- 原公式及其实际参数给出一个真正存在的反射层，而非假设闭包的接口。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ)
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
      ∀ θ : Env ℳ Γ Δ, PowerlessSourceClass.free_l θ = PowerlessComprehension.env_l η →
        ∀ hθ : ∀ t : Term ℒ Γ Δ .set, member_l ℳ (t.eval θ) U,
          (PowerlessSourceClass.form_m (PowerlessHierarchyClass.domain_m ω e T t₁ t₂ t₃) φ).satisfies θ ↔
            φ.satisfies (PowerlessHierarchyClass.lift_l hU₀ θ hθ) := by
  let ρ := PowerlessComprehension.env_l η
  let D := PowerlessHierarchyClass.domain_m ω e T t₁ t₂ t₃
  let P := PowerlessSourceWitnessDomain.domain_l
    (ω.eval ρ) (e.eval ρ) (T.eval ρ) (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ)
  obtain ⟨β, B, hαβ, hB, h₀⟩ := parameters_l hℳ hω α hα Δ ρ.freeVal hη
  obtain ⟨δ, U, hδ, hβδ, hU, h₁⟩ := PowerlessSourceFamily.exists_l hℳ
    (PowerlessSourceRequests.requests_m D φ) η ω e T t₁ t₂ t₃ β hω ht hT hB.1
  have hU₀ : ∃ x, member_l ℳ x U :=
    ⟨e.eval ρ, PowerlessStageClosure.empty_l hℳ hω hU hδ ht hT ht.1⟩
  refine ⟨δ, U, hU₀, hδ, PowerlessOrdinal.transitive_l hδ.1 β α hβδ hαβ, hU,
    fun v => PowerlessStageStructure.subset_l hℳ hω hB hU hβδ _ (h₀ v), ?_⟩
  intro θ hθρ hθ
  have h₂ : ∀ x, member_l ℳ x U → P x := fun x hx => ⟨δ, U, hU, hx⟩
  have h₃ := PowerlessSourceRequests.reflection_l P h₂ D φ
    (PowerlessHierarchyClass.lift_l hU₀ θ hθ) (by
      intro x
      rw [PowerlessHierarchyClass.env_l, hθρ]
      exact PowerlessHierarchyClass.domain_formula_l hℳ ρ ω e T t₁ t₂ t₃ x) (by
      rw [PowerlessHierarchyClass.env_l, hθρ]
      exact h₁)
  rw [PowerlessHierarchyClass.env_l] at h₃
  exact h₃

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceReflection
