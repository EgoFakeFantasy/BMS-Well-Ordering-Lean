import BMSConstructibleBridge.ThirdOrderStageElementary
import BMSConstructibleBridge.PowerlessOperatorClosure

/-!
# Cκ 成员结构中的完整源分离和收集

分离由初等早级的原源覆盖构造；收集以同一初等早级作为实际集合界。
只量化原 Formula 及任意有限参数环境，不假定成员结构已满足核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageComprehension

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)
  {hU₀ : ∃ x, member_l ℳ x U}

include hℳ hω hκ ht hT hU

theorem separation_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ)
    (η : Env (structure_l U hU₀) Γ Δ) (A : type_l U) :
    ∃ Y : type_l U, ∀ x : type_l U,
      member_l (structure_l U hU₀) x Y ↔ member_l (structure_l U hU₀) x A ∧ φ.satisfies (η.pushBound x) := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨β, B, hBU, hB₀, hβ, hB, _, _, hAB, hE, ζ, hζ⟩ :=
    ThirdOrderStageElementary.environment_l hℳ hω hκ ht hT hU A.property η
  have hBT := PowerlessStageStructure.transitive_l h₀ hω ht hT hB
  let ρ : Renaming ℒ (.set :: Γ) Δ (.set :: .set :: Γ) Δ :=
    .map (fun {s} v => match v with
      | .here => .here
      | .there v => .there (.there v)) (fun v => v)
  let ψ : Formula ℒ (.set :: .set :: Γ) Δ :=
    .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))) (φ.rename ρ)
  have hr (x : type_l B) :
      (φ.rename ρ).satisfies ((ζ.pushBound ⟨A.val, hAB⟩).pushBound x) ↔ φ.satisfies (ζ.pushBound x) := by
    rw [Formula.satisfies_rename]
    have h : ((ζ.pushBound ⟨A.val, hAB⟩).pushBound x).pullbackRenaming ρ = ζ.pushBound x := by
      apply Env.ext
      · intro s v
        cases v <;> rfl
      · intro s v
        rfl
    rw [h]
  have hψ (x : type_l B) :
      ψ.satisfies ((ζ.pushBound ⟨A.val, hAB⟩).pushBound x) ↔
        member_l ℳ x.val A.val ∧ φ.satisfies (ζ.pushBound x) := by
    change (member_l ℳ x.val A.val ∧ (φ.rename ρ).satisfies
      ((ζ.pushBound ⟨A.val, hAB⟩).pushBound x)) ↔ _
    exact and_congr Iff.rfl (hr x)
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l h₀ hω e T t₁ t₂ t₃ B
  obtain ⟨Y, hYD, hY⟩ := PowerlessSourceCoverage.operator_l h₀ hω ht hT hD ψ (ζ.pushBound ⟨A.val, hAB⟩)
  refine ⟨⟨Y, PowerlessStageClosure.image_l h₀ hω hU hB hβ hD Y hYD⟩, ?_⟩
  intro x
  have hφ (hx : member_l ℳ x.val B) :
      φ.satisfies (η.pushBound x) ↔ φ.satisfies (ζ.pushBound ⟨x.val, hx⟩) := by
    have h := hE _ _ φ (ζ.pushBound ⟨x.val, hx⟩)
    rw [PowerlessSourceInclusion.push_l (hA := hB₀) (hU := hU₀) hBU ζ ⟨x.val, hx⟩, hζ] at h
    exact h
  constructor
  · intro hx
    obtain ⟨hxB, hx⟩ := (hY x.val).mp hx
    obtain ⟨hxA, hx⟩ := (hψ ⟨x.val, hxB⟩).mp hx
    exact ⟨hxA, (hφ hxB).mpr hx⟩
  · rintro ⟨hxA, hx⟩
    have hxB := hBT A.val x.val hAB hxA
    exact (hY x.val).mpr ⟨hxB, (hψ ⟨x.val, hxB⟩).mpr ⟨hxA, (hφ hxB).mp hx⟩⟩

theorem collection_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: .set :: Γ) Δ)
    (η : Env (structure_l U hU₀) Γ Δ) (A : type_l U)
    (h : ∀ x : type_l U, member_l (structure_l U hU₀) x A →
      ∃ y : type_l U, φ.satisfies ((η.pushBound x).pushBound y)) :
    ∃ B : type_l U, ∀ x : type_l U, member_l (structure_l U hU₀) x A →
      ∃ y : type_l U, member_l (structure_l U hU₀) y B ∧ φ.satisfies ((η.pushBound x).pushBound y) := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨β, B, hBU, hB₀, hβ, hB, _, _, hAB, hE, ζ, hζ⟩ :=
    ThirdOrderStageElementary.environment_l hℳ hω hκ ht hT hU A.property η
  have hBT := PowerlessStageStructure.transitive_l h₀ hω ht hT hB
  refine ⟨⟨B, PowerlessStageStructure.member_l h₀ hω ht hT hB hU hβ⟩, ?_⟩
  intro x hx
  let x₀ : type_l B := ⟨x.val, hBT A.val x.val hAB hx⟩
  have h₁ := hE _ _ (.existsE .set φ) (ζ.pushBound x₀)
  rw [PowerlessSourceInclusion.push_l, hζ] at h₁
  obtain ⟨y, hy⟩ := h₁.mp (h x hx)
  have h₂ := hE _ _ φ ((ζ.pushBound x₀).pushBound y)
  rw [PowerlessSourceInclusion.push_l, PowerlessSourceInclusion.push_l, hζ] at h₂
  exact ⟨PowerlessSourceInclusion.inclusion_l hBU y, y.property, h₂.mpr hy⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageComprehension
