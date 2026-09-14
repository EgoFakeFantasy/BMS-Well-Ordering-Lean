import BMSConstructibleBridge.ThirdOrderStageLimit
import BMSConstructibleBridge.PowerlessStageFiniteGraphs
import BMSConstructibleBridge.PowerlessValueAbsolute

/-!
# 任意有限源环境共同落入实际初等早级

先用原源环境的有限图表示收拢所有参数，再调用已证的共尾初等层。
所得环境沿真实包含映射恰好回到原环境；不预设早级或 Cκ 的核心公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageElementary

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem environment_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U a : carrier_l ℳ} (hω : omega_l ω)
    (hκ : ThirdOrderOmegaOne.first_l ω κ) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)
    {hU₀ : ∃ x, member_l ℳ x U} (ha : member_l ℳ a U)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ) :
    ∃ β B, ∃ hBU : subset_l B U, ∃ hB₀ : ∃ x, member_l ℳ x B,
      member_l ℳ β κ ∧ PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B ∧
      member_l ℳ ω β ∧ PowerlessStagePair.limit_l β ∧ member_l ℳ a B ∧
      PowerlessSourceElementarity.elementary_l hB₀ hU₀ hBU ∧
      ∃ ζ : Env (structure_l B hB₀) Γ Δ, PowerlessSourceInclusion.env_l hBU ζ = η := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hωκ := ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ
  obtain ⟨n, f, ξ, hn, hf, _, hη⟩ := PowerlessSourceRealization.exists_l h₀ hω η
  have hfU := PowerlessStageFiniteGraphs.finite_l h₀ hω ht hT hU (ThirdOrderStageLimit.limit_l h₀ hω hκ)
    (fun x hx => PowerlessOrdinal.transitive_l hκ.1 ω x hωκ hx) n hn f hf
  obtain ⟨α, A, hα, hA, hωα, _, haA, hfA⟩ := ThirdOrderStageLimit.pair_l hℳ hω hκ ht hT hU ha hfU
  obtain ⟨S, hS⟩ := PowerlessFiniteAssignments.all_exists_l h₀ hω U
  obtain ⟨F, hF, _⟩ := PowerlessEvaluationRecursion.exists_unique_l h₀ hω e T U t₁ t₂ t₃ S
  obtain ⟨β, B, R, G, hBU, hB₀, hβ, hαβ, hB, _, hL, hBT, _, _, _, _, hE⟩ :=
    ThirdOrderSourceReflection.exists_l hℳ hω hκ ht hT hU hU₀ hS hF hα
  have hAB := PowerlessStageStructure.subset_l h₀ hω hA hB hαβ
  have hfB := hAB f hfA
  have hηB (t : Term ℒ Γ Δ .set) : member_l ℳ (t.eval η).val B :=
    (PowerlessValueAbsolute.coordinates_l hBT hfB (hη t)).2
  let ζ : Env (structure_l B hB₀) Γ Δ :=
    { boundVal := fun {s} v => match s with
        | .set => ⟨(η.boundVal v).val, hηB (.bvar v)⟩
      freeVal := fun {s} v => match s with
        | .set => ⟨(η.freeVal v).val, hηB (.fvar v)⟩ }
  have hωβ := PowerlessOrdinal.transitive_l hB.1 α ω hαβ hωα
  refine ⟨β, B, hBU, hB₀, hβ, hB, hωβ, ⟨hB.1, ⟨ω, hωβ⟩, hL⟩, hAB a haA, hE, ζ, ?_⟩
  apply Env.ext
  · intro s v
    cases s
    rfl
  · intro s v
    cases s
    rfl

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageElementary
