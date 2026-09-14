import BMSConstructibleBridge.PowerlessFiniteStageStability
import BMSConstructibleBridge.ThirdOrderFiniteStageHierarchy

/-!
# 统一有限预算下原稳定公式的实际早层解释

预算先于早层、源环境、内部稳定层号和端点确定。早层的有限模型性
与六个实际编码参数均由已有构造取得，不作为调用者的额外假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderFiniteStageStability

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U) :
    ∃ m, member_l ℳ m ω ∧ ∀ {δ A : carrier_l ℳ},
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m δ κ →
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ δ A →
      ∃ hA₀ : ∃ x, member_l ℳ x A, ∀ {Γ Δ : SortContext ℒ}
        (η : Env (structure_l A hA₀) Γ Δ) (w z V s₁ s₂ s₃ n α β : Term ℒ Γ Δ .set),
        (w.eval η).val = ω → (z.eval η).val = e → (V.eval η).val = T →
        (s₁.eval η).val = t₁ → (s₂.eval η).val = t₂ → (s₃.eval η).val = t₃ →
        ((PowerlessStageStability.stable_m w z V s₁ s₂ s₃ n α β).satisfies η ↔
          PowerlessStageStability.stable_l ω e T t₁ t₂ t₃
            (n.eval η).val (α.eval η).val (β.eval η).val) := by
  obtain ⟨m, hm, h⟩ := ThirdOrderFiniteStageHierarchy.models_l hℳ hω hκ ht hT hU
  refine ⟨m, hm, ?_⟩
  intro δ A hs hA
  obtain ⟨hA₀, h𝒩⟩ := h hs hA
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hp := hs.2.1
  obtain ⟨hw, hz, hV, hs₁, hs₂, hs₃⟩ :=
    PowerlessStageTriangular.parameters_l h₀ hω ht hT hA hp.1 hp.2.2.1
  refine ⟨hA₀, ?_⟩
  intro Γ Δ η w z V s₁ s₂ s₃ n α β h₁ h₂ h₃ h₄ h₅ h₆
  exact PowerlessFiniteStageStability.source_l
    (ω := ⟨ω, hw⟩) (e := ⟨e, hz⟩) (T := ⟨T, hV⟩)
    (t₁ := ⟨t₁, hs₁⟩) (t₂ := ⟨t₂, hs₂⟩) (t₃ := ⟨t₃, hs₃⟩)
    h₀ hω ht hT hA hp.2.2.1 h𝒩 hp.1 η w z V s₁ s₂ s₃ n α β h₁ h₂ h₃ h₄ h₅ h₆

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderFiniteStageStability
