import BMSConstructibleBridge.PowerlessSourceNaturalAbsolute
import BMSConstructibleBridge.PowerlessStageParameters

/-!
# 含实际 ω 的传递成员域正确识别原 ω 公式

归纳集合判定在传递域中绝对；内层最小性可与已在域内的实际 ω 比较，
外层最小性给反向包含，再用外部核心模型的外延性识别同一对象。
不假设子结构满足完整核心，也不从含有所有自然数偷推含有 ω。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceOmegaAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem omega_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A ω : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A}
    (hAT : PowerlessNaturalOrder.transitive_l A) (hω : ThirdOrderSemantics.omega_l ω)
    (hωA : member_l ℳ ω A) (a : type_l A) :
    ThirdOrderSemantics.omega_l (ℳ := structure_l A hA) a ↔ a.val = ω := by
  constructor
  · intro h
    have h₀ := h.2 ⟨ω, hωA⟩ ((PowerlessSourceNaturalAbsolute.inductive_l hAT).mpr hω.1)
    have h₁ := (PowerlessSourceNaturalAbsolute.subset_l hAT).mp h₀
    have h₂ := hω.2 a.val ((PowerlessSourceNaturalAbsolute.inductive_l hAT).mp h.1)
    exact (PowerlessTheory.ext_l hℳ).eq_of_same_members a.val ω (fun x => ⟨h₁ x, h₂ x⟩)
  · intro ha
    have h₀ : ThirdOrderSemantics.inductive_l a.val := ha.symm ▸ hω.1
    refine ⟨(PowerlessSourceNaturalAbsolute.inductive_l hAT).mpr h₀, ?_⟩
    intro b hb
    apply (PowerlessSourceNaturalAbsolute.subset_l hAT).mpr
    intro x hx
    exact hω.2 b.val ((PowerlessSourceNaturalAbsolute.inductive_l hAT).mp hb) x (ha ▸ hx)

theorem source_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A ω : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A}
    (hAT : PowerlessNaturalOrder.transitive_l A) (hω : ThirdOrderSemantics.omega_l ω)
    (hωA : member_l ℳ ω A) {Γ Δ : SortContext ℒ}
    (η : Env (structure_l A hA) Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderOmegaSyntax.omega_m a) ↔ (a.eval η).val = ω :=
  (ThirdOrderSemantics.omega_formula_l η a).trans (omega_l hℳ hAT hω hωA (a.eval η))

theorem stage_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hω : ThirdOrderSemantics.omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A) (hωα : member_l ℳ ω α) :
    ∃ hA₀ : ∃ a, member_l ℳ a A, ∀ (Γ Δ : SortContext ℒ)
      (η : Env (structure_l A hA₀) Γ Δ) (a : Term ℒ Γ Δ .set),
        Formula.satisfies η (SecondOrderOmegaSyntax.omega_m a) ↔ (a.eval η).val = ω := by
  have hωA := PowerlessStageParameters.omega_l hℳ hω ht hT hA hωα
  refine ⟨⟨ω, hωA⟩, ?_⟩
  intro Γ Δ η a
  exact source_l hℳ (PowerlessStageStructure.transitive_l hℳ hω ht hT hA) hω hωA η a

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceOmegaAbsolute

