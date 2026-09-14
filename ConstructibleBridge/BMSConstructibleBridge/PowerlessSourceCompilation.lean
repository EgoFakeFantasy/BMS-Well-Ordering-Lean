import BMSConstructibleBridge.PowerlessSourceReservation

/-!
# 全部上游纯集合公式的内部数码与语义对应

从固定末尾槽的统一容量定理，取无受保护变量的特例。每个公式得到
实际内部数码和最小赋值界，真值对应覆盖所有充分长的内部有限赋值。
初始源环境如何实现为实际有限图，是后续单独的存在性义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceCompilation

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceEnvironment PowerlessSourceSpecification

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m A)
    (hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ Γ Δ) (ξ : Env ℳ Γ Δ) {k : carrier_l ℳ}
    (hk : ThirdOrderSemantics.member_l ℳ k ω) (hξ : bounded_l ξ k) :
    ∃ c N, ThirdOrderSemantics.member_l ℳ c ω ∧ ThirdOrderSemantics.member_l ℳ N ω ∧
      subset_l k N ∧ spec_l ω A F c N hA ξ φ := by
  obtain ⟨J, hJ, hkJ, h⟩ := PowerlessSourceReservation.formula_l hℳ hω ht hT hF hS hA φ hk
  obtain ⟨M, hM⟩ := PowerlessNatural.successor_exists_l hℳ J
  obtain ⟨c, hc, h₀⟩ := h J hJ (fun _ hx => hx) M hM ξ (fun t => Or.inl (hξ t))
  exact ⟨c, M, hc, PowerlessNatural.successor_mem_l hℳ hω hJ hM,
    (fun x hx => (hM x).mpr (Or.inl (hkJ x hx))), h₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceCompilation
