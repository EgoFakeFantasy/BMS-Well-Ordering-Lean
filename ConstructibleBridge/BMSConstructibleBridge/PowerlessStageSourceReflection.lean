import BMSConstructibleBridge.PowerlessSourceReflectionTotal
import BMSConstructibleBridge.PowerlessStageStability

/-!
# 实际有限层稳定关系对固定源公式的反射

反射预算先于端点、求值器及参数确定。指定的两级系统通过联合唯一性
读取原始稳定关系；非空域与包含也从真实层性质取得，不新增反射公理。
这只反射成员结构内的源真值，不将内部层次公式自动解释成外部 C 层关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageSourceReflection

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessStageEvaluation

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem nonempty_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : member_l ℳ ω α) : ∃ x, member_l ℳ x A := by
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOrdinal.mem_l hA.1 hα) e T t₁ t₂ t₃
  exact ⟨B, PowerlessStageStructure.member_l hℳ hω ht hT hB hA hα⟩

theorem at_l {Γ Δ : SortContext ℒ} {φ : Formula ℒ Γ Δ}
    {n α β A B S R F G : carrier_l ℳ}
    (hφ : PowerlessSourceFiniteReflection.reflects_l ω e T t₁ t₂ t₃ n φ)
    (h : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β)
    (hA : system_l ω e T t₁ t₂ t₃ α A S F) (hB : system_l ω e T t₁ t₂ t₃ β B R G) :
    ∃ hA₀ : ∃ x, member_l ℳ x A, ∃ hB₀ : ∃ x, member_l ℳ x B, ∃ hAB : subset_l A B,
      ∀ η : Env (structure_l A hA₀) Γ Δ,
        Formula.satisfies (PowerlessSourceInclusion.env_l (hU := hB₀) hAB η) φ ↔ Formula.satisfies η φ := by
  obtain ⟨_, hp, hC⟩ := (PowerlessStageStability.compare_l hℳ hω hA hB).mp h
  have hA₀ := nonempty_l hℳ hω ht hT hA.1 hp.1
  have hAB := PowerlessStageStructure.subset_l hℳ hω hA.1 hB.1 hp.2.1
  have hB₀ : ∃ x, member_l ℳ x B := hA₀.elim (fun x hx => ⟨x, hAB x hx⟩)
  exact ⟨hA₀, hB₀, hAB, fun η => hφ hA₀ hB₀ hB.2.2 hA.2.2 hB.2.1 hAB hC η⟩

theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) :
    ∃ n, member_l ℳ n ω ∧ ∀ {α β A B S R F G : carrier_l ℳ},
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β →
      system_l ω e T t₁ t₂ t₃ α A S F → system_l ω e T t₁ t₂ t₃ β B R G →
      ∃ hA : ∃ x, member_l ℳ x A, ∃ hB : ∃ x, member_l ℳ x B, ∃ hAB : subset_l A B,
        ∀ η : Env (structure_l A hA) Γ Δ,
          Formula.satisfies (PowerlessSourceInclusion.env_l (hU := hB) hAB η) φ ↔ Formula.satisfies η φ := by
  obtain ⟨n, hn, hφ⟩ := PowerlessSourceReflectionTotal.formula_l hℳ hω ht hT φ
  exact ⟨n, hn, fun h hA hB => at_l hℳ hω ht hT hφ h hA hB⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageSourceReflection

