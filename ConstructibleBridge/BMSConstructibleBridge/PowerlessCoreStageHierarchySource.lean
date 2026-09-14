import BMSConstructibleBridge.PowerlessCoreStageHierarchy

/-! # 原 hierarchy_m 与 stage_m 在满足核心公理的实际极限层中的解释 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageHierarchySource

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m)
  (hωδ : member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ

theorem stage_l {α A : type_l U} :
    PowerlessHierarchyStage.stage_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ α A ↔
      PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val α.val A.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  constructor
  · rintro ⟨hα, β, f, hβ, hf, hA⟩
    exact ⟨(PowerlessCoreStageHierarchy.ordinal_l hℳ hUT h𝒩 α).mp hα, β.val, f.val,
      (PowerlessSourceNaturalAbsolute.successor_l hUT).mp hβ,
      (PowerlessCoreStageHierarchy.hierarchy_l hℳ hω ht hT hU hδ h𝒩 hωδ).mp hf,
      (PowerlessSourceGraphAbsolute.value_l hUT).mp hA⟩
  · rintro ⟨hα, β, f, hβ, hf, hA⟩
    have hβU := PowerlessStageGraphClosure.adjoin_l hℳ hω ht hT hU hδ
      α.property α.property hβ
    have hfU := PowerlessCoreStageHierarchy.member_l hℳ hω ht hT hU hδ h𝒩 hωδ
      (PowerlessOrdinalOrder.successor_l hℳ hα hβ) hβU hf
    exact ⟨(PowerlessCoreStageHierarchy.ordinal_l hℳ hUT h𝒩 α).mpr hα, ⟨β, hβU⟩, ⟨f, hfU⟩,
      (PowerlessSourceNaturalAbsolute.successor_l hUT).mpr hβ,
      (PowerlessCoreStageHierarchy.hierarchy_l hℳ hω ht hT hU hδ h𝒩 hωδ).mpr hf,
      (PowerlessSourceGraphAbsolute.value_l hUT).mpr hA⟩

variable {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
  (w z V s₁ s₂ s₃ : Term ℒ Γ Δ .set)
  (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
  (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)

include hw hz hV hs₁ hs₂ hs₃

theorem hierarchy_source_l (f α : Term ℒ Γ Δ .set) :
    (PowerlessHierarchyPresentation.hierarchy_m w z V s₁ s₂ s₃ f α).satisfies η ↔
      PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val (f.eval η).val (α.eval η).val := by
  have h := PowerlessHierarchyPresentation.hierarchy_formula_l h𝒩
    η w z V s₁ s₂ s₃ f α
  rw [show w.eval η = ω from Subtype.ext hw, show z.eval η = e from Subtype.ext hz,
    show V.eval η = T from Subtype.ext hV, show s₁.eval η = t₁ from Subtype.ext hs₁,
    show s₂.eval η = t₂ from Subtype.ext hs₂, show s₃.eval η = t₃ from Subtype.ext hs₃] at h
  exact h.trans (PowerlessCoreStageHierarchy.hierarchy_l hℳ hω ht hT hU hδ h𝒩 hωδ)

theorem stage_source_l (α A : Term ℒ Γ Δ .set) :
    (PowerlessHierarchyStage.stage_m w z V s₁ s₂ s₃ α A).satisfies η ↔
      PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val (α.eval η).val (A.eval η).val := by
  have h := PowerlessHierarchyStage.stage_formula_l h𝒩
    η w z V s₁ s₂ s₃ α A
  rw [show w.eval η = ω from Subtype.ext hw, show z.eval η = e from Subtype.ext hz,
    show V.eval η = T from Subtype.ext hV, show s₁.eval η = t₁ from Subtype.ext hs₁,
    show s₂.eval η = t₂ from Subtype.ext hs₂, show s₃.eval η = t₃ from Subtype.ext hs₃] at h
  exact h.trans (stage_l hℳ hω ht hT hU hδ h𝒩 hωδ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageHierarchySource
