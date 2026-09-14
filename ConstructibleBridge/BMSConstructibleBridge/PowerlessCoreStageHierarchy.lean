import BMSConstructibleBridge.PowerlessCoreStageHierarchyStep
import BMSConstructibleBridge.PowerlessOrdinalHistoryAbsolute
import BMSConstructibleBridge.PowerlessOrdinalHistoryCut
import BMSConstructibleBridge.PowerlessOrdinalBounded

/-!
# 满足核心公理的实际极限层中原层次图的绝对性

反向递归语义使用域内二次并作统一值域界，再用已证一般前史闭包取回见证。
层内核心是显式前提；先证内外一致，再用内部存在性和环境唯一性取回原图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageHierarchy

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U}

theorem history_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (hUT : PowerlessNaturalOrder.transitive_l U)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m) (f a : type_l U) :
    ∃ H : type_l U, PowerlessOrdinalRecursion.history_l H.val f.val a.val := by
  obtain ⟨H, hH⟩ := PowerlessOrdinalHistoryCut.exists_l h𝒩 f a
  exact ⟨H, (PowerlessOrdinalHistoryAbsolute.history_l hℳ hUT).mp hH⟩

theorem history_member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (hUT : PowerlessNaturalOrder.transitive_l U)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m)
    {f a H : carrier_l ℳ} (hf : member_l ℳ f U) (ha : member_l ℳ a U)
    (hH : PowerlessOrdinalRecursion.history_l H f a) : member_l ℳ H U := by
  obtain ⟨K, hK⟩ := history_exists_l hℳ hUT h𝒩 ⟨f, hf⟩ ⟨a, ha⟩
  exact (PowerlessOrdinalHistoryCut.unique_l hℳ hK hH) ▸ K.property

theorem ordinal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (hUT : PowerlessNaturalOrder.transitive_l U)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m) (a : type_l U) :
    PowerlessOrdinal.ordinal_l (ℳ := structure_l U hU₀) a ↔ PowerlessOrdinal.ordinal_l a.val := by
  let η : Env (structure_l U hU₀) [.set] [] := Env.empty.pushBound a
  exact (PowerlessOrdinal.ordinal_formula_l h𝒩 η (.bvar .here)).symm.trans
    (PowerlessOrdinalBounded.source_l hℳ hUT η (.bvar .here))

variable {δ : carrier_l ℳ} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m)
  (hωδ : member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ

theorem hierarchy_l {f α : type_l U} :
    PowerlessEvaluationHierarchy.hierarchy_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ f α ↔
      PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val f.val α.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  constructor
  · rintro ⟨B, hf, h⟩
    refine ⟨B.val, (PowerlessSourceGraphAbsolute.map_l hUT).mp hf, ?_⟩
    intro a Y hY
    obtain ⟨haU, hYU⟩ := PowerlessValueAbsolute.coordinates_l hUT f.property hY
    obtain ⟨H, hH, h⟩ := h ⟨a, haU⟩ ⟨Y, hYU⟩ ((PowerlessSourceGraphAbsolute.value_l hUT).mpr hY)
    exact ⟨H.val, (PowerlessOrdinalHistoryAbsolute.history_l hℳ hUT).mp hH,
      (PowerlessCoreStageHierarchyStep.step_l hℳ hω ht hT hU hδ h𝒩 hωδ).mp h⟩
  · rintro ⟨B, hf, h⟩
    obtain ⟨D, hD⟩ := PowerlessOrdinalHistoryAbsolute.bounds_l hℳ (B := U)
      (fun a ha b hb => PowerlessStageClosure.union_l hℳ hω hU hδ
        ht hT ha hb) f
    refine ⟨D, (PowerlessSourceGraphAbsolute.map_l hUT).mpr (PowerlessFunction.range_l hℳ hf hD), ?_⟩
    intro a Y hY
    obtain ⟨H, hH, h⟩ := h a.val Y.val ((PowerlessSourceGraphAbsolute.value_l hUT).mp hY)
    have hHU := history_member_l hℳ hUT h𝒩 f.property a.property hH
    exact ⟨⟨H, hHU⟩, (PowerlessOrdinalHistoryAbsolute.history_l hℳ hUT).mpr hH,
      (PowerlessCoreStageHierarchyStep.step_l hℳ hω ht hT hU hδ h𝒩 hωδ).mpr h⟩

theorem exists_l (α : type_l U) (hα : PowerlessOrdinal.ordinal_l α.val) : ∃ f : type_l U,
    PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val f.val α.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hω₀ := (PowerlessSourceOmegaAbsolute.omega_l (hA := hU₀) hℳ hUT hω ω.property ω).mpr rfl
  obtain ⟨f, hf, _⟩ := PowerlessEvaluationHierarchy.exists_unique_l
    h𝒩 hω₀
    ((ordinal_l hℳ hUT h𝒩 α).mpr hα) e T t₁ t₂ t₃
  exact ⟨f, (hierarchy_l hℳ hω ht hT hU hδ h𝒩 hωδ).mp hf⟩

theorem member_l {α f : carrier_l ℳ} (hα : PowerlessOrdinal.ordinal_l α) (hαU : member_l ℳ α U)
    (hf : PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val f α) :
    member_l ℳ f U := by
  obtain ⟨g, hg⟩ := exists_l hℳ hω ht hT hU hδ h𝒩 hωδ ⟨α, hαU⟩ hα
  obtain ⟨F, _, h⟩ := PowerlessEvaluationHierarchy.exists_unique_l hℳ hω hα
    e.val T.val t₁.val t₂.val t₃.val
  exact (h g.val hg).trans (h f hf).symm ▸ g.property

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageHierarchy
