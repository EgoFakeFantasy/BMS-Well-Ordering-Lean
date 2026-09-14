import BMSConstructibleBridge.PowerlessFiniteStageHierarchy
import BMSConstructibleBridge.PowerlessSourceNaturalAbsolute

/-!
# 原单层公式在有限核心早层中的解释

保留原 stage_m 的序数条件和两个存在量词；后继由添元闭包取回，
层次函数图由已证有限支持取回，不使用小结构的完整核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageSource

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageHierarchy.theory_m)
  (hωδ : member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ α A : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessHierarchyStage.stage_m w z V s₁ s₂ s₃ α A).satisfies η ↔
      PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val (α.eval η).val (A.eval η).val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  let q (t : Term ℒ Γ Δ .set) :=
    (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  have hs (β f : type_l U) :
      (PowerlessNaturalStep.successor_m (q α) (.bvar (.there .here))).satisfies ((η.pushBound β).pushBound f) ↔
      PowerlessNatural.successor_l (α.eval η).val β.val := by
    have h := (PowerlessNaturalStep.successor_formula_l ((η.pushBound β).pushBound f) (q α)
      (.bvar (.there .here))).trans (PowerlessSourceNaturalAbsolute.successor_l hUT)
    simp only [q, Term.eval_weakenBound] at h
    simpa only [Term.eval, Env.pushBound, Assignment.push] using h
  have hf (β f : type_l U) :
      (PowerlessHierarchyPresentation.hierarchy_m (q w) (q z) (q V) (q s₁) (q s₂) (q s₃)
        (.bvar .here) (.bvar (.there .here))).satisfies ((η.pushBound β).pushBound f) ↔
      PowerlessEvaluationHierarchy.hierarchy_l ω.val e.val T.val t₁.val t₂.val t₃.val f.val β.val := by
    have h := PowerlessFiniteHierarchySource.source_l hℳ hω ht hT hU hδ
      (PowerlessFiniteStageHierarchy.operator_models_l h𝒩) hωδ ((η.pushBound β).pushBound f)
      (q w) (q z) (q V) (q s₁) (q s₂) (q s₃) (.bvar .here) (.bvar (.there .here))
      (by simpa only [q, Term.eval_weakenBound] using hw)
      (by simpa only [q, Term.eval_weakenBound] using hz)
      (by simpa only [q, Term.eval_weakenBound] using hV)
      (by simpa only [q, Term.eval_weakenBound] using hs₁)
      (by simpa only [q, Term.eval_weakenBound] using hs₂)
      (by simpa only [q, Term.eval_weakenBound] using hs₃)
    simpa only [Term.eval, Env.pushBound, Assignment.push] using h
  have hv (β f : type_l U) :
      (SecondOrderObjectSyntax.value_m (.bvar .here) (q α) (q A)).satisfies ((η.pushBound β).pushBound f) ↔
      value_l f.val (α.eval η).val (A.eval η).val := by
    have h := (value_formula_l ((η.pushBound β).pushBound f) (.bvar .here) (q α) (q A)).trans
      (PowerlessSourceGraphAbsolute.value_l hUT)
    simp only [q, Term.eval_weakenBound] at h
    simpa only [Term.eval, Env.pushBound, Assignment.push] using h
  simp only [PowerlessHierarchyStage.stage_m, PowerlessHierarchyStage.stage_l, Formula.satisfies]
  rw [PowerlessOrdinalBounded.source_l hℳ hUT η α]
  apply and_congr_right
  intro hα
  constructor
  · rintro ⟨β, f, hβ, hF, hA⟩
    exact ⟨β.val, f.val, (hs β f).mp hβ, (hf β f).mp hF, (hv β f).mp hA⟩
  · rintro ⟨β, f, hβ, hF, hA⟩
    have hβU := PowerlessStageGraphClosure.adjoin_l hℳ hω ht hT hU hδ
      (α.eval η).property (α.eval η).property hβ
    have hfU := PowerlessFiniteStageHierarchy.member_l hℳ hω ht hT hU hδ h𝒩 hωδ
      (PowerlessOrdinalOrder.successor_l hℳ hα hβ) hβU hF
    exact ⟨⟨β, hβU⟩, ⟨f, hfU⟩, (hs ⟨β, hβU⟩ ⟨f, hfU⟩).mpr hβ,
      (hf ⟨β, hβU⟩ ⟨f, hfU⟩).mpr hF, (hv ⟨β, hβU⟩ ⟨f, hfU⟩).mpr hA⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageSource
