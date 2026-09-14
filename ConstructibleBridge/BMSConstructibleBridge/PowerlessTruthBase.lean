import BMSConstructibleBridge.PowerlessStageBoundedTruth
import BMSConstructibleBridge.PowerlessStageAmbientAssignments
import BMSConstructibleBridge.PowerlessTruthSign

/-!
# 有符号局部证书的有界真值基例

有限赋值 guard 保留，真假两侧读取同一个已证明的有界真值公式。
有界代码识别由上层证书另行检查；本公式不含当前域或完整求值图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthBase

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def rule_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let φ := PowerlessBoundedTruth.truth_m ω e T t₁ t₂ t₃ c f
  .conj (PowerlessAmbientAssignments.finite_m ω f)
    (.disj (.conj (.equal p e) φ) (.conj (.equal p t₁) (.neg φ)))

theorem source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
    {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ p c f : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hc : PowerlessBoundedCertificate.recognizes_l ω.val e.val T.val t₁.val t₂.val t₃.val (c.eval η).val) :
    (rule_m w z V s₁ s₂ s₃ p c f).satisfies η ↔
      (∃ n, member_l ℳ n ω.val ∧ map_l (f.eval η).val n U) ∧
        PowerlessTruthSign.sign_l e.val t₁.val H (p.eval η).val (c.eval η).val (f.eval η).val := by
  let φ := PowerlessBoundedTruth.truth_m w z V s₁ s₂ s₃ c f
  have hp : p.eval η = z.eval η ↔ (p.eval η).val = e.val :=
    ⟨fun h => (congrArg Subtype.val h).trans hz, fun h => Subtype.ext (h.trans hz.symm)⟩
  have hq : p.eval η = s₁.eval η ↔ (p.eval η).val = t₁.val :=
    ⟨fun h => (congrArg Subtype.val h).trans hs₁, fun h => Subtype.ext (h.trans hs₁.symm)⟩
  have h₀ (hf : ∃ n, member_l ℳ n ω.val ∧ map_l (f.eval η).val n U) :
      ((p.eval η = z.eval η ∧ φ.satisfies η) ∨
        (p.eval η = s₁.eval η ∧ ¬ φ.satisfies η)) ↔
          PowerlessTruthSign.sign_l e.val t₁.val H (p.eval η).val (c.eval η).val (f.eval η).val := by
    have hφ := PowerlessStageBoundedTruth.source_l hℳ hω ht hT hU hδ hωδ h𝒩
      hR hH η w z V s₁ s₂ s₃ c f hw hz hV hs₁ hs₂ hs₃ hc hf
    exact or_congr (and_congr hp hφ) (and_congr hq (not_congr hφ))
  change ((PowerlessAmbientAssignments.finite_m w f).satisfies η ∧
    ((p.eval η = z.eval η ∧ φ.satisfies η) ∨
      (p.eval η = s₁.eval η ∧ ¬ φ.satisfies η))) ↔ _
  rw [PowerlessStageAmbientAssignments.finite_source_l hℳ hω ht hT hU hδ η w f hw]
  exact ⟨fun ⟨hf, h⟩ => ⟨hf, (h₀ hf).mp h⟩, fun ⟨hf, h⟩ => ⟨hf, (h₀ hf).mpr h⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthBase
