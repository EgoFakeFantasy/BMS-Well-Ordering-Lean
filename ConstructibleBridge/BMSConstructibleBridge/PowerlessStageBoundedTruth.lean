import BMSConstructibleBridge.PowerlessBoundedTruthSource

/-!
# 有界真值公式读取整个当前层的求值

当前域 U 与它的完整求值图 H 只出现在正确性定理中，不是源公式参数。
反向把同一赋值图放入较早的传递层，取得实际域内求值见证；
结论覆盖全部内部有界证书，不把内部公式码当作外部有限语法树。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageBoundedTruth

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
  (hωδ : member_l ℳ ω.val δ)

variable (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)

include hℳ hω ht hT hU hδ hωδ h𝒩


theorem source_l {R H : carrier_l ℳ}
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ c f : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hc : PowerlessBoundedCertificate.recognizes_l ω.val e.val T.val t₁.val t₂.val t₃.val (c.eval η).val)
    (hf : ∃ n, member_l ℳ n ω.val ∧ map_l (f.eval η).val n U) :
    (PowerlessBoundedTruth.truth_m w z V s₁ s₂ s₃ c f).satisfies η ↔
      PowerlessEvaluationClause.query_l H (c.eval η).val (f.eval η).val := by
  rw [PowerlessBoundedTruthSource.source_l hℳ hω ht hT hU hδ hωδ η w z V s₁ s₂ s₃ c f hw hz hV hs₁ hs₂ hs₃]
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  constructor
  · rintro ⟨A, S, F, n, h⟩
    exact PowerlessBoundedTruth.sound_l hℳ hω ht hT hR hH
      (fun x hx => hUT A.val x A.property hx) hc h
  · intro h
    obtain ⟨n, hn, hf⟩ := hf
    obtain ⟨β, A, hβ, hA, hfA⟩ :=
      (PowerlessStageStructure.limit_l hℳ hω hU hδ.2.2 (f.eval η).val).mp (f.eval η).property
    have hAT := PowerlessStageStructure.transitive_l hℳ hω ht hT hA
    have hAU := PowerlessStageStructure.subset_l hℳ hω hA hU hβ
    have hA₀ := PowerlessStageStructure.member_l hℳ hω ht hT hA hU hβ
    have hf₀ : map_l (f.eval η).val n A := PowerlessFunction.range_l hℳ hf
      (fun _ _ hxy => (PowerlessValueAbsolute.coordinates_l hAT hfA hxy).2)
    obtain ⟨S, hS⟩ := PowerlessFiniteStageEvaluation.assignments_exists_l hℳ hω ht hT hU hωδ hδ h𝒩 ⟨A, hA₀⟩
    obtain ⟨F, hF⟩ := PowerlessFiniteStageEvaluation.evaluation_exists_l hℳ hω ht hT hU hωδ hδ h𝒩 ⟨A, hA₀⟩ S
    have hq := (PowerlessBoundedCertificateSound.recognizes_l hℳ hω ht hT hAU hAT hR hS hH hF hc
      (f.eval η).val ⟨n, hn, hf₀⟩).mp h
    exact ⟨⟨A, hA₀⟩, S, F, ⟨n, hUT ω.val n ω.property hn⟩, hAT, hn, hf₀, hS, hF, hq⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageBoundedTruth
