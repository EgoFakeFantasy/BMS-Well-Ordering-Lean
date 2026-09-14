import BMSConstructibleBridge.PowerlessBoundedCertificate
import BMSConstructibleBridge.PowerlessBoundedAgreement
import BMSConstructibleBridge.PowerlessEvaluationLogic

/-!
# 有界有限证书的全内部语义正确性

先纯公式化“证书中的码保持查询”，再沿模型内部 ω 归纳。
每条生成规则消费严格较小子码；没有宿主 Acc 或标准有限树假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCertificateSound

open Logic FirstOrder ThirdOrderSemantics PowerlessBoundedCertificate PowerlessEvaluationAgreement

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem sound_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A U t₁ t₂ t₃ S R F G D : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hAU : subset_l A U) (hA : PowerlessNaturalOrder.transitive_l A)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n U)
    (hR : ∀ f, member_l ℳ f R ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hG : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G)
    (hD : certificate_l ω e T t₁ t₂ t₃ D) : ∀ c, member_l ℳ c D → point_l ω A F G c := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 5 :=
    { bound := Fin.cases ω (Fin.cases A (Fin.cases F (Fin.cases G (fun _ => D)))), free := fun _ => U }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    .imp (SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there (.there (.there (.there (.there .here)))))))
      (point_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar .here))
  have h : ∀ c, φ.satisfies ((PowerlessComprehension.env_l η).pushFree c) ↔
      (member_l ℳ c D → point_l ω A F G c) := by
    intro c
    simp only [φ, Formula.satisfies, point_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  have h₀ := PowerlessOrdinalInduction.induction_l hℳ φ η (PowerlessOmegaOrdinal.ordinal_l hℳ hω)
    (fun c _ h₁ => (h c).mpr (by
      intro hc
      rcases hD.2 c hc with rfl | ⟨i, j, hC⟩ | ⟨i, j, hC⟩ | ⟨a, b, ha, hb, hC⟩ | ⟨i, j, b, hb, hC⟩
      · intro f _
        exact ⟨fun h => (PowerlessEvaluationLogic.zero_l hℳ hω ht hT hF f h).elim,
          fun h => (PowerlessEvaluationLogic.zero_l hℳ hω ht hT hG f h).elim⟩
      · exact PowerlessBoundedAgreement.member_l hℳ hω ht hT hAU hS hR hF hG hC
      · exact PowerlessBoundedAgreement.equal_l hℳ hω ht hT hAU hS hR hF hG hC
      · obtain ⟨ha₀, hb₀⟩ := PowerlessFormulaConstructor.bounds_l hℳ hω ht.1 hT hC
        exact PowerlessBoundedAgreement.nand_l hℳ hω ht hT hAU hS hR hF hG hC
          ((h a).mp (h₁ a ha₀) ha) ((h b).mp (h₁ b hb₀) hb)
      · exact PowerlessBoundedAgreement.bounded_l hℳ hω ht hT hAU hS hR hF hG hA hC
          ((h b).mp (h₁ b (PowerlessBoundedCode.bounds_l hℳ hω ht.1 hT hC).2.2) hb)))
  exact fun c hc => (h c).mp (h₀ c (PowerlessBoundedCertificate.natural_l hℳ hω hD hc)) hc

theorem recognizes_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A U t₁ t₂ t₃ S R F G c : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hAU : subset_l A U) (hA : PowerlessNaturalOrder.transitive_l A)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n U)
    (hR : ∀ f, member_l ℳ f R ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hG : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G)
    (hc : PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c) : point_l ω A F G c := by
  obtain ⟨D, hD, hc⟩ := hc
  exact sound_l hℳ hω ht hT hAU hA hS hR hF hG hD c hc

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCertificateSound
