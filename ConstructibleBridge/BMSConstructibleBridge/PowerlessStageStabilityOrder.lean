import BMSConstructibleBridge.PowerlessStageStability
import BMSConstructibleBridge.PowerlessLevySound

/-!
# 实际层端点稳定关系的序性质与极性保持

层号下降、端点复合及共同上端点插值均使用同一内部查询码。
零层对任意 proper 端点成立；正层仍保留真实层号一致条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageStabilityOrder

open Logic FirstOrder ThirdOrderSemantics PowerlessStageStability
open PowerlessStageEvaluation (system_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ m n α β : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hm : member_l ℳ m ω) (hmn : subset_l m n) (h : stable_l ω e T t₁ t₂ t₃ n α β) :
    stable_l ω e T t₁ t₂ t₃ m α β := by
  obtain ⟨hn, hp, A, B, S, R, F, G, hA, hB, h⟩ := h
  exact ⟨hm, hp, A, B, S, R, F, G, hA, hB,
    PowerlessLevyAgreement.monotone_l hℳ hω he hT hn hmn h⟩

theorem trans_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n α β γ : carrier_l ℳ} (hω : omega_l ω)
    (h₁ : stable_l ω e T t₁ t₂ t₃ n α β) (h₂ : stable_l ω e T t₁ t₂ t₃ n β γ) :
    stable_l ω e T t₁ t₂ t₃ n α γ := by
  obtain ⟨hn, hp, A, B, S, R, F, G, hA, hB, h⟩ := h₁
  have hq := h₂.2.1
  obtain ⟨C, Q, H, hC⟩ := PowerlessStageEvaluation.exists_l hℳ hω hq.2.2.2.1 e T t₁ t₂ t₃
  have h₃ := ((compare_l hℳ hω hB hC).mp h₂).2.2
  have hAB := PowerlessStageStructure.subset_l hℳ hω hA.1 hB.1 hp.2.1
  exact ⟨hn, ⟨hp.1, PowerlessOrdinal.transitive_l hq.2.2.2.1 β α hq.2.1 hp.2.1,
    hp.2.2.1, hq.2.2.2⟩, A, C, S, Q, F, H, hA, hC,
    PowerlessLevyComposition.trans_l hℳ hAB h h₃⟩

theorem interpolate_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n α β γ : carrier_l ℳ} (hω : omega_l ω)
    (hαβ : member_l ℳ α β)
    (h₁ : stable_l ω e T t₁ t₂ t₃ n α γ) (h₂ : stable_l ω e T t₁ t₂ t₃ n β γ) :
    stable_l ω e T t₁ t₂ t₃ n α β := by
  obtain ⟨hn, hp, A, C, S, Q, F, H, hA, hC, h⟩ := h₁
  have hq := h₂.2.1
  obtain ⟨B, R, G, hB⟩ := PowerlessStageEvaluation.exists_l hℳ hω hq.2.2.1.1 e T t₁ t₂ t₃
  have h₃ := ((compare_l hℳ hω hB hC).mp h₂).2.2
  have hAB := PowerlessStageStructure.subset_l hℳ hω hA.1 hB.1 hαβ
  exact ⟨hn, ⟨hp.1, hαβ, hp.2.2.1, hq.2.2.1⟩, A, B, S, R, F, G, hA, hB,
    PowerlessLevyComposition.interpolate_l hℳ hAB h h₃⟩

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α β : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hp : PowerlessStagePair.proper_l ω α β) : stable_l ω e T t₁ t₂ t₃ e α β := by
  obtain ⟨A, S, F, hA⟩ := PowerlessStageEvaluation.exists_l hℳ hω hp.2.2.1.1 e T t₁ t₂ t₃
  obtain ⟨B, R, G, hB⟩ := PowerlessStageEvaluation.exists_l hℳ hω hp.2.2.2.1 e T t₁ t₂ t₃
  exact ⟨PowerlessNatural.zero_mem_l hℳ hω ht.1, hp, A, B, S, R, F, G, hA, hB,
    PowerlessLevyAgreement.zero_l hℳ hω ht hT
      (PowerlessStageStructure.subset_l hℳ hω hA.1 hB.1 hp.2.1)
      (PowerlessStageStructure.transitive_l hℳ hω ht hT hA.1) hB.2.1 hA.2.1 hB.2.2 hA.2.2⟩

-- n 层稳定提供 n 后继层所需的全部严格低层一致。
theorem successor_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ m n α β A B S R F G c p : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hm : PowerlessNatural.successor_l n m) (h : stable_l ω e T t₁ t₂ t₃ n α β)
    (hA : system_l ω e T t₁ t₂ t₃ α A S F) (hB : system_l ω e T t₁ t₂ t₃ β B R G)
    (hc : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m p) :
    PowerlessEvaluationDirection.polarity_l ω A G F e t₁ p c := by
  obtain ⟨hn, hp, h₁⟩ := (compare_l hℳ hω hA hB).mp h
  have h₂ := PowerlessLevyAgreement.lower_of_agreement_l hℳ hω ht.1 hT hn h₁
  apply PowerlessLevySound.class_l hℳ hω ht hT
    (PowerlessStageStructure.subset_l hℳ hω hA.1 hB.1 hp.2.1)
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hA.1) hB.2.1 hA.2.1 hB.2.2 hA.2.2 ?_ hc
  intro k hk
  rcases (hm k).mp hk with hk | hk
  · exact h₂ k hk
  · exact hk.symm ▸ h₁

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageStabilityOrder
