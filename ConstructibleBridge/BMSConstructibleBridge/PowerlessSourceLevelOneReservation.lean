import BMSConstructibleBridge.PowerlessSourceLevy
import BMSConstructibleBridge.PowerlessSourceDeltaReservation
import BMSConstructibleBridge.PowerlessSourceSlots
import BMSConstructibleBridge.PowerlessNaturalBounds

/-!
# 原源 Σ₁/Π₁ 的带内部层号证书容量界

先按上游 Formula 构造预留界 N，再量化任意 J⊇N 及槽环境 ξ。
量词只占用 J 之前的槽；全部子公式共用 J 的后继作为赋值长度界。
递归原源 IsLevel1 证书，全部构造器保留同一码的内部第一层分类与
源语义规格。Δ₀ 分支复用已验证覆盖，不改源语法或模型自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceLevelOneReservation

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceSlots PowerlessSourceSpecification
  PowerlessLevyCertificate PowerlessSourcePolarity StabilityFrame

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)
    (hA : ∃ a, member_l ℳ a A) {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ Γ Δ} {p : Formula.LevyPolarity} (hφ : Formula.IsLevel1 membershipLevyBound p φ) {k : carrier_l ℳ} (hk : member_l ℳ k ω) :
    ∃ N, member_l ℳ N ω ∧ subset_l k N ∧
      ∀ J, member_l ℳ J ω → subset_l N J → ∀ M, PowerlessNatural.successor_l J M →
        ∀ ξ : Env ℳ Γ Δ, bounded_l ξ k J →
          ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c t₁ (code_l e t₁ p) ∧ spec_l ω A F c M hA ξ φ := by
  classical
  match hφ with
  | .delta0 hφ =>
      obtain ⟨N, hN, hkN, hφ⟩ := PowerlessSourceDeltaReservation.formula_l hℳ hω ht hT hF hS hA hφ hk
      refine ⟨N, hN, hkN, ?_⟩
      intro J hJ hNJ M hM ξ hξ
      obtain ⟨c, hc, hC, h⟩ := hφ J hJ hNJ M hM ξ hξ
      exact ⟨c, hc, PowerlessLevyCertificateClosure.base_l hℳ hω ht.1 hT
        (PowerlessEvaluationTags.natural_l hℳ hω ht).2.1
        (PowerlessSourcePolarity.natural_l hℳ hω ht p) (polarity_l e t₁ p) hC, h⟩
  | .neg hφ =>
      obtain ⟨N, hN, hkN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ hk
      refine ⟨N, hN, hkN, ?_⟩
      intro J hJ hNJ M hM ξ hξ
      obtain ⟨a, _, hC, h⟩ := hφ J hJ hNJ M hM ξ hξ
      exact PowerlessSourceLevy.negation_l hℳ hω ht hT hF hS hC h
  | .conj hφ hψ =>
      obtain ⟨N, hN, hkN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ hk
      obtain ⟨P, hP, _, hψ⟩ := formula_l hℳ hω ht hT hF hS hA hψ hk
      obtain ⟨Q, hQ, hNQ, hPQ⟩ := PowerlessNaturalBounds.upper_l hℳ hω hN hP
      refine ⟨Q, hQ, (fun x hx => hNQ x (hkN x hx)), ?_⟩
      intro J hJ hQJ M hM ξ hξ
      obtain ⟨a, _, hA₀, h₀⟩ := hφ J hJ (fun x hx => hQJ x (hNQ x hx)) M hM ξ hξ
      obtain ⟨b, _, hB₀, h₁⟩ := hψ J hJ (fun x hx => hQJ x (hPQ x hx)) M hM ξ hξ
      obtain ⟨c, hc, hC, h⟩ := PowerlessLevyLogic.conjunction_l hℳ hω ht hT hF hA₀ hB₀
      refine ⟨c, hc, hC, ?_⟩
      intro m hm hMm f hf η hη
      exact (h f ((hS f).mpr ⟨m, hm, hf⟩)).trans
        (and_congr (h₀ m hm hMm f hf η hη) (h₁ m hm hMm f hf η hη))
  | .disj hφ hψ =>
      obtain ⟨N, hN, hkN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ hk
      obtain ⟨P, hP, _, hψ⟩ := formula_l hℳ hω ht hT hF hS hA hψ hk
      obtain ⟨Q, hQ, hNQ, hPQ⟩ := PowerlessNaturalBounds.upper_l hℳ hω hN hP
      refine ⟨Q, hQ, (fun x hx => hNQ x (hkN x hx)), ?_⟩
      intro J hJ hQJ M hM ξ hξ
      obtain ⟨a, _, hA₀, h₀⟩ := hφ J hJ (fun x hx => hQJ x (hNQ x hx)) M hM ξ hξ
      obtain ⟨b, _, hB₀, h₁⟩ := hψ J hJ (fun x hx => hQJ x (hPQ x hx)) M hM ξ hξ
      obtain ⟨c, hc, hC, h⟩ := PowerlessLevyLogic.disjunction_l hℳ hω ht hT hF hA₀ hB₀
      refine ⟨c, hc, hC, ?_⟩
      intro m hm hMm f hf η hη
      exact (h f ((hS f).mpr ⟨m, hm, hf⟩)).trans
        (or_congr (h₀ m hm hMm f hf η hη) (h₁ m hm hMm f hf η hη))
  | .imp hφ hψ =>
      obtain ⟨N, hN, hkN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ hk
      obtain ⟨P, hP, _, hψ⟩ := formula_l hℳ hω ht hT hF hS hA hψ hk
      obtain ⟨Q, hQ, hNQ, hPQ⟩ := PowerlessNaturalBounds.upper_l hℳ hω hN hP
      refine ⟨Q, hQ, (fun x hx => hNQ x (hkN x hx)), ?_⟩
      intro J hJ hQJ M hM ξ hξ
      obtain ⟨a, _, hA₀, h₀⟩ := hφ J hJ (fun x hx => hQJ x (hNQ x hx)) M hM ξ hξ
      obtain ⟨b, _, hB₀, h₁⟩ := hψ J hJ (fun x hx => hQJ x (hPQ x hx)) M hM ξ hξ
      obtain ⟨c, hc, hC, h⟩ := PowerlessLevyLogic.implication_l hℳ hω ht hT hF hA₀ hB₀
      refine ⟨c, hc, hC, ?_⟩
      intro m hm hMm f hf η hη
      exact (h f ((hS f).mpr ⟨m, hm, hf⟩)).trans
        (imp_congr (h₀ m hm hMm f hf η hη) (h₁ m hm hMm f hf η hη))
  | .existsE SetTheory.SetSort.set hφ =>
      obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
      obtain ⟨N, hN, hlN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ
        (PowerlessNatural.successor_mem_l hℳ hω hk hl)
      refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
      intro J hJ hNJ M hM ξ hξ
      have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
      obtain ⟨b, _, hB, h⟩ := hφ J hJ hNJ M hM (ξ.pushBound k) (push_l hξ hl)
      exact PowerlessSourceLevy.existential_l hℳ hω ht hT hF hS ((ht.2.1 e).mpr (Or.inr rfl)) hk
        (fresh_l hℳ hξ hkJ) hB ((hM k).mpr (Or.inl hkJ)) h
  | .forallE SetTheory.SetSort.set hφ =>
      obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
      obtain ⟨N, hN, hlN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ
        (PowerlessNatural.successor_mem_l hℳ hω hk hl)
      refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
      intro J hJ hNJ M hM ξ hξ
      have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
      obtain ⟨b, _, hB, h⟩ := hφ J hJ hNJ M hM (ξ.pushBound k) (push_l hξ hl)
      exact PowerlessSourceLevy.universal_l hℳ hω ht hT hF hS ((ht.2.1 e).mpr (Or.inr rfl)) hk
        (fresh_l hℳ hξ hkJ) hB ((hM k).mpr (Or.inl hkJ)) h
  | .bounded_forall s hφ =>
      obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
      obtain ⟨N, hN, hlN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ
        (PowerlessNatural.successor_mem_l hℳ hω hk hl)
      refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
      intro J hJ hNJ M hM ξ hξ
      have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
      obtain ⟨b, _, hB, h⟩ := hφ J hJ hNJ M hM (ξ.pushBound k) (push_l hξ hl)
      exact PowerlessSourceLevy.bounded_forall_l hℳ hω ht hT hF hS s hk
        (fresh_l hℳ hξ hkJ) (PowerlessSourceSlots.natural_l hℳ hω hk hJ hξ s) hB ((hM k).mpr (Or.inl hkJ)) h
  | .bounded_exists s hφ =>
      obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
      obtain ⟨N, hN, hlN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ
        (PowerlessNatural.successor_mem_l hℳ hω hk hl)
      refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
      intro J hJ hNJ M hM ξ hξ
      have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
      obtain ⟨b, _, hB, h⟩ := hφ J hJ hNJ M hM (ξ.pushBound k) (push_l hξ hl)
      exact PowerlessSourceLevy.bounded_exists_l hℳ hω ht hT hF hS s hk
        (fresh_l hℳ hξ hkJ) (PowerlessSourceSlots.natural_l hℳ hω hk hJ hξ s) hB ((hM k).mpr (Or.inl hkJ)) h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceLevelOneReservation
