import BMSConstructibleBridge.PowerlessSourceCertified
import BMSConstructibleBridge.PowerlessSourceSlots
import BMSConstructibleBridge.PowerlessNaturalBounds

/-!
# 原源 Δ₀ 公式的带内部证书容量界

先按上游 Formula 构造预留界 N，再量化任意 J⊇N 及槽环境 ξ。
量词只占用 J 之前的槽；全部子公式共用 J 的后继作为赋值长度界。
递归原源 IsDelta0 证书，覆盖其全部构造器；每项同时保留数码的
内部有界证书和源语义规格，不假定模型内部自然数外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceDeltaReservation

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceSlots PowerlessSourceSpecification
  PowerlessBoundedCertificate StabilityFrame

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
    {φ : Formula ℒ Γ Δ} (hφ : Formula.IsDelta0 membershipLevyBound φ) {k : carrier_l ℳ} (hk : member_l ℳ k ω) :
    ∃ N, member_l ℳ N ω ∧ subset_l k N ∧
      ∀ J, member_l ℳ J ω → subset_l N J → ∀ M, PowerlessNatural.successor_l J M →
        ∀ ξ : Env ℳ Γ Δ, bounded_l ξ k J →
          ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧ spec_l ω A F c M hA ξ φ := by
  classical
  match hφ with
  | .falsum =>
      refine ⟨k, hk, (fun _ h => h), ?_⟩
      intro _ _ _ _ _ _ _
      refine ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1,
        PowerlessBoundedCertificateClosure.zero_l hℳ hω ht.1, ?_⟩
      intro _ _ _ f _ _ _
      exact ⟨fun h => PowerlessEvaluationLogic.zero_l hℳ hω ht hT hF f h, False.elim⟩
  | .truth =>
      refine ⟨k, hk, (fun _ h => h), ?_⟩
      intro _ _ _ _ _ _ _
      obtain ⟨c, hc, hC, h⟩ := PowerlessCertifiedLogic.truth_l hℳ hω ht hT hF
      refine ⟨c, hc, hC, ?_⟩
      intro m hm _ f hf _ _
      exact ⟨fun _ => trivial, fun _ => h f ((hS f).mpr ⟨m, hm, hf⟩)⟩
  | .rel SetTheory.RelationSymbol.membership (.cons s (.cons t .nil)) =>
      refine ⟨k, hk, (fun _ h => h), ?_⟩
      intro J hJ _ M _ ξ hξ
      obtain ⟨c, hc, h⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT
        (PowerlessNatural.zero_mem_l hℳ hω ht.1)
        (natural_l hℳ hω hk hJ hξ s) (natural_l hℳ hω hk hJ hξ t)
      refine ⟨c, hc, PowerlessBoundedCertificateClosure.member_l hℳ hω ht.1 hT h, ?_⟩
      intro m hm _ f hf η hη
      exact (PowerlessEvaluationEquations.member_l hℳ hω ht hT hF h f).trans
        ((and_iff_right ((hS f).mpr ⟨m, hm, hf⟩)).trans (PowerlessSourceEnvironment.member_l hℳ hf hη s t))
  | .equal (sort := SetTheory.SetSort.set) s t =>
      refine ⟨k, hk, (fun _ h => h), ?_⟩
      intro J hJ _ M _ ξ hξ
      obtain ⟨c, hc, h⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT
        (PowerlessEvaluationTags.natural_l hℳ hω ht).2.1
        (natural_l hℳ hω hk hJ hξ s) (natural_l hℳ hω hk hJ hξ t)
      refine ⟨c, hc, PowerlessBoundedCertificateClosure.equal_l hℳ hω ht.1 hT h, ?_⟩
      intro m hm _ f hf η hη
      exact (PowerlessEvaluationEquations.equal_l hℳ hω ht hT hF h f).trans
        ((and_iff_right ((hS f).mpr ⟨m, hm, hf⟩)).trans (PowerlessSourceEnvironment.equal_l hℳ hf hη s t))
  | .neg hφ =>
      obtain ⟨N, hN, hkN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ hk
      refine ⟨N, hN, hkN, ?_⟩
      intro J hJ hNJ M hM ξ hξ
      obtain ⟨a, ha, hC, h⟩ := hφ J hJ hNJ M hM ξ hξ
      exact PowerlessSourceCertified.negation_l hℳ hω ht hT hF hS ha hC h
  | .conj hφ hψ =>
      obtain ⟨N, hN, hkN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ hk
      obtain ⟨P, hP, _, hψ⟩ := formula_l hℳ hω ht hT hF hS hA hψ hk
      obtain ⟨Q, hQ, hNQ, hPQ⟩ := PowerlessNaturalBounds.upper_l hℳ hω hN hP
      refine ⟨Q, hQ, (fun x hx => hNQ x (hkN x hx)), ?_⟩
      intro J hJ hQJ M hM ξ hξ
      obtain ⟨a, ha, hA₀, h₀⟩ := hφ J hJ (fun x hx => hQJ x (hNQ x hx)) M hM ξ hξ
      obtain ⟨b, hb, hB₀, h₁⟩ := hψ J hJ (fun x hx => hQJ x (hPQ x hx)) M hM ξ hξ
      obtain ⟨c, hc, hC, h⟩ := PowerlessCertifiedLogic.conjunction_l hℳ hω ht hT hF ha hb hA₀ hB₀
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
      obtain ⟨a, ha, hA₀, h₀⟩ := hφ J hJ (fun x hx => hQJ x (hNQ x hx)) M hM ξ hξ
      obtain ⟨b, hb, hB₀, h₁⟩ := hψ J hJ (fun x hx => hQJ x (hPQ x hx)) M hM ξ hξ
      obtain ⟨c, hc, hC, h⟩ := PowerlessCertifiedLogic.disjunction_l hℳ hω ht hT hF ha hb hA₀ hB₀
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
      obtain ⟨a, ha, hA₀, h₀⟩ := hφ J hJ (fun x hx => hQJ x (hNQ x hx)) M hM ξ hξ
      obtain ⟨b, hb, hB₀, h₁⟩ := hψ J hJ (fun x hx => hQJ x (hPQ x hx)) M hM ξ hξ
      obtain ⟨c, hc, hC, h⟩ := PowerlessCertifiedLogic.implication_l hℳ hω ht hT hF ha hb hA₀ hB₀
      refine ⟨c, hc, hC, ?_⟩
      intro m hm hMm f hf η hη
      exact (h f ((hS f).mpr ⟨m, hm, hf⟩)).trans
        (imp_congr (h₀ m hm hMm f hf η hη) (h₁ m hm hMm f hf η hη))
  | .iff hφ hψ =>
      obtain ⟨N, hN, hkN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ hk
      obtain ⟨P, hP, _, hψ⟩ := formula_l hℳ hω ht hT hF hS hA hψ hk
      obtain ⟨Q, hQ, hNQ, hPQ⟩ := PowerlessNaturalBounds.upper_l hℳ hω hN hP
      refine ⟨Q, hQ, (fun x hx => hNQ x (hkN x hx)), ?_⟩
      intro J hJ hQJ M hM ξ hξ
      obtain ⟨a, ha, hA₀, h₀⟩ := hφ J hJ (fun x hx => hQJ x (hNQ x hx)) M hM ξ hξ
      obtain ⟨b, hb, hB₀, h₁⟩ := hψ J hJ (fun x hx => hQJ x (hPQ x hx)) M hM ξ hξ
      obtain ⟨c, hc, hC, h⟩ := PowerlessCertifiedLogic.biconditional_l hℳ hω ht hT hF ha hb hA₀ hB₀
      refine ⟨c, hc, hC, ?_⟩
      intro m hm hMm f hf η hη
      exact (h f ((hS f).mpr ⟨m, hm, hf⟩)).trans
        (iff_congr (h₀ m hm hMm f hf η hη) (h₁ m hm hMm f hf η hη))
  | .bounded_forall s hφ =>
      obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
      obtain ⟨N, hN, hlN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ
        (PowerlessNatural.successor_mem_l hℳ hω hk hl)
      refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
      intro J hJ hNJ M hM ξ hξ
      have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
      obtain ⟨b, hb, hB, h⟩ := hφ J hJ hNJ M hM (ξ.pushBound k) (push_l hξ hl)
      exact PowerlessSourceCertified.universal_l hℳ hω ht hT hF hS s hk
        (fresh_l hℳ hξ hkJ) (natural_l hℳ hω hk hJ hξ s) hb hB ((hM k).mpr (Or.inl hkJ)) h
  | .bounded_exists s hφ =>
      obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
      obtain ⟨N, hN, hlN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ
        (PowerlessNatural.successor_mem_l hℳ hω hk hl)
      refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
      intro J hJ hNJ M hM ξ hξ
      have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
      obtain ⟨b, hb, hB, h⟩ := hφ J hJ hNJ M hM (ξ.pushBound k) (push_l hξ hl)
      exact PowerlessSourceCertified.existential_l hℳ hω ht hT hF hS s hk
        (fresh_l hℳ hξ hkJ) (natural_l hℳ hω hk hJ hξ s) hb hB ((hM k).mpr (Or.inl hkJ)) h
  | .guarded_exists s hφ hG =>
      obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
      obtain ⟨N, hN, hlN, hφ⟩ := formula_l hℳ hω ht hT hF hS hA hφ
        (PowerlessNatural.successor_mem_l hℳ hω hk hl)
      refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
      intro J hJ hNJ M hM ξ hξ
      have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
      obtain ⟨b, hb, hB, h⟩ := hφ J hJ hNJ M hM (ξ.pushBound k) (push_l hξ hl)
      exact PowerlessSourceCertified.guarded_l hℳ hω ht hT hF hS s hG hk
        (fresh_l hℳ hξ hkJ) (natural_l hℳ hω hk hJ hξ s) hb hB ((hM k).mpr (Or.inl hkJ)) h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceDeltaReservation
