import BMSConstructibleBridge.PowerlessUniformEvaluationLogic
import BMSConstructibleBridge.PowerlessSourceSpecification

/-!
# 所有实际域共用同一码的源规格

代码、槽环境及最小长度先固定，再量化实际域和完整求值器。
量词更新仍使用模型内部有限图；不以外部列表代替赋值空间。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessUniformSourceSpecification

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}

def spec_l (ω e T t₁ t₂ t₃ c N : carrier_l ℳ) (ξ : Env ℳ Γ Δ) (φ : Formula ℒ Γ Δ) : Prop :=
  ∀ {A S F}, PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F →
    (∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A) →
      ∀ hA : ∃ a, member_l ℳ a A,
      PowerlessSourceSpecification.spec_l ω A F c N hA ξ φ

theorem widen_l {ω e T t₁ t₂ t₃ c N M : carrier_l ℳ}
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ Γ Δ}
    (h : spec_l ω e T t₁ t₂ t₃ c N ξ φ) (hN : subset_l N M) :
    spec_l ω e T t₁ t₂ t₃ c M ξ φ :=
  fun hF hS hA => PowerlessSourceSpecification.widen_l (h hF hS hA) hN

variable (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
  (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem negation_l {b N : carrier_l ℳ} {ξ : Env ℳ Γ Δ} {φ : Formula ℒ Γ Δ}
    (hb : member_l ℳ b ω) (h : spec_l ω e T t₁ t₂ t₃ b N ξ φ) :
    ∃ c, member_l ℳ c ω ∧ spec_l ω e T t₁ t₂ t₃ c N ξ (.neg φ) := by
  obtain ⟨c, hc, h₀⟩ := PowerlessUniformEvaluationLogic.negation_l hℳ hω ht hT hb
  refine ⟨c, hc, ?_⟩
  intro A S F hF hS hA m hm hM f hf η hη
  exact (h₀ hF f ((hS f).mpr ⟨m, hm, hf⟩)).trans (not_congr (h hF hS hA m hm hM f hf η hη))

theorem existential_l {b k N : carrier_l ℳ} {ξ : Env ℳ Γ Δ}
    {φ : Formula ℒ (.set :: Γ) Δ} (hk : member_l ℳ k ω)
    (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hb : member_l ℳ b ω) (hN : member_l ℳ k N)
    (h : spec_l ω e T t₁ t₂ t₃ b N (ξ.pushBound k) φ) :
    ∃ c, member_l ℳ c ω ∧ spec_l ω e T t₁ t₂ t₃ c N ξ (.existsE .set φ) := by
  obtain ⟨c, hc, h₀⟩ := PowerlessUniformEvaluationLogic.existential_l hℳ hω ht hT hk hb
  refine ⟨c, hc, ?_⟩
  intro A S F hF hS hA m hm hM f hf η hη
  refine (h₀ hF f ((hS f).mpr ⟨m, hm, hf⟩)).trans ?_
  change PowerlessEvaluationClause.exists_l ω A F f k b ↔
    ∃ a : type_l A, φ.satisfies (η.pushBound a)
  constructor
  · rintro ⟨n, _, hn, _, a, ha, g, hg, h₁, h₂⟩
    have h₃ := PowerlessAssignmentUpdate.length_unique_l hℳ hn hf
    subst n
    exact ⟨⟨a, ha⟩, (h hF hS hA m hm hM g hg (η.pushBound ⟨a, ha⟩)
      (PowerlessSourceEnvironment.update_l hξ hη ⟨a, ha⟩ h₁)).mp h₂⟩
  · rintro ⟨a, ha⟩
    obtain ⟨g, hg, h₁⟩ := PowerlessAssignmentUpdate.exists_l hℳ hf (hM k hN) a.property
    exact ⟨m, hm, hf, hM k hN, a.val, a.property, g, hg, h₁,
      (h hF hS hA m hm hM g hg (η.pushBound a)
        (PowerlessSourceEnvironment.update_l hξ hη a h₁)).mpr ha⟩

theorem universal_l {b k N : carrier_l ℳ} {ξ : Env ℳ Γ Δ}
    {φ : Formula ℒ (.set :: Γ) Δ} (hk : member_l ℳ k ω)
    (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hb : member_l ℳ b ω) (hN : member_l ℳ k N)
    (h : spec_l ω e T t₁ t₂ t₃ b N (ξ.pushBound k) φ) :
    ∃ c, member_l ℳ c ω ∧ spec_l ω e T t₁ t₂ t₃ c N ξ (.forallE .set φ) := by
  classical
  obtain ⟨p, hp, h₀⟩ := negation_l hℳ hω ht hT hb h
  obtain ⟨q, hq, h₁⟩ := existential_l hℳ hω ht hT hk hξ hp hN h₀
  obtain ⟨c, hc, h₂⟩ := negation_l hℳ hω ht hT hq h₁
  refine ⟨c, hc, ?_⟩
  intro A S F hF hS hA m hm hM f hf η hη
  simpa only [Formula.satisfies, not_exists, not_not] using h₂ hF hS hA m hm hM f hf η hη

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessUniformSourceSpecification
