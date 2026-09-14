import BMSConstructibleBridge.PowerlessSourceSpecification

/-!
# 源量词与实际赋值更新的编译对应

给定子公式的充分长赋值规格，新槽 k 已被最小赋值界包含。
存在量词逐方向构造或读取真实更新图；全称量词由同一存在规则和否定实现。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceQuantifier

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceEnvironment PowerlessSourceSpecification

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}

theorem existential_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F b k N : carrier_l ℳ} {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A}
    (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m A)
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ (.set :: Γ) Δ}
    (hk : ThirdOrderSemantics.member_l ℳ k ω) (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hb : ThirdOrderSemantics.member_l ℳ b ω) (hN : ThirdOrderSemantics.member_l ℳ k N)
    (h : spec_l ω A F b N hA (ξ.pushBound k) φ) :
    ∃ c, ThirdOrderSemantics.member_l ℳ c ω ∧ spec_l ω A F c N hA ξ (.existsE .set φ) := by
  obtain ⟨c, hc, h₀⟩ := PowerlessEvaluationLogic.existential_l hℳ hω ht hT hF hk hb
  refine ⟨c, hc, ?_⟩
  intro m hm hM f hf η hη
  refine (h₀ f ((hS f).mpr ⟨m, hm, hf⟩)).trans ?_
  change PowerlessEvaluationClause.exists_l ω A F f k b ↔ ∃ a : type_l A, Formula.satisfies (η.pushBound a) φ
  constructor
  · rintro ⟨n, _, hn, _, a, ha, g, hg, h₁, h₂⟩
    have h₃ := PowerlessAssignmentUpdate.length_unique_l hℳ hn hf
    subst n
    exact ⟨⟨a, ha⟩, (h m hm hM g hg (η.pushBound ⟨a, ha⟩)
      (PowerlessSourceEnvironment.update_l hξ hη ⟨a, ha⟩ h₁)).mp h₂⟩
  · rintro ⟨a, ha⟩
    obtain ⟨g, hg, h₁⟩ := PowerlessAssignmentUpdate.exists_l hℳ hf (hM k hN) a.property
    exact ⟨m, hm, hf, hM k hN, a.val, a.property, g, hg, h₁,
      (h m hm hM g hg (η.pushBound a) (PowerlessSourceEnvironment.update_l hξ hη a h₁)).mpr ha⟩

theorem universal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F b k N : carrier_l ℳ} {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A}
    (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m A)
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ (.set :: Γ) Δ}
    (hk : ThirdOrderSemantics.member_l ℳ k ω) (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hb : ThirdOrderSemantics.member_l ℳ b ω) (hN : ThirdOrderSemantics.member_l ℳ k N)
    (h : spec_l ω A F b N hA (ξ.pushBound k) φ) :
    ∃ c, ThirdOrderSemantics.member_l ℳ c ω ∧ spec_l ω A F c N hA ξ (.forallE .set φ) := by
  classical
  obtain ⟨p, hp, h₀⟩ := PowerlessSourceSpecification.negation_l hℳ hω ht hT hF hS hb h
  obtain ⟨q, hq, h₁⟩ := existential_l hℳ hω ht hT hF hS hk hξ hp hN h₀
  obtain ⟨c, hc, h₂⟩ := PowerlessSourceSpecification.negation_l hℳ hω ht hT hF hS hq h₁
  refine ⟨c, hc, ?_⟩
  intro m hm hM f hf η hη
  simpa only [Formula.satisfies, not_exists, not_not] using h₂ m hm hM f hf η hη

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceQuantifier
