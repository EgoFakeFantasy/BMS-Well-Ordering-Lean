import BMSConstructibleBridge.PowerlessCertifiedLogic
import BMSConstructibleBridge.PowerlessSourceBoundedCompilation

/-!
# 原源否定、有界量词和成员 guard 的带证书编译

证书闭包只用于实际产生的有界复合数码。有界全称经双重否定实现；
guarded_exists 使用原源成员 guard 的语义定理，不扩大可接受的无界量词。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceCertified

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceSpecification
  PowerlessBoundedCertificate StabilityFrame

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T A t₁ t₂ t₃ S F : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A}
  (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
  (hT : PowerlessTriangular.triangular_l ω e T)
  (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
  (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)

include hℳ hω ht hT hF hS

theorem negation_l {c N : carrier_l ℳ} {ξ : Env ℳ Γ Δ} {φ : Formula ℒ Γ Δ}
    (hc : member_l ℳ c ω) (hC : recognizes_l ω e T t₁ t₂ t₃ c)
    (h : spec_l ω A F c N hA ξ φ) :
    ∃ d, member_l ℳ d ω ∧ recognizes_l ω e T t₁ t₂ t₃ d ∧ spec_l ω A F d N hA ξ (.neg φ) := by
  obtain ⟨d, hd, hD, h₀⟩ := PowerlessCertifiedLogic.negation_l hℳ hω ht hT hF hc hC
  exact ⟨d, hd, hD, fun m hm hN f hf η hη =>
    (h₀ f ((hS f).mpr ⟨m, hm, hf⟩)).trans (not_congr (h m hm hN f hf η hη))⟩

theorem existential_l {b k N : carrier_l ℳ}
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ (.set :: Γ) Δ} (s : Term ℒ Γ Δ .set)
    (hk : member_l ℳ k ω) (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hs : member_l ℳ (s.eval ξ) ω) (hb : member_l ℳ b ω)
    (hB : recognizes_l ω e T t₁ t₂ t₃ b) (hN : member_l ℳ k N)
    (h : spec_l ω A F b N hA (ξ.pushBound k) φ) :
    ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧
      spec_l ω A F c N hA ξ (membershipLevyBound.boundedExists s φ) := by
  obtain ⟨c, hc, hC, h₀⟩ := PowerlessSourceBoundedCompilation.exists_l hℳ hω ht hT hF hS s hk hξ hs hb hN h
  exact ⟨c, hc, PowerlessBoundedCertificateClosure.bounded_l hℳ hω ht.1 hT hB hC, h₀⟩

theorem universal_l {b k N : carrier_l ℳ}
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ (.set :: Γ) Δ} (s : Term ℒ Γ Δ .set)
    (hk : member_l ℳ k ω) (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hs : member_l ℳ (s.eval ξ) ω) (hb : member_l ℳ b ω)
    (hB : recognizes_l ω e T t₁ t₂ t₃ b) (hN : member_l ℳ k N)
    (h : spec_l ω A F b N hA (ξ.pushBound k) φ) :
    ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧
      spec_l ω A F c N hA ξ (membershipLevyBound.boundedForall s φ) := by
  classical
  obtain ⟨p, hp, hP, h₀⟩ := negation_l hℳ hω ht hT hF hS hb hB h
  obtain ⟨q, hq, hQ, h₁⟩ := existential_l hℳ hω ht hT hF hS s hk hξ hs hp hP hN h₀
  obtain ⟨c, hc, hC, h₂⟩ := negation_l hℳ hω ht hT hF hS hq hQ h₁
  refine ⟨c, hc, hC, ?_⟩
  intro m hm hM f hf η hη
  refine (h₂ m hm hM f hf η hη).trans ?_
  change (¬Formula.satisfies η (membershipLevyBound.boundedExists s (.neg φ))) ↔
    Formula.satisfies η (membershipLevyBound.boundedForall s φ)
  rw [Formula.LevyBound.satisfies_boundedExists, Formula.LevyBound.satisfies_boundedForall]
  simp only [Formula.satisfies, not_exists, not_and, not_not]

theorem guarded_l {b k N : carrier_l ℳ}
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ (.set :: Γ) Δ} (s : Term ℒ Γ Δ .set)
    (hG : Formula.MembershipGuard membershipLevyBound s φ)
    (hk : member_l ℳ k ω) (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hs : member_l ℳ (s.eval ξ) ω) (hb : member_l ℳ b ω)
    (hB : recognizes_l ω e T t₁ t₂ t₃ b) (hN : member_l ℳ k N)
    (h : spec_l ω A F b N hA (ξ.pushBound k) φ) :
    ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧
      spec_l ω A F c N hA ξ (.existsE .set φ) := by
  obtain ⟨c, hc, hC, h₀⟩ := existential_l hℳ hω ht hT hF hS s hk hξ hs hb hB hN h
  refine ⟨c, hc, hC, ?_⟩
  intro m hm hM f hf η hη
  refine (h₀ m hm hM f hf η hη).trans ?_
  rw [Formula.LevyBound.satisfies_boundedExists]
  change (∃ a : type_l A, membershipLevyBound.Holds (structure_l A hA) a (s.eval η) ∧
    Formula.satisfies (η.pushBound a) φ) ↔ ∃ a : type_l A, Formula.satisfies (η.pushBound a) φ
  constructor
  · rintro ⟨a, _, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_, ha⟩
    have h₁ := hG.holds_of_satisfies (η.pushBound a) ha
    change membershipLevyBound.Holds (structure_l A hA) a
      ((s.weakenBound SetTheory.SetSort.set).eval (η.pushBound a)) at h₁
    rw [Term.eval_weakenBound η a s] at h₁
    exact h₁

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceCertified
