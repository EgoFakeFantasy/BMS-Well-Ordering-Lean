import BMSConstructibleBridge.PowerlessLevyLogic
import BMSConstructibleBridge.PowerlessSourceBoundedCompilation

/-!
# 原源量词的同层分类与语义编译

有界量词对任意层号和极性有效；普通存在/全称要求正层 Σ/Π。
每项同时给实际数码、指定分类和源语义规格，保持绑定槽的新鲜性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceLevy

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceSpecification
  PowerlessLevyCertificate PowerlessSourcePolarity StabilityFrame

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T A t₁ t₂ t₃ S F n : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A}
  (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
  (hT : PowerlessTriangular.triangular_l ω e T)
  (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
  (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A)

include hℳ hω ht hT hF hS

theorem negation_l {b N : carrier_l ℳ} {ξ : Env ℳ Γ Δ} {φ : Formula ℒ Γ Δ} {p : Formula.LevyPolarity}
    (hB : class_l ω e T t₁ t₂ t₃ b n (code_l e t₁ p)) (h : spec_l ω A F b N hA ξ φ) :
    ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n (code_l e t₁ p.flip) ∧
      spec_l ω A F c N hA ξ (.neg φ) := by
  obtain ⟨c, hc, hC, h₀⟩ := PowerlessLevyLogic.negation_l hℳ hω ht hT hF hB
  exact ⟨c, hc, hC, fun m hm hN f hf η hη =>
    (h₀ f ((hS f).mpr ⟨m, hm, hf⟩)).trans (not_congr (h m hm hN f hf η hη))⟩

theorem bounded_exists_l {b k N : carrier_l ℳ} {p : Formula.LevyPolarity}
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ (.set :: Γ) Δ} (s : Term ℒ Γ Δ .set)
    (hk : member_l ℳ k ω) (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hs : member_l ℳ (s.eval ξ) ω) (hB : class_l ω e T t₁ t₂ t₃ b n (code_l e t₁ p))
    (hN : member_l ℳ k N) (h : spec_l ω A F b N hA (ξ.pushBound k) φ) :
    ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n (code_l e t₁ p) ∧
      spec_l ω A F c N hA ξ (membershipLevyBound.boundedExists s φ) := by
  obtain ⟨c, hc, hC, h₀⟩ := PowerlessSourceBoundedCompilation.exists_l hℳ hω ht hT hF hS s hk hξ hs
    (PowerlessLevyCertificate.natural_l hB).1 hN h
  exact ⟨c, hc, PowerlessLevyGeneration.bounded_l hℳ hω ht hT
    (PowerlessLevyCertificate.natural_l hB).2.1 (fun _ hx => hx) hB hC, h₀⟩

theorem bounded_forall_l {b k N : carrier_l ℳ} {p : Formula.LevyPolarity}
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ (.set :: Γ) Δ} (s : Term ℒ Γ Δ .set)
    (hk : member_l ℳ k ω) (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hs : member_l ℳ (s.eval ξ) ω) (hB : class_l ω e T t₁ t₂ t₃ b n (code_l e t₁ p))
    (hN : member_l ℳ k N) (h : spec_l ω A F b N hA (ξ.pushBound k) φ) :
    ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n (code_l e t₁ p) ∧
      spec_l ω A F c N hA ξ (membershipLevyBound.boundedForall s φ) := by
  classical
  obtain ⟨d, _, hD, h₀⟩ := negation_l hℳ hω ht hT hF hS hB h
  obtain ⟨q, _, hQ, h₁⟩ := bounded_exists_l hℳ hω ht hT hF hS s hk hξ hs hD hN h₀
  obtain ⟨c, hc, hC, h₂⟩ := negation_l hℳ hω ht hT hF hS hQ h₁
  rw [flip_l] at hC
  refine ⟨c, hc, hC, ?_⟩
  intro m hm hM f hf η hη
  refine (h₂ m hm hM f hf η hη).trans ?_
  change (¬Formula.satisfies η (membershipLevyBound.boundedExists s (.neg φ))) ↔
    Formula.satisfies η (membershipLevyBound.boundedForall s φ)
  rw [Formula.LevyBound.satisfies_boundedExists, Formula.LevyBound.satisfies_boundedForall]
  simp only [Formula.satisfies, not_exists, not_and, not_not]

theorem existential_l {b k N : carrier_l ℳ}
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ (.set :: Γ) Δ}
    (he : member_l ℳ e n) (hk : member_l ℳ k ω)
    (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hB : class_l ω e T t₁ t₂ t₃ b n e) (hN : member_l ℳ k N)
    (h : spec_l ω A F b N hA (ξ.pushBound k) φ) :
    ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n e ∧
      spec_l ω A F c N hA ξ (.existsE .set φ) := by
  obtain ⟨c, hc, hC⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT
    (PowerlessEvaluationTags.natural_l hℳ hω ht).2.2.2 hk (PowerlessLevyCertificate.natural_l hB).1
  refine ⟨c, hc, PowerlessLevyGeneration.existential_l hℳ hω ht hT
    (PowerlessLevyCertificate.natural_l hB).2.1 he hB (Or.inl ⟨rfl, fun _ hx => hx⟩) hC, ?_⟩
  intro m hm hM f hf η hη
  refine ((PowerlessEvaluationEquations.exists_l hℳ hω ht hT hF hC f).trans
    (and_iff_right ((hS f).mpr ⟨m, hm, hf⟩))).trans ?_
  change PowerlessEvaluationClause.exists_l ω A F f k b ↔ ∃ a : type_l A, Formula.satisfies (η.pushBound a) φ
  constructor
  · rintro ⟨l, _, hl, _, a, ha, g, hg, h₀, h₁⟩
    have h₂ := PowerlessAssignmentUpdate.length_unique_l hℳ hl hf
    subst l
    exact ⟨⟨a, ha⟩, (h m hm hM g hg (η.pushBound ⟨a, ha⟩)
      (PowerlessSourceEnvironment.update_l hξ hη ⟨a, ha⟩ h₀)).mp h₁⟩
  · rintro ⟨a, ha⟩
    obtain ⟨g, hg, h₀⟩ := PowerlessAssignmentUpdate.exists_l hℳ hf (hM k hN) a.property
    exact ⟨m, hm, hf, hM k hN, a.val, a.property, g, hg, h₀,
      (h m hm hM g hg (η.pushBound a) (PowerlessSourceEnvironment.update_l hξ hη a h₀)).mpr ha⟩

theorem universal_l {b k N : carrier_l ℳ}
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ (.set :: Γ) Δ}
    (he : member_l ℳ e n) (hk : member_l ℳ k ω)
    (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k)
    (hB : class_l ω e T t₁ t₂ t₃ b n t₁) (hN : member_l ℳ k N)
    (h : spec_l ω A F b N hA (ξ.pushBound k) φ) :
    ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n t₁ ∧
      spec_l ω A F c N hA ξ (.forallE .set φ) := by
  classical
  obtain ⟨d, _, hD, h₀⟩ := negation_l hℳ hω ht hT hF hS (p := .pi) hB h
  obtain ⟨q, _, hQ, h₁⟩ := existential_l hℳ hω ht hT hF hS he hk hξ hD hN h₀
  obtain ⟨c, hc, hC, h₂⟩ := negation_l hℳ hω ht hT hF hS (p := .sigma) hQ h₁
  refine ⟨c, hc, hC, ?_⟩
  intro m hm hM f hf η hη
  simpa only [Formula.satisfies, not_exists, not_not] using h₂ m hm hM f hf η hη

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceLevy
