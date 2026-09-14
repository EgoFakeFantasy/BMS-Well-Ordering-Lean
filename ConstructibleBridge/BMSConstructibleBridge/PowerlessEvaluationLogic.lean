import BMSConstructibleBridge.PowerlessEvaluationEquations

/-!
# 上游逻辑联结词的实际数码实现

数码 0 不可能是后继节点，表示假；其余命题联结词由与非构造。
每项同时给出内部自然数数码及全部实际赋值上的真值方程。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationLogic

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationClause

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F) (f : carrier_l ℳ) : ¬query_l F e f := by
  intro h
  have h₀ := (PowerlessEvaluationRecursion.equation_l hℳ hω ht.1 hT hF
    (PowerlessNatural.zero_mem_l hℳ hω ht.1) f).mp h
  rcases h₀.2 with ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩
  all_goals exact PowerlessFormulaConstructor.nonzero_l ht.1 hc rfl

theorem nand_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F a b : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (ha : ThirdOrderSemantics.member_l ℳ a ω) (hb : ThirdOrderSemantics.member_l ℳ b ω) :
    ∃ c, ThirdOrderSemantics.member_l ℳ c ω ∧ ∀ f, ThirdOrderSemantics.member_l ℳ f S →
      (query_l F c f ↔ ¬(query_l F a f ∧ query_l F b f)) := by
  have h₂ := (PowerlessEvaluationTags.natural_l hℳ hω ht).2.2.1
  obtain ⟨c, hc, h⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT h₂ ha hb
  exact ⟨c, hc, fun f hf => (PowerlessEvaluationEquations.nand_l hℳ hω ht hT hF h f).trans (and_iff_right hf)⟩

theorem negation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F a : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (ha : ThirdOrderSemantics.member_l ℳ a ω) :
    ∃ c, ThirdOrderSemantics.member_l ℳ c ω ∧ ∀ f, ThirdOrderSemantics.member_l ℳ f S → (query_l F c f ↔ ¬query_l F a f) := by
  obtain ⟨c, hc, h⟩ := nand_l hℳ hω ht hT hF ha ha
  exact ⟨c, hc, fun f hf => (h f hf).trans (not_congr ⟨And.left, fun h => ⟨h, h⟩⟩)⟩

theorem truth_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F) :
    ∃ c, ThirdOrderSemantics.member_l ℳ c ω ∧ ∀ f, ThirdOrderSemantics.member_l ℳ f S → query_l F c f := by
  obtain ⟨c, hc, h⟩ := negation_l hℳ hω ht hT hF (PowerlessNatural.zero_mem_l hℳ hω ht.1)
  exact ⟨c, hc, fun f hf => (h f hf).mpr (zero_l hℳ hω ht hT hF f)⟩

theorem conjunction_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F a b : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (ha : ThirdOrderSemantics.member_l ℳ a ω) (hb : ThirdOrderSemantics.member_l ℳ b ω) :
    ∃ c, ThirdOrderSemantics.member_l ℳ c ω ∧ ∀ f, ThirdOrderSemantics.member_l ℳ f S →
      (query_l F c f ↔ query_l F a f ∧ query_l F b f) := by
  classical
  obtain ⟨p, hp, h₀⟩ := nand_l hℳ hω ht hT hF ha hb
  obtain ⟨c, hc, h₁⟩ := negation_l hℳ hω ht hT hF hp
  exact ⟨c, hc, fun f hf => (h₁ f hf).trans ((not_congr (h₀ f hf)).trans not_not)⟩

theorem disjunction_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F a b : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (ha : ThirdOrderSemantics.member_l ℳ a ω) (hb : ThirdOrderSemantics.member_l ℳ b ω) :
    ∃ c, ThirdOrderSemantics.member_l ℳ c ω ∧ ∀ f, ThirdOrderSemantics.member_l ℳ f S →
      (query_l F c f ↔ query_l F a f ∨ query_l F b f) := by
  classical
  obtain ⟨p, hp, h₀⟩ := negation_l hℳ hω ht hT hF ha
  obtain ⟨q, hq, h₁⟩ := negation_l hℳ hω ht hT hF hb
  obtain ⟨c, hc, h₂⟩ := nand_l hℳ hω ht hT hF hp hq
  exact ⟨c, hc, fun f hf => (h₂ f hf).trans ((not_congr (and_congr (h₀ f hf) (h₁ f hf))).trans
    (not_and_or.trans (or_congr not_not not_not)))⟩

theorem implication_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F a b : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (ha : ThirdOrderSemantics.member_l ℳ a ω) (hb : ThirdOrderSemantics.member_l ℳ b ω) :
    ∃ c, ThirdOrderSemantics.member_l ℳ c ω ∧ ∀ f, ThirdOrderSemantics.member_l ℳ f S →
      (query_l F c f ↔ (query_l F a f → query_l F b f)) := by
  classical
  obtain ⟨q, hq, h₀⟩ := negation_l hℳ hω ht hT hF hb
  obtain ⟨c, hc, h₁⟩ := nand_l hℳ hω ht hT hF ha hq
  refine ⟨c, hc, fun f hf => (h₁ f hf).trans ((not_congr (and_congr Iff.rfl (h₀ f hf))).trans ?_)⟩
  constructor
  · intro h hp
    by_contra hq
    exact h ⟨hp, hq⟩
  · rintro h ⟨hp, hq⟩
    exact hq (h hp)

theorem biconditional_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F a b : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (ha : ThirdOrderSemantics.member_l ℳ a ω) (hb : ThirdOrderSemantics.member_l ℳ b ω) :
    ∃ c, ThirdOrderSemantics.member_l ℳ c ω ∧ ∀ f, ThirdOrderSemantics.member_l ℳ f S →
      (query_l F c f ↔ (query_l F a f ↔ query_l F b f)) := by
  obtain ⟨p, hp, h₀⟩ := implication_l hℳ hω ht hT hF ha hb
  obtain ⟨q, hq, h₁⟩ := implication_l hℳ hω ht hT hF hb ha
  obtain ⟨c, hc, h₂⟩ := conjunction_l hℳ hω ht hT hF hp hq
  exact ⟨c, hc, fun f hf => (h₂ f hf).trans ((and_congr (h₀ f hf) (h₁ f hf)).trans
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)⟩

theorem existential_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F i b : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hi : ThirdOrderSemantics.member_l ℳ i ω) (hb : ThirdOrderSemantics.member_l ℳ b ω) :
    ∃ c, ThirdOrderSemantics.member_l ℳ c ω ∧ ∀ f, ThirdOrderSemantics.member_l ℳ f S →
      (query_l F c f ↔ PowerlessEvaluationClause.exists_l ω A F f i b) := by
  have h₃ := (PowerlessEvaluationTags.natural_l hℳ hω ht).2.2.2
  obtain ⟨c, hc, h⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT h₃ hi hb
  exact ⟨c, hc, fun f hf => (PowerlessEvaluationEquations.exists_l hℳ hω ht hT hF h f).trans (and_iff_right hf)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationLogic
