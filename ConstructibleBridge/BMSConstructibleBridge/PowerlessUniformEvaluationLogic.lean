import BMSConstructibleBridge.PowerlessEvaluationLogic

/-!
# 先于域和求值器选择的逻辑构造数码

同一个实际数码在所有实际求值系统中满足相应方程。
与逐域存在一个数码的接口不同，这里将存在量词移到域量词之前。
这是统一源编译的构造子层；尚不是任意原闭句的统一编译定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessUniformEvaluationLogic

open Logic FirstOrder ThirdOrderSemantics
open PowerlessEvaluationClause (query_l)
open PowerlessEvaluationRecursion (evaluation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
  (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem nand_l {a b : carrier_l ℳ} (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ ∀ {A S F}, evaluation_l ω e T A t₁ t₂ t₃ S F →
      ∀ f, member_l ℳ f S → (query_l F c f ↔ ¬(query_l F a f ∧ query_l F b f)) := by
  obtain ⟨c, hc, h⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT
    (PowerlessEvaluationTags.natural_l hℳ hω ht).2.2.1 ha hb
  exact ⟨c, hc, fun hF f hf =>
    (PowerlessEvaluationEquations.nand_l hℳ hω ht hT hF h f).trans (and_iff_right hf)⟩

theorem negation_l {a : carrier_l ℳ} (ha : member_l ℳ a ω) :
    ∃ c, member_l ℳ c ω ∧ ∀ {A S F}, evaluation_l ω e T A t₁ t₂ t₃ S F →
      ∀ f, member_l ℳ f S → (query_l F c f ↔ ¬query_l F a f) := by
  obtain ⟨c, hc, h⟩ := nand_l hℳ hω ht hT ha ha
  exact ⟨c, hc, fun hF f hf => (h hF f hf).trans (not_congr ⟨And.left, fun h => ⟨h, h⟩⟩)⟩

theorem truth_l :
    ∃ c, member_l ℳ c ω ∧ ∀ {A S F}, evaluation_l ω e T A t₁ t₂ t₃ S F →
      ∀ f, member_l ℳ f S → query_l F c f := by
  obtain ⟨c, hc, h⟩ := negation_l hℳ hω ht hT (PowerlessNatural.zero_mem_l hℳ hω ht.1)
  exact ⟨c, hc, fun hF f hf => (h hF f hf).mpr (PowerlessEvaluationLogic.zero_l hℳ hω ht hT hF f)⟩

theorem conjunction_l {a b : carrier_l ℳ} (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ ∀ {A S F}, evaluation_l ω e T A t₁ t₂ t₃ S F →
      ∀ f, member_l ℳ f S → (query_l F c f ↔ query_l F a f ∧ query_l F b f) := by
  classical
  obtain ⟨p, hp, h₀⟩ := nand_l hℳ hω ht hT ha hb
  obtain ⟨c, hc, h₁⟩ := negation_l hℳ hω ht hT hp
  exact ⟨c, hc, fun hF f hf =>
    (h₁ hF f hf).trans ((not_congr (h₀ hF f hf)).trans not_not)⟩

theorem disjunction_l {a b : carrier_l ℳ} (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ ∀ {A S F}, evaluation_l ω e T A t₁ t₂ t₃ S F →
      ∀ f, member_l ℳ f S → (query_l F c f ↔ query_l F a f ∨ query_l F b f) := by
  classical
  obtain ⟨p, hp, h₀⟩ := negation_l hℳ hω ht hT ha
  obtain ⟨q, hq, h₁⟩ := negation_l hℳ hω ht hT hb
  obtain ⟨c, hc, h₂⟩ := nand_l hℳ hω ht hT hp hq
  exact ⟨c, hc, fun hF f hf => (h₂ hF f hf).trans
    ((not_congr (and_congr (h₀ hF f hf) (h₁ hF f hf))).trans
      (not_and_or.trans (or_congr not_not not_not)))⟩

theorem implication_l {a b : carrier_l ℳ} (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ ∀ {A S F}, evaluation_l ω e T A t₁ t₂ t₃ S F →
      ∀ f, member_l ℳ f S → (query_l F c f ↔ (query_l F a f → query_l F b f)) := by
  classical
  obtain ⟨p, hp, h₀⟩ := negation_l hℳ hω ht hT hb
  obtain ⟨c, hc, h₁⟩ := nand_l hℳ hω ht hT ha hp
  refine ⟨c, hc, fun hF f hf => (h₁ hF f hf).trans ((not_congr
    (and_congr Iff.rfl (h₀ hF f hf))).trans ?_)⟩
  constructor
  · intro h ha
    by_contra hb
    exact h ⟨ha, hb⟩
  · rintro h ⟨ha, hb⟩
    exact hb (h ha)

theorem biconditional_l {a b : carrier_l ℳ} (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ ∀ {A S F}, evaluation_l ω e T A t₁ t₂ t₃ S F →
      ∀ f, member_l ℳ f S → (query_l F c f ↔ (query_l F a f ↔ query_l F b f)) := by
  obtain ⟨p, hp, h₀⟩ := implication_l hℳ hω ht hT ha hb
  obtain ⟨q, hq, h₁⟩ := implication_l hℳ hω ht hT hb ha
  obtain ⟨c, hc, h₂⟩ := conjunction_l hℳ hω ht hT hp hq
  exact ⟨c, hc, fun hF f hf => (h₂ hF f hf).trans
    ((and_congr (h₀ hF f hf) (h₁ hF f hf)).trans
      ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)⟩

theorem existential_l {i b : carrier_l ℳ} (hi : member_l ℳ i ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ ∀ {A S F}, evaluation_l ω e T A t₁ t₂ t₃ S F →
      ∀ f, member_l ℳ f S → (query_l F c f ↔ PowerlessEvaluationClause.exists_l ω A F f i b) := by
  obtain ⟨c, hc, h⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT
    (PowerlessEvaluationTags.natural_l hℳ hω ht).2.2.2 hi hb
  exact ⟨c, hc, fun hF f hf =>
    (PowerlessEvaluationEquations.exists_l hℳ hω ht hT hF h f).trans (and_iff_right hf)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessUniformEvaluationLogic
