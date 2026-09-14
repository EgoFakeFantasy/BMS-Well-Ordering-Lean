import BMSConstructibleBridge.PowerlessSourcePolarity
import BMSConstructibleBridge.PowerlessEvaluationLogic

/-!
# 同一内部层号上的布尔编译与极性

实际 NAND 构造保留数码、翻转后的分类及真值方程。派生布尔规则逐步
传递这些证据；蕴含要求前件处于反极性，与原 IsLevel1 的规则一致。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyLogic

open Logic FirstOrder ThirdOrderSemantics PowerlessLevyCertificate PowerlessSourcePolarity PowerlessEvaluationClause

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T A t₁ t₂ t₃ S F n : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)

include hℳ hω ht hT hF

theorem nand_l {a b : carrier_l ℳ} {p : Formula.LevyPolarity}
    (ha : class_l ω e T t₁ t₂ t₃ a n (code_l e t₁ p))
    (hb : class_l ω e T t₁ t₂ t₃ b n (code_l e t₁ p)) :
    ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n (code_l e t₁ p.flip) ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ ¬(query_l F a f ∧ query_l F b f)) := by
  obtain ⟨c, hc, hC⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT
    (PowerlessEvaluationTags.natural_l hℳ hω ht).2.2.1
    (PowerlessLevyCertificate.natural_l ha).1 (PowerlessLevyCertificate.natural_l hb).1
  exact ⟨c, hc, PowerlessLevyGeneration.boolean_l hℳ hω ht hT
    (PowerlessLevyCertificate.natural_l ha).2.1 (fun _ hx => hx) (fun _ hx => hx)
    (opposite_l e t₁ p) ha hb hC,
    fun f hf => (PowerlessEvaluationEquations.nand_l hℳ hω ht hT hF hC f).trans (and_iff_right hf)⟩

theorem negation_l {a : carrier_l ℳ} {p : Formula.LevyPolarity}
    (ha : class_l ω e T t₁ t₂ t₃ a n (code_l e t₁ p)) :
    ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n (code_l e t₁ p.flip) ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ ¬query_l F a f) := by
  obtain ⟨c, hc, hC, h⟩ := nand_l hℳ hω ht hT hF ha ha
  exact ⟨c, hc, hC, fun f hf => (h f hf).trans (not_congr ⟨And.left, fun h => ⟨h, h⟩⟩)⟩

theorem conjunction_l {a b : carrier_l ℳ} {p : Formula.LevyPolarity}
    (ha : class_l ω e T t₁ t₂ t₃ a n (code_l e t₁ p))
    (hb : class_l ω e T t₁ t₂ t₃ b n (code_l e t₁ p)) :
    ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n (code_l e t₁ p) ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ query_l F a f ∧ query_l F b f) := by
  classical
  obtain ⟨d, _, hD, h₀⟩ := nand_l hℳ hω ht hT hF ha hb
  obtain ⟨c, hc, hC, h₁⟩ := negation_l hℳ hω ht hT hF hD
  rw [flip_l] at hC
  exact ⟨c, hc, hC, fun f hf => (h₁ f hf).trans ((not_congr (h₀ f hf)).trans not_not)⟩

theorem disjunction_l {a b : carrier_l ℳ} {p : Formula.LevyPolarity}
    (ha : class_l ω e T t₁ t₂ t₃ a n (code_l e t₁ p))
    (hb : class_l ω e T t₁ t₂ t₃ b n (code_l e t₁ p)) :
    ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n (code_l e t₁ p) ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ query_l F a f ∨ query_l F b f) := by
  classical
  obtain ⟨d, _, hD, h₀⟩ := negation_l hℳ hω ht hT hF ha
  obtain ⟨q, _, hQ, h₁⟩ := negation_l hℳ hω ht hT hF hb
  obtain ⟨c, hc, hC, h₂⟩ := nand_l hℳ hω ht hT hF hD hQ
  rw [flip_l] at hC
  exact ⟨c, hc, hC, fun f hf => (h₂ f hf).trans ((not_congr (and_congr (h₀ f hf) (h₁ f hf))).trans
    (not_and_or.trans (or_congr not_not not_not)))⟩

theorem implication_l {a b : carrier_l ℳ} {p : Formula.LevyPolarity}
    (ha : class_l ω e T t₁ t₂ t₃ a n (code_l e t₁ p.flip))
    (hb : class_l ω e T t₁ t₂ t₃ b n (code_l e t₁ p)) :
    ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n (code_l e t₁ p) ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ (query_l F a f → query_l F b f)) := by
  classical
  obtain ⟨q, _, hQ, h₀⟩ := negation_l hℳ hω ht hT hF hb
  obtain ⟨c, hc, hC, h₁⟩ := nand_l hℳ hω ht hT hF ha hQ
  rw [flip_l] at hC
  refine ⟨c, hc, hC, fun f hf => (h₁ f hf).trans ((not_congr (and_congr Iff.rfl (h₀ f hf))).trans ?_)⟩
  constructor
  · intro h hp
    by_contra hq
    exact h ⟨hp, hq⟩
  · rintro h ⟨hp, hq⟩
    exact hq (h hp)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyLogic
