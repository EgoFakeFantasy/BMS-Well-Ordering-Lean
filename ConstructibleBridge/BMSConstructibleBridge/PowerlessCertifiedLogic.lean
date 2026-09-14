import BMSConstructibleBridge.PowerlessEvaluationLogic
import BMSConstructibleBridge.PowerlessBoundedCertificateClosure

/-!
# 带内部有界证书的命题联结词

与非节点保留实际构造关系，先合并子证书再添入新数码。
派生联结词逐步传递同一数码的证书和语义方程。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCertifiedLogic

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationClause PowerlessBoundedCertificate

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T A t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
  (hT : PowerlessTriangular.triangular_l ω e T)
  (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)

include hℳ hω ht hT hF

theorem nand_l {a b : carrier_l ℳ}
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω)
    (h₀ : recognizes_l ω e T t₁ t₂ t₃ a) (h₁ : recognizes_l ω e T t₁ t₂ t₃ b) :
    ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ ¬(query_l F a f ∧ query_l F b f)) := by
  obtain ⟨c, hc, h⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT
    (PowerlessEvaluationTags.natural_l hℳ hω ht).2.2.1 ha hb
  exact ⟨c, hc, PowerlessBoundedCertificateClosure.nand_l hℳ hω ht.1 hT h₀ h₁ h,
    fun f hf => (PowerlessEvaluationEquations.nand_l hℳ hω ht hT hF h f).trans (and_iff_right hf)⟩

theorem negation_l {a : carrier_l ℳ} (ha : member_l ℳ a ω)
    (h₀ : recognizes_l ω e T t₁ t₂ t₃ a) :
    ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ ¬query_l F a f) := by
  obtain ⟨c, hc, hC, h⟩ := nand_l hℳ hω ht hT hF ha ha h₀ h₀
  exact ⟨c, hc, hC, fun f hf => (h f hf).trans (not_congr ⟨And.left, fun h => ⟨h, h⟩⟩)⟩

theorem truth_l : ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧
    ∀ f, member_l ℳ f S → query_l F c f := by
  obtain ⟨c, hc, hC, h⟩ := negation_l hℳ hω ht hT hF
    (PowerlessNatural.zero_mem_l hℳ hω ht.1) (PowerlessBoundedCertificateClosure.zero_l hℳ hω ht.1)
  exact ⟨c, hc, hC, fun f hf => (h f hf).mpr (PowerlessEvaluationLogic.zero_l hℳ hω ht hT hF f)⟩

theorem conjunction_l {a b : carrier_l ℳ}
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω)
    (h₀ : recognizes_l ω e T t₁ t₂ t₃ a) (h₁ : recognizes_l ω e T t₁ t₂ t₃ b) :
    ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ query_l F a f ∧ query_l F b f) := by
  classical
  obtain ⟨p, hp, hP, h₂⟩ := nand_l hℳ hω ht hT hF ha hb h₀ h₁
  obtain ⟨c, hc, hC, h₃⟩ := negation_l hℳ hω ht hT hF hp hP
  exact ⟨c, hc, hC, fun f hf => (h₃ f hf).trans ((not_congr (h₂ f hf)).trans not_not)⟩

theorem disjunction_l {a b : carrier_l ℳ}
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω)
    (h₀ : recognizes_l ω e T t₁ t₂ t₃ a) (h₁ : recognizes_l ω e T t₁ t₂ t₃ b) :
    ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ query_l F a f ∨ query_l F b f) := by
  classical
  obtain ⟨p, hp, hP, h₂⟩ := negation_l hℳ hω ht hT hF ha h₀
  obtain ⟨q, hq, hQ, h₃⟩ := negation_l hℳ hω ht hT hF hb h₁
  obtain ⟨c, hc, hC, h₄⟩ := nand_l hℳ hω ht hT hF hp hq hP hQ
  exact ⟨c, hc, hC, fun f hf => (h₄ f hf).trans ((not_congr (and_congr (h₂ f hf) (h₃ f hf))).trans
    (not_and_or.trans (or_congr not_not not_not)))⟩

theorem implication_l {a b : carrier_l ℳ}
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω)
    (h₀ : recognizes_l ω e T t₁ t₂ t₃ a) (h₁ : recognizes_l ω e T t₁ t₂ t₃ b) :
    ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ (query_l F a f → query_l F b f)) := by
  classical
  obtain ⟨q, hq, hQ, h₂⟩ := negation_l hℳ hω ht hT hF hb h₁
  obtain ⟨c, hc, hC, h₃⟩ := nand_l hℳ hω ht hT hF ha hq h₀ hQ
  refine ⟨c, hc, hC, fun f hf => (h₃ f hf).trans ((not_congr (and_congr Iff.rfl (h₂ f hf))).trans ?_)⟩
  constructor
  · intro h hp
    by_contra hq
    exact h ⟨hp, hq⟩
  · rintro h ⟨hp, hq⟩
    exact hq (h hp)

theorem biconditional_l {a b : carrier_l ℳ}
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω)
    (h₀ : recognizes_l ω e T t₁ t₂ t₃ a) (h₁ : recognizes_l ω e T t₁ t₂ t₃ b) :
    ∃ c, member_l ℳ c ω ∧ recognizes_l ω e T t₁ t₂ t₃ c ∧
      ∀ f, member_l ℳ f S → (query_l F c f ↔ (query_l F a f ↔ query_l F b f)) := by
  obtain ⟨p, hp, hP, h₂⟩ := implication_l hℳ hω ht hT hF ha hb h₀ h₁
  obtain ⟨q, hq, hQ, h₃⟩ := implication_l hℳ hω ht hT hF hb ha h₁ h₀
  obtain ⟨c, hc, hC, h₄⟩ := conjunction_l hℳ hω ht hT hF hp hq hP hQ
  exact ⟨c, hc, hC, fun f hf => (h₄ f hf).trans ((and_congr (h₂ f hf) (h₃ f hf)).trans
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCertifiedLogic
