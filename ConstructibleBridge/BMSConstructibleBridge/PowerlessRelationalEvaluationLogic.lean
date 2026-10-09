import BMSConstructibleBridge.PowerlessRelativeClassEvaluationSystem
import BMSConstructibleBridge.PowerlessRelationalCodeDerivation

/-! # 集合关系求值器的跨域逻辑数码

只消费构造子全域性与实际图方程，数码先于全部求值域和图选定。
不把关系图误作旧的函数值真值列历史，也不要求完整源理论模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalEvaluationLogic

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassEvaluationSystem (spec_l)
open PowerlessRelationalCodeDerivation (derivation_l)

set_option autoImplicit false

universe u

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e T t₁ t₂ t₃ : carrier_l 𝒩}
  (hConstruct : PowerlessRelativeClassConstructorTotal.functional_l ω e T)
  (ht₂ : member_l 𝒩 t₂ ω)

include hConstruct ht₂

namespace Certified

theorem nand_l {a b : carrier_l 𝒩} (ha : member_l 𝒩 a ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧
      (∀ N, derivation_l ω e T t₁ t₂ t₃ a N → derivation_l ω e T t₁ t₂ t₃ b N → derivation_l ω e T t₁ t₂ t₃ c N) ∧
      ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ ¬(value_l G a f ∧ value_l G b f)) := by
  obtain ⟨c, hc, hCode, _⟩ := hConstruct t₂ ht₂ a ha b hb
  exact ⟨c, hc, fun _ => derivation_l.nand hCode, fun hSystem f hf =>
    ((hSystem.2.2.2.2.2 c hc f a b).2.2.1 hCode).trans (and_iff_right hf)⟩

theorem negation_l {a : carrier_l 𝒩} (ha : member_l 𝒩 a ω) :
    ∃ c, member_l 𝒩 c ω ∧
      (∀ N, derivation_l ω e T t₁ t₂ t₃ a N → derivation_l ω e T t₁ t₂ t₃ c N) ∧
      ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ ¬value_l G a f) := by
  obtain ⟨c, hc, hBuild, h⟩ := nand_l hConstruct ht₂ ha ha
  exact ⟨c, hc, fun N h => hBuild N h h, fun hSystem f hf => (h hSystem f hf).trans
    (not_congr ⟨And.left, fun h => ⟨h, h⟩⟩)⟩

theorem truth_l (he : member_l 𝒩 e ω) :
    ∃ c, member_l 𝒩 c ω ∧ (∀ N, derivation_l ω e T t₁ t₂ t₃ c N) ∧
      ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → value_l G c f := by
  obtain ⟨c, hc, hBuild, h⟩ := negation_l hConstruct ht₂ he
  exact ⟨c, hc, fun N => hBuild N .zero, fun hSystem f hf => (h hSystem f hf).mpr (hSystem.2.2.2.2.1 f)⟩

theorem conjunction_l {a b : carrier_l 𝒩} (ha : member_l 𝒩 a ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧
      (∀ N, derivation_l ω e T t₁ t₂ t₃ a N → derivation_l ω e T t₁ t₂ t₃ b N → derivation_l ω e T t₁ t₂ t₃ c N) ∧
      ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ value_l G a f ∧ value_l G b f) := by
  classical
  obtain ⟨p, hp, hBuild₀, h₀⟩ := nand_l hConstruct ht₂ ha hb
  obtain ⟨c, hc, hBuild₁, h₁⟩ := negation_l hConstruct ht₂ hp
  exact ⟨c, hc, fun N ha hb => hBuild₁ N (hBuild₀ N ha hb), fun hSystem f hf =>
    (h₁ hSystem f hf).trans ((not_congr (h₀ hSystem f hf)).trans not_not)⟩

theorem disjunction_l {a b : carrier_l 𝒩} (ha : member_l 𝒩 a ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧
      (∀ N, derivation_l ω e T t₁ t₂ t₃ a N → derivation_l ω e T t₁ t₂ t₃ b N → derivation_l ω e T t₁ t₂ t₃ c N) ∧
      ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ value_l G a f ∨ value_l G b f) := by
  classical
  obtain ⟨p, hp, hBuild₀, h₀⟩ := negation_l hConstruct ht₂ ha
  obtain ⟨q, hq, hBuild₁, h₁⟩ := negation_l hConstruct ht₂ hb
  obtain ⟨c, hc, hBuild₂, h₂⟩ := nand_l hConstruct ht₂ hp hq
  exact ⟨c, hc, fun N ha hb => hBuild₂ N (hBuild₀ N ha) (hBuild₁ N hb), fun hSystem f hf => (h₂ hSystem f hf).trans
    ((not_congr (and_congr (h₀ hSystem f hf) (h₁ hSystem f hf))).trans
      (not_and_or.trans (or_congr not_not not_not)))⟩

theorem implication_l {a b : carrier_l 𝒩} (ha : member_l 𝒩 a ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧
      (∀ N, derivation_l ω e T t₁ t₂ t₃ a N → derivation_l ω e T t₁ t₂ t₃ b N → derivation_l ω e T t₁ t₂ t₃ c N) ∧
      ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ (value_l G a f → value_l G b f)) := by
  classical
  obtain ⟨p, hp, hBuild₀, h₀⟩ := negation_l hConstruct ht₂ hb
  obtain ⟨c, hc, hBuild₁, h₁⟩ := nand_l hConstruct ht₂ ha hp
  refine ⟨c, hc, fun N ha hb => hBuild₁ N ha (hBuild₀ N hb), fun hSystem f hf => (h₁ hSystem f hf).trans
    ((not_congr (and_congr Iff.rfl (h₀ hSystem f hf))).trans ?_)⟩
  constructor
  · intro h ha
    by_contra hb
    exact h ⟨ha, hb⟩
  · rintro h ⟨ha, hb⟩
    exact hb (h ha)

theorem biconditional_l {a b : carrier_l 𝒩} (ha : member_l 𝒩 a ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧
      (∀ N, derivation_l ω e T t₁ t₂ t₃ a N → derivation_l ω e T t₁ t₂ t₃ b N → derivation_l ω e T t₁ t₂ t₃ c N) ∧
      ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ (value_l G a f ↔ value_l G b f)) := by
  obtain ⟨p, hp, hBuild₀, h₀⟩ := implication_l hConstruct ht₂ ha hb
  obtain ⟨q, hq, hBuild₁, h₁⟩ := implication_l hConstruct ht₂ hb ha
  obtain ⟨c, hc, hBuild₂, h₂⟩ := conjunction_l hConstruct ht₂ hp hq
  exact ⟨c, hc, fun N ha hb => hBuild₂ N (hBuild₀ N ha hb) (hBuild₁ N hb ha), fun hSystem f hf => (h₂ hSystem f hf).trans
    ((and_congr (h₀ hSystem f hf) (h₁ hSystem f hf)).trans
      ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)⟩

omit ht₂ in
theorem existential_l (ht₃ : member_l 𝒩 t₃ ω) {i b : carrier_l 𝒩}
    (hi : member_l 𝒩 i ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧
      (∀ N, member_l 𝒩 i N → derivation_l ω e T t₁ t₂ t₃ b N → derivation_l ω e T t₁ t₂ t₃ c N) ∧
      ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ PowerlessFiniteEvaluationRelationEquations.exists_l ω A G f i b) := by
  obtain ⟨c, hc, hCode, _⟩ := hConstruct t₃ ht₃ i hi b hb
  exact ⟨c, hc, fun _ => derivation_l.existential hCode, fun hSystem f hf =>
    ((hSystem.2.2.2.2.2 c hc f i b).2.2.2 hCode).trans (and_iff_right hf)⟩

end Certified

/-- 原语义接口保留；同一见证的有限构造证书由 Certified 接口公开。 -/
theorem nand_l {a b : carrier_l 𝒩} (ha : member_l 𝒩 a ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧ ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ ¬(value_l G a f ∧ value_l G b f)) := by
  obtain ⟨c, hc, _, h⟩ := Certified.nand_l hConstruct ht₂ ha hb
  exact ⟨c, hc, h⟩

theorem negation_l {a : carrier_l 𝒩} (ha : member_l 𝒩 a ω) :
    ∃ c, member_l 𝒩 c ω ∧ ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ ¬value_l G a f) := by
  obtain ⟨c, hc, _, h⟩ := Certified.negation_l hConstruct ht₂ ha
  exact ⟨c, hc, h⟩

theorem truth_l (he : member_l 𝒩 e ω) :
    ∃ c, member_l 𝒩 c ω ∧ ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → value_l G c f := by
  obtain ⟨c, hc, _, h⟩ := Certified.truth_l hConstruct ht₂ he
  exact ⟨c, hc, h⟩

theorem conjunction_l {a b : carrier_l 𝒩} (ha : member_l 𝒩 a ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧ ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ value_l G a f ∧ value_l G b f) := by
  obtain ⟨c, hc, _, h⟩ := Certified.conjunction_l hConstruct ht₂ ha hb
  exact ⟨c, hc, h⟩

theorem disjunction_l {a b : carrier_l 𝒩} (ha : member_l 𝒩 a ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧ ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ value_l G a f ∨ value_l G b f) := by
  obtain ⟨c, hc, _, h⟩ := Certified.disjunction_l hConstruct ht₂ ha hb
  exact ⟨c, hc, h⟩

theorem implication_l {a b : carrier_l 𝒩} (ha : member_l 𝒩 a ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧ ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ (value_l G a f → value_l G b f)) := by
  obtain ⟨c, hc, _, h⟩ := Certified.implication_l hConstruct ht₂ ha hb
  exact ⟨c, hc, h⟩

theorem biconditional_l {a b : carrier_l 𝒩} (ha : member_l 𝒩 a ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧ ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ (value_l G a f ↔ value_l G b f)) := by
  obtain ⟨c, hc, _, h⟩ := Certified.biconditional_l hConstruct ht₂ ha hb
  exact ⟨c, hc, h⟩

omit ht₂ in
theorem existential_l (ht₃ : member_l 𝒩 t₃ ω) {i b : carrier_l 𝒩}
    (hi : member_l 𝒩 i ω) (hb : member_l 𝒩 b ω) :
    ∃ c, member_l 𝒩 c ω ∧ ∀ {A S G}, spec_l ω A e t₁ t₂ t₃ T S G →
      ∀ f, member_l 𝒩 f S → (value_l G c f ↔ PowerlessFiniteEvaluationRelationEquations.exists_l ω A G f i b) := by
  obtain ⟨c, hc, _, h⟩ := Certified.existential_l hConstruct ht₃ hi hb
  exact ⟨c, hc, h⟩

#print axioms Certified.nand_l
#print axioms Certified.biconditional_l
#print axioms Certified.existential_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalEvaluationLogic
