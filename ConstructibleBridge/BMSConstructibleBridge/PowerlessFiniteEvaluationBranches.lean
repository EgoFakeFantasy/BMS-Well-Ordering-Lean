import BMSConstructibleBridge.PowerlessFiniteEvaluationClause
import BMSConstructibleBridge.PowerlessRelativeClassConstructorInjective
import BMSConstructibleBridge.PowerlessEvaluationTags

/-! # 稳定有限求值规则的四个互斥分支

规则分解只用构造子单射及实际标签互异，不调用完整源模型。
标签互异在原 Z₂ 商中由后继定义与正则性证明；不作为新增公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationBranches

open Logic FirstOrder ThirdOrderSemantics PowerlessFormulaConstructor
open PowerlessRelativeClassConstructorInjective (injective_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def distinct_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (e t₁ t₂ t₃ : carrier_l 𝒩) : Prop :=
  e ≠ t₁ ∧ e ≠ t₂ ∧ e ≠ t₃ ∧ t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃

theorem tags_distinct_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {e t₁ t₂ t₃ : SecondOrderQuotient.type_l hℳ}
    (h : PowerlessEvaluationTags.tags_l (ℳ := SecondOrderQuotient.structure_l hℳ) e t₁ t₂ t₃) :
    distinct_l (𝒩 := SecondOrderQuotient.structure_l hℳ) e t₁ t₂ t₃ := by
  have hNe (a b : SecondOrderQuotient.type_l hℳ) (hab : SecondOrderQuotient.mem_l hℳ a b) : a ≠ b := by
    rintro rfl
    exact SecondOrderNaturalCases.asymmetry_l hℳ hab hab
  have h₁ := (h.2.1 e).mpr (Or.inr rfl)
  have h₂ := (h.2.2.1 t₁).mpr (Or.inr rfl)
  have h₃ := (h.2.2.2 t₂).mpr (Or.inr rfl)
  have h₄ := (h.2.2.1 e).mpr (Or.inl h₁)
  exact ⟨hNe _ _ h₁, hNe _ _ h₄, hNe _ _ ((h.2.2.2 e).mpr (Or.inl h₄)),
    hNe _ _ h₂, hNe _ _ ((h.2.2.2 t₁).mpr (Or.inl h₂)), hNe _ _ h₃⟩

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {C ω e N T A S t₁ t₂ t₃ Q n f : carrier_l 𝒩}

theorem fiber_l (hInjective : injective_l (𝒩 := 𝒩) ω e T) {t a b : carrier_l 𝒩}
    (hn : constructor_l ω e T t a b n) (s : carrier_l 𝒩) (P : carrier_l 𝒩 → carrier_l 𝒩 → Prop) :
    (∃ i j, constructor_l ω e T s i j n ∧ P i j) ↔ s = t ∧ P a b := by
  constructor
  · rintro ⟨i, j, h, hP⟩
    obtain ⟨h₀, h₁, h₂⟩ := hInjective _ _ _ _ _ _ _ h hn
    subst i
    subst j
    exact ⟨h₀, hP⟩
  · rintro ⟨rfl, hP⟩
    exact ⟨a, b, hn, hP⟩

theorem member_l (hInjective : injective_l (𝒩 := 𝒩) ω e T) (hDistinct : distinct_l (𝒩 := 𝒩) e t₁ t₂ t₃)
    {i j : carrier_l 𝒩} (hn : constructor_l ω e T e i j n) :
    PowerlessFiniteEvaluationClause.holds_l C ω e N T A S t₁ t₂ t₃ Q n f ↔
      PowerlessEvaluationClause.member_l f i j := by
  obtain ⟨h₁, h₂, h₃, _, _, _⟩ := hDistinct
  simp only [PowerlessFiniteEvaluationClause.holds_l, fiber_l hInjective hn,
    Ne.symm h₁, Ne.symm h₂, Ne.symm h₃, true_and, false_and, or_false]

theorem equal_l (hInjective : injective_l (𝒩 := 𝒩) ω e T) (hDistinct : distinct_l (𝒩 := 𝒩) e t₁ t₂ t₃)
    {i j : carrier_l 𝒩} (hn : constructor_l ω e T t₁ i j n) :
    PowerlessFiniteEvaluationClause.holds_l C ω e N T A S t₁ t₂ t₃ Q n f ↔
      PowerlessEvaluationClause.equal_l f i j := by
  obtain ⟨h₁, _, _, h₂, h₃, _⟩ := hDistinct
  simp only [PowerlessFiniteEvaluationClause.holds_l, fiber_l hInjective hn,
    h₁, Ne.symm h₂, Ne.symm h₃, true_and, false_and, false_or, or_false]

theorem nand_l (hInjective : injective_l (𝒩 := 𝒩) ω e T) (hDistinct : distinct_l (𝒩 := 𝒩) e t₁ t₂ t₃)
    {a b : carrier_l 𝒩} (hn : constructor_l ω e T t₂ a b n) :
    PowerlessFiniteEvaluationClause.holds_l C ω e N T A S t₁ t₂ t₃ Q n f ↔
      ¬(PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q a f ∧
        PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q b f) := by
  obtain ⟨_, h₁, _, h₂, _, h₃⟩ := hDistinct
  simp only [PowerlessFiniteEvaluationClause.holds_l, fiber_l hInjective hn,
    h₁, h₂, Ne.symm h₃, true_and, false_and, false_or, or_false]

theorem exists_l (hInjective : injective_l (𝒩 := 𝒩) ω e T) (hDistinct : distinct_l (𝒩 := 𝒩) e t₁ t₂ t₃)
    {i b : carrier_l 𝒩} (hn : constructor_l ω e T t₃ i b n) :
    PowerlessFiniteEvaluationClause.holds_l C ω e N T A S t₁ t₂ t₃ Q n f ↔
      PowerlessFiniteEvaluationClause.exists_l C ω e N T A S t₁ t₂ t₃ Q f i b := by
  obtain ⟨_, _, h₁, _, h₂, h₃⟩ := hDistinct
  simp only [PowerlessFiniteEvaluationClause.holds_l, fiber_l hInjective hn,
    h₁, h₂, h₃, true_and, false_and, false_or]

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationBranches
