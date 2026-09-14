import BMSConstructibleBridge.PowerlessEvaluationRecursion
import BMSConstructibleBridge.PowerlessEvaluationTags

/-!
# 全内部构造子的精确求值方程

由实际标签互异和构造子单射，分离四个分支。定理针对实际有限图及
模型全部内部子码，不仅是外部标准公式的归纳实例；源编译仍需另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationEquations

open Logic FirstOrder ThirdOrderSemantics PowerlessFormulaConstructor PowerlessEvaluationRecursion

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F n i j : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : evaluation_l ω e T A t₁ t₂ t₃ S F) (hn : constructor_l ω e T e i j n) (f : carrier_l ℳ) :
    PowerlessEvaluationClause.query_l F n f ↔ ThirdOrderSemantics.member_l ℳ f S ∧ PowerlessEvaluationClause.member_l f i j := by
  obtain ⟨h₁, h₂, h₃, _, _, _⟩ := PowerlessEvaluationTags.distinct_l hℳ ht
  refine (equation_l hℳ hω ht.1 hT hF (natural_l hℳ hω ht.1 hT hn) f).trans (and_congr Iff.rfl ?_)
  simp only [PowerlessEvaluationClause.clause_l, fiber_l hℳ hω ht.1 hT hn,
    Ne.symm h₁, Ne.symm h₂, Ne.symm h₃, true_and, false_and, or_false]

theorem equal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F n i j : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : evaluation_l ω e T A t₁ t₂ t₃ S F) (hn : constructor_l ω e T t₁ i j n) (f : carrier_l ℳ) :
    PowerlessEvaluationClause.query_l F n f ↔ ThirdOrderSemantics.member_l ℳ f S ∧ PowerlessEvaluationClause.equal_l f i j := by
  obtain ⟨h₁, _, _, h₂, h₃, _⟩ := PowerlessEvaluationTags.distinct_l hℳ ht
  refine (equation_l hℳ hω ht.1 hT hF (natural_l hℳ hω ht.1 hT hn) f).trans (and_congr Iff.rfl ?_)
  simp only [PowerlessEvaluationClause.clause_l, fiber_l hℳ hω ht.1 hT hn,
    h₁, Ne.symm h₂, Ne.symm h₃, true_and, false_and, false_or, or_false]

theorem nand_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F n a b : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : evaluation_l ω e T A t₁ t₂ t₃ S F) (hn : constructor_l ω e T t₂ a b n) (f : carrier_l ℳ) :
    PowerlessEvaluationClause.query_l F n f ↔ ThirdOrderSemantics.member_l ℳ f S ∧
      ¬(PowerlessEvaluationClause.query_l F a f ∧ PowerlessEvaluationClause.query_l F b f) := by
  obtain ⟨_, h₁, _, h₂, _, h₃⟩ := PowerlessEvaluationTags.distinct_l hℳ ht
  refine (equation_l hℳ hω ht.1 hT hF (natural_l hℳ hω ht.1 hT hn) f).trans (and_congr Iff.rfl ?_)
  simp only [PowerlessEvaluationClause.clause_l, fiber_l hℳ hω ht.1 hT hn,
    h₁, h₂, Ne.symm h₃, true_and, false_and, false_or, or_false]

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F n i b : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : evaluation_l ω e T A t₁ t₂ t₃ S F) (hn : constructor_l ω e T t₃ i b n) (f : carrier_l ℳ) :
    PowerlessEvaluationClause.query_l F n f ↔ ThirdOrderSemantics.member_l ℳ f S ∧
      PowerlessEvaluationClause.exists_l ω A F f i b := by
  obtain ⟨_, _, h₁, _, h₂, h₃⟩ := PowerlessEvaluationTags.distinct_l hℳ ht
  refine (equation_l hℳ hω ht.1 hT hF (natural_l hℳ hω ht.1 hT hn) f).trans (and_congr Iff.rfl ?_)
  simp only [PowerlessEvaluationClause.clause_l, fiber_l hℳ hω ht.1 hT hn,
    h₁, h₂, h₃, true_and, false_and, false_or]

theorem system_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) (A : carrier_l ℳ) :
    ∃ e T t₁ t₂ t₃ S F, PowerlessEvaluationTags.tags_l e t₁ t₂ t₃ ∧
      PowerlessTriangular.triangular_l ω e T ∧
      (∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ n, ThirdOrderSemantics.member_l ℳ n ω ∧ map_l f n A) ∧
      evaluation_l ω e T A t₁ t₂ t₃ S F := by
  obtain ⟨e, he⟩ := PowerlessBasic.empty_l hℳ
  obtain ⟨T, hT⟩ := PowerlessTriangular.exists_l hℳ hω he
  obtain ⟨t₁, t₂, t₃, ht⟩ := PowerlessEvaluationTags.exists_l hℳ he
  obtain ⟨S, F, hS, hF, _⟩ := PowerlessEvaluationRecursion.exists_l hℳ hω he hT A t₁ t₂ t₃
  exact ⟨e, T, t₁, t₂, t₃, S, F, ht, hT, hS, hF⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationEquations
