import BMSConstructibleBridge.PowerlessHierarchyStructure
import BMSConstructibleBridge.PowerlessSourceCoverage

/-!
# 累计层次的后继与极限方程

由传递性得到 Cα⊆D(Cα)，将累计后继并精确化为 D(Cα)。
极限使用内部指标的无末端条件；所有值仍是同一实际函数图的值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyContinuity

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationHierarchy

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem successor_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α a b A B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hα : PowerlessOrdinal.ordinal_l α) (hf : hierarchy_l ω e T t₁ t₂ t₃ f α)
    (hb : PowerlessNatural.successor_l a b) (hA : value_l f a A) (hB : value_l f b B) :
    PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A B := by
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ A
  have h₀ := PowerlessEvaluationOperator.inclusion_l hℳ hω ht hT hD
    (PowerlessHierarchyStructure.transitive_l hℳ hω ht hT hα hf a A hA)
  have hf₁ := hf
  obtain ⟨R, hf₀, _⟩ := hf₁
  have h₁ : B = D := by
    apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
    intro x
    constructor
    · intro hx
      obtain ⟨c, C, E, hc, hC, hE, hx⟩ := (equation_l hℳ hf hB x).mp hx
      rcases (hb c).mp hc with hc | hc
      · exact h₀ x ((equation_l hℳ hf hA x).mpr ⟨c, C, E, hc, hC, hE, hx⟩)
      · subst c
        have h₂ := PowerlessFunction.value_unique_l hℳ hf₀ hC hA
        subst C
        exact (PowerlessEvaluationOperator.unique_l hℳ hω hE hD) ▸ hx
    · intro hx
      exact (equation_l hℳ hf hB x).mpr ⟨a, A, D, (hb a).mpr (Or.inr rfl), hA, hD, hx⟩
  exact h₁.symm ▸ hD

theorem limit_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α a A : carrier_l ℳ} (hα : PowerlessOrdinal.ordinal_l α)
    (hf : hierarchy_l ω e T t₁ t₂ t₃ f α) (hA : value_l f a A)
    (ha : ∀ b, member_l ℳ b a → ∃ c, member_l ℳ c a ∧ member_l ℳ b c) (x : carrier_l ℳ) :
    member_l ℳ x A ↔ ∃ b B, member_l ℳ b a ∧ value_l f b B ∧ member_l ℳ x B := by
  have hf₁ := hf
  obtain ⟨R, hf₀, _⟩ := hf₁
  have ha₀ := (PowerlessFunction.value_mem_l hℳ hf₀ hA).1
  constructor
  · intro hx
    obtain ⟨b, B, D, hb, hB, hD, hx⟩ := (equation_l hℳ hf hA x).mp hx
    obtain ⟨c, hc, hbc⟩ := ha b hb
    obtain ⟨C, hC, _⟩ := hf₀.2 c (PowerlessOrdinal.transitive_l hα a c ha₀ hc)
    exact ⟨c, C, hc, hC.2, PowerlessHierarchyStructure.image_subset_l hℳ hf hbc hC.2 hB hD x hx⟩
  · rintro ⟨b, B, hb, hB, hx⟩
    exact PowerlessHierarchyStructure.subset_l hℳ hf (PowerlessOrdinal.mem_l hα ha₀) hb hA hB x hx

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α a b A B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hf : hierarchy_l ω e T t₁ t₂ t₃ f α) (hb : ThirdOrderSemantics.member_l ℳ a b)
    (hA : value_l f a A) (hB : value_l f b B) : ThirdOrderSemantics.member_l ℳ A B := by
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ A
  exact PowerlessHierarchyStructure.image_subset_l hℳ hf hb hB hA hD A
    (PowerlessSourceCoverage.domain_l hℳ hω ht hT hD)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyContinuity
