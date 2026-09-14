import BMSConstructibleBridge.PowerlessHierarchyPresentation
import BMSConstructibleBridge.PowerlessOrdinalInduction

/-!
# 累计层次的空起点、嵌套与传递性

传递性使用实际纯公式在内部序数上归纳。嵌套直接由累计成员方程得到，
没有假定一般子集算子对载体包含关系单调。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyStructure

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationHierarchy

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α a A : carrier_l ℳ} (hf : hierarchy_l ω e T t₁ t₂ t₃ f α)
    (ha : PowerlessNatural.zero_l a) (hA : value_l f a A) : PowerlessNatural.zero_l A := by
  intro x hx
  obtain ⟨b, _, _, hb, _⟩ := (equation_l hℳ hf hA x).mp hx
  exact ha b hb

theorem image_subset_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α a b A B D : carrier_l ℳ} (hf : hierarchy_l ω e T t₁ t₂ t₃ f α)
    (hb : member_l ℳ b a) (hA : value_l f a A) (hB : value_l f b B)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D) : subset_l D A :=
  fun x hx => (equation_l hℳ hf hA x).mpr ⟨b, B, D, hb, hB, hD, hx⟩

theorem subset_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α a b A B : carrier_l ℳ} (hf : hierarchy_l ω e T t₁ t₂ t₃ f α)
    (ha : PowerlessOrdinal.ordinal_l a) (hb : member_l ℳ b a)
    (hA : value_l f a A) (hB : value_l f b B) : ThirdOrderSemantics.subset_l B A := by
  intro x hx
  obtain ⟨c, C, D, hc, hC, hD, hx⟩ := (equation_l hℳ hf hB x).mp hx
  exact (equation_l hℳ hf hA x).mpr
    ⟨c, C, D, PowerlessOrdinal.transitive_l ha b c hb hc, hC, hD, hx⟩

theorem transitive_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hα : PowerlessOrdinal.ordinal_l α) (hf : hierarchy_l ω e T t₁ t₂ t₃ f α) :
    ∀ a A, value_l f a A → PowerlessNaturalOrder.transitive_l A := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => f, free := fun _ => α }
  let φ : Formula ℒ [] [.set, .set] := .forallE .set (.imp
    (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (PowerlessNaturalOrder.transitive_m (.bvar .here)))
  have h : ∀ a, φ.satisfies ((PowerlessComprehension.env_l η).pushFree a) ↔
      ∀ A, value_l f a A → PowerlessNaturalOrder.transitive_l A := by
    intro a
    simp only [φ, Formula.satisfies, value_formula_l, PowerlessNaturalOrder.transitive_formula_l]
    rfl
  have h₀ := PowerlessOrdinalInduction.induction_l hℳ φ η hα (fun a _ h₁ => by
    apply (h a).mpr
    intro A hA x y hx hy
    obtain ⟨b, B, D, hb, hB, hD, hx⟩ := (equation_l hℳ hf hA x).mp hx
    have h₂ := (h b).mp (h₁ b hb) B hB
    have h₃ := PowerlessEvaluationOperator.transitive_l hℳ hω ht hT hD h₂
    exact (equation_l hℳ hf hA y).mpr ⟨b, B, D, hb, hB, hD, h₃ x y hx hy⟩)
  intro a A hA
  obtain ⟨B, hB, _⟩ := hf
  exact (h a).mp (h₀ a (PowerlessFunction.value_mem_l hℳ hB hA).1) A hA

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyStructure
