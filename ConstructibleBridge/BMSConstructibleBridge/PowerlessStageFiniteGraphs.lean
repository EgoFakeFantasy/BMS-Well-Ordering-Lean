import BMSConstructibleBridge.PowerlessStageGraphClosure
import BMSConstructibleBridge.PowerlessStageParameters

/-!
# 非零极限层包含所有内部有限赋值图

使用背景模型中的原纯公式归纳，覆盖内部 ω 的全部长度。
这里得到每个有限图属于 Cα，以及全部有限图的集合是 Cα 的子集；
并不把这个无限集合本身断言为 Cα 的元素。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteGraphs

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem finite_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α) :
    ∀ n, member_l ℳ n ω → ∀ f, map_l f n A → member_l ℳ f A := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => A, free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set] := .forallE .set (.imp
    (SecondOrderObjectSyntax.map_m (.bvar .here) (.fvar .here) (.fvar (.there .here)))
    (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here))))
  have h : ∀ n, φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ f, map_l f n A → member_l ℳ f A := by
    intro n
    simp only [φ, Formula.satisfies, map_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  have h₀ := PowerlessNatural.induction_l hℳ φ η hω
    (fun z hz => (h z).mpr (by
      intro f hf
      have h₁ := PowerlessFiniteAssignments.empty_unique_l hℳ hz hf
      subst f
      exact PowerlessStageClosure.empty_l hℳ hω hA hα ht hT hz))
    (fun n m hn hm h₁ => (h m).mpr (by
      intro g hg
      obtain ⟨f, a, hf, ha, hg⟩ := PowerlessAppendGraph.decompose_l hℳ hg hm
      have hnA := PowerlessStageParameters.naturals_l hℳ hω ht hT hA hωα n hn
      exact PowerlessStageGraphClosure.append_l hℳ hω ht hT hA hα ((h n).mp h₁ f hf) hnA ha hg))
  exact fun n hn => (h n).mp (h₀ n hn)

theorem assignments_l {α A S : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α)
    (hS : PowerlessEvaluationOperator.assignments_l ω A S) : subset_l S A := by
  intro f hf
  obtain ⟨n, hn, hf⟩ := (hS f).mp hf
  exact finite_l hℳ hω ht hT hA hα hωα n hn f hf

theorem first_l {A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ ω A) :
    ∀ n, member_l ℳ n ω → ∀ f, map_l f n A → member_l ℳ f A := by
  obtain ⟨z, _, hz⟩ := ((PowerlessNatural.inductive_iff_l ω).mp hω.1).1
  exact finite_l hℳ hω ht hT hA
    ⟨PowerlessOmegaOrdinal.ordinal_l hℳ hω, ⟨z, hz⟩, PowerlessOmegaOrdinal.limit_l hℳ hω⟩
    (fun _ hx => hx)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteGraphs
