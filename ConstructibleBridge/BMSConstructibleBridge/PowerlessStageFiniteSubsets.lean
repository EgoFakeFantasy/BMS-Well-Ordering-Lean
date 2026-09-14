import BMSConstructibleBridge.PowerlessStageFiniteGraphs

/-!
# 实际非零极限层包含内部自然数的所有子集

按原纯公式在环境 ω 上归纳。后继步从 D 分离 D∩n，再按 n∈D 与否添元。
不把子集当作函数图，不使用外部有限性或小结构的幂集公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteSubsets

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem finite_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hωα : subset_l ω α) :
    ∀ n, member_l ℳ n ω → ∀ D, subset_l D n → member_l ℳ D A := by
  classical
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => A, free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set] := .forallE .set (.imp
    (ThirdOrderTheory.subset_m (.bvar .here) (.fvar .here))
    (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here))))
  have h (n : carrier_l ℳ) : φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ D, subset_l D n → member_l ℳ D A := by
    simp only [φ, Formula.satisfies, subset_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  have h₀ := PowerlessNatural.induction_l hℳ φ η hω
    (fun z hz => (h z).mpr (by
      intro D hD
      exact PowerlessStageClosure.empty_l hℳ hω hA hα ht hT (fun x hx => hz x (hD x hx))))
    (fun n m hn hm h₁ => (h m).mpr (by
      intro D hD
      let ζ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
        { bound := fun _ => n, free := fun _ => D }
      let ψ : Formula ℒ [] [.set, .set] :=
        SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here))
      obtain ⟨K, hK₀⟩ := PowerlessComprehension.separation_l hℳ ψ ζ D
      have hK : ∀ x, member_l ℳ x K ↔ member_l ℳ x D ∧ member_l ℳ x n := by
        intro x
        exact hK₀ x
      have hKA := (h n).mp h₁ K (fun x hx => ((hK x).mp hx).2)
      by_cases hnD : member_l ℳ n D
      · apply PowerlessStageGraphClosure.adjoin_l hℳ hω ht hT hA hα hKA
          (PowerlessStageParameters.naturals_l hℳ hω ht hT hA hωα n hn)
        intro x
        constructor
        · intro hx
          rcases (hm x).mp (hD x hx) with hx₀ | hx₀
          · exact Or.inl ((hK x).mpr ⟨hx, hx₀⟩)
          · exact Or.inr hx₀
        · rintro (hx | rfl)
          · exact ((hK x).mp hx).1
          · exact hnD
      · have hDK : D = K := (PowerlessTheory.ext_l hℳ).eq_of_same_members D K (fun x => by
          constructor
          · intro hx
            rcases (hm x).mp (hD x hx) with hx₀ | rfl
            · exact (hK x).mpr ⟨hx, hx₀⟩
            · exact (hnD hx).elim
          · intro hx
            exact ((hK x).mp hx).1)
        exact hDK.symm ▸ hKA))
  exact fun n hn => (h n).mp (h₀ n hn)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteSubsets
