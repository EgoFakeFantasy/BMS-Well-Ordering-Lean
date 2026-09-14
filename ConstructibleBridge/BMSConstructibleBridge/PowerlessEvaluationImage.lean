import BMSConstructibleBridge.PowerlessEvaluationOperator

/-! # 子集算子的实际像函数与精确值域 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationImage

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def image_l (ω e T t₁ t₂ t₃ R E : carrier_l ℳ) : Prop :=
  ∀ D, member_l ℳ D E ↔ ∃ B, member_l ℳ B R ∧ PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) (e T t₁ t₂ t₃ R : carrier_l ℳ) :
    ∃ g E, map_l g R E ∧ (∀ D, member_l ℳ D E → ∃ B, value_l g B D) ∧ image_l ω e T t₁ t₂ t₃ R E := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 6 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁ (Fin.cases t₂ (fun _ => t₃))))),
      free := fun _ => R }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    PowerlessEvaluationOperator.operator_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there .here)) (.fvar .here)
  have h : ∀ B D, φ.satisfies (((PowerlessComprehension.env_l η).pushFree B).pushFree D) ↔
      PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D := by
    intro B D
    exact PowerlessEvaluationOperator.operator_formula_l hℳ _ _ _ _ _ _ _ _ _
  obtain ⟨g, E, hg, hE, h₀⟩ := PowerlessMapping.exists_l hℳ φ η R
    (fun B _ => by
      obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ B
      exact ⟨D, (h B D).mpr hD⟩)
    (fun B _ D E hD hE => PowerlessEvaluationOperator.unique_l hℳ hω
      ((h B D).mp hD) ((h B E).mp hE))
  refine ⟨g, E, hg, ?_, ?_⟩
  · intro D hD
    obtain ⟨B, hB, hD⟩ := (hE D).mp hD
    exact ⟨B, (h₀ B hB D).mpr hD⟩
  · intro D
    exact (hE D).trans (exists_congr fun B => and_congr Iff.rfl (h B D))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationImage
