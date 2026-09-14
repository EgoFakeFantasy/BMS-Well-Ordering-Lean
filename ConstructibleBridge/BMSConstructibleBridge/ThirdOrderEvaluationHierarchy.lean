import BMSConstructibleBridge.ThirdOrderHierarchyStep
import BMSConstructibleBridge.PowerlessHierarchyStructure
import BMSConstructibleBridge.PowerlessOrdinalHistory

/-!
# 内部可数序数级的累计层次可数

归纳性质是实际纯公式：“若指标可数，则其层次值可数”。前史具有精确
指标域，子指标可数从序数包含关系传递；不假定外部可数或外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderEvaluationHierarchy

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessEvaluationHierarchy

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem countable_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α : carrier_l ℳ} (hω : omega_l ω) (hα : PowerlessOrdinal.ordinal_l α)
    (hf : hierarchy_l ω e T t₁ t₂ t₃ f α) :
    ∀ a A, value_l f a A → ThirdOrderOmegaOne.countable_l ω a → ThirdOrderOmegaOne.countable_l ω A := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hf₀ := hf
  obtain ⟨R, hF, hS⟩ := hf₀
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => ω), free := fun _ => α }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .imp (countable_m (.fvar (.there (.there .here))) (.fvar .here))
      (.forallE .set (.imp
        (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
        (countable_m (.fvar (.there (.there .here))) (.bvar .here))))
  have h : ∀ a, φ.satisfies ((PowerlessComprehension.env_l η).pushFree a) ↔
      (ThirdOrderOmegaOne.countable_l ω a → ∀ A, value_l f a A → ThirdOrderOmegaOne.countable_l ω A) := by
    intro a
    simp only [φ, Formula.satisfies, countable_formula_l, value_formula_l]
    rfl
  have h₁ := PowerlessOrdinalInduction.induction_l h₀ φ η hα (fun a ha h₂ => by
    apply (h a).mpr
    intro ha₀ A hA
    obtain ⟨H, hH, hY⟩ := hS a A hA
    apply ThirdOrderHierarchyStep.countable_l hℳ hω (PowerlessOrdinalHistory.map_l h₀ hα hF ha hH) ha₀ ?_ hY
    intro b B hB
    have h₃ := (PowerlessEvaluationHistory.value_l h₀ hH).mp hB
    have hb : ThirdOrderOmegaOne.countable_l ω b := ThirdOrderCountableImage.subset_l h₀ ha₀
      (fun x hx => PowerlessOrdinal.transitive_l (PowerlessOrdinal.mem_l hα ha) b x h₃.2 hx)
    exact (h b).mp (h₂ b h₃.2) hb B h₃.1)
  intro a A hA ha
  exact (h a).mp (h₁ a (PowerlessFunction.value_mem_l h₀ hF hA).1) ha A hA

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderEvaluationHierarchy
