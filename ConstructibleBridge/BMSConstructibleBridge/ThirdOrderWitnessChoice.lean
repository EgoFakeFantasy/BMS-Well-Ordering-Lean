import BMSConstructibleBridge.PowerlessWitnessChoice
import BMSConstructibleBridge.ThirdOrderSelection
import BMSConstructibleBridge.PowerlessProduct

/-!
# 请求集合上的实际见证选择图

在内部积 (ω×ω)×S 上应用纯公式选择；值域收缩到 U。
选择结果是模型中的集合函数，而非宿主层对各请求分别作选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderWitnessChoice

open Logic FirstOrder ThirdOrderSemantics PowerlessWitnessChoice

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω U F d I S P : carrier_l ℳ} (hd : ThirdOrderSemantics.member_l ℳ d U)
    (hI : PowerlessProduct.product_l ω ω I) (hP : PowerlessProduct.product_l I S P) :
    ∃ W, map_l W P U ∧ ∀ p a, value_l W p a → choice_l ω U F d p a := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 4 :=
    { bound := Fin.cases ω (Fin.cases U (Fin.cases F (fun _ => d))), free := fun _ => U }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    choice_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there .here)) (.fvar .here)
  have h : ∀ p a, φ.satisfies (((PowerlessComprehension.env_l η).pushFree p).pushFree a) ↔
      choice_l ω U F d p a := fun p a => choice_formula_l _ _ _ _ _ _ _
  obtain ⟨W, D, hW, h₁⟩ := ThirdOrderSelection.exists_l hℳ φ η P (fun p hp => by
    obtain ⟨q, hq, f, _, hp⟩ := (hP p).mp hp
    obtain ⟨i, _, b, _, hq⟩ := (hI q).mp hq
    obtain ⟨a, ha⟩ := PowerlessWitnessChoice.exists_l (ω := ω) (U := U) (F := F) (d := d) hp hq
    exact ⟨a, (h p a).mpr ha⟩)
  have h₂ : ∀ p a, value_l W p a → choice_l ω U F d p a := fun p a ha => (h p a).mp (h₁ p a ha)
  exact ⟨W, PowerlessFunction.range_l h₀ hW (fun p a ha => PowerlessWitnessChoice.member_l hd (h₂ p a ha)), h₂⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderWitnessChoice
