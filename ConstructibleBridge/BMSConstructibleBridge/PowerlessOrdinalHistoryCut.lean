import BMSConstructibleBridge.PowerlessOrdinalRecursion

/-! # 任意集合图在隶属初段上的实际分离，不限于自然数前史 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalHistoryCut

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (f a : carrier_l ℳ) :
    ∃ H, PowerlessOrdinalRecursion.history_l H f a := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => a, free := fun _ => f }
  let φ : Formula ℒ [] [.set, .set] :=
    .existsE .set (.existsE .set (.conj
      (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.fvar (.there .here)))))
  have h (p : carrier_l ℳ) : φ.satisfies ((PowerlessComprehension.env_l η).pushFree p) ↔
      ∃ x y, ordered_l x y p ∧ member_l ℳ x a := by
    simp only [φ, Formula.satisfies, ordered_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  obtain ⟨H, hH⟩ := PowerlessComprehension.separation_l hℳ φ η f
  refine ⟨H, fun p => (hH p).trans ((and_congr Iff.rfl (h p)).trans ?_)⟩
  constructor
  · rintro ⟨hp, x, y, h₀, hx⟩
    exact ⟨x, y, h₀, hx, p, hp, h₀⟩
  · rintro ⟨x, y, h₀, hx, q, hq, h₁⟩
    have h₂ := PowerlessBasic.ordered_unique_l hℳ h₀ h₁
    exact ⟨h₂.symm ▸ hq, x, y, h₀, hx⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {H K f a : carrier_l ℳ} (hH : PowerlessOrdinalRecursion.history_l H f a)
    (hK : PowerlessOrdinalRecursion.history_l K f a) : H = K :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members H K (fun p => (hH p).trans (hK p).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalHistoryCut
