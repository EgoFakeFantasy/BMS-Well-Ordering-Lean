import BMSConstructibleBridge.PowerlessTruthSign
import BMSConstructibleBridge.PowerlessOrdinalInduction
import BMSConstructibleBridge.PowerlessOmegaOrdinal

/-! # 真值记录可靠性的内部公式码归纳

归纳性质为原纯公式可表达的记录可靠性。局部规则可由不同固定层的
检查式给出，但必须真正证明其消费较小子码后保持可靠性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthInduction

open Logic FirstOrder ThirdOrderSemantics PowerlessTruthSign PowerlessTruthRecord

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

theorem sound_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e t H D : carrier_l ℳ} (hω : omega_l ω)
    (hD : ∀ p c f, entry_l D p c f → member_l ℳ c ω ∧
      ((∀ d, member_l ℳ d c → ∀ a g, entry_l D a d g → sign_l e t H a d g) →
        sign_l e t H p c f)) : valid_l e t H D := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 4 :=
    { bound := Fin.cases e (Fin.cases t (Fin.cases H (fun _ => D))), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    .forallE .set (.forallE .set (.imp
      (entry_m (.fvar (.there (.there (.there (.there .here)))))
        (.bvar (.there .here)) (.fvar .here) (.bvar .here))
      (sign_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.fvar .here) (.bvar .here))))
  have hφ (c : carrier_l ℳ) : φ.satisfies ((PowerlessComprehension.env_l η).pushFree c) ↔
      ∀ p f, entry_l D p c f → sign_l e t H p c f := by
    simp only [φ, Formula.satisfies, entry_formula_l, sign_formula_l]
    rfl
  have h := PowerlessOrdinalInduction.induction_l hℳ φ η (PowerlessOmegaOrdinal.ordinal_l hℳ hω)
    (fun c _ h => (hφ c).mpr (by
      intro p f hc
      exact (hD p c f hc).2 (fun d hd a g => (hφ d).mp (h d hd) a g)))
  exact fun p c f hc => (hφ c).mp (h c (hD p c f hc).1) p f hc

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthInduction
