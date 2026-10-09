import BMSConstructibleBridge.SecondOrderSubstitution

/-! # 完整二阶算术语言在参数全称闭包下保持 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLanguageClosure

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

theorem forall_top_m {Γ Δ : SortContext signature_m} (s : sort_m)
    (φ : Formula signature_m Γ (s :: Δ)) :
    language_m (φ.forallFreeTop s) = language_m φ := by
  apply SecondOrderSubstitution.form_subst_m φ
  · intro t v
    rfl
  · intro t v
    cases v <;> rfl

theorem forall_close_m {Δ : SortContext signature_m} (φ : Formula signature_m [] Δ) :
    language_m (Metatheory.Formula.forall_close φ) = language_m φ := by
  induction Δ with
  | nil => rfl
  | cons s Δ ih =>
      exact (ih (φ.forallFreeTop s)).trans (forall_top_m s φ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLanguageClosure
