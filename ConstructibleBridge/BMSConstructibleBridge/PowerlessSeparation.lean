import BMSConstructibleBridge.PowerlessTheory
import YesMetaZFC.SetTheory.Separation

/-! # 无幂集核心中的完整分离模式 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSeparation

open Logic FirstOrder
open SetTheory.Definitional.Project

set_option autoImplicit false

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : FirstOrder.Theory.Models ℳ PowerlessTheory.theory_m) {n : Nat}
    (φ : UnarySchema n) (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) n)
    (A : (FirstOrderSemantics.reduct ℳ).Domain) :
    ∃ B, ∀ x, (FirstOrderSemantics.reduct ℳ).mem x B ↔
      (FirstOrderSemantics.reduct ℳ).mem x A ∧
        SetTheory.Definitional.Project.Formula.satisfies (η.push x) φ.body := by
  have h₀ := (PowerlessTheory.project_l hℳ).2 _ (PowerlessTheory.axiom_m.separation φ) η.free
  have h₁ : SetTheory.Definitional.Project.Formula.satisfies η
      (SetTheory.Axioms.Schema.separationCore φ) := by
    have h₂ := (SetTheory.Definitional.Project.Formula.satisfies_forallClosure_iff
      η.free (SetTheory.Axioms.Schema.separationCore φ)).mp h₀
    exact h₂ η.bound
  exact (SetTheory.Axioms.Schema.separation_sat_iff_d η φ).mp h₁ A

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSeparation
