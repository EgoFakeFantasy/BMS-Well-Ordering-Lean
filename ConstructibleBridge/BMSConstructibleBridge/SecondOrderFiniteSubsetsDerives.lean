import BMSConstructibleBridge.PowerlessFiniteSubsets
import BMSConstructibleBridge.SecondOrderFiniteClosureDerives

/-!
# 有限子集集合的原 Z₂ 对象推导

使用已证明的有限闭包及分离，取得精确有限子集集合闭句的原图翻译。
不假设一般幂集、完整 Collection，也不把语义辅助结论当作对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteSubsetsDerives

open Logic FirstOrder PowerlessFiniteSubsets

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (ω : SecondOrderQuotient.type_l hℳ) (hω : SecondOrderOmega.omega_l hℳ ω)
    (x : SecondOrderQuotient.type_l hℳ) :
    ∃ p, spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω x p := by
  obtain ⟨c, hc⟩ := SecondOrderFiniteClosureDerives.exists_l hℳ ω hω x
  exact PowerlessFiniteSubsets.exists_l (SecondOrderWeakSetTheory.models_l hℳ) ω x c hc.1 hc.2.1

theorem sentence_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) ↔
      ∀ ω : SecondOrderQuotient.type_l hℳ, SecondOrderOmega.omega_l hℳ ω →
        ∀ x, ∃ p, spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω x p := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies,
    SecondOrderOmegaSyntax.omega_l, spec_formula_l, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) :=
  (sentence_formula_l hℳ).mpr (exists_l hℳ)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteSubsetsDerives
