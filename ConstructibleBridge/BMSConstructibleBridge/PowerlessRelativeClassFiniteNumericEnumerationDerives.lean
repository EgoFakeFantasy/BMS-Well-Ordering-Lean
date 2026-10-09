import BMSConstructibleBridge.PowerlessRelativeClassFiniteNumericEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationUnionDerives

/-! # 内部有限自然数序列可数的原 Z₂ 推导

对象句量化类内实际序列集及 ω 满射，正式出口是原理论的 Derives。
它不自动覆盖任意值域的有限序列，也不是最终 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteNumericEnumerationDerives

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

def sentence_m : Sentence ℒ := .forallE .set <|
  .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <| .existsE .set <| .conj
    (PowerlessFiniteSequencesSyntax.spec_m (.bvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
    (PowerlessRelativeClassEnumerationUnionDerives.conclusion_m (.bvar (.there .here)) (.bvar .here))

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y, SecondOrderQuotient.mem_l hℳ y x →
      SecondOrderQuotient.mem_l hℳ y B) :
    sentence_m.TrueIn (PowerlessRelativeClassStructure.structure_l hℳ B hBase) := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l,
    PowerlessRelativeClassEnumerationUnionDerives.conclusion_l, Term.eval]
  exact fun _ hω => PowerlessRelativeClassFiniteNumericEnumeration.exists_l (hBase := hBase) hω

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteNumericEnumerationDerives
