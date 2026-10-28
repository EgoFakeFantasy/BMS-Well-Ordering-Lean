import BMSConstructibleBridge.SecondOrderMemberEnumeration
import BMSConstructibleBridge.SecondOrderAxioms
import BMSConstructibleBridge.SecondOrderObjectSyntax

/-!
# 非空集合由内部 ω 满射的对象定理

满射为实际集合函数；定义域为公式指定的最小归纳对象，覆盖全部内部数。
不添加选择公理、幂集或 Collection。空母集不满足前提，其 Def 分支需另行处理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberEnumerationDerives

open Logic FirstOrder SecondOrderObjectSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def sentence_m : Sentence ℒ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <|
    .forallE .set <| .imp
      (.existsE .set (member_m (.bvar .here) (.bvar (.there .here)))) <|
      .existsE .set <| .conj
        (map_m (.bvar .here) (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
        .forallE .set <| .imp (member_m (.bvar .here) (.bvar (.there (.there .here)))) <|
          .existsE .set <| .conj
            (member_m (.bvar .here) (.bvar (.there (.there (.there (.there .here))))))
            (value_m (.bvar (.there (.there .here))) (.bvar .here) (.bvar (.there .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (ω X : SecondOrderQuotient.type_l hℳ) (hω : SecondOrderOmega.omega_l hℳ ω)
    (hX : ∃ z, SecondOrderQuotient.mem_l hℳ z X) :
    ∃ f, SecondOrderFunctionObjects.map_l hℳ f ω X ∧
      ∀ y, SecondOrderQuotient.mem_l hℳ y X → ∃ x,
        SecondOrderQuotient.mem_l hℳ x ω ∧ SecondOrderFunctionObjects.value_l hℳ f x y := by
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωC := SecondOrderOmega.unique_l hℳ hω C.omega_spec
  rw [hωC]
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ X
  obtain ⟨z, hz⟩ := hX
  obtain ⟨Z, rfl⟩ := SecondOrderQuotient.surj_l hℳ z
  obtain ⟨a, ha, _⟩ := hz
  obtain ⟨f, hf, _, hCover⟩ := SecondOrderMemberEnumeration.exists_l C A a ha
  exact ⟨f, hf, hCover⟩

theorem sentence_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) ↔
      ∀ ω, SecondOrderOmega.omega_l hℳ ω → ∀ X,
        (∃ z, SecondOrderQuotient.mem_l hℳ z X) → ∃ f,
          SecondOrderFunctionObjects.map_l hℳ f ω X ∧
            ∀ y, SecondOrderQuotient.mem_l hℳ y X → ∃ x,
              SecondOrderQuotient.mem_l hℳ x ω ∧ SecondOrderFunctionObjects.value_l hℳ f x y := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    SecondOrderObjectSyntax.member_m, SecondOrderObjectSyntax.map_l,
    ThirdOrderSemantics.value_formula_l, Arguments.eval, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) :=
  (sentence_formula_l hℳ).mpr (fun ω hω X hX => exists_l hℳ ω X hω hX)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberEnumerationDerives
