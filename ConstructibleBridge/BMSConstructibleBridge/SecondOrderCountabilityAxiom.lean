import BMSConstructibleBridge.SecondOrderCountability
import BMSConstructibleBridge.SecondOrderOmegaSyntax
import BMSConstructibleBridge.SecondOrderAxioms

/-!
# 可数性公理的二阶对象推导

完整源句子明确量化最小归纳对象与单射集合函数，没有 ω 或有序对的扩展
函数符号。证明覆盖任意非标准二阶模型，而非仅宿主可数图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCountabilityAxiom

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderObjectSyntax

set_option autoImplicit false

universe u

/-- 每个集合可单射到最小归纳对象，单射本身也是集合。 -/
def formula_m : Sentence ℒ :=
  .forallE .set <| .existsE .set <| .existsE .set <|
    .conj (SecondOrderOmegaSyntax.omega_m (.bvar (.there .here)))
      (.conj (map_m (.bvar .here) (.bvar (.there (.there .here))) (.bvar (.there .here)))
        (injective_m (.bvar .here)))

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) :
    formula_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  simp only [formula_m, Formula.TrueIn, Formula.satisfies,
    SecondOrderOmegaSyntax.omega_l, SecondOrderObjectSyntax.map_l, SecondOrderObjectSyntax.injective_l]
  change ∀ a : SecondOrderQuotient.type_l hℳ, ∃ o f,
    SecondOrderOmega.omega_l hℳ o ∧ SecondOrderFunctionObjects.map_l hℳ f a o ∧
      SecondOrderFunctionObjects.injective_l hℳ f
  obtain ⟨R, hR⟩ := SecondOrderNaturalGraph.relation_exists_l hℳ
  obtain ⟨Ω, hΩ⟩ := SecondOrderNaturalNumbers.range_l hℳ R hR
  intro a
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨f, hf, h⟩ := SecondOrderCountability.exists_l hℳ R hR Ω A hΩ
  exact ⟨SecondOrderQuotient.mk_l hℳ Ω, f, SecondOrderOmega.range_l hℳ R hR Ω hΩ, hf, h⟩

theorem derives_m : Derives theory_m [] (GraphTranslation.form_m formula_m) :=
  SecondOrderAxioms.interpretation_m formula_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCountabilityAxiom
