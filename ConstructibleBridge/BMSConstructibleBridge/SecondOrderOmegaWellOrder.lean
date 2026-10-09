import BMSConstructibleBridge.PowerlessRelativeClassOmegaAmbientOrder

/-! # 原商 ω 隶属序图的环境良序对象推导

结论中的 wellOrder 保留全部环境子集量词，句子不整体相对化到类。
利用空基点只构造同一关系图，再单独证明其环境最小元条款。
最终回传原 Z₂ 推导核；这给后续环境良序传输的初始层，不是 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmegaWellOrder

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {ω : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) :
    ∃ R : SecondOrderQuotient.type_l hℳ,
      wellOrder_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω R := by
  obtain ⟨B, hEmpty⟩ := SecondOrderQuotient.empty_l hℳ
  have hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
      ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B :=
    fun x hx => (hEmpty x hx).elim
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)
  let ω' : type_l hℳ B := ⟨ω, hClass⟩
  have hΩ := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr hω
  obtain ⟨R, _, hRead⟩ := PowerlessRelativeClassOmegaWellOrder.exists_l hΩ
  exact ⟨R.val, PowerlessRelativeClassOmegaAmbientOrder.of_comparison_l hΩ hRead⟩

def schema_m : Formula ℒ [] [.set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar .here)) <|
    .existsE .set (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (.fvar .here) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, Term.eval]
  exact fun hω => exists_l hℳ hω

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmegaWellOrder
