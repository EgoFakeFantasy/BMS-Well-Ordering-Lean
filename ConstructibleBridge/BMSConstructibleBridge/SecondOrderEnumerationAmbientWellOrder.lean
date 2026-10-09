import BMSConstructibleBridge.PowerlessRelativeClassWellOrderPullbackAmbient
import BMSConstructibleBridge.PowerlessRelativeClassOmegaAmbientOrder
import BMSConstructibleBridge.SecondOrderFiniteParameterEnvelope
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 给定内部自然数满射的环境良序

最小原像逆图是单射，故可拉回实际 ω 的环境良序。临时辅助类只用于
构造关系图；最小元条款量化所有环境子集，不暗加子集属于类的条件。
原核出口复用既有枚举模式的同一句子，但去掉辅助类相对化。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEnumerationAmbientWellOrder

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 参数均按实际给定图提升；没有对环境对象定义选码函数。 -/
theorem exists_l {ω G X : type_l hℳ}
    (hω : omega_l (ℳ := 𝒱) ω) (hG : map_l (ℳ := 𝒱) G ω X)
    (hOnto : ∀ y, mem_l hℳ y X → ∃ i, mem_l hℳ i ω ∧ value_l (ℳ := 𝒱) G i y) :
    ∃ R : type_l hℳ, wellOrder_l (ℳ := 𝒱) X R := by
  obtain ⟨B, hBase, hωB, hParameters⟩ := SecondOrderFiniteParameterEnvelope.exists_l hℳ ω [G, X]
  let ω' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨ω, PowerlessRelativeClassCorrespondence.base_l hℳ hBase hωB⟩
  let G' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨G, PowerlessRelativeClassCorrespondence.base_l hℳ hBase (hParameters G (by simp))⟩
  let X' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨X, PowerlessRelativeClassCorrespondence.base_l hℳ hBase (hParameters X (by simp))⟩
  let 𝒩 := PowerlessRelativeClassStructure.structure_l hℳ B hBase
  have hΩ : omega_l (ℳ := 𝒩) ω' :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr hω
  have hMap : map_l (ℳ := 𝒩) G' ω' X' :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G' ω' X').mpr hG
  have hSurj : ∀ y : PowerlessRelativeClassStructure.type_l hℳ B,
      mem_l hℳ y.val X'.val → ∃ i : PowerlessRelativeClassStructure.type_l hℳ B,
        mem_l hℳ i.val ω'.val ∧ value_l (ℳ := 𝒩) G' i y :=
    (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) G' ω' X').mpr hOnto
  obtain ⟨J, hJ, hRead⟩ := PowerlessRelativeClassEnumerationSection.exists_l hΩ hSurj
  have hInject : injective_l (ℳ := 𝒩) J := by
    intro x y i hxi hyi
    exact PowerlessRelativeClassFunctionProperties.value_unique_l hMap
      ((hRead x i).mp hxi).2.2.1 ((hRead y i).mp hyi).2.2.1
  obtain ⟨N, _, hN⟩ := PowerlessRelativeClassOmegaWellOrder.exists_l hΩ
  have hAmbient := PowerlessRelativeClassOmegaAmbientOrder.of_comparison_l hΩ hN
  obtain ⟨R, hR, _⟩ := PowerlessRelativeClassWellOrderPullbackAmbient.exists_l hJ hInject hAmbient
  exact ⟨R.val, hR⟩

def sentence_m : Sentence ℒ := PowerlessRelativeClassEnumerationWellOrder.sentence_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [PowerlessRelativeClassEnumerationWellOrder.schema_m,
    Formula.satisfies, omega_formula_l, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    Term.eval_weakenBound, Term.eval]
  exact fun hω hG hOnto => exists_l (hℳ := hℳ) hω hG hOnto

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEnumerationAmbientWellOrder
