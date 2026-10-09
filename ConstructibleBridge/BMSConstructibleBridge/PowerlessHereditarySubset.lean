import BMSConstructibleBridge.PowerlessHereditaryExtension

/-! # 遗传类对相对类内子集封闭

子集 Y 必须先属于相对类；没有声称环境中任意子集都属于可构造类。
沿用 X 的类内可数传递包络，单点扩张加入 Y，给出实际原 Z₂ 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySubset

open Logic FirstOrder
open SecondOrderQuotient (mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B X Y : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : PowerlessHereditaryClass.member_l hℳ B X)
    (hY : PowerlessRelativeClassCorrespondence.member_l hℳ B Y)
    (hSubset : ∀ x, mem_l hℳ x Y → mem_l hℳ x X) :
    PowerlessHereditaryClass.member_l hℳ B Y := by
  let X' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨X, PowerlessHereditaryClass.contained_l hℳ hBase hX⟩
  let Y' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨Y, hY⟩
  obtain ⟨C, f, w, hXC, hTrans, hω, hMap, hOnto⟩ :=
    (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) X').mp hX
  apply (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) Y').mpr
  exact PowerlessHereditaryExtension.exists_l w Y' C f hω hTrans
    (fun x hx => hTrans X' hXC x (hSubset x.val hx)) hMap hOnto

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessHereditaryClass.formula_m (.fvar .here) (.fvar (.there .here))) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m (.fvar .here) (.fvar (.there (.there .here)))) <|
        .imp (ThirdOrderTheory.subset_m (.fvar (.there (.there .here))) (.fvar (.there .here)))
          (PowerlessHereditaryClass.formula_m (.fvar .here) (.fvar (.there (.there .here))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hTrans hX hY hSubset
  exact (PowerlessHereditaryClass.formula_l K η _ _).mpr <|
    member_l hℳ
      ((PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η _).mp hTrans)
      ((PowerlessHereditaryClass.formula_l K η _ _).mp hX)
      ((PowerlessRelativeHierarchySemantics.class_formula_l K η _ _).mp hY)
      ((ThirdOrderSemantics.subset_formula_l η _ _).mp hSubset)

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms member_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySubset
