import BMSConstructibleBridge.PowerlessRealSeedEnumeration
import BMSConstructibleBridge.PowerlessHereditaryExtension

/-! # 同一遗传类同时包含实数参数、ω 和精确基集

用已验证的单点包络扩张分别处理 ω ⊆ B 与 B ⊆ B。基集作为对象进入
遗传类后，其成员 R 由遗传传递性进入。对象存在句在原 Z₂ 中可推导；
遗传类满足完整源公理仍是后续义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealBasis

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem coverage_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (ω R : SecondOrderQuotient.type_l hℳ) (hω : SecondOrderOmega.omega_l hℳ ω)
    (hR : ∀ x, mem_l hℳ x R → mem_l hℳ x ω) : ∃ B,
      (∀ x, mem_l hℳ x B ↔ mem_l hℳ x ω ∨ x = R) ∧
        PowerlessHereditaryClass.member_l hℳ B R ∧ PowerlessHereditaryClass.member_l hℳ B ω ∧
          PowerlessHereditaryClass.member_l hℳ B B := by
  obtain ⟨B, hSpec, hBase⟩ := PowerlessRealSeed.exists_l hℳ ω R hω hR
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hSpec' : ∀ x, mem_l hℳ x B ↔ mem_l hℳ x K.omega ∨ x = R := by
    simpa only [hωEq] using hSpec
  obtain ⟨f, hf, hMap, hOnto⟩ := PowerlessRealSeedEnumeration.enumeration_l K R B hSpec' hBase
  let C : type_l hℳ B := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let F : type_l hℳ B := ⟨f, hf⟩
  have hωClass := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec
  have hTransClass := (PowerlessHereditaryClassInternals.transitive_l (hBase := hBase) C).mpr hBase
  have hMapClass := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F O C).mpr hMap
  have hOntoClass := (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) F O C).mpr hOnto
  have hB : PowerlessHereditaryClass.member_l hℳ B B :=
    (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) C).mpr
      (PowerlessHereditaryExtension.exists_l O C C F hωClass hTransClass (fun _ hx => hx) hMapClass hOntoClass)
  have hO : PowerlessHereditaryClass.member_l hℳ B K.omega :=
    (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) O).mpr
      (PowerlessHereditaryExtension.exists_l O O C F hωClass hTransClass
        (fun x hx => (hSpec' x.val).mpr (Or.inl hx)) hMapClass hOntoClass)
  refine ⟨B, hSpec, PowerlessHereditaryClass.transitive_l hℳ hB ((hSpec R).mpr (Or.inr rfl)), ?_, hB⟩
  simpa only [hωEq] using hO

def schema_m : Formula ℒ [] [.set, .set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar .here)) <|
    .imp (ThirdOrderTheory.subset_m (.fvar (.there .here)) (.fvar .here)) <|
      .existsE .set <| .conj (PowerlessRealSeed.spec_m (.fvar .here) (.fvar (.there .here)) (.bvar .here)) <|
        .conj (PowerlessHereditaryClass.formula_m (.bvar .here) (.fvar (.there .here))) <|
          .conj (PowerlessHereditaryClass.formula_m (.bvar .here) (.fvar .here))
            (PowerlessHereditaryClass.formula_m (.bvar .here) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω hR
  obtain ⟨B, hSpec, hHR, hHω, hHB⟩ := coverage_l hℳ (η.freeVal .here) (η.freeVal (.there .here))
    ((SecondOrderOmegaSyntax.omega_l hℳ η (.fvar .here)).mp hω)
    ((ThirdOrderSemantics.subset_formula_l η (.fvar (.there .here)) (.fvar .here)).mp hR)
  exact ⟨B, (PowerlessRealSeed.spec_formula_l (η.pushBound B) (.fvar .here) (.fvar (.there .here)) (.bvar .here)).mpr hSpec,
    (PowerlessHereditaryClass.formula_l K (η.pushBound B) (.bvar .here) (.fvar (.there .here))).mpr hHR,
    (PowerlessHereditaryClass.formula_l K (η.pushBound B) (.bvar .here) (.fvar .here)).mpr hHω,
    (PowerlessHereditaryClass.formula_l K (η.pushBound B) (.bvar .here) (.bvar .here)).mpr hHB⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms coverage_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealBasis
