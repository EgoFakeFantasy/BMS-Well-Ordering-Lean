import BMSConstructibleBridge.PowerlessRealSeedEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationWellOrder
import BMSConstructibleBridge.PowerlessRelativeClassInstantiation

/-! # 实数基集的实际类内良序

仅对明确基集 B=ω∪{R} 应用已有类内枚举，不假设任意传递 B 已可枚举。
所得良序关系属于相对并类，最小元条款量化该类中的子集。纯对象句
明确保留这一相对化范围；此处不宣称全层次规范良序或跨层相容性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRealSeedWellOrder

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} (K : source_coding_l hℳ)
    (R B : SecondOrderQuotient.type_l hℳ)
    (hSpec : ∀ x, mem_l hℳ x B ↔ mem_l hℳ x K.omega ∨ x = R)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    ∃ W : type_l hℳ B, wellOrder_l (ℳ := structure_l hℳ B hBase)
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ W := by
  let X : type_l hℳ B := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  obtain ⟨f, hf, hMap, hOnto⟩ := PowerlessRealSeedEnumeration.enumeration_l K R B hSpec hBase
  let F : type_l hℳ B := ⟨f, hf⟩
  have hωClass := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec
  have hMapClass := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F O X).mpr hMap
  have hOntoClass := (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) F O X).mpr hOnto
  obtain ⟨W, hW, _⟩ := PowerlessRelativeClassEnumerationWellOrder.exists_l hωClass hMapClass hOntoClass
  exact ⟨W, hW⟩

/-- 源良序模板头槽为载体 B，第二槽为关系 W。 -/
private def orderParameters_m : VariableSubstitution ℒ [.set, .set] [.set, .set] [.set, .set]
  | _, .here => .bvar (.there .here)
  | _, .there .here => .bvar .here

def schema_m : Formula ℒ [] [.set, .set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar .here)) <|
    .imp (ThirdOrderTheory.subset_m (.fvar (.there .here)) (.fvar .here)) <|
      .existsE .set <|
        .conj (PowerlessRealSeed.spec_m (.fvar .here) (.fvar (.there .here)) (.bvar .here)) <|
          .conj (PowerlessRelativeHierarchyDerives.transitive_m (.bvar .here)) <|
            .existsE .set <|
              .conj (PowerlessRelativeHierarchySyntax.class_m (.bvar (.there .here)) (.bvar .here))
                (PowerlessRelativeClassInstantiation.formula_m (.bvar (.there .here))
                  ThirdOrderTheory.wellOrder_template_m orderParameters_m)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ρ hω hR
  have hω' := (SecondOrderOmegaSyntax.omega_l hℳ ρ (.fvar .here)).mp hω
  have hR' := (ThirdOrderSemantics.subset_formula_l ρ (.fvar (.there .here)) (.fvar .here)).mp hR
  obtain ⟨B, hSpec, hBase⟩ := PowerlessRealSeed.exists_l hℳ
    (ρ.freeVal .here) (ρ.freeVal (.there .here)) hω' hR'
  have hEq := SecondOrderOmega.unique_l hℳ hω' K.omega_spec
  change ρ.freeVal .here = K.omega at hEq
  have hSpec' : ∀ x, mem_l hℳ x B ↔ mem_l hℳ x K.omega ∨ x = ρ.freeVal (.there .here) := by
    simpa only [hEq] using hSpec
  obtain ⟨W, hW⟩ := exists_l K (ρ.freeVal (.there .here)) B hSpec' hBase
  let X : type_l hℳ B := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let η : Env (structure_l hℳ B hBase) [] [.set, .set] := ((Env.empty).pushFree W).pushFree X
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [.set, .set] [.set, .set] :=
    (ρ.pushBound B).pushBound W.val
  refine ⟨B, ?_, ?_, W.val, ?_, ?_⟩
  · exact (PowerlessRealSeed.spec_formula_l (ρ.pushBound B) (.fvar .here) (.fvar (.there .here)) (.bvar .here)).mpr hSpec
  · exact (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ (ρ.pushBound B) (.bvar .here)).mpr hBase
  · exact (PowerlessRelativeHierarchySemantics.class_formula_l K ξ (.bvar (.there .here)) (.bvar .here)).mpr W.property
  · apply (PowerlessRelativeClassInstantiation.formula_l K ThirdOrderTheory.wellOrder_template_m
      η ξ (.bvar (.there .here)) orderParameters_m rfl ?_).mpr
    · exact (wellOrder_formula_l η).mpr hW
    · intro v
      cases v with
      | here => rfl
      | there v =>
          cases v with
          | here => rfl
          | there v => nomatch v

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRealSeedWellOrder
