import BMSConstructibleBridge.PowerlessHereditaryOrdinalCountability
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationSectionDerives

/-! # 实际类内满射的可数性与截断反证

以最小内部编号取得逆图，证明任意类对象的类内 ω 满射给出类内单射。
首个类内不可数序数因而没有这种满射。全部图须实际属于相对类，
不以环境中的满射代替，也不从 Type 中抽取编号或逆函数。
两项闭句均回到原 Z₂ 推导核；尚未证明秩族的界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOntoCountability

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

include hBase in
theorem countable_l (K : source_coding_l hℳ) {ω X f : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hf : PowerlessRelativeClassCorrespondence.member_l hℳ B f)
    (hMap : map_l (ℳ := 𝒱) f ω X)
    (hOnto : ∀ y, mem_l hℳ y X → ∃ i, mem_l hℳ i ω ∧ value_l (ℳ := 𝒱) f i y) :
    PowerlessRelativeOrdinalCutoff.countable_l B ω X := by
  let A : type_l hℳ B := ⟨X, hX⟩
  let G : type_l hℳ B := ⟨f, hf⟩
  let O : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  have hωClass := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr hω
  have hOntoClass : ∀ y : type_l hℳ B, mem_l hℳ y.val A.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val O.val ∧ value_l (ℳ := ClassModel) G i y := by
    intro y hy
    obtain ⟨i, hi, hiy⟩ := hOnto y.val hy
    let i' : type_l hℳ B := ⟨i, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hi⟩
    exact ⟨i', hi, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G i' y).mpr hiy⟩
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassEnumerationSection.exists_l hωClass hOntoClass
  refine ⟨R.val, R.property, (PowerlessRelativeClassFunctionAbsolute.map_l R A O).mp hR, ?_⟩
  intro x z i hxi hzi
  obtain ⟨hx, hi⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase R hxi
  obtain ⟨hz, _⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase R hzi
  let x' : type_l hℳ B := ⟨x, hx⟩
  let z' : type_l hℳ B := ⟨z, hz⟩
  let i' : type_l hℳ B := ⟨i, hi⟩
  have hix := ((hRead x' i').mp ((PowerlessRelativeClassFunctionAbsolute.value_l R x' i').mpr hxi)).2.2.1
  have hiz := ((hRead z' i').mp ((PowerlessRelativeClassFunctionAbsolute.value_l R z' i').mpr hzi)).2.2.1
  exact SecondOrderFunctionProperties.value_unique_l hℳ hMap
    ((PowerlessRelativeClassFunctionAbsolute.value_l G i' x').mp hix)
    ((PowerlessRelativeClassFunctionAbsolute.value_l G i' z').mp hiz)

include hBase in
theorem cutoff_l (K : source_coding_l hℳ) {ω Ω f : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hf : PowerlessRelativeClassCorrespondence.member_l hℳ B f)
    (hMap : map_l (ℳ := 𝒱) f ω Ω)
    (hOnto : ∀ y, mem_l hℳ y Ω → ∃ i, mem_l hℳ i ω ∧ value_l (ℳ := 𝒱) f i y) : False :=
  hΩ.2.1 (countable_l (hBase := hBase) K hω
    (PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hΩ.1) hf hMap hOnto)

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let f : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let X := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let B := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B X) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B f) <|
          .imp (SecondOrderObjectSyntax.map_m f ω X) <|
            .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m f ω X)
              (PowerlessRelativeOrdinalCutoff.countable_m B ω X)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

def cutoff_schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let f : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let Ω := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let B := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .neg (.conj (PowerlessRelativeHierarchySyntax.class_m B f) <|
          .conj (SecondOrderObjectSyntax.map_m f ω Ω)
            (PowerlessRelativeClassEnumerationSectionDerives.onto_m f ω Ω))

def cutoff_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close cutoff_schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    map_formula_l, PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, Term.eval]
  intro η hBase hω hX hf hMap hOnto
  exact countable_l (hBase := hBase) K hω hX hf hMap hOnto

theorem cutoff_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    cutoff_sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [cutoff_schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l, Term.eval]
  intro η hBase hω hΩ h
  exact cutoff_l (hBase := hBase) K hω hΩ h.1 h.2.1 h.2.2

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

theorem cutoff_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m cutoff_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => cutoff_models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOntoCountability
