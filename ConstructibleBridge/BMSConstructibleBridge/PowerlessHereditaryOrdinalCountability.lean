import BMSConstructibleBridge.PowerlessRelativeOrdinalCutoff
import BMSConstructibleBridge.PowerlessRelativeClassInjectionEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationSection
import BMSConstructibleBridge.PowerlessHereditaryOmega

/-! # 类内可数序数与遗传域的精确对应

可数性使用真正的类内单射图。非空传递对象由其逆枚举和单点扩张
取得遗传包络；空对象单独处理。反向沿已有包络枚举取最小编号，
得到类内单射。全部数与函数均在原模型内，不使用 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOrdinalCountability

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
local notation "𝒞" => structure_l hℳ B hBase

include hBase in
/-- 最小编号逆图对原对象的全部成员给出类内单射，不仅对序数有效。 -/
theorem countable_of_hereditary_l (K : source_coding_l hℳ) {ω X : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hX : PowerlessHereditaryClass.member_l hℳ B X) :
    PowerlessRelativeOrdinalCutoff.countable_l B ω X := by
  obtain ⟨T, f, w, hT, hf, hXT, hTrans, hw, hMap, hOnto⟩ := hX
  have hwEq := SecondOrderOmega.unique_l hℳ hw hω
  subst w
  let A : type_l hℳ B := ⟨X, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hT hXT⟩
  let D : type_l hℳ B := ⟨T, hT⟩
  let G : type_l hℳ B := ⟨f, hf⟩
  let O : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  have hωClass := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr hω
  have hGX : ∀ y : type_l hℳ B, mem_l hℳ y.val A.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val O.val ∧ value_l (ℳ := 𝒞) G i y := by
    intro y hy
    obtain ⟨i, hi, hiy⟩ := hOnto y.val (hTrans X hXT y.val hy)
    let i' : type_l hℳ B := ⟨i, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property hi⟩
    exact ⟨i', hi, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G i' y).mpr hiy⟩
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassEnumerationSection.exists_l hωClass hGX
  refine ⟨R.val, R.property, (PowerlessRelativeClassFunctionAbsolute.map_l R A O).mp hR, ?_⟩
  intro x z i hxi hzi
  obtain ⟨hx, hi⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase R hxi
  obtain ⟨hz, _⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase R hzi
  let x' : type_l hℳ B := ⟨x, hx⟩
  let z' : type_l hℳ B := ⟨z, hz⟩
  let i' : type_l hℳ B := ⟨i, hi⟩
  have hix := ((hRead x' i').mp
    ((PowerlessRelativeClassFunctionAbsolute.value_l R x' i').mpr hxi)).2.2.1
  have hiz := ((hRead z' i').mp
    ((PowerlessRelativeClassFunctionAbsolute.value_l R z' i').mpr hzi)).2.2.1
  exact SecondOrderFunctionProperties.value_unique_l hℳ hMap
    ((PowerlessRelativeClassFunctionAbsolute.value_l G i' x').mp hix)
    ((PowerlessRelativeClassFunctionAbsolute.value_l G i' z').mp hiz)

include hBase in
/-- 传递类对象的类内单射可逆成满射；默认值仅用于非空分支。 -/
theorem hereditary_of_countable_l (K : source_coding_l hℳ) {ω X : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hTrans : ∀ x, mem_l hℳ x X → ∀ y, mem_l hℳ y x → mem_l hℳ y X)
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B ω X) :
    PowerlessHereditaryClass.member_l hℳ B X := by
  classical
  by_cases hNonempty : ∃ d, mem_l hℳ d X
  · obtain ⟨d, hd⟩ := hNonempty
    obtain ⟨f, hf, hMap, hInjective⟩ := hCount
    let A : type_l hℳ B := ⟨X, hX⟩
    let O : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
    let R : type_l hℳ B := ⟨f, hf⟩
    let d' : type_l hℳ B := ⟨d, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hX hd⟩
    have hR := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) R A O).mpr hMap
    have hInj (x y i : type_l hℳ B) (hx : value_l (ℳ := 𝒞) R x i)
        (hy : value_l (ℳ := 𝒞) R y i) : x = y := Subtype.ext (hInjective x.val y.val i.val
      ((PowerlessRelativeClassFunctionAbsolute.value_l R x i).mp hx)
      ((PowerlessRelativeClassFunctionAbsolute.value_l R y i).mp hy))
    obtain ⟨G, hG, hOnto, _⟩ := PowerlessRelativeClassInjectionEnumeration.exists_l hR hInj (d := d') hd
    exact (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) A).mpr
      (PowerlessHereditaryExtension.exists_l O A A G
        ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr hω)
        (fun x hx y hy => hTrans x.val hx y.val hy) (fun _ hx => hx) hG hOnto)
  · obtain ⟨e, he, heω⟩ := hω.1.1
    have hXe : X = e := SecondOrderQuotient.ext_l hℳ X e
      (fun x => ⟨fun hx => False.elim (hNonempty ⟨x, hx⟩), fun hx => False.elim (he x hx)⟩)
    exact hXe.symm ▸ PowerlessHereditaryClass.transitive_l hℳ
      (PowerlessHereditaryOmega.member_l hℳ hBase hω) heω

include hBase in
theorem ordinal_iff_l (K : source_coding_l hℳ) {ω α : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hα : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α) :
    PowerlessRelativeOrdinalCutoff.countable_l B ω α ↔ PowerlessHereditaryClass.member_l hℳ B α :=
  ⟨hereditary_of_countable_l (hBase := hBase) K hω
    (PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hα) hα.transitive,
    countable_of_hereditary_l (hBase := hBase) K hω⟩

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let α := .fvar (.there (.there .here))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.ordinal_m α) <|
        .iff (PowerlessRelativeOrdinalCutoff.countable_m B ω α) (PowerlessHereditaryClass.formula_m B α)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    SecondOrderOmegaSyntax.omega_l hℳ, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, PowerlessHereditaryClass.formula_l K, Term.eval]
  exact fun hBase hω hα => ordinal_iff_l (hBase := hBase) K hω hα

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms countable_of_hereditary_l
#print axioms hereditary_of_countable_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOrdinalCountability
