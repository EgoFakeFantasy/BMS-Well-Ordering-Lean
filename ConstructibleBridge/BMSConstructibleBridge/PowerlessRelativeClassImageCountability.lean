import BMSConstructibleBridge.PowerlessRelativeClassOntoCountability
import BMSConstructibleBridge.PowerlessRelativeClassInjectionEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassFunctionComposition

/-! # 相对类内可数对象的实际满射像

把已有单射图逆成带默认值的内部枚举，与实际满射复合，再取最小编号。
所有图均实际属于 Class；空定义域时由满射规格证明像也空，不选默认值。
结论是原可数性对象公式，既不以环境枚举替代类内图，也不预设 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassImageCountability

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase

include hBase in
theorem countable_l (K : source_coding_l hℳ) {ω X Y f : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hY : PowerlessRelativeClassCorrespondence.member_l hℳ B Y)
    (hf : PowerlessRelativeClassCorrespondence.member_l hℳ B f)
    (hMap : map_l (ℳ := 𝒱) f X Y)
    (hOnto : ∀ y, mem_l hℳ y Y → ∃ x, mem_l hℳ x X ∧ value_l (ℳ := 𝒱) f x y)
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B ω X) :
    PowerlessRelativeOrdinalCutoff.countable_l B ω Y := by
  classical
  by_cases h : ∃ d, mem_l hℳ d X
  · obtain ⟨d, hd⟩ := h
    obtain ⟨r, hr, hR, hInjective⟩ := hCount
    let A : type_l hℳ B := ⟨X, hX⟩
    let D : type_l hℳ B := ⟨Y, hY⟩
    let F : type_l hℳ B := ⟨f, hf⟩
    let R : type_l hℳ B := ⟨r, hr⟩
    let O : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
    let a : type_l hℳ B := ⟨d,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hX hd⟩
    have hRClass := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) R A O).mpr hR
    have hInjectiveClass : ∀ x z i : type_l hℳ B, value_l (ℳ := 𝒩) R x i →
        value_l (ℳ := 𝒩) R z i → x = z := by
      intro x z i hxi hzi
      exact Subtype.ext (hInjective x.val z.val i.val
        ((PowerlessRelativeClassFunctionAbsolute.value_l R x i).mp hxi)
        ((PowerlessRelativeClassFunctionAbsolute.value_l R z i).mp hzi))
    obtain ⟨E, hE, hEOnto, _⟩ := PowerlessRelativeClassInjectionEnumeration.exists_l
      hRClass hInjectiveClass (show mem_l hℳ a.val A.val from hd)
    have hFClass := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F A D).mpr hMap
    have hFOnto := (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) F A D).mpr hOnto
    obtain ⟨G, hG, hRead⟩ := PowerlessRelativeClassFunctionComposition.exists_l hE hFClass
    have hGOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val D.val →
        ∃ i : type_l hℳ B, mem_l hℳ i.val O.val ∧ value_l (ℳ := 𝒩) G i y := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := hFOnto y hy
      obtain ⟨i, hi, hix⟩ := hEOnto x hx
      exact ⟨i, hi, (hRead i y).mpr ⟨hi, hy, x, hx, hix, hxy⟩⟩
    exact PowerlessRelativeClassOntoCountability.countable_l (hBase := hBase) K hω
      hY G.property ((PowerlessRelativeClassFunctionAbsolute.map_l G O D).mp hG)
      ((PowerlessRelativeClassFunctionAbsolute.onto_l G O D).mp hGOnto)
  · have hEq : X = Y := by
      apply SecondOrderQuotient.ext_l hℳ
      intro x
      constructor
      · intro hx; exact False.elim (h ⟨x, hx⟩)
      · intro hy
        obtain ⟨z, hz, _⟩ := hOnto x hy
        exact False.elim (h ⟨z, hz⟩)
    simpa only [← hEq] using hCount

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let f : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let Y := .fvar (.there .here)
  let X := .fvar (.there (.there .here))
  let ω := .fvar (.there (.there (.there .here)))
  let B := .fvar (.there (.there (.there (.there .here))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B X) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B Y) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B f) <|
            .imp (SecondOrderObjectSyntax.map_m f X Y) <|
              .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m f X Y) <|
                .imp (PowerlessRelativeOrdinalCutoff.countable_m B ω X)
                  (PowerlessRelativeOrdinalCutoff.countable_m B ω Y)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    map_formula_l, PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, Term.eval]
  intro η hBase hω hX hY hf hMap hOnto hCount
  exact countable_l (hBase := hBase) K hω hX hY hf hMap hOnto hCount

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassImageCountability
