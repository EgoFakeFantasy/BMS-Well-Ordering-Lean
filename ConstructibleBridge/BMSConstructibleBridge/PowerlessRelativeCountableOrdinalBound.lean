import BMSConstructibleBridge.PowerlessRelativeClassFunctionRestriction
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage
import BMSConstructibleBridge.PowerlessRelativeOrdinalCutoff
import BMSConstructibleBridge.SecondOrderOmegaOrdinal

/-! # 类内可数序数严格低于首不可数截断

对象语言为纯隶属 ℒ，背景为原 Z₂。若 γ 不低于首不可数 Ω，就将
γ 的实际类内单射限制到 Ω，得到矛盾。不假设环境枚举属于类，也不
假设截断结构已经满足 Collection。闭句通过原解释回到正式推导核。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCountableOrdinalBound

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
local notation "𝒩" => structure_l hℳ B hBase
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

include hBase in
theorem below_l (K : source_coding_l hℳ) {ω γ Ω : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hγ : Ordinal γ)
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B ω γ)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω) : mem_l hℳ γ Ω := by
  rcases SecondOrderOrdinalComparison.compare_l hℳ hγ hΩ.1 with hEq | hBelow | hAbove
  · exact (hΩ.2.1 (hEq ▸ hCount)).elim
  · exact hBelow
  · obtain ⟨f, hfClass, hf, hInj⟩ := hCount
    let A : type_l hℳ B := ⟨γ, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hγ⟩
    let C : type_l hℳ B := ⟨Ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hΩ.1⟩
    let O : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
    let F : type_l hℳ B := ⟨f, hfClass⟩
    have hF : map_l (ℳ := 𝒩) F A O :=
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F A O).mpr hf
    have hCA : subset_l (ℳ := 𝒩) C A := fun x hx => hγ.transitive Ω hAbove x.val hx
    obtain ⟨G, hG, hRead⟩ := PowerlessRelativeClassFunctionRestriction.exists_l hF hCA
    have hGInj : injective_l (ℳ := 𝒱) G.val := by
      intro x z i hxi hzi
      obtain ⟨hx, hi⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G hxi
      obtain ⟨hz, _⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G hzi
      let x' : type_l hℳ B := ⟨x, hx⟩
      let z' : type_l hℳ B := ⟨z, hz⟩
      let i' : type_l hℳ B := ⟨i, hi⟩
      have hFx := ((hRead x' i').mp
        ((PowerlessRelativeClassFunctionAbsolute.value_l G x' i').mpr hxi)).2
      have hFz := ((hRead z' i').mp
        ((PowerlessRelativeClassFunctionAbsolute.value_l G z' i').mpr hzi)).2
      exact hInj x z i ((PowerlessRelativeClassFunctionAbsolute.value_l F x' i').mp hFx)
        ((PowerlessRelativeClassFunctionAbsolute.value_l F z' i').mp hFz)
    exact (hΩ.2.1 ⟨G.val, G.property,
      (PowerlessRelativeClassFunctionAbsolute.map_l G C O).mp hG, hGInj⟩).elim

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let γ := .fvar (.there (.there .here))
  let Ω := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.ordinal_m γ) <|
        .imp (PowerlessRelativeOrdinalCutoff.countable_m B ω γ) <|
          .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω)
            (SecondOrderObjectSyntax.member_m γ Ω)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval, SecondOrderQuotient.structure_l]
  exact fun hBase hω hγ hCount hΩ => below_l (hBase := hBase) K hω hγ hCount hΩ

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms below_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCountableOrdinalBound
