import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseClass
import BMSConstructibleBridge.PowerlessRelativeClassImageCountability
import BMSConstructibleBridge.PowerlessRelativeCountableOrdinalBound

/-! # 同一实际坍缩的类内可数像及严格序数界

原内部预算给出同一 H 的 Class 身份后，原类内满射像定理将 I 的实际
可数性传给 T。序数子域的单射由类内限制图构造，再与首不可数序数矛盾。
不把环境枚举当作类内可数性，不假定 ClassH、CountT 或严格高度界。
正式出口为原 Z₂ 中的 GraphTranslation Derives，不是最终 BMS 闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseCountability

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

theorem countable_l (K : source_coding_l hℳ) {B ω I T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hBI : ∀ x, mem_l hℳ x B → mem_l hℳ x I)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hT : PowerlessRelativeClassCorrespondence.member_l hℳ B T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B ω I) :
    PowerlessRelativeOrdinalCutoff.countable_l B ω T :=
  PowerlessRelativeClassImageCountability.countable_l (hBase := hBase) K hω hI hT
    (PowerlessRelativeMembershipCollapseClass.class_l K hBase hBI hI hT hH)
    hH.2.1 hH.2.2.1 hCount

/-- 序数子域的实际 Class 单射是既有图的限制，不能用环境可数性替代。 -/
theorem ordinal_countable_l (K : source_coding_l hℳ) {B ω T γ : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hγ : Ordinal γ)
    (hT : PowerlessRelativeClassCorrespondence.member_l hℳ B T)
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B ω T)
    (hSub : ∀ x, mem_l hℳ x γ → mem_l hℳ x T) :
    PowerlessRelativeOrdinalCutoff.countable_l B ω γ := by
  obtain ⟨f, hf, hMap, hInj⟩ := hCount
  let A : PowerlessRelativeClassStructure.type_l hℳ B := ⟨T, hT⟩
  let C : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨γ, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hγ⟩
  let O : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  let F : PowerlessRelativeClassStructure.type_l hℳ B := ⟨f, hf⟩
  have hF := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F A O).mpr hMap
  have hCA : subset_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) C A :=
    fun x hx => hSub x.val hx
  obtain ⟨G, hG, hRead⟩ := PowerlessRelativeClassFunctionRestriction.exists_l hF hCA
  have hInjective : injective_l (ℳ := 𝒱) G.val := by
    intro x z i hxi hzi
    obtain ⟨hx, hi⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G hxi
    obtain ⟨hz, _hi⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G hzi
    let x₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨x, hx⟩
    let z₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨z, hz⟩
    let i₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨i, hi⟩
    have hFx := ((hRead x₀ i₀).mp
      ((PowerlessRelativeClassFunctionAbsolute.value_l G x₀ i₀).mpr hxi)).2
    have hFz := ((hRead z₀ i₀).mp
      ((PowerlessRelativeClassFunctionAbsolute.value_l G z₀ i₀).mpr hzi)).2
    exact hInj x z i ((PowerlessRelativeClassFunctionAbsolute.value_l F x₀ i₀).mp hFx)
      ((PowerlessRelativeClassFunctionAbsolute.value_l F z₀ i₀).mp hFz)
  exact ⟨G.val, G.property, (PowerlessRelativeClassFunctionAbsolute.map_l G C O).mp hG, hInjective⟩

/-- 坍缩目标中的任何实际序数子域严格低于首不可数截断。 -/
theorem below_l (K : source_coding_l hℳ) {B ω I T H γ Ω : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hBI : ∀ x, mem_l hℳ x B → mem_l hℳ x I)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hT : PowerlessRelativeClassCorrespondence.member_l hℳ B T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B ω I)
    (hγ : Ordinal γ) (hSub : ∀ x, mem_l hℳ x γ → mem_l hℳ x T)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω) : mem_l hℳ γ Ω :=
  PowerlessRelativeCountableOrdinalBound.below_l (hBase := hBase) K hω hγ
    (ordinal_countable_l K hBase hω hγ hT (countable_l K hBase hBI hω hI hT hH hCount) hSub) hΩ

def schema_m {Δ : SortContext ℒ} (B ω I T H γ Ω : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (ThirdOrderTheory.subset_m B I) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B T) <|
          .imp (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
            .imp (PowerlessRelativeOrdinalCutoff.countable_m B ω I) <|
              .conj (PowerlessRelativeOrdinalCutoff.countable_m B ω T) <|
                .imp (PowerlessRelativeHierarchySyntax.ordinal_m γ) <|
                  .imp (ThirdOrderTheory.subset_m γ T) <|
                    .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω)
                      (SecondOrderObjectSyntax.member_m γ Ω)

def sentence_m {Δ : SortContext ℒ} (B ω I T H γ Ω : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I T H γ Ω)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (B ω I T H γ Ω : Term ℒ [] Δ .set) :
    (sentence_m B ω I T H γ Ω).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeMembershipCollapse.spec_formula_l, PowerlessRelativeOrdinalCutoff.countable_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hBase hBI hω hI hT hH hCount
  exact ⟨countable_l K hBase hBI hω hI hT hH hCount,
    fun hγ hSub hΩ => below_l K hBase hBI hω hI hT hH hCount hγ hSub hΩ⟩

theorem derives_m {Δ : SortContext ℒ} (B ω I T H γ Ω : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω I T H γ Ω)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I T H γ Ω)

#print axioms countable_l
#print axioms ordinal_countable_l
#print axioms below_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseCountability
