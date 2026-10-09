import BMSConstructibleBridge.PowerlessRelativeCutoffClassOrderHistory
import BMSConstructibleBridge.PowerlessRelativeClassWellOrderUnion

/-! # 整个首不可数截断的实际 Class 环境良序图

真实层历史覆盖 W，真实比较历史相容。并集关系通过纯有界正文重建为
Class 对象，且对全部 raw 非空子集有最小元。初始 Class 序图守卫仍明确
保留；不声称输出序图属于 W，亦不把本定理当作枚举或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffClassWellOrder

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

theorem exists_l (K : source_coding_l hℳ) {B ω Ω W : Raw}
    (P₀ : type_l hℳ B) (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀.val)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) :
    ∃ R : type_l hℳ B, wellOrder_l (ℳ := 𝒱) W R.val := by
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx y hy => hSeed.2.1 x y hx hy
  obtain ⟨F, H, q, hF, hH, hStages, hCoherent⟩ :=
    PowerlessRelativeCutoffClassOrderHistory.exists_l K P₀ hSeed hω hΩ hW
  let I : type_l hℳ B := ⟨Ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hΩ.1⟩
  let C : type_l hℳ B := ⟨W, PowerlessRelativeLevelClosure.class_l hℳ hBase hW⟩
  have hMapF : map_l (ℳ := 𝒱) F.val Ω W := hF.1
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  have hCover : SecondOrderWellOrderCoherentUnion.cover_l (ℳ₀ := 𝒱) W Ω F.val := by
    intro x
    refine (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hW x).trans ?_
    constructor
    · rintro ⟨a, A, ha, hA, hx⟩
      obtain ⟨D, hD, _hUnique⟩ := hMapF.2 a ha
      have hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B a D :=
        ⟨Ω, F.val, W, hΩ.1, ha, hF, hD.2⟩
      have hEq := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hA hLevel
      exact ⟨a, A, ha, hEq.symm ▸ hD.2, hx⟩
    · rintro ⟨a, A, ha, hValue, hx⟩
      exact ⟨a, A, ha, ⟨Ω, F.val, W, hΩ.1, ha, hF, hValue⟩, hx⟩
  obtain ⟨R, hR, _hRead⟩ := PowerlessRelativeClassWellOrderUnion.exists_l
    hBase I F H C C hΩ.1 hMapF hH hCoherent hStages hCover
  exact ⟨R, hR⟩

/-- 自由槽依次为 W、Ω、ω、P₀、B；输出是实际 Class 序图。 -/
def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let W : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let Ω := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let P₀ := .fvar (.there (.there (.there .here)))
  let B := .fvar (.there (.there (.there (.there .here))))
  .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .existsE .set <|
              .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
                (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (up W) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, SecondOrderCanonicalLevelDerives.guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  intro η hSeed hP₀ hω hΩ hW
  obtain ⟨R, hR⟩ := exists_l K ⟨_, hP₀⟩ hSeed hω hΩ hW
  exact ⟨R.val, R.property, hR⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩)

#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffClassWellOrder
