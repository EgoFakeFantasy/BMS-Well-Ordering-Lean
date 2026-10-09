import BMSConstructibleBridge.PowerlessRelativeCutoffClassOrderHistory
import BMSConstructibleBridge.PowerlessRelativeClassWellOrderUnion

/-! # 任意共尾非零极限层的实际 Class 良序及 Z₂ 对象推导

背景为原 SecondOrderArithmetic.theory_m，语言为纯隶属 ℒ。
无需首不可数序数：编码、两张实际历史及并集良序均在证明内取得。
序图满足对全部 raw 非空子集的最小元条件，不宣称图属于层内。
该构造供后续有限 Skolem 闭包使用，不替代凝聚或完整源公理证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalClassWellOrder

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

theorem exists_l (K : source_coding_l hℳ) {B β W : Raw}
    (P₀ : type_l hℳ B) (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀.val)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    (hωW : mem_l hℳ K.omega W) :
    ∃ R : type_l hℳ B, wellOrder_l (ℳ := 𝒱) W R.val := by
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx y hy => hSeed.2.1 x y hx hy
  obtain ⟨F, H, q, hF, hH, hStages, hCoherent⟩ :=
    PowerlessRelativeCutoffClassOrderHistory.exists_cofinal_l K P₀ hSeed hLimit hW hCofinal hωW
  have hOrd := PowerlessRelativeLevelClosure.ordinal_l hℳ hW
  let I : type_l hℳ B := ⟨β, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hOrd⟩
  let C : type_l hℳ B := ⟨W, PowerlessRelativeLevelClosure.class_l hℳ hBase hW⟩
  have hMapF : map_l (ℳ := 𝒱) F.val β W := hF.1
  have hCover : SecondOrderWellOrderCoherentUnion.cover_l (ℳ₀ := 𝒱) W β F.val := by
    intro x
    refine (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hW x).trans ?_
    constructor
    · rintro ⟨a, A, ha, hA, hx⟩
      obtain ⟨D, hD, _hUnique⟩ := hMapF.2 a ha
      have hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B a D :=
        ⟨β, F.val, W, hOrd, ha, hF, hD.2⟩
      have hEq := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hA hLevel
      exact ⟨a, A, ha, hEq.symm ▸ hD.2, hx⟩
    · rintro ⟨a, A, ha, hValue, hx⟩
      exact ⟨a, A, ha, ⟨β, F.val, W, hOrd, ha, hF, hValue⟩, hx⟩
  obtain ⟨R, hR, _hRead⟩ := PowerlessRelativeClassWellOrderUnion.exists_l
    hBase I F H C C hOrd hMapF hH hCoherent hStages hCover
  exact ⟨R, hR⟩

/-- 自由槽依次为 W、β、ω、P₀、B。 -/
def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let W : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let β := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let P₀ := .fvar (.there (.there (.there .here)))
  let B := .fvar (.there (.there (.there (.there .here))))
  .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
          .imp (PowerlessRelativeCofinalLimitBounds.cofinal_m β) <|
            .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
              .imp (SecondOrderObjectSyntax.member_m ω W) <|
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
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro η hSeed hP₀ hω hLimit hCofinal hW hωW
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  obtain ⟨R, hR⟩ := exists_l K ⟨_, hP₀⟩ hSeed hLimit hW hCofinal (hωEq ▸ hωW)
  exact ⟨R.val, R.property, hR⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩)

#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalClassWellOrder
