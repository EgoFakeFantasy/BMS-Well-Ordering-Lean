import BMSConstructibleBridge.PowerlessEvaluationFamilyAbsolute
import BMSConstructibleBridge.PowerlessOperatorClosure

/-!
# 整个求值子集族的定义子集成员性

族 D 不是参数。输入必须给出 D⊆B；随后用原切片成员条件定义整个 D。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFamilyCut

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem operator_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {B D E e T t₁ t₂ t₃ : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B)
    (hP : ∀ {a b p : carrier_l ℳ}, member_l ℳ a B → member_l ℳ b B →
      ordered_l a b p → member_l ℳ p B) {ω A F S : type_l B}
    (hω : omega_l ω.val) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω.val e T)
    (hE : PowerlessEvaluationOperator.operator_l ω.val e T t₁ t₂ t₃ B E)
    (hD : PowerlessEvaluationFamily.family_l ω.val A.val F.val S.val D)
    (hDB : subset_l D B) : member_l ℳ D E := by
  let η : Env (structure_l B hB) [.set, .set, .set, .set] [] :=
    ((((Env.empty (σ := ℒ) (M := structure_l B hB)).pushBound
      (sort := SetTheory.SetSort.set) S).pushBound F).pushBound A).pushBound ω
  let φ : Formula ℒ [.set, .set, .set, .set, .set] [] :=
    .existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here))))
      (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there (.there (.there (.there (.there .here))))))))
        (PowerlessEvaluationSlice.slice_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here)))))))
  apply PowerlessOperatorClosure.specified_l hℳ hω ht hT hE φ η
  intro Y
  have h₀ (hY : member_l ℳ Y B) : φ.satisfies (η.pushBound ⟨Y, hY⟩) ↔ member_l ℳ Y D := by
    simp only [φ, Formula.satisfies, PowerlessEvaluationSlice.slice_formula_l]
    change (∃ c : type_l B, member_l (structure_l B hB) c ω ∧ ∃ f : type_l B,
      member_l (structure_l B hB) f S ∧
        PowerlessEvaluationSlice.slice_l (ℳ := structure_l B hB) ω A F c f ⟨Y, hY⟩) ↔ member_l ℳ Y D
    exact (PowerlessEvaluationFamilyAbsolute.entry_l hBT hP).trans (hD Y).symm
  constructor
  · intro hY
    exact ⟨hDB Y hY, (h₀ (hDB Y hY)).mpr hY⟩
  · rintro ⟨hY, h⟩
    exact (h₀ hY).mp h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFamilyCut
