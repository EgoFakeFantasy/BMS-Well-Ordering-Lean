import BMSConstructibleBridge.PowerlessEvaluationSliceAbsolute
import BMSConstructibleBridge.PowerlessOperatorClosure

/-! # 原求值切片在定义子集算子中的成员性 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationSliceCut

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem operator_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {B D Y e T t₁ t₂ t₃ : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B)
    (hP : ∀ {a b p : carrier_l ℳ}, member_l ℳ a B → member_l ℳ b B →
      ordered_l a b p → member_l ℳ p B) {ω A F c f : type_l B}
    (hω : omega_l ω.val) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω.val e T)
    (hD : PowerlessEvaluationOperator.operator_l ω.val e T t₁ t₂ t₃ B D)
    (hY : PowerlessEvaluationSlice.slice_l ω.val A.val F.val c.val f.val Y) : member_l ℳ Y D := by
  let η : Env (structure_l B hB) [.set, .set, .set, .set, .set] [] :=
    (((((Env.empty (σ := ℒ) (M := structure_l B hB)).pushBound
      (sort := SetTheory.SetSort.set) f).pushBound c).pushBound F).pushBound A).pushBound ω
  let φ : Formula ℒ [.set, .set, .set, .set, .set, .set] [] :=
    .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here))))
      (PowerlessEvaluationSlice.point_m (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there (.there (.there .here)))))) (.bvar .here))
  apply PowerlessOperatorClosure.specified_l hℳ hω ht hT hD φ η
  intro x
  have h₀ (hx : member_l ℳ x B) : φ.satisfies (η.pushBound ⟨x, hx⟩) ↔ member_l ℳ x Y := by
    simp only [φ, Formula.satisfies, PowerlessEvaluationSlice.point_formula_l]
    change (member_l ℳ x A.val ∧ PowerlessEvaluationSlice.point_l
      (ℳ := structure_l B hB) ω A F c f ⟨x, hx⟩) ↔ member_l ℳ x Y
    exact (and_congr Iff.rfl (PowerlessEvaluationSliceAbsolute.point_l hBT hP)).trans (hY x).symm
  constructor
  · intro hx
    have hxB := hBT A.val x A.property ((hY x).mp hx).1
    exact ⟨hxB, (h₀ hxB).mpr hx⟩
  · rintro ⟨hx, h⟩
    exact (h₀ hx).mp h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationSliceCut
