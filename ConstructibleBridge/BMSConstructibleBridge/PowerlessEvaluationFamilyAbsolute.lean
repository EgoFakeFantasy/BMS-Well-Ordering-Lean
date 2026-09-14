import BMSConstructibleBridge.PowerlessEvaluationSliceAbsolute
import BMSConstructibleBridge.PowerlessEvaluationFamily

/-!
# 原求值子集族的成员条件与全称公式绝对性

逐点成员条件只需取回数码和参数图。整个族判定另需实际切片属于域，
不能将该条件从切片的子集性中省略。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFamilyAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {B : carrier_l ℳ}
  {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
  (hP : ∀ {a b p : carrier_l ℳ}, member_l ℳ a B → member_l ℳ b B →
    ordered_l a b p → member_l ℳ p B)

include hBT hP

theorem entry_l {ω A F S Y : type_l B} :
    (∃ c : type_l B, member_l (structure_l B hB) c ω ∧ ∃ f : type_l B,
      member_l (structure_l B hB) f S ∧
        PowerlessEvaluationSlice.slice_l (ℳ := structure_l B hB) ω A F c f Y) ↔
      ∃ c, member_l ℳ c ω.val ∧ ∃ f, member_l ℳ f S.val ∧
        PowerlessEvaluationSlice.slice_l ω.val A.val F.val c f Y.val := by
  constructor
  · rintro ⟨c, hc, f, hf, hY⟩
    exact ⟨c.val, hc, f.val, hf, (PowerlessEvaluationSliceAbsolute.slice_l hBT hP).mp hY⟩
  · rintro ⟨c, hc, f, hf, hY⟩
    exact ⟨⟨c, hBT ω.val c ω.property hc⟩, hc, ⟨f, hBT S.val f S.property hf⟩, hf,
      (PowerlessEvaluationSliceAbsolute.slice_l hBT hP).mpr hY⟩

theorem family_l {ω A F S D : type_l B}
    (hC : ∀ c f Y, member_l ℳ c ω.val → member_l ℳ f S.val →
      PowerlessEvaluationSlice.slice_l ω.val A.val F.val c f Y → member_l ℳ Y B) :
    PowerlessEvaluationFamily.family_l (ℳ := structure_l B hB) ω A F S D ↔
      PowerlessEvaluationFamily.family_l ω.val A.val F.val S.val D.val := by
  constructor
  · intro h Y
    constructor
    · intro hY
      have hYB := hBT D.val Y D.property hY
      exact (entry_l hBT hP).mp ((h ⟨Y, hYB⟩).mp hY)
    · rintro ⟨c, hc, f, hf, hY⟩
      have hYB := hC c f Y hc hf hY
      exact (h ⟨Y, hYB⟩).mpr ((entry_l hBT hP).mpr ⟨c, hc, f, hf, hY⟩)
  · intro h Y
    exact (h Y.val).trans (entry_l hBT hP).symm

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (ω A F S D : Term ℒ Γ Δ .set)
    (hC : ∀ c f Y, member_l ℳ c (ω.eval η).val → member_l ℳ f (S.eval η).val →
      PowerlessEvaluationSlice.slice_l (ω.eval η).val (A.eval η).val (F.eval η).val c f Y → member_l ℳ Y B) :
    (PowerlessEvaluationFamily.family_m ω A F S D).satisfies η ↔
      PowerlessEvaluationFamily.family_l (ω.eval η).val (A.eval η).val
        (F.eval η).val (S.eval η).val (D.eval η).val :=
  (PowerlessEvaluationFamily.family_formula_l η ω A F S D).trans (family_l hBT hP hC)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFamilyAbsolute
