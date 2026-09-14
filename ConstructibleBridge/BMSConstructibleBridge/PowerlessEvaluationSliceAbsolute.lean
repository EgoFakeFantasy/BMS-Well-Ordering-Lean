import BMSConstructibleBridge.PowerlessAppendAbsolute
import BMSConstructibleBridge.PowerlessEvaluationSlice
import BMSConstructibleBridge.PowerlessStageGraphClosure

/-!
# 原求值切片及逐点公式的绝对性

追加图由实际查询的正见证沿 F 的成员链取回，故无需另加无限图闭包。
所有项与参数槽沿原 point_m、slice_m 保持。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationSliceAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {B : carrier_l ℳ}
  {hB : ∃ x, member_l ℳ x B}

theorem point_l (hBT : PowerlessNaturalOrder.transitive_l B)
    (hP : ∀ {a b p : carrier_l ℳ}, member_l ℳ a B → member_l ℳ b B →
      ordered_l a b p → member_l ℳ p B) {ω A F c f x : type_l B} :
    PowerlessEvaluationSlice.point_l (ℳ := structure_l B hB) ω A F c f x ↔
      PowerlessEvaluationSlice.point_l ω.val A.val F.val c.val f.val x.val := by
  constructor
  · rintro ⟨m, hm, hf, g, hg, hq⟩
    exact ⟨m.val, hm, (PowerlessSourceGraphAbsolute.map_l hBT).mp hf, g.val,
      (PowerlessAppendAbsolute.append_l hBT hP).mp hg, (PowerlessValueAbsolute.query_l hBT).mp hq⟩
  · rintro ⟨m, hm, hf, g, hg, Y, hY, hq⟩
    have hmB := hBT ω.val m ω.property hm
    have hgB := hBT Y g (PowerlessValueAbsolute.coordinates_l hBT F.property hY).2 hq
    exact ⟨⟨m, hmB⟩, hm, (PowerlessSourceGraphAbsolute.map_l hBT).mpr hf, ⟨g, hgB⟩,
      (PowerlessAppendAbsolute.append_l hBT hP).mpr hg,
      (PowerlessValueAbsolute.query_l hBT).mpr ⟨Y, hY, hq⟩⟩

theorem slice_l (hBT : PowerlessNaturalOrder.transitive_l B)
    (hP : ∀ {a b p : carrier_l ℳ}, member_l ℳ a B → member_l ℳ b B →
      ordered_l a b p → member_l ℳ p B) {ω A F c f Y : type_l B} :
    PowerlessEvaluationSlice.slice_l (ℳ := structure_l B hB) ω A F c f Y ↔
      PowerlessEvaluationSlice.slice_l ω.val A.val F.val c.val f.val Y.val := by
  constructor
  · intro h x
    constructor
    · intro hx
      have hxB := hBT Y.val x Y.property hx
      obtain ⟨hxA, hp⟩ := (h ⟨x, hxB⟩).mp hx
      exact ⟨hxA, (point_l hBT hP).mp hp⟩
    · rintro ⟨hxA, hp⟩
      have hxB := hBT A.val x A.property hxA
      exact (h ⟨x, hxB⟩).mpr ⟨hxA, (point_l hBT hP).mpr hp⟩
  · intro h x
    exact (h x.val).trans (and_congr Iff.rfl (point_l hBT hP)).symm

theorem point_source_l (hBT : PowerlessNaturalOrder.transitive_l B)
    (hP : ∀ {a b p : carrier_l ℳ}, member_l ℳ a B → member_l ℳ b B →
      ordered_l a b p → member_l ℳ p B)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ) (ω A F c f x : Term ℒ Γ Δ .set) :
    (PowerlessEvaluationSlice.point_m ω A F c f x).satisfies η ↔
      PowerlessEvaluationSlice.point_l (ω.eval η).val (A.eval η).val (F.eval η).val
        (c.eval η).val (f.eval η).val (x.eval η).val :=
  (PowerlessEvaluationSlice.point_formula_l η ω A F c f x).trans (point_l hBT hP)

theorem slice_source_l (hBT : PowerlessNaturalOrder.transitive_l B)
    (hP : ∀ {a b p : carrier_l ℳ}, member_l ℳ a B → member_l ℳ b B →
      ordered_l a b p → member_l ℳ p B)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ) (ω A F c f Y : Term ℒ Γ Δ .set) :
    (PowerlessEvaluationSlice.slice_m ω A F c f Y).satisfies η ↔
      PowerlessEvaluationSlice.slice_l (ω.eval η).val (A.eval η).val (F.eval η).val
        (c.eval η).val (f.eval η).val (Y.eval η).val :=
  (PowerlessEvaluationSlice.slice_formula_l η ω A F c f Y).trans (slice_l hBT hP)

theorem stage_point_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hC : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α B) (hα : PowerlessStagePair.limit_l α)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ) (w A F c f x : Term ℒ Γ Δ .set) :
    (PowerlessEvaluationSlice.point_m w A F c f x).satisfies η ↔
      PowerlessEvaluationSlice.point_l (w.eval η).val (A.eval η).val (F.eval η).val
        (c.eval η).val (f.eval η).val (x.eval η).val :=
  point_source_l (PowerlessStageStructure.transitive_l hℳ hω ht hT hC)
    (PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hC hα) η w A F c f x

theorem stage_slice_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hC : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α B) (hα : PowerlessStagePair.limit_l α)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ) (w A F c f Y : Term ℒ Γ Δ .set) :
    (PowerlessEvaluationSlice.slice_m w A F c f Y).satisfies η ↔
      PowerlessEvaluationSlice.slice_l (w.eval η).val (A.eval η).val (F.eval η).val
        (c.eval η).val (f.eval η).val (Y.eval η).val :=
  slice_source_l (PowerlessStageStructure.transitive_l hℳ hω ht hT hC)
    (PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hC hα) η w A F c f Y

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationSliceAbsolute
