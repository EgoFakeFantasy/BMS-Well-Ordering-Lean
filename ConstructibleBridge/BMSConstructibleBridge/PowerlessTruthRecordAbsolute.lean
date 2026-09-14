import BMSConstructibleBridge.PowerlessTruthRecord
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessStageGraphClosure

/-!
# 真值记录的坐标落级与原公式绝对性

只用传递性取得中间对和记录见证；构造新记录时再用实际极限层闭包。
记录集合不要求有限，因有界量词可以有集合多个赋值分支。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthRecordAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hUT : PowerlessNaturalOrder.transitive_l U)

include hUT

theorem ordered_coordinates_l {a b r : carrier_l ℳ} (hr : member_l ℳ r U)
    (h : ordered_l a b r) : member_l ℳ a U ∧ member_l ℳ b U := by
  obtain ⟨x, y, _, hy, h⟩ := h
  have hyU := hUT r y hr ((h y).mpr (Or.inr rfl))
  exact ⟨hUT y a hyU ((hy a).mpr (Or.inl rfl)), hUT y b hyU ((hy b).mpr (Or.inr rfl))⟩

theorem coordinates_l {p c f r : carrier_l ℳ} (hr : member_l ℳ r U)
    (h : PowerlessTruthRecord.record_l p c f r) :
    member_l ℳ p U ∧ member_l ℳ c U ∧ member_l ℳ f U := by
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨hp, hsU⟩ := ordered_coordinates_l hUT hr h
  exact ⟨hp, ordered_coordinates_l hUT hsU hs⟩

theorem record_l {p c f r : type_l U} :
    PowerlessTruthRecord.record_l (ℳ := structure_l U hU₀) p c f r ↔
      PowerlessTruthRecord.record_l p.val c.val f.val r.val := by
  constructor
  · rintro ⟨s, hs, hr⟩
    exact ⟨s.val, (PowerlessSourceGraphAbsolute.ordered_l hUT).mp hs,
      (PowerlessSourceGraphAbsolute.ordered_l hUT).mp hr⟩
  · rintro ⟨s, hs, hr⟩
    have hsU := (ordered_coordinates_l hUT r.property hr).2
    exact ⟨⟨s, hsU⟩, (PowerlessSourceGraphAbsolute.ordered_l hUT).mpr hs,
      (PowerlessSourceGraphAbsolute.ordered_l hUT).mpr hr⟩

theorem entry_l {D p c f : type_l U} :
    PowerlessTruthRecord.entry_l (ℳ := structure_l U hU₀) D p c f ↔
      PowerlessTruthRecord.entry_l D.val p.val c.val f.val := by
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r.val, hr, (record_l hUT).mp h⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨⟨r, hUT D.val r D.property hr⟩, hr, (record_l hUT).mpr h⟩

theorem record_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (p c f r : Term ℒ Γ Δ .set) :
    (PowerlessTruthRecord.record_m p c f r).satisfies η ↔
      PowerlessTruthRecord.record_l (p.eval η).val (c.eval η).val (f.eval η).val (r.eval η).val :=
  (PowerlessTruthRecord.record_formula_l η p c f r).trans (record_l hUT)

theorem entry_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (D p c f : Term ℒ Γ Δ .set) :
    (PowerlessTruthRecord.entry_m D p c f).satisfies η ↔
      PowerlessTruthRecord.entry_l (D.eval η).val (p.eval η).val (c.eval η).val (f.eval η).val :=
  (PowerlessTruthRecord.entry_formula_l η D p c f).trans (entry_l hUT)

omit hUT in
theorem stage_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ δ p c f r : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ δ U) (hδ : PowerlessStagePair.limit_l δ)
    (hp : member_l ℳ p U) (hc : member_l ℳ c U) (hf : member_l ℳ f U)
    (hr : PowerlessTruthRecord.record_l p c f r) : member_l ℳ r U := by
  obtain ⟨s, hs, hr⟩ := hr
  have hsU := PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hU hδ hc hf hs
  exact PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hU hδ hp hsU hr

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthRecordAbsolute
