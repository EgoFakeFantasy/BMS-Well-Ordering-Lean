import BMSConstructibleBridge.PowerlessTruthSign
import BMSConstructibleBridge.PowerlessTruthRecordAbsolute

/-!
# 可靠记录的实际添元与集合族合并

证书容器允许集合多个分支，不把有界量词的界误当成有限集合。
只构造并维护记录及其语义可靠性；完整局部规则证书仍须另行验证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthSet

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure
open PowerlessTruthRecord (record_l entry_l)
open PowerlessTruthSign (sign_l valid_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)

include hℳ

theorem extend_l {e t H D p c f : carrier_l ℳ} (hD : valid_l e t H D)
    (h : sign_l e t H p c f) :
    ∃ E, (∀ r, member_l ℳ r E ↔ member_l ℳ r D ∨ record_l p c f r) ∧
      valid_l e t H E ∧ entry_l E p c f := by
  obtain ⟨s, hs⟩ := PowerlessBasic.ordered_exists_l hℳ c f
  obtain ⟨E, hE⟩ := PowerlessAppendGraph.exists_l hℳ D p s
  have hr : ∀ r, record_l p c f r ↔ ordered_l p s r := by
    intro r
    constructor
    · rintro ⟨q, hq, hr⟩
      have hqs := PowerlessBasic.ordered_unique_l hℳ hq hs
      exact hqs ▸ hr
    · intro h
      exact ⟨s, hs, h⟩
  have h₀ : ∀ r, member_l ℳ r E ↔ member_l ℳ r D ∨ record_l p c f r :=
    fun r => (hE r).trans (or_congr Iff.rfl (hr r).symm)
  refine ⟨E, h₀, ?_, ?_⟩
  · rintro q b g ⟨r, hrE, hr₀⟩
    rcases (h₀ r).mp hrE with hrD | hr₁
    · exact hD q b g ⟨r, hrD, hr₀⟩
    · obtain ⟨rfl, rfl, rfl⟩ := PowerlessTruthRecord.injective_l hℳ hr₀ hr₁
      exact h
  · obtain ⟨r, hr₀⟩ := PowerlessTruthRecord.exists_l hℳ p c f
    exact ⟨r, (h₀ r).mpr (Or.inr hr₀), hr₀⟩

theorem union_l {e t H A : carrier_l ℳ} (hA : ∀ E, member_l ℳ E A → valid_l e t H E) :
    ∃ D, (∀ r, member_l ℳ r D ↔ ∃ E, member_l ℳ E A ∧ member_l ℳ r E) ∧ valid_l e t H D := by
  obtain ⟨D, hD⟩ := PowerlessBasic.union_l hℳ A
  exact ⟨D, hD, PowerlessTruthSign.union_l hD hA⟩

variable {U δ ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ δ U) (hδ : PowerlessStagePair.limit_l δ)

include hω ht hT hU hδ

theorem stage_extend_l {H : carrier_l ℳ} (D p c f : type_l U)
    (hD : valid_l e t₁ H D.val) (h : sign_l e t₁ H p.val c.val f.val) :
    ∃ E : type_l U, valid_l e t₁ H E.val ∧ entry_l E.val p.val c.val f.val ∧ subset_l D.val E.val := by
  obtain ⟨E, hE, hV, hq⟩ := extend_l hℳ hD h
  obtain ⟨r, hr⟩ := PowerlessTruthRecord.exists_l hℳ p.val c.val f.val
  have hrU := PowerlessTruthRecordAbsolute.stage_l hℳ hω ht hT hU hδ p.property c.property f.property hr
  have h₀ : ∀ s, member_l ℳ s E ↔ member_l ℳ s D.val ∨ s = r := by
    intro s
    refine (hE s).trans (or_congr Iff.rfl ?_)
    exact ⟨fun hs => PowerlessTruthRecord.unique_l hℳ hs hr, fun hs => hs.symm ▸ hr⟩
  have hEU := PowerlessStageGraphClosure.adjoin_l hℳ hω ht hT hU hδ D.property hrU h₀
  exact ⟨⟨E, hEU⟩, hV, hq, fun r hr => (hE r).mpr (Or.inl hr)⟩

theorem stage_union_l {H : carrier_l ℳ} (A : type_l U)
    (hA : ∀ E, member_l ℳ E A.val → valid_l e t₁ H E) :
    ∃ D : type_l U,
      (∀ r, member_l ℳ r D.val ↔ ∃ E, member_l ℳ E A.val ∧ member_l ℳ r E) ∧ valid_l e t₁ H D.val := by
  obtain ⟨D, hD, hV⟩ := union_l hℳ hA
  exact ⟨⟨D, PowerlessStageClosure.union_l hℳ hω hU hδ ht hT A.property hD⟩, hD, hV⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthSet
