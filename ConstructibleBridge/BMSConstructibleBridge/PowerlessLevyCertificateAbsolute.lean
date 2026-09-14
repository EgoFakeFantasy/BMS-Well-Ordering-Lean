import BMSConstructibleBridge.PowerlessLevyRuleAbsolute
import BMSConstructibleBridge.PowerlessLevyCertificate

/-!
# 原内部有限层级分类的绝对性

证书的全称判断由原记录的三个自然数 guard 限定，环境中的全部实际
有限证书由有限子集闭包取回。实际极限层的出口消去两个闭包条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyCertificateAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)

section Absolute

variable {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
  {ω e T : type_l B} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hI : ∀ x, member_l ℳ x ω.val → ∀ F,
    PowerlessAddition.iteration_l ω.val e.val x F → member_l ℳ F B)
  (hD : ∀ n, member_l ℳ n ω.val → ∀ D, subset_l D n → member_l ℳ D B)

include hℳ hBT hω he hT hI hD

theorem certificate_l {t₁ t₂ t₃ D : type_l B} :
    PowerlessLevyCertificate.certificate_l (ℳ := structure_l B hB) ω e T t₁ t₂ t₃ D ↔
      PowerlessLevyCertificate.certificate_l ω.val e.val T.val t₁.val t₂.val t₃.val D.val := by
  constructor
  · rintro ⟨⟨N, hN, hDN⟩, h⟩
    refine ⟨⟨N.val, hN, (PowerlessSourceNaturalAbsolute.subset_l hBT).mp hDN⟩, ?_⟩
    intro c n p hc
    obtain ⟨hcω, hnω, hpω⟩ := PowerlessLevyEntry.natural_l hc
    have h₀ := h ⟨c, hBT ω.val c ω.property hcω⟩ ⟨n, hBT ω.val n ω.property hnω⟩
      ⟨p, hBT ω.val p ω.property hpω⟩ ((PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mpr hc)
    exact ⟨PowerlessLevyEntryAbsolute.polarity_l.mp h₀.1,
      (PowerlessLevyRuleAbsolute.step_l hℳ hBT hω he hT hI hD).mp h₀.2⟩
  · rintro ⟨⟨N, hN, hDN⟩, h⟩
    refine ⟨⟨⟨N, hBT ω.val N ω.property hN⟩, hN,
      (PowerlessSourceNaturalAbsolute.subset_l hBT).mpr hDN⟩, ?_⟩
    intro c n p hc
    have h₀ := h c.val n.val p.val ((PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mp hc)
    exact ⟨PowerlessLevyEntryAbsolute.polarity_l.mpr h₀.1,
      (PowerlessLevyRuleAbsolute.step_l hℳ hBT hω he hT hI hD).mpr h₀.2⟩

theorem class_l {t₁ t₂ t₃ c n p : type_l B} :
    PowerlessLevyCertificate.class_l (ℳ := structure_l B hB) ω e T t₁ t₂ t₃ c n p ↔
      PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val n.val p.val := by
  constructor
  · rintro ⟨D, h, hc⟩
    exact ⟨D.val, (certificate_l hℳ hBT hω he hT hI hD).mp h,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mp hc⟩
  · rintro ⟨D, h, hc⟩
    obtain ⟨N, hN, hDN⟩ := h.1
    exact ⟨⟨D, hD N hN D hDN⟩, (certificate_l hℳ hBT hω he hT hI hD).mpr h,
      (PowerlessLevyEntryAbsolute.entry_l hℳ hBT hω he hT hI).mpr hc⟩

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (w z U t₁ t₂ t₃ c n p : Term ℒ Γ Δ .set)
    (hw : w.eval η = ω) (hz : z.eval η = e) (hU : U.eval η = T) :
    Formula.satisfies η (PowerlessLevyCertificate.class_m w z U t₁ t₂ t₃ c n p) ↔
      PowerlessLevyCertificate.class_l ω.val e.val T.val (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val
        (c.eval η).val (n.eval η).val (p.eval η).val := by
  rw [PowerlessLevyCertificate.class_formula_l, hw, hz, hU]
  exact class_l hℳ hBT hω he hT hI hD

end Absolute

include hℳ

theorem stage_l {ω e T t₁ t₂ t₃ β B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B)
    (hωβ : member_l ℳ ω β) (hβ : PowerlessStagePair.limit_l β) :
    ∃ hB₀ : ∃ x, member_l ℳ x B, ∃ w z U s₁ s₂ s₃ : type_l B,
      w.val = ω ∧ z.val = e ∧ U.val = T ∧ s₁.val = t₁ ∧ s₂.val = t₂ ∧ s₃.val = t₃ ∧
      ∀ c n p : type_l B,
        PowerlessLevyCertificate.class_l (ℳ := structure_l B hB₀) w z U s₁ s₂ s₃ c n p ↔
          PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c.val n.val p.val := by
  obtain ⟨hw, hz, hU, h₁, h₂, h₃⟩ := PowerlessStageTriangular.parameters_l hℳ hω ht hT hB hωβ hβ
  have hBT := PowerlessStageStructure.transitive_l hℳ hω ht hT hB
  refine ⟨⟨ω, hw⟩, ⟨ω, hw⟩, ⟨e, hz⟩, ⟨T, hU⟩, ⟨t₁, h₁⟩, ⟨t₂, h₂⟩, ⟨t₃, h₃⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro c n p
  apply class_l hℳ hBT hω ht.1 hT
  · exact fun x hx F hF => PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hB hωβ hβ hx hF
  · exact PowerlessStageFiniteSubsets.finite_l hℳ hω ht hT hB hβ
      (fun x hx => PowerlessOrdinal.transitive_l hβ.1 ω x hωβ hx)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyCertificateAbsolute
