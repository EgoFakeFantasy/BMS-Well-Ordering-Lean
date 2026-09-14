import BMSConstructibleBridge.PowerlessPairingCode
import BMSConstructibleBridge.PowerlessStageAdditionIteration
import BMSConstructibleBridge.PowerlessStageTriangular

/-!
# 原三角数配数公式的传递子域绝对性

保留原无限迭代加法及原配数公式。三角数图的取值给出中间值的自然数界，
早级迭代图成员性消去加法见证的闭包前提；不要求成员域满足无幂集核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPairingAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)

include hℳ

theorem code_l {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A}
    (hAT : PowerlessNaturalOrder.transitive_l A) {ω e T a b c : type_l A}
    (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val) (ha : member_l ℳ a.val ω.val)
    (hI : ∀ x, member_l ℳ x ω.val → ∀ F,
      PowerlessAddition.iteration_l ω.val e.val x F → member_l ℳ F A) :
    PowerlessPairingCode.code_l (ℳ := structure_l A hA) ω e T a b c ↔
      PowerlessPairingCode.code_l ω.val e.val T.val a.val b.val c.val := by
  constructor
  · rintro ⟨s, t, hs, ht, hc⟩
    have ht₀ := (PowerlessSourceGraphAbsolute.value_l hAT).mp ht
    have htω := (PowerlessFunction.value_mem_l hℳ hT.1 ht₀).2
    exact ⟨s.val, t.val, (PowerlessAdditionAbsolute.addition_l hℳ hAT hω he ha (hI a.val ha)).mp hs,
      ht₀, (PowerlessAdditionAbsolute.addition_l hℳ hAT hω he htω (hI t.val htω)).mp hc⟩
  · rintro ⟨s, t, hs, ht, hc⟩
    have h₀ := PowerlessFunction.value_mem_l hℳ hT.1 ht
    have hsA := hAT ω.val s ω.property h₀.1
    have htA := hAT ω.val t ω.property h₀.2
    exact ⟨⟨s, hsA⟩, ⟨t, htA⟩,
      (PowerlessAdditionAbsolute.addition_l hℳ hAT hω he ha (hI a.val ha)).mpr hs,
      (PowerlessSourceGraphAbsolute.value_l hAT).mpr ht,
      (PowerlessAdditionAbsolute.addition_l hℳ hAT hω he h₀.2 (hI t h₀.2)).mpr hc⟩

theorem source_l {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A}
    (hAT : PowerlessNaturalOrder.transitive_l A) {Γ Δ : SortContext ℒ}
    (η : Env (structure_l A hA) Γ Δ) (ω e T a b c : Term ℒ Γ Δ .set)
    (hω : omega_l (ω.eval η).val) (he : PowerlessNatural.zero_l (e.eval η).val)
    (hT : PowerlessTriangular.triangular_l (ω.eval η).val (e.eval η).val (T.eval η).val)
    (ha : member_l ℳ (a.eval η).val (ω.eval η).val)
    (hI : ∀ x, member_l ℳ x (ω.eval η).val → ∀ F,
      PowerlessAddition.iteration_l (ω.eval η).val (e.eval η).val x F → member_l ℳ F A) :
    Formula.satisfies η (PowerlessPairingCode.code_m ω e T a b c) ↔
      PowerlessPairingCode.code_l (ω.eval η).val (e.eval η).val (T.eval η).val
        (a.eval η).val (b.eval η).val (c.eval η).val :=
  (PowerlessPairingCode.code_formula_l η ω e T a b c).trans (code_l hℳ hAT hω he hT ha hI)

theorem stage_l {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α) :
    ∃ hA₀ : ∃ x, member_l ℳ x A, ∃ w z U : type_l A, w.val = ω ∧ z.val = e ∧ U.val = T ∧
      ∀ a b c : type_l A, member_l ℳ a.val ω →
        (PowerlessPairingCode.code_l (ℳ := structure_l A hA₀) w z U a b c ↔
          PowerlessPairingCode.code_l ω e T a.val b.val c.val) := by
  obtain ⟨hw, hz, hU, _⟩ := PowerlessStageTriangular.parameters_l hℳ hω ht hT hA hωα hα
  have hAT := PowerlessStageStructure.transitive_l hℳ hω ht hT hA
  refine ⟨⟨ω, hw⟩, ⟨ω, hw⟩, ⟨e, hz⟩, ⟨T, hU⟩, rfl, rfl, rfl, ?_⟩
  intro a b c ha
  exact code_l hℳ hAT hω ht.1 hT ha
    (fun x hx F hF => PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hA hωα hα hx hF)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPairingAbsolute
