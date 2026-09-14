import BMSConstructibleBridge.PowerlessEvaluationFamilyCut
import BMSConstructibleBridge.ThirdOrderStageEvaluationSlice

/-!
# Cκ 中的整个切片集合族及原族公式

先将所有切片统一放入某个后继早级 J，再把 J 作为元素放入较高极限层。
这给整个族的源覆盖界，不要求该族预先属于 Cκ，也不依赖其外部可数性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)

include hℳ hω hκ ht hT hU

theorem member_l {A F S D : carrier_l ℳ}
    (hA : ThirdOrderSemantics.member_l ℳ A U) (hF : ThirdOrderSemantics.member_l ℳ F U)
    (hS : ThirdOrderSemantics.member_l ℳ S U)
    (hD : PowerlessEvaluationFamily.family_l ω A F S D) : ThirdOrderSemantics.member_l ℳ D U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hκ₀ := ThirdOrderStageLimit.limit_l h₀ hω hκ
  obtain ⟨p, hp⟩ := PowerlessBasic.pairing_l h₀ A F
  have hpU := PowerlessStageClosure.pair_l h₀ hω hU hκ₀ ht hT hA hF hp
  obtain ⟨q, hq⟩ := PowerlessBasic.pairing_l h₀ p S
  have hqU := PowerlessStageClosure.pair_l h₀ hω hU hκ₀ ht hT hpU hS hq
  obtain ⟨α, B, hα, hB, hωα, hα₀, hqB⟩ := ThirdOrderStageLimit.member_l hℳ hω hκ ht hT hU hqU
  have hBT := PowerlessStageStructure.transitive_l h₀ hω ht hT hB
  have hpB := hBT q p hqB ((hq p).mpr (Or.inl rfl))
  have hAB := hBT p A hpB ((hp A).mpr (Or.inl rfl))
  have hFB := hBT p F hpB ((hp F).mpr (Or.inr rfl))
  have hSB := hBT q S hqB ((hq S).mpr (Or.inr rfl))
  have hωB := PowerlessStageParameters.omega_l h₀ hω ht hT hB hωα
  obtain ⟨β, hαβ⟩ := PowerlessNatural.successor_exists_l h₀ α
  have hβ := ThirdOrderCountableSuccessor.limit_l h₀ hω hκ hα hαβ
  obtain ⟨J, hJ⟩ := PowerlessHierarchyStage.exists_l h₀ hω
    (PowerlessOrdinal.mem_l hκ.1 hβ) e T t₁ t₂ t₃
  have hBJ := PowerlessStageStructure.successor_l h₀ hω ht hT hB hJ hαβ
  have hDJ : subset_l D J := by
    intro Y hY
    obtain ⟨c, hc, f, hf, hY⟩ := (hD Y).mp hY
    exact PowerlessStageEvaluationSlice.operator_l h₀ hω ht hT hB hωα hα₀ hBJ hAB hFB
      (hBT ω c hωB hc) (hBT S f hSB hf) hY
  have hJU := PowerlessStageStructure.member_l h₀ hω ht hT hJ hU hβ
  obtain ⟨γ, C, hγ, hC, hωγ, hγ₀, hqC, hJC⟩ := ThirdOrderStageLimit.pair_l hℳ hω hκ ht hT hU hqU hJU
  have hCT := PowerlessStageStructure.transitive_l h₀ hω ht hT hC
  have hpC := hCT q p hqC ((hq p).mpr (Or.inl rfl))
  have hAC := hCT p A hpC ((hp A).mpr (Or.inl rfl))
  have hFC := hCT p F hpC ((hp F).mpr (Or.inr rfl))
  have hSC := hCT q S hqC ((hq S).mpr (Or.inr rfl))
  have hωC := PowerlessStageParameters.omega_l h₀ hω ht hT hC hωγ
  obtain ⟨E, hE⟩ := PowerlessEvaluationOperator.exists_l h₀ hω e T t₁ t₂ t₃ C
  apply PowerlessStageClosure.image_l h₀ hω hU hC hγ hE D
  exact PowerlessEvaluationFamilyCut.operator_l (hB := ⟨ω, hωC⟩)
    (ω := ⟨ω, hωC⟩) (A := ⟨A, hAC⟩) (F := ⟨F, hFC⟩) (S := ⟨S, hSC⟩)
    h₀ hCT (PowerlessStageGraphClosure.ordered_l h₀ hω ht hT hC hγ₀)
    hω ht hT hE hD (fun Y hY => hCT J Y hJC (hDJ Y hY))

theorem source_l {hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U}
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w A F S D : Term ℒ Γ Δ .set) (hw : (w.eval η).val = ω) :
    (PowerlessEvaluationFamily.family_m w A F S D).satisfies η ↔
      PowerlessEvaluationFamily.family_l ω (A.eval η).val (F.eval η).val (S.eval η).val (D.eval η).val := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hUT := PowerlessStageStructure.transitive_l h₀ hω ht hT hU
  have hP : ∀ {a b p : carrier_l ℳ}, ThirdOrderSemantics.member_l ℳ a U →
      ThirdOrderSemantics.member_l ℳ b U → ordered_l a b p → ThirdOrderSemantics.member_l ℳ p U :=
    PowerlessStageGraphClosure.ordered_l h₀ hω ht hT hU (ThirdOrderStageLimit.limit_l h₀ hω hκ)
  have hC : ∀ c f Y, ThirdOrderSemantics.member_l ℳ c (w.eval η).val →
      ThirdOrderSemantics.member_l ℳ f (S.eval η).val →
      PowerlessEvaluationSlice.slice_l (w.eval η).val (A.eval η).val (F.eval η).val c f Y →
        ThirdOrderSemantics.member_l ℳ Y U := by
    intro c f Y hc hf hY
    exact ThirdOrderStageEvaluationSlice.member_l hℳ hω hκ ht hT hU (A.eval η).property (F.eval η).property
      (hUT (w.eval η).val c (w.eval η).property hc) (hUT (S.eval η).val f (S.eval η).property hf)
      (by simpa only [hw] using hY)
  simpa only [hw] using PowerlessEvaluationFamilyAbsolute.source_l hUT hP η w A F S D hC

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationFamily
