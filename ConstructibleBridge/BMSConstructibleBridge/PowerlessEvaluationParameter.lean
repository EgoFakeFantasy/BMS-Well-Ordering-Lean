import BMSConstructibleBridge.PowerlessEvaluationSlice
import BMSConstructibleBridge.PowerlessEvaluationAtoms

/-!
# 一个实际集合参数的隶属切片

当数码表示“末尾新变量属于原参数槽 j”时，求值切片精确读取该参数
集合的成员。原图的长度唯一性消去切片定义中重新量化的长度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationParameter

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationSlice

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F c f m j a x : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ n, ThirdOrderSemantics.member_l ℳ n ω ∧ map_l f n A)
    (hm : ThirdOrderSemantics.member_l ℳ m ω) (hf : map_l f m A) (ha : value_l f j a)
    (hc : PowerlessFormulaConstructor.constructor_l ω e T e m j c) (hx : ThirdOrderSemantics.member_l ℳ x A) :
    point_l ω A F c f x ↔ ThirdOrderSemantics.member_l ℳ x a := by
  have h : ∀ g, PowerlessAppendGraph.append_l f m x g →
      (PowerlessEvaluationClause.query_l F c g ↔ ThirdOrderSemantics.member_l ℳ x a) := by
    intro g hg
    obtain ⟨k, hk⟩ := PowerlessNatural.successor_exists_l hℳ m
    have h₀ := PowerlessAppendGraph.map_l hℳ hf hx hk hg
    have h₁ : value_l g m x := (PowerlessAppendGraph.value_l hℳ hg).mpr (Or.inr ⟨rfl, rfl⟩)
    have h₂ : value_l g j a := (PowerlessAppendGraph.value_l hℳ hg).mpr (Or.inl ha)
    have h₃ := (hS g).mpr ⟨k, PowerlessNatural.successor_mem_l hℳ hω hm hk, h₀⟩
    exact (PowerlessEvaluationEquations.member_l hℳ hω ht hT hF hc g).trans
      ((and_iff_right h₃).trans (PowerlessEvaluationAtoms.member_l hℳ h₀ h₁ h₂))
  constructor
  · rintro ⟨n, _, hn, g, hg, h₀⟩
    have h₁ := PowerlessAssignmentUpdate.length_unique_l hℳ hn hf
    subst n
    exact (h g hg).mp h₀
  · intro h₀
    obtain ⟨g, hg⟩ := PowerlessAppendGraph.exists_l hℳ f m x
    exact ⟨m, hm, hf, g, hg, (h g hg).mpr h₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationParameter
