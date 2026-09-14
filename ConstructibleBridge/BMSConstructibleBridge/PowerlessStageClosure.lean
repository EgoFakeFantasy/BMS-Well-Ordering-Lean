import BMSConstructibleBridge.PowerlessOperatorClosure
import BMSConstructibleBridge.PowerlessStageStructure
import BMSConstructibleBridge.PowerlessStagePair

/-!
# 非零极限层的基本集合闭包

先把有限个参数放入同一个较早层，再用实际 D 算子的源公式覆盖。
所得集合属于极限层；证明不要求极限层本身满足无幂集背景理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hω : omega_l ω)
  (hA : stage_l ω e T t₁ t₂ t₃ α A)

include hℳ hω hA

theorem image_l {β B D : carrier_l ℳ} (hB : stage_l ω e T t₁ t₂ t₃ β B)
    (hβα : member_l ℳ β α) (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D) :
    subset_l D A := by
  obtain ⟨hα, γ, f, hγ, hf, hA⟩ := hA
  have hγ₀ := PowerlessOrdinalOrder.successor_l hℳ hα hγ
  have hB₀ := (value_iff_l hℳ hω hγ₀ hf ((hγ β).mpr (Or.inl hβα))).mpr hB
  exact PowerlessHierarchyStructure.image_subset_l hℳ hf hβα hA hB₀ hD

variable (hα : PowerlessStagePair.limit_l α)

include hα

theorem common_l {a b : carrier_l ℳ} (ha : member_l ℳ a A) (hb : member_l ℳ b A) :
    ∃ β B, member_l ℳ β α ∧ stage_l ω e T t₁ t₂ t₃ β B ∧ member_l ℳ a B ∧ member_l ℳ b B := by
  obtain ⟨β, B, hβ, hB, ha⟩ := (PowerlessStageStructure.limit_l hℳ hω hA hα.2.2 a).mp ha
  obtain ⟨γ, C, hγ, hC, hb⟩ := (PowerlessStageStructure.limit_l hℳ hω hA hα.2.2 b).mp hb
  rcases PowerlessOrdinal.compare_l hℳ hα.1 hβ hγ with h | h | h
  · exact ⟨γ, C, hγ, hC, PowerlessStageStructure.subset_l hℳ hω hB hC h a ha, hb⟩
  · subst γ
    have h := unique_l hℳ hω hB hC
    subst C
    exact ⟨β, B, hβ, hB, ha, hb⟩
  · exact ⟨β, B, hβ, hB, ha, PowerlessStageStructure.subset_l hℳ hω hC hB h b hb⟩

variable (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include ht hT

theorem empty_l {z : carrier_l ℳ} (hz : PowerlessNatural.zero_l z) : member_l ℳ z A := by
  obtain ⟨β, hβ⟩ := hα.2.1
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOrdinal.mem_l hα.1 hβ) e T t₁ t₂ t₃
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ B
  exact image_l hℳ hω hA hB hβ hD z (PowerlessOperatorClosure.empty_l hℳ hω ht hT hD hz)

theorem pair_l {a b p : carrier_l ℳ} (ha : member_l ℳ a A) (hb : member_l ℳ b A)
    (hp : ThirdOrderSemantics.pair_l a b p) : member_l ℳ p A := by
  obtain ⟨β, B, hβ, hB, ha, hb⟩ := common_l hℳ hω hA hα ha hb
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ B
  exact image_l hℳ hω hA hB hβ hD p (PowerlessOperatorClosure.pair_l hℳ hω ht hT hD ha hb hp)

theorem successor_l {a b : carrier_l ℳ} (ha : member_l ℳ a A)
    (hb : PowerlessNatural.successor_l a b) : member_l ℳ b A := by
  obtain ⟨β, B, hβ, hB, ha⟩ := (PowerlessStageStructure.limit_l hℳ hω hA hα.2.2 a).mp ha
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ B
  have hBT := PowerlessStageStructure.transitive_l hℳ hω ht hT hB
  exact image_l hℳ hω hA hB hβ hD b (PowerlessOperatorClosure.successor_l hℳ hω ht hT hD hBT ha hb)

theorem union_l {a b : carrier_l ℳ} (ha : member_l ℳ a A)
    (hb : ∀ x, member_l ℳ x b ↔ ∃ y, member_l ℳ y a ∧ member_l ℳ x y) : member_l ℳ b A := by
  obtain ⟨β, B, hβ, hB, ha⟩ := (PowerlessStageStructure.limit_l hℳ hω hA hα.2.2 a).mp ha
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ B
  have hBT := PowerlessStageStructure.transitive_l hℳ hω ht hT hB
  exact image_l hℳ hω hA hB hβ hD b (PowerlessOperatorClosure.union_l hℳ hω ht hT hD hBT ha hb)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageClosure
