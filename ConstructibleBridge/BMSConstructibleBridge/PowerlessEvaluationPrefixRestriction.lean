import BMSConstructibleBridge.PowerlessEvaluationPrefix
import BMSConstructibleBridge.PowerlessRestriction

/-!
# 求值初段的真实限制与取值一致

限制集合函数保留严格前史，故仍满足同一个求值步骤；原递归唯一性
识别任意候选初段与该限制。没有用候选图的外部有限性替代模型内部证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationPrefixRestriction

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationPrefix

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)

include hℳ

theorem exists_l {ω e T A t₁ t₂ t₃ S F α β : carrier_l ℳ}
    (hF : prefix_l ω e T A t₁ t₂ t₃ S F α) (hβ : PowerlessOrdinal.ordinal_l β) (hβα : subset_l β α) :
    ∃ G, prefix_l ω e T A t₁ t₂ t₃ S G β ∧
      ∀ n Y, value_l G n Y ↔ member_l ℳ n β ∧ value_l F n Y := by
  obtain ⟨D, hF, hE⟩ := hF
  obtain ⟨G, hG, h⟩ := PowerlessRestriction.exists_l hℳ hF hβα
  refine ⟨G, ⟨D, hG, ?_⟩, h⟩
  intro n Y hY
  obtain ⟨hn, hY⟩ := (h n Y).mp hY
  obtain ⟨H, hH, hY⟩ := hE n Y hY
  refine ⟨H, ?_, hY⟩
  intro p
  refine (hH p).trans ?_
  constructor
  · rintro ⟨k, Z, hp, hk, hZ⟩
    exact ⟨k, Z, hp, hk, (h k Z).mpr ⟨PowerlessOrdinal.transitive_l hβ n k hn hk, hZ⟩⟩
  · rintro ⟨k, Z, hp, hk, hZ⟩
    exact ⟨k, Z, hp, hk, ((h k Z).mp hZ).2⟩

theorem value_l {ω e T A t₁ t₂ t₃ S F G α β : carrier_l ℳ}
    (hF : prefix_l ω e T A t₁ t₂ t₃ S F α) (hG : prefix_l ω e T A t₁ t₂ t₃ S G β)
    (hβ : PowerlessOrdinal.ordinal_l β) (hβα : subset_l β α) :
    ∀ n Y, ThirdOrderSemantics.value_l G n Y ↔ member_l ℳ n β ∧ ThirdOrderSemantics.value_l F n Y := by
  obtain ⟨H, hH, h⟩ := exists_l hℳ hF hβ hβα
  obtain ⟨K, _, h₀⟩ := PowerlessEvaluationPrefix.exists_unique_l hℳ
    (ω := ω) (e := e) (T := T) (A := A) (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (S := S) hβ
  have h₁ := (h₀ G hG).trans (h₀ H hH).symm
  exact h₁.symm ▸ h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationPrefixRestriction
