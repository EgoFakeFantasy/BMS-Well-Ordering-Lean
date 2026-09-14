import BMSConstructibleBridge.PowerlessEvaluationClause
import BMSConstructibleBridge.PowerlessOrdinalRecursion

/-!
# 局部求值只读取严格前驱

实际前史在 k∈n 处与总图取值相同；构造子的子码界把这个事实传给
与非及存在量词规则。无需把内部自然数关系变成宿主良基关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationHistory

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationClause

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem value_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {H F n k Y : carrier_l ℳ} (hH : PowerlessOrdinalRecursion.history_l H F n) :
    ThirdOrderSemantics.value_l H k Y ↔ ThirdOrderSemantics.value_l F k Y ∧ ThirdOrderSemantics.member_l ℳ k n := by
  constructor
  · rintro ⟨p, hp, h₀⟩
    obtain ⟨x, y, h₁, hx, hy⟩ := (hH p).mp hp
    obtain ⟨h₂, h₃⟩ := (PowerlessBasic.ordered_eq_l hℳ h₀ h₁).mp rfl
    subst x
    subst y
    exact ⟨hy, hx⟩
  · rintro ⟨⟨p, hp, h₀⟩, hk⟩
    exact ⟨p, (hH p).mpr ⟨k, Y, h₀, hk, p, hp, h₀⟩, h₀⟩

theorem query_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {H F n k f : carrier_l ℳ} (hH : PowerlessOrdinalRecursion.history_l H F n)
    (hk : ThirdOrderSemantics.member_l ℳ k n) :
    PowerlessEvaluationClause.query_l H k f ↔ PowerlessEvaluationClause.query_l F k f := by
  apply exists_congr
  intro Y
  exact and_congr ((value_l hℳ hH).trans (and_iff_left hk)) Iff.rfl

theorem congr_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ H G n f : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (h : ∀ k, ThirdOrderSemantics.member_l ℳ k n → ∀ g,
      PowerlessEvaluationClause.query_l H k g ↔ PowerlessEvaluationClause.query_l G k g) :
    clause_l ω e T A t₁ t₂ t₃ H n f ↔ clause_l ω e T A t₁ t₂ t₃ G n f := by
  unfold clause_l
  refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr ?_ ?_))
  · apply exists_congr
    intro a
    apply exists_congr
    intro b
    apply and_congr_right
    intro hc
    obtain ⟨ha, hb⟩ := PowerlessFormulaConstructor.bounds_l hℳ hω he hT hc
    exact not_congr (and_congr (h a ha f) (h b hb f))
  · apply exists_congr
    intro i
    apply exists_congr
    intro b
    apply and_congr_right
    intro hc
    have h₀ := h b (PowerlessFormulaConstructor.bounds_l hℳ hω he hT hc).2
    simp only [PowerlessEvaluationClause.exists_l, h₀]

theorem clause_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ H F n f : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hH : PowerlessOrdinalRecursion.history_l H F n) :
    PowerlessEvaluationClause.clause_l ω e T A t₁ t₂ t₃ H n f ↔
      PowerlessEvaluationClause.clause_l ω e T A t₁ t₂ t₃ F n f :=
  congr_l hℳ hω he hT (fun _ hk _ => query_l hℳ hH hk)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationHistory
