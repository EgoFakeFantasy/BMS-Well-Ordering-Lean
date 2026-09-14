import BMSConstructibleBridge.PowerlessOrdinalRecursion

/-! # 内部序数前史的精确映射域 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalHistory

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem map_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {α f B a H : carrier_l ℳ} (hα : PowerlessOrdinal.ordinal_l α) (hf : ThirdOrderSemantics.map_l f α B)
    (ha : member_l ℳ a α) (hH : PowerlessOrdinalRecursion.history_l H f a) : ThirdOrderSemantics.map_l H a B := by
  obtain ⟨R, hR⟩ := PowerlessOrdinalRelation.exists_l hℳ α
  exact PowerlessHistory.map_l hℳ ⟨(fun _ hx => hx), (fun _ _ _ hy _ => hy)⟩ ha hf
    (PowerlessOrdinalRelation.predecessor_l hℳ hα hR ha)
    ((PowerlessOrdinalRecursion.history_iff_l hℳ hR hf ha).mpr hH)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalHistory
