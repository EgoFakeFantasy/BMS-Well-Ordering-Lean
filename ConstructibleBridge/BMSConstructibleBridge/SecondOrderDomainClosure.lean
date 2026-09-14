import BMSConstructibleBridge.SecondOrderDomain
import BMSConstructibleBridge.SecondOrderChainMaps

/-!
# 内部根域的直接子节点闭包

若所有直接子根都满足内部无链性质，则根也满足。证明只在模型内去掉链的
首项，不需要外部良基归纳；这与已证子根遗传性给出完整根域方程。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDomainClosure

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderDomain

set_option autoImplicit false

universe u

theorem intro_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (a : num_l ℳ)
    (h : ∀ b, relation_l R b a → wf_l R b) : wf_l R a := by
  intro X hX h₀
  by_contra h₁
  have h₂ : ∀ i b c, relation_l X i b → relation_l X (succ_l i) c → relation_l R c b := by
    intro i b c hb hc
    by_contra h₃
    exact h₁ ⟨i, b, c, hb, hc, h₃⟩
  obtain ⟨b, hb, _⟩ := hX (succ_l (zero_l ℳ))
  obtain ⟨Y, hY⟩ := SecondOrderChainMaps.tail_l hℳ X
  obtain ⟨i, c, d, hc, hd, h₃⟩ := h b (h₂ (zero_l ℳ) a b h₀ hb) Y
    (SecondOrderChainMaps.tail_function_l X Y hX hY) ((hY (zero_l ℳ) b).mpr hb)
  exact h₃ (h₂ (succ_l i) c d ((hY i c).mp hc) ((hY (succ_l i) d).mp hd))

theorem iff_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (a : num_l ℳ) :
    wf_l R a ↔ ∀ b, relation_l R b a → wf_l R b :=
  ⟨fun h b h₁ => child_l hℳ R a b h h₁, intro_l hℳ R a⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDomainClosure
