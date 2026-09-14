import BMSConstructibleBridge.SecondOrderGraft
import BMSConstructibleBridge.SecondOrderChainMaps
import BMSConstructibleBridge.SecondOrderDomain

/-!
# 内部拼接图的根域保持

假设有内部全下降链，则去首项和后继拉回均由模型理解构造内部函数图。
旧根或被选子根的内部无链证书产生断点。证明不对非标准长度作宿主递归，
也不要求整张旧关系全局良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraftDomain

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderDomain SecondOrderChainMaps

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def chain (X G : set_l ℳ) : Prop :=
  ∀ i b c, relation_l X i b → relation_l X (succ_l i) c → relation_l G c b

private theorem chain_of_no_break (X G : set_l ℳ)
    (h : ¬∃ i b c, relation_l X i b ∧ relation_l X (succ_l i) c ∧ ¬relation_l G c b) :
    chain X G := by
  intro i b c hb hc
  by_contra h₁
  exact h ⟨i, b, c, hb, hc, h₁⟩

/-- 每个旧根的移位副本保留内部域证书。 -/
theorem shift_l (hℳ : Theory.Models ℳ theory_m) (R P G : set_l ℳ)
    (hG : SecondOrderGraft.spec_l R P G) (a : num_l ℳ) (hR : wf_l R a) :
    wf_l G (succ_l a) := by
  intro X hX h₀
  by_contra h
  have h := chain_of_no_break X G h
  have h₁ : ∀ i, ¬relation_l X i (zero_l ℳ) := by
    intro i h₂
    rcases predecessor_l hℳ i with rfl | ⟨i, rfl⟩
    · exact nonzero_l hℳ a ((hX (zero_l ℳ)).unique h₂ h₀).symm
    · obtain ⟨b, hb, _⟩ := hX i
      exact hG.zero b (h i b (zero_l ℳ) hb h₂)
  obtain ⟨Y, hY⟩ := pullback_l hℳ X
  obtain ⟨i, b, c, hb, hc, h₂⟩ := hR Y (pullback_function_l hℳ X Y hX hY h₁)
    ((hY (zero_l ℳ) a).mpr h₀)
  exact h₂ ((hG.shift c b).mp (h i (succ_l b) (succ_l c)
    ((hY i b).mp hb) ((hY (succ_l i) c).mp hc)))

/-- 只要求被选节点各自满足内部根域，不要求所有旧节点良基。 -/
theorem root_l (hℳ : Theory.Models ℳ theory_m) (R P G : set_l ℳ)
    (hG : SecondOrderGraft.spec_l R P G) (hR : ∀ a, mem_l a P → wf_l R a) :
    wf_l G (zero_l ℳ) := by
  intro X hX h₀
  by_contra h
  have h := chain_of_no_break X G h
  obtain ⟨a, ha, _⟩ := hX (succ_l (zero_l ℳ))
  have h₁ := h (zero_l ℳ) (zero_l ℳ) a h₀ ha
  rcases predecessor_l hℳ a with rfl | ⟨a, rfl⟩
  · exact hG.zero (zero_l ℳ) h₁
  · have hR := hR a ((hG.root a).mp h₁)
    obtain ⟨T, hT⟩ := tail_l hℳ X
    have h₂ : ∀ i, ¬relation_l T i (zero_l ℳ) := by
      intro i h₃
      obtain ⟨b, hb, _⟩ := hX i
      exact hG.zero b (h i b (zero_l ℳ) hb ((hT i (zero_l ℳ)).mp h₃))
    obtain ⟨Y, hY⟩ := pullback_l hℳ T
    obtain ⟨i, b, c, hb, hc, h₃⟩ := hR Y
      (pullback_function_l hℳ T Y (tail_function_l X T hX hT) hY h₂)
      ((hY (zero_l ℳ) a).mpr ((hT (zero_l ℳ) (succ_l a)).mpr ha))
    exact h₃ ((hG.shift c b).mp (h (succ_l i) (succ_l b) (succ_l c)
      ((hT i (succ_l b)).mp ((hY i b).mp hb))
      ((hT (succ_l i) (succ_l c)).mp ((hY (succ_l i) c).mp hc))))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraftDomain
