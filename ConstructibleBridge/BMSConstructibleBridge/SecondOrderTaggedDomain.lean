import BMSConstructibleBridge.SecondOrderTaggedGraph
import BMSConstructibleBridge.SecondOrderDomain

/-!
# 带标签副本的内部根域保持

实际公式归纳证明内部下降链始终留在起始标签中，再以内部理解投影回旧图。
量化全部模型索引，不能只沿标准有限步验证标签不变性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTaggedDomain

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderDomain SecondOrderTaggedGraph

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private theorem closed (hℳ : Theory.Models ℳ theory_m) (k a : num_l ℳ) (R G X : set_l ℳ)
    (hG : fiber_l k R G) (hX : function_l X) (h₀ : relation_l X (zero_l ℳ) (value_l k a))
    (h : ∀ i b c, relation_l X i b → relation_l X (succ_l i) c → relation_l G c b) :
    ∀ i, ∃ b, relation_l X i (value_l k b) := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here))))
  apply induct_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree X).pushFree k)
    (fun i => ∃ b, relation_l X i (value_l k b)) ?_ ⟨a, h₀⟩ ?_
  · intro i
    simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l]
    change (∃ b p, value_l k b = p ∧ relation_l X i p) ↔ _
    exact ⟨fun ⟨b, _, rfl, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, value_l k b, rfl, hb⟩⟩
  · rintro i ⟨b, hb⟩
    obtain ⟨c, hc, _⟩ := hX (succ_l i)
    obtain ⟨d, rfl, _⟩ := (hG c b).mp (h i (value_l k b) c hb hc)
    exact ⟨d, hc⟩

theorem pullback_l (hℳ : Theory.Models ℳ theory_m) (k : num_l ℳ) (X : set_l ℳ) :
    ∃ Y : set_l ℳ, ∀ i b, relation_l Y i b ↔ relation_l X i (value_l k b) := by
  let φ : Formula signature_m [] [.num, .num, .num, .set] :=
    .existsE .num (.conj
      (PrimitiveFormulas.pair_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar .here)))
  obtain ⟨Y, hY⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree X).pushFree k)
  refine ⟨Y, fun i b => (hY i b).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l]
  change (∃ p, value_l k b = p ∧ relation_l X i p) ↔ _
  simp

theorem wf_l (hℳ : Theory.Models ℳ theory_m) (k : num_l ℳ) (R G : set_l ℳ)
    (hG : fiber_l k R G) (a : num_l ℳ) (hR : SecondOrderDomain.wf_l R a) :
    SecondOrderDomain.wf_l G (value_l k a) := by
  intro X hX h₀
  by_contra h
  have h₁ : ∀ i b c, relation_l X i b → relation_l X (succ_l i) c → relation_l G c b := by
    intro i b c hb hc
    by_contra h₂
    exact h ⟨i, b, c, hb, hc, h₂⟩
  have h₂ := closed hℳ k a R G X hG hX h₀ h₁
  obtain ⟨Y, hY⟩ := pullback_l hℳ k X
  have h₃ : function_l Y := by
    intro i
    obtain ⟨b, hb⟩ := h₂ i
    refine ⟨b, (hY i b).mpr hb, fun c hc => ?_⟩
    exact (SecondOrderPairingBounds.injective_l hℳ _ _ _ _
      ((hX i).unique ((hY i c).mp hc) hb)).2
  obtain ⟨i, b, c, hb, hc, h₄⟩ := hR Y h₃ ((hY (zero_l ℳ) a).mpr h₀)
  exact h₄ ((SecondOrderTaggedGraph.edge_l hℳ k R G hG c b).mp
    (h₁ i (value_l k b) (value_l k c) ((hY i b).mp hb) ((hY (succ_l i) c).mp hc)))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTaggedDomain
