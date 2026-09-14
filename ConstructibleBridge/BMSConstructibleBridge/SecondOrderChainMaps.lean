import BMSConstructibleBridge.SecondOrderFunctions

/-!
# 内部函数链的去首项和后继拉回

两个操作都给出实际理解公式，在模型数域的全部索引上成立。后继拉回仅在
原函数所有值非零时保持全函数性，不隐藏这一必要条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderChainMaps

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions

set_option autoImplicit false

universe u

private def succ {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons t .nil)

theorem tail_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (X : set_l ℳ) :
    ∃ Y : set_l ℳ, ∀ i b, relation_l Y i b ↔ relation_l X (succ_l i) b := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    GraphSyntax.edge_m (.fvar (.there (.there .here))) (succ (.fvar .here)) (.fvar (.there .here))
  obtain ⟨Y, hY⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree X)
  refine ⟨Y, fun i b => (hY i b).trans ?_⟩
  exact SecondOrderPairing.edge_l _ _ _ _

theorem pullback_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (X : set_l ℳ) :
    ∃ Y : set_l ℳ, ∀ i b, relation_l Y i b ↔ relation_l X i (succ_l b) := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (succ (.fvar (.there .here)))
  obtain ⟨Y, hY⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree X)
  refine ⟨Y, fun i b => (hY i b).trans ?_⟩
  exact SecondOrderPairing.edge_l _ _ _ _

theorem tail_function_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (X Y : set_l ℳ) (h : function_l X)
    (h₁ : ∀ i b, relation_l Y i b ↔ relation_l X (succ_l i) b) : function_l Y := by
  intro i
  simpa only [h₁] using h (succ_l i)

theorem pullback_function_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) (h : function_l X)
    (h₁ : ∀ i b, relation_l Y i b ↔ relation_l X i (succ_l b))
    (h₂ : ∀ i, ¬relation_l X i (zero_l ℳ)) : function_l Y := by
  intro i
  obtain ⟨a, ha, h₃⟩ := h i
  rcases predecessor_l hℳ a with rfl | ⟨a, rfl⟩
  · exact False.elim (h₂ i ha)
  · refine ⟨a, (h₁ i a).mpr ha, fun b hb => ?_⟩
    exact SecondOrderModel.injective_l hℳ (h₃ (succ_l b) ((h₁ i b).mp hb))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderChainMaps
