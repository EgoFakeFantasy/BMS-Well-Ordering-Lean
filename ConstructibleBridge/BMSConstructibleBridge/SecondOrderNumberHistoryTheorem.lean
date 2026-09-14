import BMSConstructibleBridge.SecondOrderNumberHistory
import BMSConstructibleBridge.SecondOrderPowerSyntax
import BMSConstructibleBridge.SecondOrderCompleteness

/-!
# 数值有限历史存在性的对象定理

闭句先给出同一模型内的二进制幂图，再对全部全域数值转移关系、初值及长度
提供数值历史码。真实 `Derives` 来自全模型语义和已证强完备性，不宣称提取
原始递归证明码或在 PRA 中验证 BM4 的 `(G)`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumberHistoryTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

private def two {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons
    (Term.app (σ := signature_m) .succ (.cons (Term.app (σ := signature_m) .zero .nil) .nil)) .nil)

def formula_m : Sentence signature_m :=
  .existsE .set (.conj (SecondOrderPowerSyntax.formula_m (.bvar .here) two)
    (.forallE .set (.imp
      (.forallE .num (.existsE .num
        (GraphSyntax.edge_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))))
      (.forallE .num (.forallE .num (.existsE .num
        (SecondOrderNumberHistory.instantiate_m (.bvar (.there (.there (.there (.there .here)))))
          (.bvar (.there (.there (.there .here)))) (.bvar .here)
          (.bvar (.there (.there .here))) (.bvar (.there .here)))))))))

theorem pure_m : language_m formula_m = true := rfl

theorem models_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m)
    (hℳ : Theory.Models ℳ theory_m) : formula_m.TrueIn ℳ := by
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  refine ⟨E, ?_, ?_⟩
  · exact (SecondOrderPowerSyntax.formula_l _ _ _).mpr hE
  · intro F hF a n
    have h : ∀ b, ∃ d, SecondOrderPairing.relation_l F b d := by
      simp only [Formula.satisfies, SecondOrderPairing.edge_l] at hF
      exact hF
    obtain ⟨c, hc⟩ := SecondOrderNumberHistory.exists_l hℳ hE F a h n
    refine ⟨c, ?_⟩
    exact (SecondOrderNumberHistory.instantiate_l _ _ _ _ _ _ hE).mpr hc

theorem derives_m : Derives theory_m [] formula_m :=
  SecondOrderCompleteness.derives_m models_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumberHistoryTheorem
