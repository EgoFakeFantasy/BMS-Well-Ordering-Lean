import BMSConstructibleBridge.SecondOrderHistory

/-!
# 任意模型中的内部数值迭代

用实际公式归纳比较任意两段内部历史，再以含历史实数量词的理解公式构造
完整迭代图。这里不假定集合选择，也不把标准自然数递归扩充到非标准索引。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderIteration

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderHistory

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

/-- 两段相同确定性迭代历史在共同定义的全部模型索引上相容。 -/
theorem compatible_l (hℳ : Theory.Models ℳ theory_m) (F H K : set_l ℳ)
    (a n m : num_l ℳ) (hF : function_l F) (hH : spec_l F H a n) (hK : spec_l F K a m)
    (i : num_l ℳ) :
    SecondOrderOrder.lt_l i (succ_l n) → SecondOrderOrder.lt_l i (succ_l m) →
      ∀ b c, relation_l H i b → relation_l K i c → b = c := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  let φ : Formula signature_m [] [.num, .num, .num, .set, .set] :=
    .imp (PrimitiveFormulas.lt_m (.fvar .here) (succ (.fvar (.there .here))))
      (.imp (PrimitiveFormulas.lt_m (.fvar .here) (succ (.fvar (.there (.there .here)))))
        (.forallE .num (.forallE .num (.imp
          (GraphSyntax.edge_m (.fvar (.there (.there (.there .here))))
            (.fvar .here) (.bvar (.there .here)))
          (.imp (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here)))))
            (.fvar .here) (.bvar .here)) (.equal (.bvar (.there .here)) (.bvar .here)))))))
  have h₀ (j : num_l ℳ) : j < succ_l j :=
    (SecondOrderNaturalGraph.lt_succ_l hℳ j j).mpr le_rfl
  apply induct_l hℳ φ (pure_language_m _ rfl)
    (((((Env.empty (M := ℳ)).pushFree K).pushFree H).pushFree m).pushFree n)
    (fun i => i < succ_l n → i < succ_l m →
      ∀ b c, relation_l H i b → relation_l K i c → b = c) ?_ ?_ ?_ i
  · intro j
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
    rfl
  · intro hn hm b c hb hc
    exact ((hH.1 _ hn).unique hb hH.2.1).trans ((hK.1 _ hm).unique hc hK.2.1).symm
  · intro j hj hn hm b c hb hc
    have hn₁ : j < n := lt_of_lt_of_le (h₀ j)
      ((SecondOrderNaturalGraph.lt_succ_l hℳ _ n).mp hn)
    have hm₁ : j < m := lt_of_lt_of_le (h₀ j)
      ((SecondOrderNaturalGraph.lt_succ_l hℳ _ m).mp hm)
    have hn₂ := lt_trans hn₁ (h₀ n)
    have hm₂ := lt_trans hm₁ (h₀ m)
    obtain ⟨d, hd, _⟩ := hH.1 j hn₂
    obtain ⟨e, he, _⟩ := hK.1 j hm₂
    have h := hj hn₂ hm₂ d e hd he
    subst e
    exact (hF d).unique (hH.2.2 j d b hn₁ hd hb) (hK.2.2 j d c hm₁ he hc)

/-- 理解全部有限历史的端点；不是先选择一个外部历史族再要求其为内部集合。 -/
theorem graph_l (hℳ : Theory.Models ℳ theory_m) (F : set_l ℳ) (a : num_l ℳ) :
    ∃ X : set_l ℳ, ∀ i b, relation_l X i b ↔ ∃ H, spec_l F H a i ∧ relation_l H i b := by
  let φ : Formula signature_m [] [.num, .num, .set, .num] :=
    .existsE .set (.conj
      (formula_m (.fvar (.there (.there .here))) (.bvar .here)
        (.fvar (.there (.there (.there .here)))) (.fvar .here))
      (GraphSyntax.edge_m (.bvar .here) (.fvar .here) (.fvar (.there .here))))
  have hφ : language_m φ = true := by
    change (language_m (formula_m (Γ := [.set]) (Δ := [.num, .num, .set, .num])
      (.fvar (.there (.there .here))) (.bvar .here)
      (.fvar (.there (.there (.there .here)))) (.fvar .here)) &&
      language_m (GraphSyntax.edge_m (.bvar .here) (.fvar .here) (.fvar (.there .here)))) = true
    rw [SecondOrderHistory.pure_m _ _ _ _ rfl rfl rfl rfl]
    rfl
  obtain ⟨X, hX⟩ := SecondOrderRelations.comprehension_l hℳ φ hφ
    (((Env.empty (M := ℳ)).pushFree a).pushFree F)
  refine ⟨X, fun i b => (hX i b).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderHistory.formula_l, SecondOrderPairing.edge_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (F : set_l ℳ) (a : num_l ℳ)
    (hF : function_l F) :
    ∃ X : set_l ℳ, function_l X ∧ relation_l X (zero_l ℳ) a ∧
      ∀ i b c, relation_l X i b → relation_l X (succ_l i) c → relation_l F b c := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have h₀ (j : num_l ℳ) : j < succ_l j :=
    (SecondOrderNaturalGraph.lt_succ_l hℳ j j).mpr le_rfl
  obtain ⟨X, hX⟩ := graph_l hℳ F a
  refine ⟨X, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨H, hH⟩ := SecondOrderHistory.exists_l hℳ F a (fun b => (hF b).exists) i
    obtain ⟨b, hb, _⟩ := hH.1 i (h₀ i)
    refine ⟨b, (hX i b).mpr ⟨H, hH, hb⟩, fun c hc => ?_⟩
    obtain ⟨K, hK, hc⟩ := (hX i c).mp hc
    exact compatible_l hℳ F K H a i i hF hK hH i (h₀ i) (h₀ i) c b hc hb
  · obtain ⟨H, hH⟩ := SecondOrderHistory.base_l hℳ F a
    exact (hX (zero_l ℳ) a).mpr ⟨H, hH, hH.2.1⟩
  · intro i b c hb hc
    obtain ⟨H, hH, hb⟩ := (hX i b).mp hb
    obtain ⟨K, hK, hc⟩ := (hX (succ_l i) c).mp hc
    have h := lt_trans (h₀ i) (h₀ (succ_l i))
    obtain ⟨d, hd, _⟩ := hK.1 i h
    have h₁ := compatible_l hℳ F H K a i (succ_l i) hF hH hK i (h₀ i) h b d hb hd
    subst d
    exact hK.2.2 i b c (h₀ i) hd hc

/-- 数值关系的依赖链由最小输出和内部迭代产生，不消费集合选择方案。 -/
theorem chain_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (a : num_l ℳ)
    (hR : ∀ b, ∃ c, relation_l R b c) :
    ∃ X : set_l ℳ, function_l X ∧ relation_l X (zero_l ℳ) a ∧
      ∀ i b c, relation_l X i b → relation_l X (succ_l i) c → relation_l R b c := by
  obtain ⟨F, hF, h⟩ := SecondOrderMinimum.choice_l hℳ R hR
  obtain ⟨X, hX, h₀, h₁⟩ := exists_l hℳ F a hF
  exact ⟨X, hX, h₀, fun i b c hb hc => h b c (h₁ i b c hb hc)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderIteration
