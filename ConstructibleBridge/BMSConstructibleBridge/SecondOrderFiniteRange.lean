import BMSConstructibleBridge.SecondOrderIteration

/-!
# 内部有限函数的数值界

截段函数先以零补全为内部全函数。实际公式归纳给出全部模型长度上的统一
值域界，不把非标准有限域当作 Lean 的有限类型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteRange

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem complete_l (hℳ : Theory.Models ℳ theory_m) (H : set_l ℳ) (n : num_l ℳ)
    (hH : ∀ i, SecondOrderOrder.lt_l i n → ∃! a, relation_l H i a) :
    ∃ F : set_l ℳ, function_l F ∧
      ∀ i, SecondOrderOrder.lt_l i n → ∀ a, relation_l F i a ↔ relation_l H i a := by
  let φ : Formula signature_m [] [.num, .num, .num, .set] :=
    .disj (.conj (PrimitiveFormulas.lt_m (.fvar .here) (.fvar (.there (.there .here))))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there .here))))
      (.conj (.neg (PrimitiveFormulas.lt_m (.fvar .here) (.fvar (.there (.there .here)))))
        (.equal (.fvar (.there .here)) (Term.app (σ := signature_m) .zero .nil)))
  obtain ⟨F, hF⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree H).pushFree n)
  have h : ∀ i a, relation_l F i a ↔
      (SecondOrderOrder.lt_l i n ∧ relation_l H i a) ∨
        (¬SecondOrderOrder.lt_l i n ∧ a = zero_l ℳ) := by
    intro i a
    refine (hF i a).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderOrder.formula_l, SecondOrderPairing.edge_l]
    rfl
  refine ⟨F, ?_, fun i hi a => by simp only [h, hi, true_and, not_true_eq_false, false_and, or_false]⟩
  intro i
  by_cases hi : SecondOrderOrder.lt_l i n
  · obtain ⟨a, ha, h₁⟩ := hH i hi
    refine ⟨a, (h i a).mpr (Or.inl ⟨hi, ha⟩), ?_⟩
    intro b hb
    exact h₁ b (((h i b).mp hb).resolve_right (fun h => h.1 hi)).2
  · refine ⟨zero_l ℳ, (h i _).mpr (Or.inr ⟨hi, rfl⟩), ?_⟩
    intro b hb
    exact (((h i b).mp hb).resolve_left (fun h => hi h.1)).2

theorem bound_l (hℳ : Theory.Models ℳ theory_m) (F : set_l ℳ) (hF : function_l F)
    (n : num_l ℳ) :
    ∃ b, ∀ i, SecondOrderOrder.lt_l i n → ∀ a, relation_l F i a → SecondOrderOrder.lt_l a b := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  let φ : Formula signature_m [] [.num, .set] :=
    .existsE .num (.forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar .here))
      (.forallE .num (.imp
        (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
        (PrimitiveFormulas.lt_m (.bvar .here) (.bvar (.there (.there .here))))))))
  apply induct_l hℳ φ (pure_language_m _ rfl) ((Env.empty (M := ℳ)).pushFree F)
    (fun n => ∃ b, ∀ i, i < n → ∀ a, relation_l F i a → a < b) ?_ ?_ ?_ n
  · intro n
    simp only [φ, Formula.satisfies, SecondOrderOrder.formula_l, SecondOrderPairing.edge_l]
    rfl
  · exact ⟨0, fun i hi => False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi)⟩
  · rintro n ⟨b, hb⟩
    obtain ⟨a, ha, _⟩ := hF n
    refine ⟨max b (succ_l a), ?_⟩
    intro i hi c hc
    rcases eq_or_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ i n).mp hi) with rfl | hi
    · obtain rfl := (hF i).unique hc ha
      exact lt_of_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ _ _).mpr le_rfl) (le_max_right _ _)
    · exact lt_of_lt_of_le (hb i hi c hc) (le_max_left _ _)

/-- 只在所需截段全定义的关系也有统一值域界。 -/
theorem partial_bound_l (hℳ : Theory.Models ℳ theory_m) (H : set_l ℳ) (n : num_l ℳ)
    (hH : ∀ i, SecondOrderOrder.lt_l i n → ∃! a, relation_l H i a) :
    ∃ b, ∀ i, SecondOrderOrder.lt_l i n → ∀ a, relation_l H i a → SecondOrderOrder.lt_l a b := by
  obtain ⟨F, hF, h⟩ := complete_l hℳ H n hH
  obtain ⟨b, hb⟩ := bound_l hℳ F hF n
  exact ⟨b, fun i hi a ha => hb i hi a ((h i hi a).mpr ha)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteRange
