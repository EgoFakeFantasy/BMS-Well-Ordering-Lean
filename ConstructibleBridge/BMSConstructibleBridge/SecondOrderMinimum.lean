import BMSConstructibleBridge.SecondOrderNaturalGraph

/-!
# 模型内部最小元与逐数选择

最小元原理来自实际有界公式的模型归纳，不使用模型数序的外部良基性。
逐数选择的输出是同一模型中的关系实数，不选择集合实数族。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMinimum

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (X : set_l ℳ)
    (hX : ∃ a, mem_l a X) :
    ∃ a, mem_l a X ∧ ∀ b, SecondOrderOrder.lt_l b a → ¬mem_l b X := by
  classical
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  by_contra h
  have h₁ : ∀ a, mem_l a X → ∃ b, b < a ∧ mem_l b X := by
    intro a ha
    by_contra h₂
    exact h ⟨a, ha, fun b hb hc => h₂ ⟨b, hb, hc⟩⟩
  let φ : Formula signature_m [] [.num, .set] :=
    .forallE .num (.imp
      (PrimitiveFormulas.lt_m (.bvar .here)
        (Term.app (σ := signature_m) .succ (.cons (.fvar .here) .nil)))
      (.neg (.rel .mem (.cons (.bvar .here) (.cons (.fvar (.there .here)) .nil)))))
  have h₂ : ∀ n : num_l ℳ, ∀ a, a ≤ n → ¬mem_l a X := by
    apply induct_l hℳ φ (pure_language_m _ rfl)
      ((Env.empty (M := ℳ)).pushFree X) (fun n => ∀ a, a ≤ n → ¬mem_l a X) ?_ ?_ ?_
    · intro n
      simp only [φ, Formula.satisfies, SecondOrderOrder.formula_l]
      change (∀ a, a < succ_l n → ¬mem_l a X) ↔ _
      simp only [SecondOrderNaturalGraph.lt_succ_l hℳ]
    · intro a ha hb
      have h₃ : a = 0 := le_antisymm ha (zero_le_l hℳ a)
      obtain ⟨b, hc, _⟩ := h₁ a hb
      exact (not_lt_of_ge (zero_le_l hℳ b)) (h₃ ▸ hc)
    · intro n hn a ha hb
      rcases eq_or_lt_of_le ha with rfl | ha
      · obtain ⟨b, hc, hd⟩ := h₁ (succ_l n) hb
        exact hn b ((SecondOrderNaturalGraph.lt_succ_l hℳ b n).mp hc) hd
      · exact hn a ((SecondOrderNaturalGraph.lt_succ_l hℳ a n).mp ha) hb
  obtain ⟨a, ha⟩ := hX
  exact h₂ a a le_rfl ha

/-- 每个非空内部数值纤维有最小输出；不要求集合选择公理。 -/
theorem choice_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a, ∃ b, relation_l R a b) :
    ∃ F : set_l ℳ, SecondOrderFunctions.function_l F ∧
      ∀ a b, relation_l F a b → relation_l R a b := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .conj (GraphSyntax.edge_m (.fvar (.there (.there .here)))
      (.fvar .here) (.fvar (.there .here)))
      (.forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here)))
        (.neg (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here)))))
  obtain ⟨F, hF⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree R)
  have h₁ : ∀ a b, relation_l F a b ↔ relation_l R a b ∧
      ∀ c, SecondOrderOrder.lt_l c b → ¬relation_l R a c := by
    intro a b
    refine (hF a b).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
    rfl
  refine ⟨F, ?_, fun a b h => ((h₁ a b).mp h).1⟩
  intro a
  let ψ : Formula signature_m [] [.num, .num, .set] :=
    GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  obtain ⟨X, hX⟩ := comprehension_l hℳ ψ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree R).pushFree a)
  have h₂ : ∀ b, mem_l b X ↔ relation_l R a b :=
    fun b => (hX b).trans (SecondOrderPairing.edge_l _ _ _ _)
  obtain ⟨b, hb, h₃⟩ := exists_l hℳ X (by
    obtain ⟨b, hb⟩ := hR a
    exact ⟨b, (h₂ b).mpr hb⟩)
  have h₄ : relation_l F a b :=
    (h₁ a b).mpr ⟨(h₂ b).mp hb, fun c hc hd => h₃ c hc ((h₂ c).mpr hd)⟩
  refine ⟨b, h₄, fun c hc => ?_⟩
  rcases SecondOrderOrder.trichotomy_l hℳ c b with h | h | h
  · exact False.elim (h₃ c h ((h₂ c).mpr ((h₁ a c).mp hc).1))
  · exact h
  · exact False.elim (((h₁ a c).mp hc).2 b h ((h₂ b).mp hb))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMinimum
