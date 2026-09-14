import BMSConstructibleBridge.SecondOrderRelations

/-!
# 模型内部全函数图及链的前缀

全函数的定义只量化模型内部的数和关系实数。前缀图由实际关系理解公式产生，
为内部无下降链的根遗传性提供封闭操作，不假设任意外部函数都有内部图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctions

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

def function_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (X : set_l ℳ) : Prop :=
  ∀ n : num_l ℳ, ∃! m, relation_l X n m

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

/-- 自由槽位依次是输入、输出、原函数实数、新首项。 -/
def prefix_m : Formula signature_m [] [.num, .num, .set, .num] :=
  .disj (.conj (.equal (.fvar .here) zero)
    (.equal (.fvar (.there .here)) (.fvar (.there (.there (.there .here))))))
    (.existsE .num (.conj (.equal (.fvar .here) (succ (.bvar .here)))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar (.there .here)))))

theorem prefix_pure_m : language_m prefix_m = true := pure_language_m _ rfl

theorem prefix_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (X : set_l ℳ) (a i b : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree a).pushFree X).pushFree b).pushFree i)
      prefix_m ↔ (i = zero_l ℳ ∧ b = a) ∨ ∃ j, i = succ_l j ∧ relation_l X j b := by
  simp only [prefix_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

/-- 前缀图存在于同一模型中，且对所有模型数有逐点规格。 -/
theorem prefix_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (X : set_l ℳ) (a : num_l ℳ) :
    ∃ Y : set_l ℳ, (∀ b, relation_l Y (zero_l ℳ) b ↔ b = a) ∧
      ∀ i b, relation_l Y (succ_l i) b ↔ relation_l X i b := by
  obtain ⟨Y, hY⟩ := SecondOrderRelations.comprehension_l hℳ prefix_m prefix_pure_m
    (((Env.empty (M := ℳ)).pushFree a).pushFree X)
  simp_rw [prefix_formula_l] at hY
  refine ⟨Y, ?_, ?_⟩
  · intro b
    rw [hY]
    constructor
    · rintro (⟨_, h⟩ | ⟨j, h, _⟩)
      · exact h
      · exact False.elim (nonzero_l hℳ j h.symm)
    · exact fun h => Or.inl ⟨rfl, h⟩
  · intro i b
    rw [hY]
    constructor
    · rintro (⟨h, _⟩ | ⟨j, h, h₁⟩)
      · exact False.elim (nonzero_l hℳ i h)
      · exact (SecondOrderModel.injective_l hℳ h) ▸ h₁
    · exact fun h => Or.inr ⟨i, rfl, h⟩

/-- 前缀逐点规格保持内部全函数性。 -/
theorem prefix_function_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) (a : num_l ℳ)
    (h : function_l X) (h₀ : ∀ b, relation_l Y (zero_l ℳ) b ↔ b = a)
    (h₁ : ∀ i b, relation_l Y (succ_l i) b ↔ relation_l X i b) : function_l Y := by
  intro n
  rcases predecessor_l hℳ n with rfl | ⟨n, rfl⟩
  · exact ⟨a, (h₀ a).mpr rfl, fun b hb => (h₀ b).mp hb⟩
  · simpa only [h₁] using h n

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctions
