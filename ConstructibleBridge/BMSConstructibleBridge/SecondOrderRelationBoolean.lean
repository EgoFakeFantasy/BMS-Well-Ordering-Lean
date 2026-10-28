import BMSConstructibleBridge.SecondOrderFunctions

/-! # 内部关系一列的零一函数图

关系及列号均是原模型参数；实际理解公式产生函数图。不把任意宿主谓词
加入模型集合域，也不抽取数值选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationBoolean

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderPairing

set_option autoImplicit false

universe u

def formula_m : Formula signature_m [] [.num, .num, .set, .num] :=
  let r := GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here)
    (.fvar (.there (.there (.there .here))))
  let z : Term signature_m [] [.num, .num, .set, .num] .num := Term.app (σ := signature_m) .zero .nil
  let o : Term signature_m [] [.num, .num, .set, .num] .num := Term.app (σ := signature_m) .succ (.cons z .nil)
  .disj (.conj r (.equal (.fvar (.there .here)) o))
    (.conj (.neg r) (.equal (.fvar (.there .here)) z))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

def spec_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (V : set_l ℳ) (l : num_l ℳ) (E : set_l ℳ) : Prop :=
  ∀ i j, relation_l E i j ↔
    (relation_l V i l ∧ j = succ_l (zero_l ℳ)) ∨ (¬relation_l V i l ∧ j = zero_l ℳ)

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (V : set_l ℳ) (l i j : num_l ℳ) :
    formula_m.satisfies (((((Env.empty).pushFree l).pushFree V).pushFree j).pushFree i) ↔
      (relation_l V i l ∧ j = succ_l (zero_l ℳ)) ∨ (¬relation_l V i l ∧ j = zero_l ℳ) := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

theorem function_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    {V E : set_l ℳ} {l : num_l ℳ} (h : spec_l V l E) : SecondOrderFunctions.function_l E := by
  classical
  intro i
  by_cases hi : relation_l V i l
  · refine ⟨succ_l (zero_l ℳ), (h i _).mpr (Or.inl ⟨hi, rfl⟩), ?_⟩
    intro j hj
    rcases (h i j).mp hj with hj | hj
    · exact hj.2
    · exact (hj.1 hi).elim
  · refine ⟨zero_l ℳ, (h i _).mpr (Or.inr ⟨hi, rfl⟩), ?_⟩
    intro j hj
    rcases (h i j).mp hj with hj | hj
    · exact (hi hj.1).elim
    · exact hj.2

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (V : set_l ℳ) (l : num_l ℳ) :
    ∃ E, SecondOrderFunctions.function_l E ∧ spec_l V l E := by
  obtain ⟨E, hE⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    (((Env.empty).pushFree l).pushFree V)
  have h : spec_l V l E := fun i j => (hE i j).trans (formula_l V l i j)
  exact ⟨E, function_l h, h⟩

/-- 产生同一零一图的实际原理解实例。 -/
theorem derives_m : Derives theory_m []
    (SecondOrderArithmetic.comprehension_m (SecondOrderRelations.formula_m formula_m)) :=
  SecondOrderRelations.comprehension_m formula_m pure_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationBoolean
