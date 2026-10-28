import BMSConstructibleBridge.SecondOrderFunctions

/-! # 任意内部实数的数字成员零一函数图

直接检验 i ∈ V，不将 V 解释为二维关系再固定某一列。原理解公式产生
模型内部总函数图；分情况只用于 Prop 证明，不抽取 Type 层选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMembershipBoolean

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderPairing

set_option autoImplicit false

universe u

/-- 自由槽位依次为输入数、输出数、原实数参数。 -/
def formula_m : Formula signature_m [] [.num, .num, .set] :=
  let r : Formula signature_m [] [.num, .num, .set] :=
    .rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil))
  let z : Term signature_m [] [.num, .num, .set] .num :=
    Term.app (σ := signature_m) .zero .nil
  let o : Term signature_m [] [.num, .num, .set] .num :=
    Term.app (σ := signature_m) .succ (.cons z .nil)
  .disj (.conj r (.equal (.fvar (.there .here)) o))
    (.conj (.neg r) (.equal (.fvar (.there .here)) z))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

def spec_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (V E : set_l ℳ) : Prop :=
  ∀ i j, relation_l E i j ↔
    (mem_l i V ∧ j = succ_l (zero_l ℳ)) ∨ (¬mem_l i V ∧ j = zero_l ℳ)

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (V : set_l ℳ) (i j : num_l ℳ) :
    formula_m.satisfies ((((Env.empty).pushFree V).pushFree j).pushFree i) ↔
      (mem_l i V ∧ j = succ_l (zero_l ℳ)) ∨ (¬mem_l i V ∧ j = zero_l ℳ) := by
  simp only [formula_m, Formula.satisfies]
  rfl

theorem function_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    {V E : set_l ℳ} (h : spec_l V E) : SecondOrderFunctions.function_l E := by
  classical
  intro i
  by_cases hi : mem_l i V
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
    (hℳ : Theory.Models ℳ theory_m) (V : set_l ℳ) :
    ∃ E, SecondOrderFunctions.function_l E ∧ spec_l V E := by
  obtain ⟨E, hE⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    ((Env.empty).pushFree V)
  have h : spec_l V E := fun i j => (hE i j).trans (formula_l V i j)
  exact ⟨E, function_l h, h⟩

/-- 产生直接成员零一图的实际原 Z₂ 理解实例。 -/
theorem derives_m : Derives theory_m []
    (SecondOrderArithmetic.comprehension_m (SecondOrderRelations.formula_m formula_m)) :=
  SecondOrderRelations.comprehension_m formula_m pure_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMembershipBoolean
