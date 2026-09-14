import BMSConstructibleBridge.SecondOrderOrder
import BMSConstructibleBridge.GraphSyntax

/-!
# 任意模型中的实际配对图及边查询

原配对公式在任意双排序结构中都有唯一输出：两种互斥分支各使用一个总项。
这只证明正向配对图的总性和函数性，尚未证明其双射性或反向投影总性。
图边查询直接消费同一公式，不能转用尚无公理的配对函数符号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairing

open Logic FirstOrder SecondOrderSyntax SecondOrderModel

set_option autoImplicit false

universe u

/-- 使用模型自身运算与实际正差测试的配对值，不读取额外的配对函数符号。 -/
noncomputable def value_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (m n : num_l ℳ) : num_l ℳ := by
  classical
  exact if SecondOrderOrder.lt_l m n then add_l (mul_l n n) m
    else add_l (add_l (mul_l m m) m) n

/-- 对所有模型、环境和项，原配对模板精确描述此分支函数。 -/
theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t v : Term signature_m Γ Δ .num) :
    Formula.satisfies η (PrimitiveFormulas.pair_m s t v) ↔ value_l (s.eval η) (t.eval η) = v.eval η := by
  rw [PrimitiveFormulas.pair_m]
  simp only [Formula.satisfies, SecondOrderOrder.formula_l]
  change ((SecondOrderOrder.lt_l (s.eval η) (t.eval η) ∧
      add_l (mul_l (t.eval η) (t.eval η)) (s.eval η) = v.eval η) ∨
    (¬SecondOrderOrder.lt_l (s.eval η) (t.eval η) ∧
      add_l (add_l (mul_l (s.eval η) (s.eval η)) (s.eval η)) (t.eval η) = v.eval η)) ↔ _
  classical
  by_cases h : SecondOrderOrder.lt_l (s.eval η) (t.eval η) <;> simp [value_l, h]

def environment_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (m n p : num_l ℳ) : Env ℳ [] [.num, .num, .num] :=
  (((Env.empty (M := ℳ)).pushFree p).pushFree n).pushFree m

/-- 正向配对图的任意输入存在唯一性；不暗含模型标准性或配对单射性。 -/
theorem total_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (m n : num_l ℳ) :
    ∃! p, Formula.satisfies (environment_l m n p)
      (PrimitiveFormulas.pair_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))) := by
  simp_rw [formula_l]
  change ∃! p, value_l m n = p
  exact ⟨value_l m n, rfl, fun _ h => h.symm⟩

def relation_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (X : set_l ℳ) (m n : num_l ℳ) : Prop := mem_l (value_l m n) X

/-- 同一边模板在任意模型中等于用实际配对图查集合成员。 -/
theorem edge_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (X : Term signature_m Γ Δ .set) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (GraphSyntax.edge_m X s t) ↔ relation_l (X.eval η) (s.eval η) (t.eval η) := by
  simp only [GraphSyntax.edge_m, Formula.satisfies, formula_l,
    Term.eval_weakenBound, Term.eval, Arguments.eval]
  change (∃ p : num_l ℳ, value_l (s.eval η) (t.eval η) = p ∧ mem_l p (X.eval η)) ↔ _
  simp [relation_l]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairing
