import BMSConstructibleBridge.SecondOrderProgramValue

/-!
# 实际回调图的可组合值规格

复杂接线中的回调已有原 graph_m 语义，可以从其全函数图选出同一模型上的宿主
取值函数，再使用 Value 模块组合投影、配对和复合。所选函数只是实际图的外部
记法：不把它加入对象签名，不用于任意谓词归纳或集合收集，更不替代内部递归证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCallbackValue

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramArithmetic
open SecondOrderProgramValue
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同一实际编译公式的两张语义图逐输入输出等价，不依赖集合外延性。 -/
theorem graph_equiv_l (c : code_m) {C D : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m c) D)
    (x y : num_l ℳ) : relation_l C x y ↔ relation_l D x y :=
  (graph_point_l (graph_m c) C hC x y).trans (graph_point_l (graph_m c) D hD x y).symm

/-- 从一张实际图的逐点取值得到可与全部语义图组合的值规格。 -/
theorem value_of_graph_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) {f : num_l ℳ → num_l ℳ}
    (hf : ∀ x, relation_l C x (f x)) : value_spec_l c f := by
  intro D hD x y
  rw [← graph_equiv_l c hC hD x y]
  constructor
  · exact function_value_unique_l (function_of_semantics_l hℳ c hC) (hf x)
  · intro hy
    exact hy ▸ hf x

/-- 回调图的实际总唯一性给出宿主值记法；图关系与所有内部输入保持不变。 -/
theorem value_exists_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) :
    ∃ f : num_l ℳ → num_l ℳ, value_spec_l c f ∧ ∀ x, relation_l C x (f x) := by
  classical
  have hCf := function_of_semantics_l hℳ c hC
  let f := fun x => Classical.choose (hCf x)
  have hf (x : num_l ℳ) : relation_l C x (f x) := (Classical.choose_spec (hCf x)).1
  exact ⟨f, value_of_graph_l hℳ c hC hf, hf⟩

#print axioms graph_equiv_l
#print axioms value_of_graph_l
#print axioms value_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCallbackValue
