import BMSConstructibleBridge.SecondOrderProgramArithmetic

/-!
# 原程序图的可组合内部值规格

把已证明的逐图规格组合起来，方便审查多层数组坐标的接线。这里的值函数作用于
同一个模型的全部内部数；每个构造都由原 graph_m 的语义证明，不从标准 eval 推广。
不增加程序原语或递归公理。原图存在性仍由原 Z₂ 模型上的 graph_total_l 提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramValue

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 固定原程序的每一张实际语义图，都与给定内部值函数逐点一致。 -/
def value_spec_l (c : code_m) (f : num_l ℳ → num_l ℳ) : Prop :=
  ∀ {R : set_l ℳ}, graph_semantics_l (graph_m c) R → ∀ x y, relation_l R x y ↔ f x = y

/-- 零程序的内部值。 -/
theorem zero_value_l (hℳ : Theory.Models ℳ theory_m) :
    value_spec_l .zero (fun _ : num_l ℳ => zero_l ℳ) := by
  intro R hR x y
  exact zero_rel_l hℳ hR x y

/-- 后继程序的内部值。 -/
theorem succ_value_l (hℳ : Theory.Models ℳ theory_m) :
    value_spec_l .succ (succ_l (ℳ := ℳ)) := by
  intro R hR x y
  exact succ_rel_l hℳ hR x y

/-- 恒等程序的内部值。 -/
theorem id_value_l (hℳ : Theory.Models ℳ theory_m) :
    value_spec_l PrimitiveProgram.id_m (fun x : num_l ℳ => x) := by
  intro R hR x y
  exact id_spec_l hℳ hR x y

/-- 左投影读取原内部反配对的第一坐标。 -/
theorem left_value_l (hℳ : Theory.Models ℳ theory_m) :
    value_spec_l .left (fun x => (SecondOrderUnpairing.value_l hℳ x).1) := by
  intro R hR x y
  exact left_rel_l hℳ hR x y

/-- 右投影读取原内部反配对的第二坐标。 -/
theorem right_value_l (hℳ : Theory.Models ℳ theory_m) :
    value_spec_l .right (fun x => (SecondOrderUnpairing.value_l hℳ x).2) := by
  intro R hR x y
  exact right_rel_l hℳ hR x y

/-- 原复合构造保持两个内部值规格，函数顺序为先g再f。 -/
theorem comp_value_l (hℳ : Theory.Models ℳ theory_m) {c d : code_m}
    {f g : num_l ℳ → num_l ℳ} (hf : value_spec_l c f) (hg : value_spec_l d g) :
    value_spec_l (.comp c d) (fun x => f (g x)) := by
  intro R hR x y
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ c
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ d
  rw [comp_rel_l hℳ (graph_m c) (graph_m d) F G hF hG hR]
  simp only [hg hG, hf hF, exists_eq_left']

/-- 原配对构造按左、右两个值规格保持坐标顺序。 -/
theorem pair_value_l (hℳ : Theory.Models ℳ theory_m) {c d : code_m}
    {f g : num_l ℳ → num_l ℳ} (hf : value_spec_l c f) (hg : value_spec_l d g) :
    value_spec_l (.pair c d) (fun x => value_l (f x) (g x)) := by
  intro R hR x y
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ c
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ d
  rw [pair_rel_l hℳ (graph_m c) (graph_m d) F G hF hG hR]
  simp only [hf hF, hg hG]
  constructor
  · rintro ⟨_, _, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨f x, g x, rfl, rfl, h⟩

#print axioms value_spec_l
#print axioms zero_value_l
#print axioms succ_value_l
#print axioms id_value_l
#print axioms left_value_l
#print axioms right_value_l
#print axioms comp_value_l
#print axioms pair_value_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramValue
