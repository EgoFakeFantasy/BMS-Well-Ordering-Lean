import BMSConstructibleBridge.SecondOrderProgramValue
import BMSConstructibleBridge.SecondOrderProgramConditional

/-!
# 可组合的实际条件分支值规格

分支的三个值函数都必须来自同一模型中原程序的统一图语义。结论只是该原分支图
逐点的条件等式，不把宿主条件表达式加入对象语言，也不对它调用内部归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramConditionalValue

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramValue
open SecondOrderProgramConditional (branch_m branch_rel_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 测试值为零取no，否则取yes；三个子程序保留同一个原输入。 -/
theorem branch_value_l (hℳ : Theory.Models ℳ theory_m) {t y n : code_m}
    {ft fy fn : num_l ℳ → num_l ℳ} (ht : value_spec_l t ft)
    (hy : value_spec_l y fy) (hn : value_spec_l n fn) :
    letI := Classical.propDecidable
    value_spec_l (branch_m t y n) (fun x => if ft x = zero_l ℳ then fn x else fy x) := by
  classical
  intro B hB x z
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ t
  obtain ⟨Y, _, hY⟩ := graph_total_l hℳ y
  obtain ⟨N, _, hN⟩ := graph_total_l hℳ n
  rw [branch_rel_l hℳ t y n hT hY hN hB]
  simp only [ht hT, hy hY, hn hN]
  by_cases h : ft x = zero_l ℳ <;> simp [h]

#print axioms branch_value_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramConditionalValue
