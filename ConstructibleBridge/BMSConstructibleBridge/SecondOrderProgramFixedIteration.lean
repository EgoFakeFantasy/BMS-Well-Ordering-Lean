import BMSConstructibleBridge.SecondOrderProgramIteration

/-!
# 固定状态在任意内部迭代次数下保持

若同一原状态转换图把x送回x，则同一原迭代图在全部内部次数上仍返回x。
归纳使用实际原语言公式，而不是只证明宿主自然数次迭代后就推广到非标准次数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramFixedIteration

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[n,x,R]，实际正文为原迭代图R(pair x n)=x。 -/
def fixed_m : Formula signature_m [] [.num, .num, .set] :=
  output_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here) (.fvar (.there .here))

/-- 固定状态归纳正文属于原语言。 -/
theorem fixed_language_m : language_m fixed_m = true := pure_language_m _ rfl

/-- 实际归纳公式与固定状态断言精确对应。 -/
theorem fixed_syntax_l (R : set_l ℳ) (x n : num_l ℳ) :
    Formula.satisfies ((((Env.empty (M := ℳ)).pushFree R).pushFree x).pushFree n) fixed_m ↔
      relation_l R (value_l x n) x := by
  simp only [fixed_m, output_syntax_l]
  rfl

/-- 已知原程序的一步固定点，在任意内部次数的原迭代图中仍固定。 -/
theorem fixed_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) {x : num_l ℳ}
    (hx : relation_l C x x) (n : num_l ℳ) : relation_l R (value_l x n) x := by
  apply induct_l hℳ fixed_m fixed_language_m
    (((Env.empty (M := ℳ)).pushFree R).pushFree x)
    (fun n => relation_l R (value_l x n) x) (fixed_syntax_l R x) ?_ ?_ n
  · exact (repeat_zero_l hℳ c hR x x).mpr rfl
  · intro k ih
    exact (repeat_succ_l hℳ c hR hC x k x).mpr ⟨x, ih, hx⟩

/-- 固定点的完整输出规格由同一原图的函数性给出。 -/
theorem fixed_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) {x : num_l ℳ}
    (hx : relation_l C x x) (n y : num_l ℳ) : relation_l R (value_l x n) y ↔ x = y := by
  have h := fixed_l hℳ c hR hC hx n
  constructor
  · exact function_value_unique_l (function_of_semantics_l hℳ (repeat_m c) hR) h
  · exact fun he => he ▸ h

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramFixedIteration
