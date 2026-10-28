import BMSConstructibleBridge.SecondOrderProgramIteration

/-!
# 原程序迭代的内部次数合成

从x执行k步到t，再执行n步，与从x执行k+n步具有同一输出。
次数可以非标准；通过真实共同输出公式内部归纳证明，不调用宿主函数迭代恒等式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramIterationComposition

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[n,x,k,t,R]；唯一绑定槽是两次原图调用的共同输出。 -/
def composition_m : Formula signature_m [] [.num, .num, .num, .num, .set] :=
  .existsE .num (.conj
    (output_m (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here))
      (Term.app (σ := signature_m) .add
        (.cons (.fvar (.there (.there .here))) (.cons (.fvar .here) .nil))) (.bvar .here))
    (output_m (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar .here)))

/-- 次数合成不变量属于原语言。 -/
theorem composition_language_m : language_m composition_m = true := pure_language_m _ rfl

/-- 实际语法解释保留两次调用之间的同一中间状态。 -/
theorem composition_syntax_l (R : set_l ℳ) (x k t n : num_l ℳ) :
    Formula.satisfies ((((((Env.empty (M := ℳ)).pushFree R).pushFree t).pushFree k).pushFree x).pushFree n)
      composition_m ↔ ∃ y, relation_l R (value_l x (add_l k n)) y ∧ relation_l R (value_l t n) y := by
  simp only [composition_m, Formula.satisfies, output_syntax_l]
  rfl

/-- 真实公式内部归纳给出任意内部次数合成的共同输出。 -/
theorem composition_common_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) {x k t : num_l ℳ}
    (hxt : relation_l R (value_l x k) t) (n : num_l ℳ) :
    ∃ y, relation_l R (value_l x (add_l k n)) y ∧ relation_l R (value_l t n) y := by
  apply induct_l hℳ composition_m composition_language_m
    (((((Env.empty (M := ℳ)).pushFree R).pushFree t).pushFree k).pushFree x)
    (fun n => ∃ y, relation_l R (value_l x (add_l k n)) y ∧ relation_l R (value_l t n) y)
    (composition_syntax_l R x k t) ?_ ?_ n
  · rw [add_zero_l hℳ]
    exact ⟨t, hxt, (repeat_zero_l hℳ c hR t t).mpr rfl⟩
  · rintro j ⟨v, hxv, htv⟩
    obtain ⟨w, hvw, _⟩ := function_of_semantics_l hℳ c hC v
    rw [add_succ_l hℳ]
    exact ⟨w, (repeat_succ_l hℳ c hR hC x (add_l k j) w).mpr ⟨v, hxv, hvw⟩,
      (repeat_succ_l hℳ c hR hC t j w).mpr ⟨v, htv, hvw⟩⟩

/-- 原图函数性把共同输出升级为所有输出上的合成等价。 -/
theorem composition_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) {x k t : num_l ℳ}
    (hxt : relation_l R (value_l x k) t) (n y : num_l ℳ) :
    relation_l R (value_l x (add_l k n)) y ↔ relation_l R (value_l t n) y := by
  obtain ⟨z, hxz, htz⟩ := composition_common_l hℳ c hR hC hxt n
  have hRf := function_of_semantics_l hℳ (repeat_m c) hR
  constructor
  · exact fun hxy => (function_value_unique_l hRf hxz hxy) ▸ htz
  · exact fun hty => (function_value_unique_l hRf htz hty) ▸ hxz

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramIterationComposition
