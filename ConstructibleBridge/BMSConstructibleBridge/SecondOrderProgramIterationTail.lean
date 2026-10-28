import BMSConstructibleBridge.SecondOrderProgramFixedIteration

/-!
# 原迭代到达固定点后的任意内部尾段

起点不必已经固定：在第b步到达一步固定点u后，第b+n步仍为u。自由参数b、n
均可非标准，证明用含加法的实际公式归纳，未把标准函数迭代定理外推到内部模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramIterationTail

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[n,x,b,u,R]，原迭代图在次数b+n处的值为同一u。 -/
def tail_m : Formula signature_m [] [.num, .num, .num, .num, .set] :=
  output_m (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here))
    (Term.app (σ := signature_m) .add
      (.cons (.fvar (.there (.there .here))) (.cons (.fvar .here) .nil)))
    (.fvar (.there (.there (.there .here))))

/-- 固定尾段正文属于原算术语言。 -/
theorem tail_language_m : language_m tail_m = true := pure_language_m _ rfl

/-- 实际公式语义保留相同起点、基准次数和终点。 -/
theorem tail_syntax_l (R : set_l ℳ) (x b y n : num_l ℳ) :
    Formula.satisfies ((((((Env.empty (M := ℳ)).pushFree R).pushFree y).pushFree b).pushFree x).pushFree n)
      tail_m ↔ relation_l R (value_l x (add_l b n)) y := by
  simp only [tail_m, output_syntax_l]
  rfl

/-- 实际迭代在第b步达到一步固定点后，全部内部尾段均保持该值。 -/
theorem tail_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) {x b y : num_l ℳ}
    (hb : relation_l R (value_l x b) y) (hy : relation_l C y y) (n : num_l ℳ) :
    relation_l R (value_l x (add_l b n)) y := by
  apply induct_l hℳ tail_m tail_language_m
    (((((Env.empty (M := ℳ)).pushFree R).pushFree y).pushFree b).pushFree x)
    (fun n => relation_l R (value_l x (add_l b n)) y) (tail_syntax_l R x b y) ?_ ?_ n
  · simpa only [add_zero_l hℳ] using hb
  · intro j ih
    rw [add_succ_l hℳ]
    exact (repeat_succ_l hℳ c hR hC x (add_l b j) y).mpr ⟨y, ih, hy⟩

/-- 固定尾段的精确输出规格，由同一原迭代图的函数性给出。 -/
theorem tail_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) {x b y : num_l ℳ}
    (hb : relation_l R (value_l x b) y) (hy : relation_l C y y) (n z : num_l ℳ) :
    relation_l R (value_l x (add_l b n)) z ↔ y = z := by
  have h := tail_l hℳ c hR hC hb hy n
  constructor
  · exact function_value_unique_l (function_of_semantics_l hℳ (repeat_m c) hR) h
  · exact fun he => he ▸ h

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramIterationTail
