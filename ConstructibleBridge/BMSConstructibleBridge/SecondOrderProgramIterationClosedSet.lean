import BMSConstructibleBridge.SecondOrderProgramIteration

/-! # 原程序迭代保持模型内部的封闭集合 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramIterationClosedSet

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramIteration
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[n,S,R]；内部全称量词遍历初始状态和实际输出。 -/
def kept_m : Formula signature_m [] [.num, .set, .set] :=
  .forallE .num (.forallE .num (.imp
    (.rel .mem (.cons (.bvar (.there .here)) (.cons (.fvar (.there .here)) .nil)))
    (.imp (output_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.fvar .here) (.bvar .here))
      (.rel .mem (.cons (.bvar .here) (.cons (.fvar (.there .here)) .nil))))))

theorem kept_language_m : language_m kept_m = true := pure_language_m _ rfl

theorem kept_syntax_l (R S : set_l ℳ) (n : num_l ℳ) :
    kept_m.satisfies ((((Env.empty (M := ℳ)).pushFree R).pushFree S).pushFree n) ↔
      ∀ x y, mem_l x S → relation_l R (value_l x n) y → mem_l y S := by
  simp only [kept_m, Formula.satisfies, output_syntax_l, Arguments.eval]
  rfl

/-- 只对实际内部集合做公式归纳，不将任意宿主性质作为归纳模式。 -/
theorem repeat_mem_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C S : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R)
    (hC : graph_semantics_l (graph_m c) C)
    (hS : ∀ x y, mem_l x S → relation_l C x y → mem_l y S)
    {x y n : num_l ℳ} (hx : mem_l x S) (hy : relation_l R (value_l x n) y) : mem_l y S := by
  have h (n : num_l ℳ) : ∀ x y, mem_l x S → relation_l R (value_l x n) y → mem_l y S := by
    apply induct_l hℳ kept_m kept_language_m (((Env.empty (M := ℳ)).pushFree R).pushFree S)
      (fun n => ∀ x y, mem_l x S → relation_l R (value_l x n) y → mem_l y S)
      (kept_syntax_l R S) ?_ ?_ n
    · intro x y hx hy
      exact ((repeat_zero_l hℳ c hR x y).mp hy) ▸ hx
    · intro n ih x y hx hy
      obtain ⟨z, hz, hzy⟩ := (repeat_succ_l hℳ c hR hC x n y).mp hy
      exact hS z y (ih x z hx hz) hzy
  exact h n x y hx hy

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramIterationClosedSet
