import BMSConstructibleBridge.SecondOrderProgramRun
import BMSConstructibleBridge.SecondOrderListInduction
import BMSConstructibleBridge.SecondOrderProgramListShift

/-!
# 原生成轨迹保留对展开封闭的内部集合

归纳性质必须来自下述实际纯公式：对于该轨迹的每个内部初值及实际输出，
属于S的初值仍产生属于S的输出。S是同一模型中的集合，不允许任意外部性质归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRunClosedSet

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramRun (run_m run_zero_l run_cons_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[轨迹t,内部集合S,R]；先绑定任意初值v，再绑定实际输出y。 -/
def kept_m : Formula signature_m [] [.num, .set, .set] :=
  .forallE .num (.forallE .num (.imp
    (.rel .mem (.cons (.bvar (.there .here)) (.cons (.fvar (.there .here)) .nil)))
    (.imp (output_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there .here)) (.bvar .here))
      (.rel .mem (.cons (.bvar .here) (.cons (.fvar (.there .here)) .nil))))))

/-- 封闭集合的轨迹保持公式仍在原纯语言中。 -/
theorem kept_language_m : language_m kept_m = true := pure_language_m _ rfl

/-- 实际公式保留同一轨迹、初值、输出和内部集合。 -/
theorem kept_syntax_l (R S : set_l ℳ) (t : num_l ℳ) :
    Formula.satisfies ((((Env.empty (M := ℳ)).pushFree R).pushFree S).pushFree t) kept_m ↔
      ∀ v y, mem_l v S → relation_l R (value_l t v) y → mem_l y S := by
  simp only [kept_m, Formula.satisfies, output_syntax_l, Arguments.eval]
  rfl

/-- 任意内部轨迹的原run输出都保留对原展开封闭的内部集合性质。 -/
theorem run_mem_l (hℳ : Theory.Models ℳ theory_m) {R X S : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hclosed : ∀ v i w : num_l ℳ, mem_l v S → relation_l X (value_l v i) w → mem_l w S)
    {t v y : num_l ℳ} (hv : mem_l v S) (hy : relation_l R (value_l t v) y) : mem_l y S := by
  have hall (t : num_l ℳ) : ∀ v y, mem_l v S → relation_l R (value_l t v) y → mem_l y S := by
    apply SecondOrderListInduction.list_induct_l hℳ kept_m kept_language_m
      (((Env.empty (M := ℳ)).pushFree R).pushFree S)
      (fun t => ∀ v y, mem_l v S → relation_l R (value_l t v) y → mem_l y S)
      (kept_syntax_l R S) ?_ ?_ t
    · intro v y hv hy
      exact ((run_zero_l hℳ hR v y).mp hy) ▸ hv
    · intro i t ih v y hv hy
      obtain ⟨w, hw, ht⟩ := (run_cons_l hℳ hR hX i t v y).mp hy
      exact ih w y (hclosed v i w hv hw) ht
  exact hall t v y hv hy

#print axioms kept_m
#print axioms kept_language_m
#print axioms kept_syntax_l
#print axioms run_mem_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRunClosedSet
