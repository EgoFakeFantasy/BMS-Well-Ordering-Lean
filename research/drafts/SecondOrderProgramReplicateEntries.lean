import BMSConstructibleBridge.SecondOrderProgramReplicate
import BMSConstructibleBridge.SecondOrderProgramListLookup

/-!
# 重复列的全部内部条目

补足重复列的内容规格：任何小于内部长度的内部下标都读出指定元素。证明使用
同一重复程序、同一读取程序和真实算术归纳公式；不从宿主 `List.replicate` 的
标准正确性推断非标准模型结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramReplicateEntries

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramArithmetic SecondOrderProgramListShift SecondOrderProgramListLookup
open SecondOrderProgramReplicate
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽 `[n,a,R,E]`，绑定槽先输出 `x` 再下标 `j`；只约束 `j < n`。 -/
def entries_m : Formula signature_m [] [.num, .num, .set, .set] :=
  .forallE .num (.imp
    (output_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (.forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar .here))
      (output_m (.fvar (.there (.there (.there .here)))) (.bvar (.there .here))
        (.bvar .here) (.fvar (.there .here))))))

/-- 内部条目不变量属于原纯算术语言。 -/
theorem entries_language_m : language_m entries_m = true := pure_language_m _ rfl

/-- 实际公式量化全部内部输出与下标，没有外部有限列表假设。 -/
theorem entries_syntax_l (R E : set_l ℳ) (a n : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree E).pushFree R).pushFree a).pushFree n)
      entries_m ↔ ∀ x, relation_l R (value_l a n) x →
        ∀ j, SecondOrderOrder.lt_l j n → relation_l E (value_l x j) a := by
  simp only [entries_m, Formula.satisfies, output_syntax_l, SecondOrderOrder.formula_l]
  rfl

/-- 原重复列图的任意输出，其所有合法位置都返回指定元素。 -/
theorem replicate_entries_l (hℳ : Theory.Models ℳ theory_m) {R E : set_l ℳ}
    (hR : graph_semantics_l (graph_m replicate_m) R)
    (hE : graph_semantics_l (graph_m lookup_m) E) (a n : num_l ℳ) :
    ∀ x, relation_l R (value_l a n) x →
      ∀ j, SecondOrderOrder.lt_l j n → relation_l E (value_l x j) a := by
  apply induct_l hℳ entries_m entries_language_m
    ((((Env.empty (M := ℳ)).pushFree E).pushFree R).pushFree a)
    (fun n => ∀ x, relation_l R (value_l a n) x →
      ∀ j, SecondOrderOrder.lt_l j n → relation_l E (value_l x j) a)
    (entries_syntax_l R E a) ?_ ?_ n
  · intro x _ j hj
    letI := order_l hℳ
    exact False.elim ((not_lt_of_ge (zero_le_l hℳ j)) hj)
  · intro k ih x hx j hj
    obtain ⟨v, hv, rfl⟩ := (replicate_succ_l hℳ hR a k x).mp hx
    rcases predecessor_l hℳ j with rfl | ⟨i, rfl⟩
    · exact (lookup_cons_zero_l hℳ hE a v a).mpr rfl
    · exact (lookup_cons_succ_l hℳ hE a v i a).mpr
        (ih v hv i ((SecondOrderOrder.succ_iff_l hℳ i k).mp hj))

/-- 合法位置的完整读取规格；排除读取图的其他输出由原程序函数性给出。 -/
theorem replicate_lookup_l (hℳ : Theory.Models ℳ theory_m) {R E : set_l ℳ}
    (hR : graph_semantics_l (graph_m replicate_m) R)
    (hE : graph_semantics_l (graph_m lookup_m) E) {a n x j : num_l ℳ}
    (hx : relation_l R (value_l a n) x) (hj : SecondOrderOrder.lt_l j n) (y : num_l ℳ) :
    relation_l E (value_l x j) y ↔ a = y := by
  have ha := replicate_entries_l hℳ hR hE a n x hx j hj
  constructor
  · exact function_value_unique_l (function_of_semantics_l hℳ lookup_m hE) ha
  · intro h
    exact h ▸ ha

#print axioms entries_m
#print axioms entries_language_m
#print axioms entries_syntax_l
#print axioms replicate_entries_l
#print axioms replicate_lookup_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramReplicateEntries
