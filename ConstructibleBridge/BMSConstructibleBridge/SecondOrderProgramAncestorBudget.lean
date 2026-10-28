import BMSConstructibleBridge.SecondOrderProgramAncestorBoundary
import BMSConstructibleBridge.SecondOrderProgramLength

/-!
# 原祖先累计表的内部长度预算

同一原祖先步每次至多接入一个父节点。用实际公式归纳证明：从空累计表起，
任意内部fuel后的状态仍保留同一参数，其累计表的真实长度不超过fuel。fuel、
当前列以及累计表均可非标准；不以宿主List的有限长度代替内部证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorBudget

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l step_some_l)
open SecondOrderProgramListShift (output_m output_syntax_l length_cons_l)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListIteration (iterate_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原状态配对的实际公式模板，不增加三元配对原语。 -/
def state_m {Γ Δ : SortContext signature_m} (x k v s : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num (.conj
      (PrimitiveFormulas.pair_m (k.weakenBound sort_m.num) (v.weakenBound sort_m.num) (.bvar .here))
      (PrimitiveFormulas.pair_m (x.weakenBound sort_m.num) (.bvar .here) (s.weakenBound sort_m.num)))

/-- 状态公式精确对应保留参数的原嵌套配对。 -/
theorem state_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (x k v s : Term signature_m Γ Δ .num) :
    Formula.satisfies η (state_m x k v s) ↔ value_l (x.eval η) (value_l (k.eval η) (v.eval η)) = s.eval η := by
  simp only [state_m, Formula.satisfies, SecondOrderPairing.formula_l, Term.eval_weakenBound]
  change (∃ q, value_l (k.eval η) (v.eval η) = q ∧ value_l (x.eval η) q = s.eval η) ↔ _
  simp only [exists_eq_left']

/-- 原迭代图中存在同参数状态，累计表的原length输出不超过fuel。 -/
def budget_l (R L : set_l ℳ) (s x n : num_l ℳ) : Prop := ∃ u k v m,
  relation_l R (value_l s n) u ∧ value_l x (value_l k v) = u ∧
    relation_l L v m ∧ (m = n ∨ SecondOrderOrder.lt_l m n)

/-- 自由槽[n,s,x,R,L]，绑定槽依次状态u、当前列k、累计码v、长度m。 -/
def budget_m : Formula signature_m [] [.num, .num, .num, .set, .set] :=
  .existsE .num (.existsE .num (.existsE .num (.existsE .num (.conj
    (output_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)) (.fvar .here)
      (.bvar (.there (.there (.there .here)))))
    (.conj (state_m (.fvar (.there (.there .here))) (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar (.there (.there (.there .here)))))
      (.conj (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here)))))
        (.bvar (.there .here)) (.bvar .here))
        (.disj (.equal (.bvar .here) (.fvar .here))
          (PrimitiveFormulas.lt_m (.bvar .here) (.fvar .here)))))))))

/-- 预算不变量属于原纯算术语言。 -/
theorem budget_language_m : language_m budget_m = true := pure_language_m _ rfl

/-- 真实归纳公式不改变原迭代图、长度图、初始状态或外层参数。 -/
theorem budget_syntax_l (R L : set_l ℳ) (s x n : num_l ℳ) :
    Formula.satisfies ((((((Env.empty (M := ℳ)).pushFree L).pushFree R).pushFree x).pushFree s).pushFree n)
      budget_m ↔ budget_l R L s x n := by
  simp only [budget_m, budget_l, Formula.satisfies, output_syntax_l, state_syntax_l,
    SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
  rfl

/-- 任意内部fuel的长度预算，由实际预算公式逐步归纳获得。 -/
theorem budget_invariant_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R L : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hL : graph_semantics_l (graph_m length_m) L) (x k n : num_l ℳ) :
    budget_l R L (value_l x (value_l k (zero_l ℳ))) x n := by
  letI := order_l hℳ
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (step_m c)
  obtain ⟨C, hCf, hC⟩ := graph_total_l hℳ c
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  apply induct_l hℳ budget_m budget_language_m
    (((((Env.empty (M := ℳ)).pushFree L).pushFree R).pushFree x).pushFree
      (value_l x (value_l k (zero_l ℳ))))
    (fun n => budget_l R L (value_l x (value_l k (zero_l ℳ))) x n)
    (budget_syntax_l R L (value_l x (value_l k (zero_l ℳ))) x) ?_ ?_ n
  · exact ⟨_, k, zero_l ℳ, zero_l ℳ,
      (repeat_zero_l hℳ (step_m c) hR _ _).mpr rfl, rfl,
      (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl), Or.inl rfl⟩
  · rintro j ⟨u, t, v, m, hr, he, hl, hm⟩
    subst u
    obtain ⟨q, hq, _⟩ := hCf (value_l x t)
    rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
    · exact ⟨_, t, v, m,
        (repeat_succ_l hℳ (step_m c) hR hS _ j _).mpr
          ⟨_, hr, (step_none_l hℳ c hS hC hq v _).mpr rfl⟩, rfl, hl,
        Or.inr (lt_of_le_of_lt (show m ≤ j from hm) (lt_own_succ_l hℳ j))⟩
    · refine ⟨_, p, succ_l (value_l p v), succ_l m,
        (repeat_succ_l hℳ (step_m c) hR hS _ j _).mpr
          ⟨_, hr, (step_some_l hℳ c hS hC hq v _).mpr rfl⟩, rfl, ?_, ?_⟩
      · exact (length_rel_l hℳ hL hI _ _).mpr
          ((length_cons_l hℳ hI p v m).mpr ((length_rel_l hℳ hL hI v m).mp hl))
      · rcases hm with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ((SecondOrderOrder.succ_iff_l hℳ m j).mpr hlt)

/-- 任意给定的原迭代输出也满足同参数和真实累计长度预算。 -/
theorem output_budget_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R L : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hL : graph_semantics_l (graph_m length_m) L) {x k n u : num_l ℳ}
    (hu : relation_l R (value_l (value_l x (value_l k (zero_l ℳ))) n) u) :
    ∃ t v m, u = value_l x (value_l t v) ∧ relation_l L v m ∧
      (m = n ∨ SecondOrderOrder.lt_l m n) := by
  obtain ⟨s, t, v, m, hs, he, hl, hm⟩ := budget_invariant_l hℳ c hR hL x k n
  have hsu := function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m c)) hR) hs hu
  exact ⟨t, v, m, hsu.symm.trans he.symm, hl, hm⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorBudget
