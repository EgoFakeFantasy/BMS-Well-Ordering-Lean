import BMSConstructibleBridge.SecondOrderProgramAncestorBudget
import BMSConstructibleBridge.SecondOrderProgramListEntryBound

/-!
# 原祖先累计表中的列号严格界

假定给定原parent图的每个some输出都小于输入列号，用真实内部归纳证明：
从初始列b出发，当前列始终不超过b，累计表的每个有效内部位置严格小于b。
该parent假设是待由具体parent程序消去的局部算法规格，不是良序性假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l step_some_l)
open SecondOrderProgramAncestorBudget (state_m state_syntax_l)
open SecondOrderProgramListEntryBound
open SecondOrderProgramListShift (output_m output_syntax_l length_cons_l)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同参数迭代状态、真实累计长度、当前列界及全部有效条目的严格界。 -/
def ordered_l (R L E : set_l ℳ) (s x b n : num_l ℳ) : Prop := ∃ u t v m,
  relation_l R (value_l s n) u ∧ value_l x (value_l t v) = u ∧ relation_l L v m ∧
    (t = b ∨ SecondOrderOrder.lt_l t b) ∧ below_l E v m b

/-- 自由槽[n,s,x,b,R,L,E]；四个绑定槽依次为状态u、当前列t、累计码v、长度m。 -/
def ordered_m : Formula signature_m [] [.num, .num, .num, .num, .set, .set, .set] :=
  .existsE .num (.existsE .num (.existsE .num (.existsE .num (.conj
    (output_m (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here)) (.fvar .here)
      (.bvar (.there (.there (.there .here)))))
    (.conj (state_m (.fvar (.there (.there .here))) (.bvar (.there (.there .here)))
      (.bvar (.there .here)) (.bvar (.there (.there (.there .here)))))
      (.conj (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there .here)) (.bvar .here))
        (.conj (.disj (.equal (.bvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))))
          (PrimitiveFormulas.lt_m (.bvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))))
          (below_m (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
            (.bvar (.there .here)) (.bvar .here) (.fvar (.there (.there (.there .here))))))))))))

/-- 原语言允许该算术图不变量作为内部归纳正文。 -/
theorem ordered_language_m : language_m ordered_m = true := pure_language_m _ rfl

/-- 实际公式精确对应列号界，不引入外部标准性限制。 -/
theorem ordered_syntax_l (R L E : set_l ℳ) (s x b n : num_l ℳ) :
    Formula.satisfies ((((((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree R).pushFree b).pushFree x).pushFree s).pushFree n)
      ordered_m ↔ ordered_l R L E s x b n := by
  simp only [ordered_m, ordered_l, Formula.satisfies, output_syntax_l, state_syntax_l,
    SecondOrderPairing.edge_l, SecondOrderOrder.formula_l, below_syntax_l]
  rfl

/-- 原parent严格下降时，任意内部fuel后的当前列和全部祖先条目保留初始列界。 -/
theorem ordered_invariant_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R L E C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hC : graph_semantics_l (graph_m c) C) (x b n : num_l ℳ)
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t) :
    ordered_l R L E (value_l x (value_l b (zero_l ℳ))) x b n := by
  letI := order_l hℳ
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (step_m c)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  apply induct_l hℳ ordered_m ordered_language_m
    (((((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree R).pushFree b).pushFree x).pushFree
      (value_l x (value_l b (zero_l ℳ))))
    (fun n => ordered_l R L E (value_l x (value_l b (zero_l ℳ))) x b n)
    (ordered_syntax_l R L E (value_l x (value_l b (zero_l ℳ))) x b) ?_ ?_ n
  · exact ⟨_, b, zero_l ℳ, zero_l ℳ,
      (repeat_zero_l hℳ (step_m c) hR _ _).mpr rfl, rfl,
      (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl),
      Or.inl rfl, below_zero_l hℳ E _ b⟩
  · rintro j ⟨u, t, v, m, hr, he, hl, ht, hb⟩
    subst u
    obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ c hC (value_l x t)
    rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
    · exact ⟨_, t, v, m,
        (repeat_succ_l hℳ (step_m c) hR hS _ j _).mpr
          ⟨_, hr, (step_none_l hℳ c hS hC hq v _).mpr rfl⟩, rfl, hl, ht, hb⟩
    · have hpb : SecondOrderOrder.lt_l p b := lt_of_lt_of_le (hparent t p hq) (show t ≤ b from ht)
      exact ⟨_, p, succ_l (value_l p v), succ_l m,
        (repeat_succ_l hℳ (step_m c) hR hS _ j _).mpr
          ⟨_, hr, (step_some_l hℳ c hS hC hq v _).mpr rfl⟩, rfl,
        (length_rel_l hℳ hL hI _ _).mpr
          ((length_cons_l hℳ hI p v m).mpr ((length_rel_l hℳ hL hI v m).mp hl)),
        Or.inr hpb, below_cons_l hℳ hE hpb hb⟩

/-- 同一原迭代图的任意给定输出都满足全部有效祖先严格界。 -/
theorem output_order_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R L E C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hC : graph_semantics_l (graph_m c) C) {x b n u : num_l ℳ}
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hu : relation_l R (value_l (value_l x (value_l b (zero_l ℳ))) n) u) :
    ∃ t v m, u = value_l x (value_l t v) ∧ relation_l L v m ∧
      (t = b ∨ SecondOrderOrder.lt_l t b) ∧ below_l E v m b := by
  obtain ⟨s, t, v, m, hs, he, hl, ht, hb⟩ := ordered_invariant_l hℳ c hR hL hE hC x b n hparent
  have hsu := function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m c)) hR) hs hu
  exact ⟨t, v, m, hsu.symm.trans he.symm, hl, ht, hb⟩

#print axioms ordered_l
#print axioms ordered_m
#print axioms ordered_language_m
#print axioms ordered_syntax_l
#print axioms ordered_invariant_l
#print axioms output_order_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorOrder
