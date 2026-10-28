import BMSConstructibleBridge.SecondOrderProgramParentOrder

/-!
# 原祖先迭代的内部燃料充分性

当原parent图的some输出严格减小列号时，以起始列b为燃料已经到达none。
真实公式归纳保持“已停止，或当前列加已用步数不超过b”，故结论也适用于
非标准内部b；不使用宿主自然数归纳或外部良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorTermination

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l step_some_l)
open SecondOrderProgramAncestorBudget (state_m state_syntax_l)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 若当前尚有parent，已用步数与剩余列号之和受到原初始列的约束。 -/
def fuel_l (R C : set_l ℳ) (s x b n : num_l ℳ) : Prop := ∃ u t v,
  relation_l R (value_l s n) u ∧ value_l x (value_l t v) = u ∧
    (relation_l C (value_l x t) (zero_l ℳ) ∨
      add_l t n = b ∨ SecondOrderOrder.lt_l (add_l t n) b)

/-- 自由槽[n,s,x,b,R,C]；绑定槽[u,t,v]保留同一真实迭代状态。 -/
def fuel_m : Formula signature_m [] [.num, .num, .num, .num, .set, .set] :=
  let n : Term signature_m [.num, .num, .num] _ .num := .fvar .here
  let x : Term signature_m [.num, .num, .num] _ .num := .fvar (.there (.there .here))
  let b : Term signature_m [.num, .num, .num] _ .num := .fvar (.there (.there (.there .here)))
  let t : Term signature_m [.num, .num, .num] _ .num := .bvar (.there .here)
  let sum := Term.app (σ := signature_m) .add (.cons t (.cons n .nil))
  .existsE .num (.existsE .num (.existsE .num (.conj
    (output_m (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here)) n
      (.bvar (.there (.there .here))))
    (.conj (state_m x t (.bvar .here) (.bvar (.there (.there .here))))
      (.disj (output_m (.fvar (.there (.there (.there (.there (.there .here)))))) x t
        (Term.app (σ := signature_m) .zero .nil))
        (.disj (.equal sum b) (PrimitiveFormulas.lt_m sum b)))))))

/-- 停止或燃料界不变量是原内部归纳所允许的真实算术公式。 -/
theorem fuel_language_m : language_m fuel_m = true := pure_language_m _ rfl

/-- 公式解释准确保留原parent图与迭代图，没有附加标准性。 -/
theorem fuel_syntax_l (R C : set_l ℳ) (s x b n : num_l ℳ) :
    Formula.satisfies (((((((Env.empty (M := ℳ)).pushFree C).pushFree R).pushFree b).pushFree x).pushFree s).pushFree n)
      fuel_m ↔ fuel_l R C s x b n := by
  simp only [fuel_m, fuel_l, Formula.satisfies, output_syntax_l, state_syntax_l,
    SecondOrderOrder.formula_l]
  rfl

/-- 每次有效步至少消耗一个列号；none步保持整个状态和停止证据。 -/
theorem fuel_invariant_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hC : graph_semantics_l (graph_m c) C) (x b v n : num_l ℳ)
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t) :
    fuel_l R C (value_l x (value_l b v)) x b n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (step_m c)
  apply induct_l hℳ fuel_m fuel_language_m
    ((((((Env.empty (M := ℳ)).pushFree C).pushFree R).pushFree b).pushFree x).pushFree
      (value_l x (value_l b v)))
    (fun n => fuel_l R C (value_l x (value_l b v)) x b n)
    (fuel_syntax_l R C (value_l x (value_l b v)) x b) ?_ ?_ n
  · exact ⟨_, b, v, (repeat_zero_l hℳ (step_m c) hR _ _).mpr rfl,
      rfl, Or.inr (Or.inl (add_zero_l hℳ b))⟩
  · rintro j ⟨u, t, w, hr, he, ht⟩
    subst u
    obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ c hC (value_l x t)
    rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
    · exact ⟨_, t, w, (repeat_succ_l hℳ (step_m c) hR hS _ j _).mpr
        ⟨_, hr, (step_none_l hℳ c hS hC hq w _).mpr rfl⟩, rfl, Or.inl hq⟩
    · have hbound : add_l t j ≤ b := by
        rcases ht with hz | ht
        · exact False.elim (nonzero_l hℳ p
            (function_value_unique_l (function_of_semantics_l hℳ c hC) hq hz))
        · exact ht
      have hp : succ_l p ≤ t := by
        simpa only [succ_eq_l hℳ] using (lt_iff_add_one_le_l hℳ p t).mp (hparent t p hq)
      have hnext : add_l p (succ_l j) ≤ b := calc
        add_l p (succ_l j) = add_l (succ_l p) j := by
          rw [add_succ_l hℳ, SecondOrderNumbers.succ_add_l hℳ]
        _ ≤ add_l t j := by
          change succ_l p + j ≤ t + j
          simpa only [add_comm] using (add_le_add_right hp j)
        _ ≤ b := hbound
      exact ⟨_, p, succ_l (value_l p w),
        (repeat_succ_l hℳ (step_m c) hR hS _ j _).mpr
          ⟨_, hr, (step_some_l hℳ c hS hC hq w _).mpr rfl⟩, rfl, Or.inr hnext⟩

/-- 起始列b步后已停止；输出状态通过原图函数性与归纳见证对齐。 -/
theorem output_terminal_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hC : graph_semantics_l (graph_m c) C) {x b v u : num_l ℳ}
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hu : relation_l R (value_l (value_l x (value_l b v)) b) u) :
    ∃ t w, u = value_l x (value_l t w) ∧ relation_l C (value_l x t) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  obtain ⟨s, t, w, hs, he, ht⟩ := fuel_invariant_l hℳ c hR hC x b v b hparent
  have hsu := function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m c)) hR) hs hu
  refine ⟨t, w, hsu.symm.trans he.symm, ?_⟩
  rcases ht with ht | ht
  · exact ht
  · have ht0 : t ≤ (0 : num_l ℳ) := (add_le_add_iff_right b).mp
      (by simpa only [zero_add] using (show t + b ≤ b from ht))
    have he0 : t = zero_l ℳ := le_antisymm ht0 (zero_le_l hℳ t)
    obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ c hC (value_l x t)
    rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
    · exact hq
    · have hpt := hparent t p hq
      rw [he0] at hpt
      exact False.elim ((not_lt_of_ge (zero_le_l hℳ p)) hpt)

/-- 每个固定外部行号的真实parent均已消去局部下降前提。 -/
theorem parent_terminal_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) {R P : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m (SecondOrderProgramParentSuccessor.parent_m r)))) R)
    (hP : graph_semantics_l (graph_m (SecondOrderProgramParentSuccessor.parent_m r)) P)
    {x b v u : num_l ℳ} (hu : relation_l R (value_l (value_l x (value_l b v)) b) u) :
    ∃ t w, u = value_l x (value_l t w) ∧ relation_l P (value_l x t) (zero_l ℳ) :=
  output_terminal_l hℳ (SecondOrderProgramParentSuccessor.parent_m r) hR hP
    (fun _ _ hp => SecondOrderProgramParentOrder.parent_lt_l hℳ r hP hp) hu

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorTermination
