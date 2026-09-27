import BMSConstructibleBridge.SecondOrderProgramParentRowState
import BMSConstructibleBridge.SecondOrderProgramUniformParent

/-!
# 原父表迭代在所有内部步数上的状态不变量

原数组不变，行槽增加实际迭代次数，父表与原数组等宽。归纳使用下面实际纯公式，
而不是对模型内部步数执行宿主Nat归纳。表项正确性和严格下降未包含在宽度不变量中。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRowIteration

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramParentRow (step_m initial_m)
open SecondOrderProgramParentRowState (step_width_l initial_width_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 含原数组x、下一行r及宽度n的完整状态。 -/
def state_l (L : set_l ℳ) (x r n y : num_l ℳ) : Prop :=
  ∃ v, y = value_l x (value_l r v) ∧ relation_l L v n

/-- 状态的实际纯模板；中间配对值仍用数量词及原配对关系表示。 -/
def state_m {Γ Δ : SortContext signature_m} (L : Term signature_m Γ Δ .set)
    (x r n y : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (twice_m r) (.bvar (.there .here)) (.bvar .here))
    (.conj (PrimitiveFormulas.pair_m (twice_m x) (.bvar .here) (twice_m y))
      (GraphSyntax.edge_m ((L.weakenBound sort_m.num).weakenBound sort_m.num)
        (.bvar (.there .here)) (twice_m n)))))

/-- 真实模板逐环境等于状态规格，无额外模型假设。 -/
theorem state_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (L : Term signature_m Γ Δ .set) (x r n y : Term signature_m Γ Δ .num) :
    Formula.satisfies η (state_m L x r n y) ↔
      state_l (L.eval η) (x.eval η) (r.eval η) (n.eval η) (y.eval η) := by
  simp only [state_m, state_l, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, twice_m, Term.eval_weakenBound]
  change (∃ v p, value_l (r.eval η) v = p ∧ value_l (x.eval η) p = y.eval η ∧
      relation_l (L.eval η) v (n.eval η)) ↔ _
  apply exists_congr
  intro v
  constructor
  · rintro ⟨p, rfl, hy, hn⟩
    exact ⟨hy.symm, hn⟩
  · rintro ⟨hy, hn⟩
    exact ⟨_, rfl, hy.symm, hn⟩

/-- 自由槽k,s,x,r,n,R,L：从s迭代k次的实际输出有行槽r+k及相同宽度n。 -/
def invariant_m : Formula signature_m [] [.num, .num, .num, .num, .num, .set, .set] :=
  .existsE .num (.conj
    (output_m (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (state_m (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there .here)))
      (Term.app (σ := signature_m) .add
        (.cons (.fvar (.there (.there (.there .here)))) (.cons (.fvar .here) .nil)))
      (.fvar (.there (.there (.there (.there .here))))) (.bvar .here)))

/-- 原归纳所用的完整公式属于纯算术语言。 -/
theorem invariant_language_m : language_m invariant_m = true := pure_language_m _ rfl

/-- 模板的自由槽次序在归纳前完整核验。 -/
theorem invariant_syntax_l (R L : set_l ℳ) (s x r n k : num_l ℳ) :
    Formula.satisfies
      ((((((((Env.empty (M := ℳ)).pushFree L).pushFree R).pushFree n).pushFree r).pushFree x).pushFree s).pushFree k)
      invariant_m ↔
      ∃ y, relation_l R (value_l s k) y ∧ state_l L x (add_l r k) n y := by
  simp only [invariant_m, Formula.satisfies, output_syntax_l, state_syntax_l]
  rfl

/-- 内部次数归纳给出实际输出及状态不变量，不假定步数为标准数码。 -/
theorem repeat_exists_l (hℳ : Theory.Models ℳ theory_m) {R L : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m step_m)) R)
    (hL : graph_semantics_l (graph_m length_m) L) {s x r n : num_l ℳ}
    (hn : relation_l L x n) (hs : state_l L x r n s) (k : num_l ℳ) :
    ∃ y, relation_l R (value_l s k) y ∧ state_l L x (add_l r k) n y := by
  obtain ⟨S, hSf, hS⟩ := graph_total_l hℳ step_m
  apply induct_l hℳ invariant_m invariant_language_m
    (((((((Env.empty (M := ℳ)).pushFree L).pushFree R).pushFree n).pushFree r).pushFree x).pushFree s)
    (fun k => ∃ y, relation_l R (value_l s k) y ∧ state_l L x (add_l r k) n y)
    (invariant_syntax_l R L s x r n) ?_ ?_ k
  · refine ⟨s, (repeat_zero_l hℳ step_m hR s s).mpr rfl, ?_⟩
    simpa only [add_zero_l hℳ] using hs
  · rintro i ⟨y, hy, v, hyv, _⟩
    obtain ⟨z, hz, _⟩ := hSf y
    have hzv := hz
    rw [hyv] at hzv
    obtain ⟨w, hzw, hwidth⟩ := step_width_l hℳ hS hL hn hzv
    refine ⟨z, (repeat_succ_l hℳ step_m hR hS s i z).mpr ⟨y, hy, hz⟩, w, ?_, hwidth⟩
    simpa only [add_succ_l hℳ] using hzw

/-- 原图的任意输出都满足不变量，由实际程序函数性消去存在输出的选择。 -/
theorem repeat_state_l (hℳ : Theory.Models ℳ theory_m) {R L : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m step_m)) R)
    (hL : graph_semantics_l (graph_m length_m) L) {s x r n k y : num_l ℳ}
    (hn : relation_l L x n) (hs : state_l L x r n s) (hy : relation_l R (value_l s k) y) :
    state_l L x (add_l r k) n y := by
  obtain ⟨z, hz, hstate⟩ := repeat_exists_l hℳ hR hL hn hs k
  exact (function_value_unique_l (function_of_semantics_l hℳ (repeat_m step_m) hR) hz hy) ▸ hstate

#print axioms state_l
#print axioms state_m
#print axioms state_syntax_l
#print axioms invariant_m
#print axioms invariant_language_m
#print axioms invariant_syntax_l
#print axioms repeat_exists_l
#print axioms repeat_state_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRowIteration
