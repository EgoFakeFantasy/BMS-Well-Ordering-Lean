import BMSConstructibleBridge.SecondOrderProgramListLength

/-!
# 取尾迭代的移位与内部长度后继式

若 `tail x = t`，则从 `x` 取尾 `succ k` 次与从 `t` 取尾 `k` 次有同一输出。
证明对真实共同输出公式作模型内部归纳；它不借助外部列表、标准数假设或宿主递归。
由此给同一最小归零步长度图补上非空构造的后继式，尚非长度程序的正确性证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListShift

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListCode
open SecondOrderProgramListIteration SecondOrderProgramListLength
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原迭代图输出模板；配对仍由原纯算术公式描述。 -/
def output_m {Γ Δ : SortContext signature_m} (I : Term signature_m Γ Δ .set)
    (x k y : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (x.weakenBound sort_m.num) (k.weakenBound sort_m.num) (.bvar .here))
    (GraphSyntax.edge_m (I.weakenBound sort_m.num) (.bvar .here) (y.weakenBound sort_m.num)))

/-- 实际模板的解释就是原图在配对输入上的关系。 -/
theorem output_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (I : Term signature_m Γ Δ .set) (x k y : Term signature_m Γ Δ .num) :
    Formula.satisfies η (output_m I x k y) ↔
      relation_l (I.eval η) (value_l (x.eval η) (k.eval η)) (y.eval η) := by
  simp only [output_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, Term.eval_weakenBound]
  change (∃ q, value_l (x.eval η) (k.eval η) = q ∧ relation_l (I.eval η) q (y.eval η)) ↔ _
  simp only [exists_eq_left']

/-- 共同输出的归纳公式；自由槽 `[k, x, t, I]`，存在量词只增加输出绑定槽。 -/
def shift_m : Formula signature_m [] [.num, .num, .num, .set] :=
  .existsE .num (.conj
    (output_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here))
      (Term.app (σ := signature_m) .succ (.cons (.fvar .here) .nil)) (.bvar .here))
    (output_m (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
      (.fvar .here) (.bvar .here)))

/-- 共同输出公式属于原语言。 -/
theorem shift_language_m : language_m shift_m = true := pure_language_m _ rfl

/-- 共同输出公式与所需不变量精确对应。 -/
theorem shift_syntax_l (I : set_l ℳ) (x t k : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree I).pushFree t).pushFree x).pushFree k)
      shift_m ↔ ∃ y, relation_l I (value_l x (succ_l k)) y ∧ relation_l I (value_l t k) y := by
  simp only [shift_m, Formula.satisfies, output_syntax_l]
  rfl

/-- 对全部内部步数，两种移位输入有共同输出。只使用真实公式归纳。 -/
theorem common_output_l (hℳ : Theory.Models ℳ theory_m) {I T : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hT : graph_semantics_l (graph_m tail_m) T) (x t : num_l ℳ)
    (hxt : relation_l T x t) (k : num_l ℳ) :
    ∃ y, relation_l I (value_l x (succ_l k)) y ∧ relation_l I (value_l t k) y := by
  apply induct_l hℳ shift_m shift_language_m
    ((((Env.empty (M := ℳ)).pushFree I).pushFree t).pushFree x)
    (fun k => ∃ y, relation_l I (value_l x (succ_l k)) y ∧ relation_l I (value_l t k) y)
    (shift_syntax_l I x t) ?_ ?_ k
  · exact ⟨t,
      (iterate_succ_l hℳ hI hT x (zero_l ℳ) t).mpr
        ⟨x, (iterate_zero_l hℳ hI x x).mpr rfl, hxt⟩,
      (iterate_zero_l hℳ hI t t).mpr rfl⟩
  · rintro n ⟨v, hxv, htv⟩
    obtain ⟨w, hvw, _⟩ := function_of_semantics_l hℳ tail_m hT v
    exact ⟨w,
      (iterate_succ_l hℳ hI hT x (succ_l n) w).mpr ⟨v, hxv, hvw⟩,
      (iterate_succ_l hℳ hI hT t n w).mpr ⟨v, htv, hvw⟩⟩

/-- 图的函数性把共同输出升级为所有输出的双向移位式。 -/
theorem shift_l (hℳ : Theory.Models ℳ theory_m) {I T : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hT : graph_semantics_l (graph_m tail_m) T) (x t : num_l ℳ)
    (hxt : relation_l T x t) (k y : num_l ℳ) :
    relation_l I (value_l x (succ_l k)) y ↔ relation_l I (value_l t k) y := by
  obtain ⟨v, hxv, htv⟩ := common_output_l hℳ hI hT x t hxt k
  have hIf := function_of_semantics_l hℳ iterate_m hI
  constructor
  · intro hxy
    exact (function_value_unique_l hIf hxv hxy) ▸ htv
  · intro hty
    exact (function_value_unique_l hIf htv hty) ▸ hxv

/-- 非空构造的内部长度恰为尾码长度的后继。头码和尾码均可为非标准内部数。 -/
theorem length_cons_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (a t k : num_l ℳ) :
    length_spec_l I (succ_l (value_l a t)) (succ_l k) ↔ length_spec_l I t k := by
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ tail_m
  have htail : relation_l T (succ_l (value_l a t)) t :=
    (tail_cons_l hℳ hT a t t).mpr rfl
  have hshift := shift_l hℳ hI hT (succ_l (value_l a t)) t htail
  constructor
  · intro h
    refine ⟨(hshift k (zero_l ℳ)).mp h.1, ?_⟩
    intro j hj hz
    exact h.2 (succ_l j) ((SecondOrderOrder.succ_iff_l hℳ j k).mpr hj)
      ((hshift j (zero_l ℳ)).mpr hz)
  · intro h
    refine ⟨(hshift k (zero_l ℳ)).mpr h.1, ?_⟩
    intro j hj hz
    rcases predecessor_l hℳ j with rfl | ⟨i, rfl⟩
    · exact nonzero_l hℳ (value_l a t)
        ((iterate_zero_l hℳ hI (succ_l (value_l a t)) (zero_l ℳ)).mp hz)
    · exact h.2 i ((SecondOrderOrder.succ_iff_l hℳ i k).mp hj)
        ((hshift i (zero_l ℳ)).mp hz)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListShift
