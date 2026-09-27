import BMSConstructibleBridge.SecondOrderProgramCopyIncrease
import BMSConstructibleBridge.SecondOrderProgramConditionalValue

/-!
# 原 copyBlock 的双 Option 数值分支

输入 pair value (pair copyNumber (pair firstOption lastOption))，Option 使用原编码。
任一项缺失均保留原值；两项都存在才去掉后继壳并执行原增量。这是 ascending 成功
之后的完整数值分支，外层上升条件仍须由原祖先程序判定，不能据此宣称完整 copyBlock。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyOptional

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramConditional (branch_m branch_eval_l)
open SecondOrderProgramConditionalValue (branch_value_l)
open SecondOrderProgramListCode (pred_m pred_eval_l pred_succ_l)
open SecondOrderProgramCopyIncrease (increase_m increase_eval_l increase_rel_l)
open SecondOrderProgramSubtraction (sub_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原首列可选项，零代表缺失而非合法数值零。 -/
def first_m : code_m := .comp (.comp .left .right) .right

/-- 原末列可选项。 -/
def last_m : code_m := .comp (.comp .right .right) .right

/-- 两个非零 Option 码取前驱，其他数值参数不变。 -/
def input_m : code_m := .pair .left (.pair (.comp .left .right)
  (.pair (.comp pred_m first_m) (.comp pred_m last_m)))

/-- 两项存在时才使用的原增量分支。 -/
def present_m : code_m := .comp increase_m input_m

/-- 缺任一项时保留原值，不把 none 当作数值零参加减法。 -/
def update_m : code_m := branch_m first_m (branch_m last_m present_m .left) .left

/-- 标准输入的两个可选码读取。 -/
theorem options_eval_l (v k f l : Nat) :
    eval_l first_m (Nat.pair v (Nat.pair k (Nat.pair f l))) = f ∧
    eval_l last_m (Nat.pair v (Nat.pair k (Nat.pair f l))) = l := by
  simp only [first_m, last_m, eval_l, Nat.unpair_pair, and_self]

/-- 同时存在时，原后继壳被准确去掉。 -/
theorem present_eval_l (v k f l : Nat) :
    eval_l present_m (Nat.pair v (Nat.pair k (Nat.pair (f + 1) (l + 1)))) = v + k * (l - f) := by
  change eval_l increase_m (eval_l input_m
    (Nat.pair v (Nat.pair k (Nat.pair (f + 1) (l + 1))))) = _
  have hi : eval_l input_m (Nat.pair v (Nat.pair k (Nat.pair (f + 1) (l + 1)))) =
      Nat.pair v (Nat.pair k (Nat.pair f l)) := by
    simp only [input_m, eval_l, Nat.unpair_pair, (options_eval_l v k (f + 1) (l + 1)).1,
      (options_eval_l v k (f + 1) (l + 1)).2, pred_eval_l, Nat.pred_succ]
  rw [hi, increase_eval_l]

/-- 逐标准 Option 输入等于原 copyBlock 数值分支，包括 some 0 与 none 的区别。 -/
theorem update_encode_l (v k : Nat) (f l : Option Nat) :
    eval_l update_m (Nat.pair v (Nat.pair k (Nat.pair (Encodable.encode f) (Encodable.encode l)))) =
      match f, l with
      | some a, some b => v + k * (b - a)
      | _, _ => v := by
  rw [update_m, branch_eval_l, (options_eval_l v k (Encodable.encode f) (Encodable.encode l)).1]
  cases f with
  | none =>
      simp only [show Encodable.encode (none : Option Nat) = 0 from rfl, eval_l, Nat.unpair_pair]
      rfl
  | some f =>
      rw [show Encodable.encode (some f) = f + 1 from rfl, if_neg (Nat.add_one_ne_zero f),
        branch_eval_l, (options_eval_l v k (f + 1) (Encodable.encode l)).2]
      cases l with
      | none =>
          simp only [show Encodable.encode (none : Option Nat) = 0 from rfl, eval_l, Nat.unpair_pair]
          rfl
      | some l =>
          rw [show Encodable.encode (some l) = l + 1 from rfl, if_neg (Nat.add_one_ne_zero l), present_eval_l]

/-- 所有内部可选码上的完整分支规格；去壳仍调用真实前驱图。 -/
theorem update_rel_l (hℳ : Theory.Models ℳ theory_m) {U I P : set_l ℳ}
    (hU : graph_semantics_l (graph_m update_m) U)
    (hI : graph_semantics_l (graph_m increase_m) I)
    (hP : graph_semantics_l (graph_m pred_m) P) (v k f l y : num_l ℳ) :
    relation_l U (value_l v (value_l k (value_l f l))) y ↔
      (f = zero_l ℳ ∧ v = y) ∨ (f ≠ zero_l ℳ ∧ l = zero_l ℳ ∧ v = y) ∨
        (f ≠ zero_l ℳ ∧ l ≠ zero_l ℳ ∧ ∃ a b,
          relation_l P f a ∧ relation_l P l b ∧ relation_l I (value_l v (value_l k (value_l a b))) y) := by
  classical
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ increase_m hI
  obtain ⟨p, hp, _⟩ := value_exists_l hℳ pred_m hP
  have hf : value_spec_l first_m _ :=
    comp_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)) (right_value_l hℳ)
  have hl : value_spec_l last_m _ :=
    comp_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (right_value_l hℳ)
  have hi : value_spec_l input_m _ := pair_value_l hℳ (left_value_l hℳ)
    (pair_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ))
      (pair_value_l hℳ (comp_value_l hℳ hp hf) (comp_value_l hℳ hp hl)))
  have hu := (branch_value_l hℳ hf
    (branch_value_l hℳ hl (comp_value_l hℳ hg hi) (left_value_l hℳ)) (left_value_l hℳ))
    hU (value_l v (value_l k (value_l f l))) y
  simp only [SecondOrderUnpairing.unpair_l] at hu
  rw [hu]
  simp only [hp hP, hg hI]
  by_cases hfz : f = zero_l ℳ <;> by_cases hlz : l = zero_l ℳ <;> simp [hfz, hlz]

/-- 任一内部项缺失时，实际输出恰为原值。 -/
theorem update_none_l (hℳ : Theory.Models ℳ theory_m) {U : set_l ℳ}
    (hU : graph_semantics_l (graph_m update_m) U) (v k f l y : num_l ℳ)
    (h : f = zero_l ℳ ∨ l = zero_l ℳ) :
    relation_l U (value_l v (value_l k (value_l f l))) y ↔ v = y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ increase_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ pred_m
  rw [update_rel_l hℳ hU hI hP]
  classical
  rcases h with h | h
  · simp [h]
  · by_cases hf : f = zero_l ℳ <;> simp [h, hf]

/-- 两项存在的任意内部数值上，输出精确是原值加同一截断差值的复制倍数。 -/
theorem update_some_l (hℳ : Theory.Models ℳ theory_m) {U D : set_l ℳ}
    (hU : graph_semantics_l (graph_m update_m) U)
    (hD : graph_semantics_l (graph_m sub_m) D) (v k f l y : num_l ℳ) :
    relation_l U (value_l v (value_l k (value_l (succ_l f) (succ_l l)))) y ↔
      ∃ d, relation_l D (value_l l f) d ∧ add_l v (mul_l k d) = y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ increase_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ pred_m
  rw [update_rel_l hℳ hU hI hP]
  simpa [nonzero_l hℳ f, nonzero_l hℳ l, pred_succ_l hℳ hP] using
    increase_rel_l hℳ hI hD v k f l y

#print axioms first_m
#print axioms last_m
#print axioms input_m
#print axioms present_m
#print axioms update_m
#print axioms options_eval_l
#print axioms present_eval_l
#print axioms update_encode_l
#print axioms update_rel_l
#print axioms update_none_l
#print axioms update_some_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyOptional
