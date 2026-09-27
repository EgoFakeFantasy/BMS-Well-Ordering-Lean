import BMSConstructibleBridge.SecondOrderProgramUniformParent
import BMSConstructibleBridge.SecondOrderProgramConditionalValue
import BMSConstructibleBridge.SecondOrderProgramOptionalCompare

/-!
# 原复制上升条件的统一程序

输入pair (pair 数组 (pair 最大行 父列)) (pair 局部列 行)，目标列为父列加局部列。
程序先检查行严格小于最大行，再检查局部列为零或严格祖先成员。输出按非零判真，
不要求真值码一定为一。标准端与原ascending相同；内部端明确用实际统一父程序
生成的祖先图，不提前假定尚待证明的非标准逐行正确性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAscending

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramConditional SecondOrderProgramConditionalValue
open SecondOrderProgramOptionalCompare (less_m less_eval_l less_zero_l)
open SecondOrderProgramUniformParent (parent_m member_encode_l)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (code_m eval_l graph_m add_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原数组码。 -/
def array_m : code_m := .comp .left .left

/-- 本次展开的最大父行。 -/
def limit_m : code_m := .comp (.comp .left .right) .left

/-- 本次复制块的原父列。 -/
def parent_column_m : code_m := .comp (.comp .right .right) .left

/-- 块内局部列下标。 -/
def local_m : code_m := .comp .left .right

/-- 原行下标。 -/
def row_m : code_m := .comp .right .right

/-- 祖先查询输入pair(pair(pair数组行)目标列)候选祖先列。 -/
def member_input_m : code_m :=
  .pair (.pair (.pair array_m row_m) (.comp add_m (.pair parent_column_m local_m))) parent_column_m

/-- 使用实际统一父程序的严格祖先测试。 -/
def member_test_m : code_m := .comp (member_m parent_m) member_input_m

/-- 非零恰好表示当前行小于本次最大父行。 -/
def below_m : code_m := .comp less_m (.pair row_m limit_m)

/-- 原上升条件；首个局部列不要求额外祖先条件。 -/
def ascending_m : code_m := branch_m below_m
  (branch_m local_m member_test_m (PrimitiveProgram.const_m 1)) .zero

/-- 标准坐标接线，明确候选为父列而目标为父列加局部列。 -/
theorem member_input_eval_l (x m p j r : Nat) :
    eval_l member_input_m (Nat.pair (Nat.pair x (Nat.pair m p)) (Nat.pair j r)) =
      Nat.pair (Nat.pair (Nat.pair x r) (p + j)) p := by
  change Nat.pair (Nat.pair
    (eval_l (.pair array_m row_m) (Nat.pair (Nat.pair x (Nat.pair m p)) (Nat.pair j r)))
    (eval_l add_m (eval_l (.pair parent_column_m local_m)
      (Nat.pair (Nat.pair x (Nat.pair m p)) (Nat.pair j r)))))
    (eval_l parent_column_m (Nat.pair (Nat.pair x (Nat.pair m p)) (Nat.pair j r))) = _
  simp only [array_m, row_m, parent_column_m, local_m, eval_l, Nat.unpair_pair,
    PrimitiveProgram.add_l]

/-- 标准祖先条件准确保留原行、原父列和目标列。 -/
theorem member_test_encode_l (a : BMSArray) (m p j r : Nat) :
    decide (eval_l member_test_m
      (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p)) (Nat.pair j r)) ≠ 0) =
        BMS.isAncestor a r p (p + j) := by
  change decide (eval_l (member_m parent_m) (eval_l member_input_m
    (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p)) (Nat.pair j r))) ≠ 0) = _
  rw [member_input_eval_l, member_encode_l]

/-- 标准行比较的数值为截断差，非零表示严格小于。 -/
theorem below_eval_l (x m p j r : Nat) :
    eval_l below_m (Nat.pair (Nat.pair x (Nat.pair m p)) (Nat.pair j r)) = m - r := by
  change eval_l less_m (eval_l (.pair row_m limit_m)
    (Nat.pair (Nat.pair x (Nat.pair m p)) (Nat.pair j r))) = _
  simp only [row_m, limit_m, eval_l, Nat.unpair_pair, less_eval_l]

/-- 所有标准参数的上升测试与原定义相同，包括局部首列和非上升行。 -/
theorem ascending_encode_l (a : BMSArray) (m p j r : Nat) :
    decide (eval_l ascending_m
      (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p)) (Nat.pair j r)) ≠ 0) =
        BMS.ascending a m p j r := by
  rw [ascending_m, branch_eval_l, below_eval_l]
  by_cases hr : r < m
  · rw [if_neg (by omega), branch_eval_l]
    simp only [local_m, eval_l, Nat.unpair_pair]
    by_cases hj : j = 0
    · subst j
      simp [BMS.ascending, hr, PrimitiveProgram.const_l]
    · rw [if_neg hj, member_test_encode_l]
      simp [BMS.ascending, hr, hj]
  · rw [if_pos (by omega)]
    simp [eval_l, BMS.ascending, hr]

private theorem add_value_l (hℳ : Theory.Models ℳ theory_m) :
    value_spec_l add_m (fun q : num_l ℳ =>
      add_l (SecondOrderUnpairing.value_l hℳ q).1 (SecondOrderUnpairing.value_l hℳ q).2) := by
  intro A hA q y
  obtain ⟨a, b, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ q
  simpa only [SecondOrderUnpairing.unpair_l] using add_spec_l hℳ hA a b y

/-- 任意内部输入的祖先坐标接线，由真实原图组合证明。 -/
theorem member_input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m member_input_m) I) (x m p j r y : num_l ℳ) :
    relation_l I (value_l (value_l x (value_l m p)) (value_l j r)) y ↔
      value_l (value_l (value_l x r) (add_l p j)) p = y := by
  have ha : value_spec_l array_m _ := comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ)
  have hr : value_spec_l row_m _ := comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)
  have hp : value_spec_l parent_column_m _ :=
    comp_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (left_value_l hℳ)
  have hj : value_spec_l local_m _ := comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)
  have hv := (pair_value_l hℳ (pair_value_l hℳ (pair_value_l hℳ ha hr)
    (comp_value_l hℳ (add_value_l hℳ) (pair_value_l hℳ hp hj))) hp)
    hI (value_l (value_l x (value_l m p)) (value_l j r)) y
  simpa only [SecondOrderUnpairing.unpair_l] using hv

/-- 祖先测试图在全部内部坐标上保持真实统一祖先程序的同一查询。 -/
theorem member_test_rel_l (hℳ : Theory.Models ℳ theory_m) {T A : set_l ℳ}
    (hT : graph_semantics_l (graph_m member_test_m) T)
    (hA : graph_semantics_l (graph_m (member_m parent_m)) A) (x m p j r y : num_l ℳ) :
    relation_l T (value_l (value_l x (value_l m p)) (value_l j r)) y ↔
      relation_l A (value_l (value_l (value_l x r) (add_l p j)) p) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ member_input_m
  rw [comp_rel_l hℳ (graph_m (member_m parent_m)) (graph_m member_input_m) A I hA hI hT]
  simp only [member_input_rel_l hℳ hI, exists_eq_left']

/-- 内部上升测试的准确失败条件：超出行界，或非首列且祖先测试失败。 -/
theorem ascending_zero_l (hℳ : Theory.Models ℳ theory_m) {B A : set_l ℳ}
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hA : graph_semantics_l (graph_m (member_m parent_m)) A) (x m p j r : num_l ℳ) :
    letI := SecondOrderAlgebra.order_l hℳ
    relation_l B (value_l (value_l x (value_l m p)) (value_l j r)) (zero_l ℳ) ↔
      m ≤ r ∨ (j ≠ zero_l ℳ ∧
        relation_l A (value_l (value_l (value_l x r) (add_l p j)) p) (zero_l ℳ)) := by
  classical
  letI := SecondOrderAlgebra.order_l hℳ
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ less_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ member_test_m
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ less_m hL
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ member_test_m hT
  have hr : value_spec_l row_m _ := comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)
  have hm : value_spec_l limit_m _ :=
    comp_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)) (left_value_l hℳ)
  have hj : value_spec_l local_m _ := comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)
  have hone : value_spec_l (PrimitiveProgram.const_m 1) (fun _ : num_l ℳ => succ_l (zero_l ℳ)) := by
    intro C hC q y
    simpa only [numeral_val_succ_l, numeral_val_zero_l] using
      (const_spec_l hℳ 1 hC q y).trans eq_comm
  have hv := (branch_value_l hℳ (comp_value_l hℳ hf (pair_value_l hℳ hr hm))
    (branch_value_l hℳ hj hg hone) (zero_value_l hℳ))
    hB (value_l (value_l x (value_l m p)) (value_l j r)) (zero_l ℳ)
  simp only [SecondOrderUnpairing.unpair_l] at hv
  have hz : f (value_l r m) = zero_l ℳ ↔ m ≤ r :=
    (hf hL _ _).symm.trans (less_zero_l hℳ hL r m)
  have ha : g (value_l (value_l x (value_l m p)) (value_l j r)) = zero_l ℳ ↔
      relation_l A (value_l (value_l (value_l x r) (add_l p j)) p) (zero_l ℳ) :=
    (hg hT _ _).symm.trans (member_test_rel_l hℳ hT hA x m p j r _)
  rw [hv]
  by_cases hlt : m ≤ r
  · simp only [if_pos (hz.mpr hlt), hlt, true_or]
  · simp only [if_neg (fun h => hlt (hz.mp h)), hlt, false_or]
    by_cases hjz : j = zero_l ℳ
    · rw [if_pos hjz]
      simp only [ne_eq, hjz, not_true_eq_false, false_and,
        SecondOrderModel.nonzero_l hℳ (zero_l ℳ)]
    · rw [if_neg hjz, ha]
      simp only [ne_eq, hjz, not_false_eq_true, true_and]

#print axioms array_m
#print axioms limit_m
#print axioms parent_column_m
#print axioms local_m
#print axioms row_m
#print axioms member_input_m
#print axioms member_test_m
#print axioms below_m
#print axioms ascending_m
#print axioms member_input_eval_l
#print axioms member_test_encode_l
#print axioms below_eval_l
#print axioms ascending_encode_l
#print axioms member_input_rel_l
#print axioms member_test_rel_l
#print axioms ascending_zero_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAscending
