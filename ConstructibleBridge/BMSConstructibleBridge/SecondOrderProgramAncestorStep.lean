import BMSConstructibleBridge.SecondOrderProgramValue
import BMSConstructibleBridge.SecondOrderProgramConditional
import BMSConstructibleBridge.SecondOrderProgramListCode

/-!
# 原祖先链的累积状态步

状态 pair 参数 (pair 当前列 逆序累计表)。给定原parent程序，先查询当前列；
none保持整个状态，some p则把当前列改为p，并把p接到累计表头。none之后再次
查询同一列仍是none，因此保持状态不会伪造新祖先。最后反转累计表才得到原顺序。
本节仅证明原程序的单步规格，未把有限迭代或标准求值当作完整内部祖先链证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorStep

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramConditional
open SecondOrderProgramListCode (pred_m pred_eval_l pred_succ_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 状态中提取同一外层参数与当前列。 -/
def query_input_m : code_m := .pair .left (.comp .left .right)

/-- 对当前列调用原parent程序，不改变其参数。 -/
def query_m (c : code_m) : code_m := .comp c query_input_m

/-- 已查询状态 pair 原状态 parent的Option码 中提取some的原数值。 -/
def next_parent_m : code_m := .comp pred_m .right

/-- 更新逆序累计表，仅在parent为some时使用。 -/
def next_list_m : code_m := .comp .succ
  (.pair next_parent_m (.comp (.comp .right .right) .left))

/-- some分支：保留参数、更新当前列、接入一个真实parent。 -/
def advance_m : code_m := .pair (.comp .left .left) (.pair next_parent_m next_list_m)

/-- 已查询结果为none时原样返回旧状态。 -/
def gate_m : code_m := branch_m .right advance_m .left

/-- 一步祖先状态转换，只使用给定原parent程序和已有七构造。 -/
def step_m (c : code_m) : code_m :=
  .comp gate_m (.pair PrimitiveProgram.id_m (query_m c))

/-- 标准查询仍输入同一参数与当前列。 -/
theorem query_eval_l (c : code_m) (x k v : Nat) :
    eval_l (query_m c) (Nat.pair x (Nat.pair k v)) = eval_l c (Nat.pair x k) := by
  change eval_l c (Nat.pair (Nat.pair x (Nat.pair k v)).unpair.1
    (Nat.pair x (Nat.pair k v)).unpair.2.unpair.1) = _
  rw [Nat.unpair_pair, Nat.unpair_pair]

/-- 标准选择分支准确处理Option码，不把none当作第0列。 -/
theorem gate_eval_l (x k v q : Nat) :
    eval_l gate_m (Nat.pair (Nat.pair x (Nat.pair k v)) q) =
      if q = 0 then Nat.pair x (Nat.pair k v)
      else Nat.pair x (Nat.pair q.pred (Nat.succ (Nat.pair q.pred v))) := by
  rw [gate_m, branch_eval_l]
  simp only [advance_m, next_parent_m, next_list_m, eval_l, Nat.unpair_pair, pred_eval_l]

/-- 原parent返回some的准确单步身份。 -/
theorem step_some_eval_l (c : code_m) (x k v p : Nat)
    (hp : eval_l c (Nat.pair x k) = p + 1) :
    eval_l (step_m c) (Nat.pair x (Nat.pair k v)) =
      Nat.pair x (Nat.pair p (Nat.succ (Nat.pair p v))) := by
  change eval_l gate_m (Nat.pair (eval_l PrimitiveProgram.id_m (Nat.pair x (Nat.pair k v)))
    (eval_l (query_m c) (Nat.pair x (Nat.pair k v)))) = _
  rw [PrimitiveProgram.id_l, query_eval_l, hp, gate_eval_l]
  simp only [Nat.add_one_ne_zero, if_false, Nat.pred_succ]

/-- 原parent返回none的准确单步身份：整个原状态不变。 -/
theorem step_none_eval_l (c : code_m) (x k v : Nat)
    (hp : eval_l c (Nat.pair x k) = 0) :
    eval_l (step_m c) (Nat.pair x (Nat.pair k v)) = Nat.pair x (Nat.pair k v) := by
  change eval_l gate_m (Nat.pair (eval_l PrimitiveProgram.id_m (Nat.pair x (Nat.pair k v)))
    (eval_l (query_m c) (Nat.pair x (Nat.pair k v)))) = _
  rw [PrimitiveProgram.id_l, query_eval_l, hp, gate_eval_l, if_pos rfl]

/-- 任意内部状态的查询输入接线。 -/
theorem query_input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m query_input_m) I) (x k v y : num_l ℳ) :
    relation_l I (value_l x (value_l k v)) y ↔ value_l x k = y := by
  have h := (pair_value_l hℳ (left_value_l hℳ)
    (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ))) hI (value_l x (value_l k v)) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 任意内部状态的查询图保持同一原parent调用。 -/
theorem query_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {Q C : set_l ℳ}
    (hQ : graph_semantics_l (graph_m (query_m c)) Q)
    (hC : graph_semantics_l (graph_m c) C) (x k v y : num_l ℳ) :
    relation_l Q (value_l x (value_l k v)) y ↔ relation_l C (value_l x k) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ query_input_m
  rw [comp_rel_l hℳ (graph_m c) (graph_m query_input_m) C I hC hI hQ]
  simp only [query_input_rel_l hℳ hI, exists_eq_left']

/-- 内部some分支提取原parent值；仅使用原前驱程序的后继规格。 -/
theorem next_parent_rel_l (hℳ : Theory.Models ℳ theory_m) {P : set_l ℳ}
    (hP : graph_semantics_l (graph_m next_parent_m) P) (s p y : num_l ℳ) :
    relation_l P (value_l s (succ_l p)) y ↔ p = y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ pred_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  rw [comp_rel_l hℳ (graph_m pred_m) (graph_m .right) D R hD hR hP]
  simp only [right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l, exists_eq_left', pred_succ_l hℳ hD]

/-- 内部some分支接入原parent值，不改变既有累计表。 -/
theorem next_list_rel_l (hℳ : Theory.Models ℳ theory_m) {N : set_l ℳ}
    (hN : graph_semantics_l (graph_m next_list_m) N) (x k v p y : num_l ℳ) :
    relation_l N (value_l (value_l x (value_l k v)) (succ_l p)) y ↔
      succ_l (value_l p v) = y := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ next_parent_m
  obtain ⟨V, _, hV⟩ := graph_total_l hℳ (.comp (.comp .right .right) .left)
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ (.pair next_parent_m (.comp (.comp .right .right) .left))
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ .succ
  have hv (z : num_l ℳ) :
      relation_l V (value_l (value_l x (value_l k v)) (succ_l p)) z ↔ v = z := by
    have h := (comp_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ))
      (left_value_l hℳ)) hV (value_l (value_l x (value_l k v)) (succ_l p)) z
    simpa only [SecondOrderUnpairing.unpair_l] using h
  rw [comp_rel_l hℳ (graph_m .succ)
    (graph_m (.pair next_parent_m (.comp (.comp .right .right) .left))) U B hU hB hN]
  simp only [pair_rel_l hℳ (graph_m next_parent_m)
    (graph_m (.comp (.comp .right .right) .left)) P V hP hV hB, next_parent_rel_l hℳ hP,
    hv, succ_rel_l hℳ hU]
  constructor
  · rintro ⟨_, ⟨_, _, rfl, rfl, rfl⟩, hy⟩
    exact hy
  · exact fun hy => ⟨value_l p v, ⟨p, v, rfl, rfl, rfl⟩, hy⟩

/-- 内部some分支的完整状态输出。 -/
theorem advance_rel_l (hℳ : Theory.Models ℳ theory_m) {A : set_l ℳ}
    (hA : graph_semantics_l (graph_m advance_m) A) (x k v p y : num_l ℳ) :
    relation_l A (value_l (value_l x (value_l k v)) (succ_l p)) y ↔
      value_l x (value_l p (succ_l (value_l p v))) = y := by
  obtain ⟨X, _, hX⟩ := graph_total_l hℳ (.comp .left .left)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ next_parent_m
  obtain ⟨N, _, hN⟩ := graph_total_l hℳ next_list_m
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ (.pair next_parent_m next_list_m)
  have hx (z : num_l ℳ) :
      relation_l X (value_l (value_l x (value_l k v)) (succ_l p)) z ↔ x = z := by
    have h := (comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ))
      hX (value_l (value_l x (value_l k v)) (succ_l p)) z
    simpa only [SecondOrderUnpairing.unpair_l] using h
  rw [pair_rel_l hℳ (graph_m (.comp .left .left)) (graph_m (.pair next_parent_m next_list_m))
    X B hX hB hA]
  simp only [hx, pair_rel_l hℳ (graph_m next_parent_m) (graph_m next_list_m) P N hP hN hB,
    next_parent_rel_l hℳ hP, next_list_rel_l hℳ hN]
  constructor
  · rintro ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, hy⟩
    exact hy
  · exact fun hy => ⟨x, value_l p (succ_l (value_l p v)), rfl,
      ⟨p, succ_l (value_l p v), rfl, rfl, rfl⟩, hy⟩

#print axioms query_input_m
#print axioms query_m
#print axioms next_parent_m
#print axioms next_list_m
#print axioms advance_m
#print axioms gate_m
#print axioms step_m
#print axioms query_eval_l
#print axioms gate_eval_l
#print axioms step_some_eval_l
#print axioms step_none_eval_l
#print axioms query_input_rel_l
#print axioms query_rel_l
#print axioms next_parent_rel_l
#print axioms next_list_rel_l
#print axioms advance_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorStep
