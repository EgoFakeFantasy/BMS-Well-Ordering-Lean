import BMSConstructibleBridge.SecondOrderProgramEntry
import BMSConstructibleBridge.SecondOrderProgramOptionalCompare
import BMSConstructibleBridge.SecondOrderProgramValue

/-!
# 原父节点候选的坐标比较程序

查询输入为 pair (pair 数组 (pair 目标列 行号)) 候选列，正好供 greatest_m 使用。
两个坐标都按原 entry? 读取，非零表示两项存在且候选值较小。
这里只处理坐标比较，不省略父节点的宽度检查或高行号所需的祖先条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramEntryCompare

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramEntry SecondOrderProgramValue
open SecondOrderProgramOptionalCompare (optional_less_m optional_nonzero_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 保留同一数组和行号，用候选列替换目标列。 -/
def candidate_input_m : code_m :=
  .pair (.comp .left .left) (.pair .right (.comp (.comp .right .right) .left))

/-- 读取候选坐标的原 Option 码。 -/
def candidate_m : code_m := .comp entry_m candidate_input_m

/-- 查询参数本身已经是目标坐标的三元输入。 -/
def target_m : code_m := .comp entry_m .left

/-- 原两个可选坐标的严格比较，非零才表示成功。 -/
def compare_m : code_m := .comp optional_less_m (.pair candidate_m target_m)

/-- 标准四坐标接线，数组码和行号不变。 -/
theorem candidate_input_eval_l (a t r i : Nat) :
    eval_l candidate_input_m (Nat.pair (Nat.pair a (Nat.pair t r)) i) = Nat.pair a (Nat.pair i r) := by
  simp only [candidate_input_m, eval_l, Nat.unpair_pair]

/-- 标准候选值就是原 entry? a i r。 -/
theorem candidate_encode_l (a : BMSArray) (t r i : Nat) :
    eval_l candidate_m (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair t r)) i) =
      Encodable.encode (BMS.entry? a i r) := by
  change eval_l entry_m (eval_l candidate_input_m
    (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair t r)) i)) = _
  rw [candidate_input_eval_l, entry_encode_l]

/-- 标准目标值就是原 entry? a t r。 -/
theorem target_encode_l (a : BMSArray) (t r i : Nat) :
    eval_l target_m (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair t r)) i) =
      Encodable.encode (BMS.entry? a t r) := by
  change eval_l entry_m (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair t r)) i).unpair.1 = _
  rw [Nat.unpair_pair, entry_encode_l]

/-- 标准非零测试精确等于原父节点定义中的双 Option 比较。 -/
theorem compare_encode_l (a : BMSArray) (t r i : Nat) :
    decide (eval_l compare_m (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair t r)) i) ≠ 0) =
      (match BMS.entry? a i r, BMS.entry? a t r with
        | some x, some y => decide (x < y) | _, _ => false) := by
  change decide (eval_l optional_less_m (Nat.pair
    (eval_l candidate_m (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair t r)) i))
    (eval_l target_m (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair t r)) i))) ≠ 0) = _
  rw [candidate_encode_l, target_encode_l, SecondOrderProgramOptionalCompare.optional_encode_l]
  cases BMS.entry? a i r <;> cases BMS.entry? a t r <;> rfl

/-- 原内部反配对保证四坐标接线，不要求其数值标准。 -/
theorem candidate_input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m candidate_input_m) I) (a t r i y : num_l ℳ) :
    relation_l I (value_l (value_l a (value_l t r)) i) y ↔ value_l a (value_l i r) = y := by
  have h := (pair_value_l hℳ
    (comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ))
    (pair_value_l hℳ (right_value_l hℳ)
      (comp_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (left_value_l hℳ))))
    hI (value_l (value_l a (value_l t r)) i) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 内部候选图保持同一 entry 图的候选列和行号。 -/
theorem candidate_rel_l (hℳ : Theory.Models ℳ theory_m) {C J : set_l ℳ}
    (hC : graph_semantics_l (graph_m candidate_m) C)
    (hJ : graph_semantics_l (graph_m entry_m) J) (a t r i y : num_l ℳ) :
    relation_l C (value_l (value_l a (value_l t r)) i) y ↔ relation_l J (value_l a (value_l i r)) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ candidate_input_m
  rw [comp_rel_l hℳ (graph_m entry_m) (graph_m candidate_input_m) J I hJ hI hC]
  simp only [candidate_input_rel_l hℳ hI, exists_eq_left']

/-- 内部目标图不依赖当前候选下标。 -/
theorem target_rel_l (hℳ : Theory.Models ℳ theory_m) {T J : set_l ℳ}
    (hT : graph_semantics_l (graph_m target_m) T)
    (hJ : graph_semantics_l (graph_m entry_m) J) (a t r i y : num_l ℳ) :
    relation_l T (value_l (value_l a (value_l t r)) i) y ↔ relation_l J (value_l a (value_l t r)) y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  rw [comp_rel_l hℳ (graph_m entry_m) (graph_m .left) J L hJ hL hT]
  simp only [left_rel_l hℳ hL, SecondOrderUnpairing.unpair_l, exists_eq_left']

/-- 原比较图返回非零，恰好有两个实际存在的坐标且候选值严格较小。 -/
theorem compare_nonzero_l (hℳ : Theory.Models ℳ theory_m) {B J : set_l ℳ}
    (hB : graph_semantics_l (graph_m compare_m) B)
    (hJ : graph_semantics_l (graph_m entry_m) J) (a t r i : num_l ℳ) :
    ¬relation_l B (value_l (value_l a (value_l t r)) i) (zero_l ℳ) ↔
      ∃ x y, relation_l J (value_l a (value_l i r)) (succ_l x) ∧
        relation_l J (value_l a (value_l t r)) (succ_l y) ∧ SecondOrderOrder.lt_l x y := by
  obtain ⟨C, hCf, hC⟩ := graph_total_l hℳ candidate_m
  obtain ⟨T, hTf, hT⟩ := graph_total_l hℳ target_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (.pair candidate_m target_m)
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_less_m
  let q := value_l (value_l a (value_l t r)) i
  obtain ⟨u, hu, _⟩ := hCf q
  obtain ⟨v, hv, _⟩ := hTf q
  have hp (p : num_l ℳ) : relation_l P q p ↔ value_l u v = p := by
    rw [pair_rel_l hℳ (graph_m candidate_m) (graph_m target_m) C T hC hT hP]
    constructor
    · rintro ⟨u', v', hu', hv', he⟩
      rw [← function_value_unique_l hCf hu hu', ← function_value_unique_l hTf hv hv'] at he
      exact he
    · intro he
      exact ⟨u, v, hu, hv, he⟩
  have hb : relation_l B q (zero_l ℳ) ↔ relation_l O (value_l u v) (zero_l ℳ) := by
    rw [comp_rel_l hℳ (graph_m optional_less_m) (graph_m (.pair candidate_m target_m)) O P hO hP hB]
    simp only [hp, exists_eq_left']
  change (¬relation_l B q (zero_l ℳ)) ↔ _
  rw [hb, optional_nonzero_l hℳ hO]
  constructor
  · rintro ⟨x, y, rfl, rfl, hxy⟩
    exact ⟨x, y, (candidate_rel_l hℳ hC hJ a t r i _).mp hu,
      (target_rel_l hℳ hT hJ a t r i _).mp hv, hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨x, y, function_value_unique_l hCf hu ((candidate_rel_l hℳ hC hJ a t r i _).mpr hx),
      function_value_unique_l hTf hv ((target_rel_l hℳ hT hJ a t r i _).mpr hy), hxy⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramEntryCompare
