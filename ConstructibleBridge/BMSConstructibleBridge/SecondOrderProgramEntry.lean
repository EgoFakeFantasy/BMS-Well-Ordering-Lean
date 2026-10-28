import BMSConstructibleBridge.SecondOrderProgramOptionalLookup
import BMSConstructibleBridge.SecondOrderProgramTrimHeight

/-!
# 原数组 entry? 的两层可选读取程序

输入为 `pair 数组码 (pair 列下标 行下标)`。先取得可选列码，仅在该列存在时读取
行值。标准端直接等于原 `BMS.entry?` 的 Option 编码；内部端给出同一可选读取图
的精确 bind 规格，没有把缺项替换成合法零值，也不要求内部数组宽度或行号标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListCode SecondOrderProgramOptionalLookup
open SecondOrderProgramConditional
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 从三元输入保留数组与列下标。 -/
def column_input_m : code_m := .pair .left pred_step_m

/-- 在原外层列表中可选读取一列，输出仍是 Option 码。 -/
def column_m : code_m := .comp optional_m column_input_m

/-- 取内部行下标。 -/
def row_m : code_m := .comp .right .right

/-- 非空列码解去 Option 后继，再与原行下标配对。 -/
def row_input_m : code_m := .pair (.comp pred_m column_m) row_m

/-- 已存在列上的内层可选读取。 -/
def present_m : code_m := .comp optional_m row_input_m

/-- 原两层可选读取，缺列时输出 none。 -/
def entry_m : code_m := branch_m column_m present_m .zero

/-- 标准外层读取保留原 Option 列码及列下标。 -/
theorem column_encode_l (a : BMSArray) (i r : Nat) :
    eval_l column_m (Nat.pair (Encodable.encode a) (Nat.pair i r)) = Encodable.encode (a[i]?) := by
  change eval_l optional_m (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair i r)).unpair.1
    (Nat.pair (Encodable.encode a) (Nat.pair i r)).unpair.2.unpair.1) = _
  rw [Nat.unpair_pair, Nat.unpair_pair, SecondOrderProgramTrimHeight.array_encode_l,
    optional_encode_l, List.getElem?_map]
  cases a[i]? <;> rfl

/-- 已存在列上的标准内层读取，使用原列码而非另一份数组。 -/
theorem present_encode_l (a : BMSArray) (i r : Nat) (s : List Nat) (hs : a[i]? = some s) :
    eval_l present_m (Nat.pair (Encodable.encode a) (Nat.pair i r)) = Encodable.encode (s[r]?) := by
  change eval_l optional_m (Nat.pair
    (eval_l pred_m (eval_l column_m (Nat.pair (Encodable.encode a) (Nat.pair i r))))
    (Nat.pair (Encodable.encode a) (Nat.pair i r)).unpair.2.unpair.2) = _
  rw [Nat.unpair_pair, Nat.unpair_pair, column_encode_l, hs, Encodable.encode_some,
    pred_eval_l, Nat.pred_succ, optional_encode_l]

/-- 标准端与原 BMS.entry? 逐输入相同，明确区分缺列、缺行和合法零值。 -/
theorem entry_encode_l (a : BMSArray) (i r : Nat) :
    eval_l entry_m (Nat.pair (Encodable.encode a) (Nat.pair i r)) = Encodable.encode (BMS.entry? a i r) := by
  rw [entry_m, branch_eval_l, column_encode_l]
  cases hs : a[i]? with
  | none =>
      rw [Encodable.encode_none, if_pos rfl]
      simp only [eval_l, BMS.entry?, hs, Option.bind_none, Encodable.encode_none]
  | some s =>
      rw [Encodable.encode_some, if_neg (Nat.succ_ne_zero _), present_encode_l a i r s hs]
      simp only [BMS.entry?, hs, Option.bind_some]

/-- 内部外层列图与同一个可选读取图逐点对应。 -/
theorem column_rel_l (hℳ : Theory.Models ℳ theory_m) {C O : set_l ℳ}
    (hC : graph_semantics_l (graph_m column_m) C)
    (hO : graph_semantics_l (graph_m optional_m) O) (a i r y : num_l ℳ) :
    relation_l C (value_l a (value_l i r)) y ↔ relation_l O (value_l a i) y := by
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ .left
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ pred_step_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ column_input_m
  rw [comp_rel_l hℳ (graph_m optional_m) (graph_m column_input_m) O P hO hP hC]
  simp only [pair_rel_l hℳ (graph_m .left) (graph_m pred_step_m) A K hA hK hP,
    left_rel_l hℳ hA, pred_step_rel_l hℳ hK, SecondOrderUnpairing.unpair_l]
  constructor
  · rintro ⟨p, ⟨u, v, rfl, rfl, rfl⟩, hy⟩
    exact hy
  · intro hy
    exact ⟨value_l a i, ⟨a, i, rfl, rfl, rfl⟩, hy⟩

/-- 给定外层图返回某列的 some 码，内层图精确读取该列的原行下标。 -/
theorem present_rel_l (hℳ : Theory.Models ℳ theory_m) {S C O : set_l ℳ}
    (hS : graph_semantics_l (graph_m present_m) S)
    (hC : graph_semantics_l (graph_m column_m) C)
    (hO : graph_semantics_l (graph_m optional_m) O) {a i r c : num_l ℳ}
    (hc : relation_l C (value_l a (value_l i r)) (succ_l c)) (y : num_l ℳ) :
    relation_l S (value_l a (value_l i r)) y ↔ relation_l O (value_l c r) y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ (.comp pred_m column_m)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ pred_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ row_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ row_input_m
  have hd (z : num_l ℳ) : relation_l D (value_l a (value_l i r)) z ↔ c = z := by
    rw [comp_rel_l hℳ (graph_m pred_m) (graph_m column_m) P C hP hC hD]
    constructor
    · rintro ⟨q, hq, hz⟩
      have heq := function_value_unique_l (function_of_semantics_l hℳ column_m hC) hc hq
      rw [← heq] at hz
      exact (pred_succ_l hℳ hP c z).mp hz
    · intro hz
      exact ⟨succ_l c, hc, (pred_succ_l hℳ hP c z).mpr hz⟩
  have hg (z : num_l ℳ) : relation_l G (value_l a (value_l i r)) z ↔ r = z := by
    rw [comp_rel_l hℳ (graph_m .right) (graph_m .right) R R hR hR hG]
    simp only [right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [comp_rel_l hℳ (graph_m optional_m) (graph_m row_input_m) O I hO hI hS]
  simp only [pair_rel_l hℳ (graph_m (.comp pred_m column_m)) (graph_m row_m) D G hD hG hI, hd, hg]
  constructor
  · rintro ⟨p, ⟨u, v, rfl, rfl, rfl⟩, hy⟩
    exact hy
  · intro hy
    exact ⟨value_l c r, ⟨c, r, rfl, rfl, rfl⟩, hy⟩

/-- 原数组读取图在全部内部三元输入上遵守可选列/行 bind 规格。 -/
theorem entry_rel_l (hℳ : Theory.Models ℳ theory_m) {J O : set_l ℳ}
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O) (a i r y : num_l ℳ) :
    relation_l J (value_l a (value_l i r)) y ↔
      (relation_l O (value_l a i) (zero_l ℳ) ∧ zero_l ℳ = y) ∨
        ∃ c, relation_l O (value_l a i) (succ_l c) ∧ relation_l O (value_l c r) y := by
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ column_m
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ present_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  rw [branch_rel_l hℳ column_m present_m .zero hC hS hZ hJ]
  simp only [zero_rel_l hℳ hZ]
  constructor
  · rintro (⟨hc, hy⟩ | ⟨q, hq, hc, hy⟩)
    · exact Or.inl ⟨(column_rel_l hℳ hC hO a i r _).mp hc, hy⟩
    · rcases predecessor_l hℳ q with hz | ⟨c, rfl⟩
      · exact False.elim (hq hz)
      · exact Or.inr ⟨c, (column_rel_l hℳ hC hO a i r _).mp hc,
          (present_rel_l hℳ hS hC hO hc y).mp hy⟩
  · rintro (⟨hc, hy⟩ | ⟨c, hc, hy⟩)
    · exact Or.inl ⟨(column_rel_l hℳ hC hO a i r _).mpr hc, hy⟩
    · have hc' := (column_rel_l hℳ hC hO a i r _).mpr hc
      exact Or.inr ⟨succ_l c, nonzero_l hℳ c, hc', (present_rel_l hℳ hS hC hO hc' y).mpr hy⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramEntry
