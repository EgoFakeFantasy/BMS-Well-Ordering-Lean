import BMSConstructibleBridge.SecondOrderProgramUniformParent
import BMSConstructibleBridge.SecondOrderProgramGreatestCorrectness

/-!
# 原 maximalParentRow 的统一程序

从同一数组计算末列、末列长度，搜索具有父节点的最大行号。空数组的末列约定
为空列，搜索预算自然为零。标准身份覆盖全部数组；内部规格使用实际统一父程序
的图与实际末列高度图，尚不把该图冒称为已建立逐行不变量的抽象父关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMaximalParentRow

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramListCode (pred_m pred_eval_l)
open SecondOrderProgramLength (length_m length_encode_l)
open SecondOrderProgramListLookup (lookup_m lookup_encode_l)
open SecondOrderProgramTrimHeight (array_encode_l)
open SecondOrderProgramUniformParent (parent_m parent_encode_l)
open SecondOrderProgramGreatest (greatest_m greatest_eval_l)
open SecondOrderProgramGreatestCorrectness (greatest_some_l greatest_none_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 宽度的截断前驱；空数组时为零。 -/
def last_index_m : code_m := .comp pred_m length_m

/-- 读取末列的原列表码，空数组时返回空码。 -/
def last_column_m : code_m := .comp lookup_m (.pair PrimitiveProgram.id_m last_index_m)

/-- 原搜索预算是末列长度，不是全数组裁剪高度。 -/
def height_m : code_m := .comp length_m last_column_m

/-- 搜索测试输入pair数组行号，改接到同一统一父程序的末列查询。 -/
def test_input_m : code_m := .pair PrimitiveProgram.id_m (.comp last_index_m .left)

/-- 父结果非零即some；不把some零误判为none。 -/
def test_m : code_m := .comp parent_m test_input_m

/-- 有限搜索返回原Option行号码，空高度时自动返回none。 -/
def maximal_m : code_m := .comp (greatest_m test_m) (.pair PrimitiveProgram.id_m height_m)

/-- 末列下标的标准身份。 -/
theorem last_index_encode_l (a : BMSArray) :
    eval_l last_index_m (Encodable.encode a) = a.length.pred := by
  change eval_l pred_m (eval_l length_m (Encodable.encode a)) = _
  rw [array_encode_l, length_encode_l, List.length_map, pred_eval_l]

/-- 原嵌套码的末列读取，含空数组默认空列。 -/
theorem last_column_encode_l (a : BMSArray) :
    eval_l last_column_m (Encodable.encode a) =
      Encodable.encode (a[a.length.pred]?.getD []) := by
  change eval_l lookup_m (Nat.pair (eval_l PrimitiveProgram.id_m (Encodable.encode a))
    (eval_l last_index_m (Encodable.encode a))) = _
  rw [PrimitiveProgram.id_l, last_index_encode_l, array_encode_l, lookup_encode_l,
    List.getElem?_map]
  cases a[a.length.pred]? <;> rfl

/-- 搜索高度准确来自原末列，不依赖数组矩形性。 -/
theorem height_encode_l (a : BMSArray) :
    eval_l height_m (Encodable.encode a) = (a[a.length.pred]?.getD []).length := by
  change eval_l length_m (eval_l last_column_m (Encodable.encode a)) = _
  rw [last_column_encode_l, length_encode_l]

/-- 原最大行搜索测试的逐标准输入身份。 -/
theorem test_encode_l (a : BMSArray) (r : Nat) :
    decide (eval_l test_m (Nat.pair (Encodable.encode a) r) ≠ 0) =
      (BMS.parent r a a.length.pred).isSome := by
  change decide (eval_l parent_m (Nat.pair
    (eval_l PrimitiveProgram.id_m (Nat.pair (Encodable.encode a) r))
    (eval_l last_index_m (Nat.pair (Encodable.encode a) r).unpair.1)) ≠ 0) = _
  rw [PrimitiveProgram.id_l, Nat.unpair_pair, last_index_encode_l, parent_encode_l]
  cases BMS.parent r a a.length.pred <;> simp [Encodable.encode_some]

/-- 同一固定程序在全部标准数组上等于原maximalParentRow。 -/
theorem maximal_encode_l (a : BMSArray) :
    eval_l maximal_m (Encodable.encode a) = Encodable.encode (BMS.maximalParentRow a) := by
  change eval_l (greatest_m test_m) (Nat.pair (eval_l PrimitiveProgram.id_m (Encodable.encode a))
    (eval_l height_m (Encodable.encode a))) = _
  rw [PrimitiveProgram.id_l, height_encode_l, greatest_eval_l]
  simp only [test_encode_l]
  cases hn : a.length with
  | zero =>
      have ha : a = [] := by
        cases a with
        | nil => rfl
        | cons _ _ => simp at hn
      subst a
      rfl
  | succ n =>
      simp only [BMS.maximalParentRow, hn, Nat.pred_succ]
      cases a[n]? <;> rfl

/-- 任意内部数组及行号的测试值来自同一实际统一父图。 -/
theorem test_rel_l (hℳ : Theory.Models ℳ theory_m) {T P J : set_l ℳ}
    (hT : graph_semantics_l (graph_m test_m) T)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hJ : graph_semantics_l (graph_m last_index_m) J) (x r y : num_l ℳ) :
    relation_l T (value_l x r) y ↔
      ∃ j, relation_l J x j ∧ relation_l P (value_l (value_l x r) j) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ last_index_m hJ
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ parent_m hP
  have hi : value_spec_l test_input_m _ :=
    pair_value_l hℳ (id_value_l hℳ) (comp_value_l hℳ hf (left_value_l hℳ))
  have hv := (comp_value_l hℳ hg hi) hT (value_l x r) y
  simp only [SecondOrderUnpairing.unpair_l] at hv
  rw [hv]
  simp only [hf hJ, hg hP, exists_eq_left']

/-- 实际高度图的输出就是原最大搜索的预算，保留全部内部数。 -/
theorem maximal_rel_l (hℳ : Theory.Models ℳ theory_m) {M G H : set_l ℳ}
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hG : graph_semantics_l (graph_m (greatest_m test_m)) G)
    (hH : graph_semantics_l (graph_m height_m) H) {x h : num_l ℳ}
    (hh : relation_l H x h) (y : num_l ℳ) :
    relation_l M x y ↔ relation_l G (value_l x h) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ height_m hH
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ (greatest_m test_m) hG
  have hv := (comp_value_l hℳ hg (pair_value_l hℳ (id_value_l hℳ) hf)) hM x y
  rw [hv]
  change g (value_l x (f x)) = y ↔ relation_l G (value_l x h) y
  rw [(hf hH x h).mp hh, hg hG]

/-- 返回none当且仅当实际末列高度内没有一行通过实际父程序测试。 -/
theorem maximal_none_l (hℳ : Theory.Models ℳ theory_m) {M G H T : set_l ℳ}
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hG : graph_semantics_l (graph_m (greatest_m test_m)) G)
    (hH : graph_semantics_l (graph_m height_m) H)
    (hT : graph_semantics_l (graph_m test_m) T) {x h : num_l ℳ}
    (hh : relation_l H x h) :
    relation_l M x (zero_l ℳ) ↔
      ∀ r, SecondOrderOrder.lt_l r h → relation_l T (value_l x r) (zero_l ℳ) := by
  rw [maximal_rel_l hℳ hM hG hH hh, greatest_none_l hℳ test_m hG hT]

/-- 返回some行号恰好是界内最后一个测试成功的位置。 -/
theorem maximal_some_l (hℳ : Theory.Models ℳ theory_m) {M G H T : set_l ℳ}
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hG : graph_semantics_l (graph_m (greatest_m test_m)) G)
    (hH : graph_semantics_l (graph_m height_m) H)
    (hT : graph_semantics_l (graph_m test_m) T) {x h : num_l ℳ}
    (hh : relation_l H x h) (r : num_l ℳ) :
    relation_l M x (succ_l r) ↔ SecondOrderOrder.lt_l r h ∧
      ¬relation_l T (value_l x r) (zero_l ℳ) ∧
      ∀ j, SecondOrderOrder.lt_l r j → SecondOrderOrder.lt_l j h →
        relation_l T (value_l x j) (zero_l ℳ) := by
  rw [maximal_rel_l hℳ hM hG hH hh, greatest_some_l hℳ test_m hG hT]

#print axioms last_index_m
#print axioms last_column_m
#print axioms height_m
#print axioms test_input_m
#print axioms test_m
#print axioms maximal_m
#print axioms last_index_encode_l
#print axioms last_column_encode_l
#print axioms height_encode_l
#print axioms test_encode_l
#print axioms maximal_encode_l
#print axioms test_rel_l
#print axioms maximal_rel_l
#print axioms maximal_none_l
#print axioms maximal_some_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMaximalParentRow
