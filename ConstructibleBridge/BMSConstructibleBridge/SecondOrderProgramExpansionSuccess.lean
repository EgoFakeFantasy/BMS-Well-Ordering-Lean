import BMSConstructibleBridge.SecondOrderProgramCopies
import BMSConstructibleBridge.SecondOrderProgramMaximalParentRow
import BMSConstructibleBridge.SecondOrderProgramSlice

/-!
# 原 expandRaw 的成功分支

输入pair数组(pair展开下标(pair最大父行父列))。此分支按原父列分好坏部分，
坏块不含末列；复制次数是展开下标加一，末列和原数组保持。这里只处理已选定
父行、父列后的正文；Option失败分支由完整expandRaw程序另行处理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionSuccess

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramListAppend (append_m)
open SecondOrderProgramListTake (take_m take_array_encode_l)
open SecondOrderProgramSlice (slice_m slice_encode_l)
open SecondOrderProgramSubtraction (sub_m sub_eval_l)
open SecondOrderProgramMaximalParentRow (last_index_m last_index_encode_l last_column_m last_column_encode_l)
open SecondOrderProgramCopies (copies_m copies_encode_l append_array_encode_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 展开下标。 -/
def index_m : code_m := .comp .left .right

/-- 最大父行的原自然数值，已去Option壳。 -/
def row_m : code_m := .comp (.comp .left .right) .right

/-- 原父列自然数值，已去Option壳。 -/
def parent_m : code_m := .comp (.comp .right .right) .right

/-- 好部分是父列之前的原前缀。 -/
def good_m : code_m := .comp take_m (.pair .left parent_m)

/-- 坏块从父列开始，长度为末列下标减父列，因此不含原末列。 -/
def bad_m : code_m := .comp slice_m (.pair (.pair .left parent_m)
  (.comp sub_m (.pair (.comp last_index_m .left) parent_m)))

/-- 固定原坏块、完整上升参数和原末列作为复制参数。 -/
def parameter_m : code_m := .pair bad_m
  (.pair (.pair .left (.pair row_m parent_m)) (.comp last_column_m .left))

/-- 原展开下标n对应第0至n份，共n+1份。 -/
def copies_input_m : code_m := .pair parameter_m (.comp .succ index_m)

/-- 拼接全部原副本。 -/
def copied_m : code_m := .comp copies_m copies_input_m

/-- 好部分在左、全部复制坏块在右。 -/
def success_m : code_m := .comp append_m (.pair good_m copied_m)

private theorem slots_eval_l (x n m p : Nat) :
    let q := Nat.pair x (Nat.pair n (Nat.pair m p))
    eval_l index_m q = n ∧ eval_l row_m q = m ∧ eval_l parent_m q = p := by
  simp only [index_m, row_m, parent_m, eval_l, Nat.unpair_pair, and_self]

/-- 原好部分身份，父列越界时仍保留原take约定。 -/
theorem good_encode_l (a : BMSArray) (n m p : Nat) :
    eval_l good_m (Nat.pair (Encodable.encode a) (Nat.pair n (Nat.pair m p))) =
      Encodable.encode (a.take p) := by
  change eval_l take_m (Nat.pair
    (Nat.pair (Encodable.encode a) (Nat.pair n (Nat.pair m p))).unpair.1
    (eval_l parent_m (Nat.pair (Encodable.encode a) (Nat.pair n (Nat.pair m p))))) = _
  rw [Nat.unpair_pair, (slots_eval_l (Encodable.encode a) n m p).2.2, take_array_encode_l]

/-- 原坏部分身份：真实slice而非整个尾部或末列。 -/
theorem bad_encode_l (a : BMSArray) (n m p : Nat) :
    eval_l bad_m (Nat.pair (Encodable.encode a) (Nat.pair n (Nat.pair m p))) =
      Encodable.encode (BMS.slice a p (a.length.pred - p)) := by
  let q := Nat.pair (Encodable.encode a) (Nat.pair n (Nat.pair m p))
  change eval_l slice_m (Nat.pair (Nat.pair q.unpair.1 (eval_l parent_m q))
    (eval_l sub_m (Nat.pair (eval_l last_index_m q.unpair.1) (eval_l parent_m q)))) = _
  rw [(slots_eval_l (Encodable.encode a) n m p).2.2]
  simp only [q, Nat.unpair_pair, last_index_encode_l, sub_eval_l, slice_encode_l]

/-- 参数从同一原数组/坏块/末列取得，复制预算精确为n+1。 -/
theorem copied_encode_l (a : BMSArray) (n m p : Nat) :
    eval_l copied_m (Nat.pair (Encodable.encode a) (Nat.pair n (Nat.pair m p))) =
      Encodable.encode ((List.range (n + 1)).flatMap (fun k =>
        BMS.copyBlock a (BMS.slice a p (a.length.pred - p)) m p k (a[a.length.pred]?.getD []))) := by
  let q := Nat.pair (Encodable.encode a) (Nat.pair n (Nat.pair m p))
  have hi : eval_l copies_input_m q = Nat.pair
      (Nat.pair (Encodable.encode (BMS.slice a p (a.length.pred - p)))
        (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p))
          (Encodable.encode (a[a.length.pred]?.getD [])))) (n + 1) := by
    change Nat.pair (Nat.pair (eval_l bad_m q)
      (Nat.pair (Nat.pair q.unpair.1 (Nat.pair (eval_l row_m q) (eval_l parent_m q)))
        (eval_l last_column_m q.unpair.1))) (Nat.succ (eval_l index_m q)) = _
    rw [bad_encode_l, (slots_eval_l (Encodable.encode a) n m p).1,
      (slots_eval_l (Encodable.encode a) n m p).2.1,
      (slots_eval_l (Encodable.encode a) n m p).2.2]
    simp only [q, Nat.unpair_pair, last_column_encode_l]
  change eval_l copies_m (eval_l copies_input_m q) = _
  rw [hi, copies_encode_l]

/-- 原成功分支的完整标准身份；父存在性由调用方的Option分支负责。 -/
theorem success_encode_l (a : BMSArray) (n m p : Nat) :
    eval_l success_m (Nat.pair (Encodable.encode a) (Nat.pair n (Nat.pair m p))) =
      Encodable.encode (a.take p ++ (List.range (n + 1)).flatMap (fun k =>
        BMS.copyBlock a (BMS.slice a p (a.length.pred - p)) m p k (a[a.length.pred]?.getD []))) := by
  let q := Nat.pair (Encodable.encode a) (Nat.pair n (Nat.pair m p))
  change eval_l append_m (Nat.pair (eval_l good_m q) (eval_l copied_m q)) = _
  rw [good_encode_l, copied_encode_l, append_array_encode_l]

/-- 任意内部输入上的成功图由同一好部分、复制和拼接三图组成。 -/
theorem success_rel_l (hℳ : Theory.Models ℳ theory_m) {S G C P : set_l ℳ}
    (hS : graph_semantics_l (graph_m success_m) S)
    (hG : graph_semantics_l (graph_m good_m) G)
    (hC : graph_semantics_l (graph_m copied_m) C)
    (hP : graph_semantics_l (graph_m append_m) P) (x y : num_l ℳ) :
    relation_l S x y ↔ ∃ g c, relation_l G x g ∧ relation_l C x c ∧ relation_l P (value_l g c) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ good_m hG
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ copied_m hC
  obtain ⟨p, hp, _⟩ := value_exists_l hℳ append_m hP
  have hv := (comp_value_l hℳ hp (pair_value_l hℳ hf hg)) hS x y
  rw [hv]
  simp only [hf hG, hg hC, hp hP]
  constructor
  · intro h
    exact ⟨f x, g x, rfl, rfl, h⟩
  · rintro ⟨_, _, rfl, rfl, h⟩
    exact h

#print axioms index_m
#print axioms row_m
#print axioms parent_m
#print axioms good_m
#print axioms bad_m
#print axioms parameter_m
#print axioms copies_input_m
#print axioms copied_m
#print axioms success_m
#print axioms good_encode_l
#print axioms bad_encode_l
#print axioms copied_encode_l
#print axioms success_encode_l
#print axioms success_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionSuccess
