import BMSConstructibleBridge.SecondOrderProgramListCode
import BMSConstructibleBridge.SecondOrderProgramListFold
import BMSConstructibleBridge.SecondOrderProgramListReverse
import BMSConstructibleBridge.SecondOrderProgramCallbackValue

/-!
# 带参数 mapIdx 的原七构造程序

Qwen 任务34-A 的原程序与公共合同保留；Codex 接手修复首轮构建失败的证明。
主输入 pair p 列表码，回调输入 pair p (pair 下标 条目)。折叠状态为
pair p (pair currentIndex reverseAcc)，零初值后最终反转，使用原 Encodable 码。
标准端保留任意起始下标和累计列表；内部端仅证明真实一步与初末接线。
全内部长度及下标对应由阶段B的真实公式归纳另证，不把标准身份外推到非标准模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListMap

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListCode SecondOrderProgramListFold
open SecondOrderProgramListReverse SecondOrderProgramValue SecondOrderProgramCallbackValue
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 主输入 pair p x 变成折叠输入 pair x (pair p (pair 0 0))。 -/
def map_call_m : code_m := .pair .right (.pair .left (.pair .zero .zero))

/-- 从 pair (pair p (pair i acc)) a 读取原参数。 -/
def map_p_m : code_m := .comp .left .left

/-- 读取当前下标。 -/
def map_i_m : code_m := .comp (.comp .left .right) .left

/-- 读取逆序累计表。 -/
def map_acc_m : code_m := .comp (.comp .right .right) .left

/-- 原回调输入保持同一参数、当前下标和当前条目。 -/
def map_in_m : code_m := .pair map_p_m (.pair map_i_m .right)

/-- 回调输出接到逆序表首，下标加一，参数不变。 -/
def map_step_m (c : code_m) : code_m :=
  .pair map_p_m (.pair (.comp .succ map_i_m)
    (.comp .succ (.pair (.comp c map_in_m) map_acc_m)))

/-- 最终状态中读取逆序累计码。 -/
def map_extract_m : code_m := .comp .right .right

/-- 原折叠后反转累计表，得到从零编号的保序带参映射。 -/
def map_m (c : code_m) : code_m :=
  .comp reverse_m (.comp map_extract_m (.comp (fold_m (map_step_m c)) map_call_m))

/-- 原单步的标准求值。 -/
theorem map_step_eval_l (c : code_m) (p i A a : Nat) :
    eval_l (map_step_m c) (Nat.pair (Nat.pair p (Nat.pair i A)) a) =
      Nat.pair p (Nat.pair (i + 1)
        (Nat.succ (Nat.pair (eval_l c (Nat.pair p (Nat.pair i a))) A))) := by
  simp only [map_step_m, map_p_m, map_i_m, map_acc_m, map_in_m, eval_l, Nat.unpair_pair]

/-- 广义折叠保留任意起始下标及累计表：新映射逆序接在旧累计表之前。 -/
theorem foldl_map_step_l (c : code_m) (p : Nat) :
    ∀ (s : List Nat) (k : Nat) (t : List Nat),
      List.foldl (fun w a => eval_l (map_step_m c) (Nat.pair w a))
        (Nat.pair p (Nat.pair k (Encodable.encode t))) s =
      Nat.pair p (Nat.pair (k + s.length)
        (Encodable.encode
          ((s.mapIdx (fun i a => eval_l c (Nat.pair p (Nat.pair (k + i) a)))).reverse ++ t))) := by
  intro s
  induction s with
  | nil =>
      intro k t
      simp only [List.foldl_nil, List.length_nil, Nat.add_zero,
        List.mapIdx_nil, List.reverse_nil, List.nil_append]
  | cons a s ih =>
      intro k t
      rw [List.foldl_cons, map_step_eval_l]
      have hcs : Nat.succ (Nat.pair (eval_l c (Nat.pair p (Nat.pair k a))) (Encodable.encode t)) =
          Encodable.encode (eval_l c (Nat.pair p (Nat.pair k a)) :: t) := cons_encode_l _ _
      rw [hcs, ih (k + 1) (_ :: t)]
      have hlen : k + (a :: s).length = (k + 1) + s.length := by
        simp only [List.length_cons]
        omega
      have hz : (fun i b => eval_l c (Nat.pair p (Nat.pair (k + (i + 1)) b))) =
          (fun i b => eval_l c (Nat.pair p (Nat.pair ((k + 1) + i) b))) := by
        funext i b
        rw [show k + (i + 1) = (k + 1) + i by omega]
      rw [List.mapIdx_cons]
      simp only [Nat.add_zero, List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [hz, hlen]

private theorem pipeline_eval_l (a b c d : code_m) (q : Nat) :
    eval_l (.comp a (.comp b (.comp c d))) q = eval_l a (eval_l b (eval_l c (eval_l d q))) := rfl

/-- 标准标题身份：下标从零开始，输出使用同一原列表编码。 -/
theorem map_encode_l (c : code_m) (p : Nat) (s : List Nat) :
    eval_l (map_m c) (Nat.pair p (Encodable.encode s)) =
      Encodable.encode (s.mapIdx (fun i a => eval_l c (Nat.pair p (Nat.pair i a)))) := by
  have hcall : eval_l map_call_m (Nat.pair p (Encodable.encode s)) =
      Nat.pair (Encodable.encode s) (Nat.pair p (Nat.pair 0 (Encodable.encode ([] : List Nat)))) := by
    simp only [map_call_m, eval_l, Nat.unpair_pair]
    rfl
  have hex (j z : Nat) : eval_l map_extract_m (Nat.pair p (Nat.pair j z)) = z := by
    simp only [map_extract_m, eval_l, Nat.unpair_pair]
  rw [map_m, pipeline_eval_l, hcall, fold_encode_l, foldl_map_step_l c p s 0 ([] : List Nat), hex,
    List.append_nil, reverse_encode_l, List.reverse_reverse]
  simp only [Nat.zero_add]

/-- 全内部数域上的真实一步。回调取值记法来自同一实际图，不是新对象函数。 -/
theorem map_step_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {C S : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C)
    (hS : graph_semantics_l (graph_m (map_step_m c)) S) (p i A a y : num_l ℳ) :
    relation_l S (value_l (value_l p (value_l i A)) a) y ↔
      ∃ m, relation_l C (value_l p (value_l i a)) m ∧
        value_l p (value_l (succ_l i) (succ_l (value_l m A))) = y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ c hC
  have hp : value_spec_l map_p_m _ := comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ)
  have hi : value_spec_l map_i_m _ :=
    comp_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)) (left_value_l hℳ)
  have ha : value_spec_l map_acc_m _ :=
    comp_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (left_value_l hℳ)
  have hin : value_spec_l map_in_m _ := pair_value_l hℳ hp (pair_value_l hℳ hi (right_value_l hℳ))
  have hv := (pair_value_l hℳ hp (pair_value_l hℳ (comp_value_l hℳ (succ_value_l hℳ) hi)
    (comp_value_l hℳ (succ_value_l hℳ) (pair_value_l hℳ (comp_value_l hℳ hf hin) ha))))
    hS (value_l (value_l p (value_l i A)) a) y
  simp only [SecondOrderUnpairing.unpair_l] at hv
  rw [hv]
  simp only [hf hC, exists_eq_left']

/-- 任意内部参数和列表码上的初值接线。 -/
theorem map_call_rel_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    (hB : graph_semantics_l (graph_m map_call_m) B) (p x y : num_l ℳ) :
    relation_l B (value_l p x) y ↔
      value_l x (value_l p (value_l (zero_l ℳ) (zero_l ℳ))) = y := by
  have h := (pair_value_l hℳ (right_value_l hℳ)
    (pair_value_l hℳ (left_value_l hℳ) (pair_value_l hℳ (zero_value_l hℳ) (zero_value_l hℳ))))
    hB (value_l p x) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 从实际末状态取出逆序累计码。 -/
theorem map_extract_rel_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m map_extract_m) E) (p n acc y : num_l ℳ) :
    relation_l E (value_l p (value_l n acc)) y ↔ acc = y := by
  have h := (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ))
    hE (value_l p (value_l n acc)) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 完整映射图就是零初值折叠、实际提取、实际反转的同一组合。 -/
theorem map_graph_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {T F E B : set_l ℳ}
    (hT : graph_semantics_l (graph_m (map_m c)) T)
    (hF : graph_semantics_l (graph_m (fold_m (map_step_m c))) F)
    (hE : graph_semantics_l (graph_m map_extract_m) E)
    (hB : graph_semantics_l (graph_m map_call_m) B)
    (R : set_l ℳ) (hR : graph_semantics_l (graph_m reverse_m) R) (p x y : num_l ℳ) :
    relation_l T (value_l p x) y ↔
      ∃ v s, relation_l F (value_l x (value_l p (value_l (zero_l ℳ) (zero_l ℳ)))) v ∧
        relation_l E v s ∧ relation_l R s y := by
  obtain ⟨Ex, _, hEx⟩ := graph_total_l hℳ (.comp map_extract_m (.comp (fold_m (map_step_m c)) map_call_m))
  obtain ⟨Cf, _, hCf⟩ := graph_total_l hℳ (.comp (fold_m (map_step_m c)) map_call_m)
  rw [comp_rel_l hℳ (graph_m reverse_m)
    (graph_m (.comp map_extract_m (.comp (fold_m (map_step_m c)) map_call_m))) R Ex hR hEx hT]
  simp only [comp_rel_l hℳ (graph_m map_extract_m)
    (graph_m (.comp (fold_m (map_step_m c)) map_call_m)) E Cf hE hCf hEx,
    comp_rel_l hℳ (graph_m (fold_m (map_step_m c))) (graph_m map_call_m) F B hF hB hCf,
    map_call_rel_l hℳ hB, exists_eq_left']
  constructor
  · rintro ⟨s, ⟨v, hf, he⟩, hr⟩
    exact ⟨v, s, hf, he, hr⟩
  · rintro ⟨v, s, hf, he, hr⟩
    exact ⟨s, ⟨v, hf, he⟩, hr⟩

#print axioms map_call_m
#print axioms map_p_m
#print axioms map_i_m
#print axioms map_acc_m
#print axioms map_in_m
#print axioms map_step_m
#print axioms map_extract_m
#print axioms map_m
#print axioms map_step_eval_l
#print axioms foldl_map_step_l
#print axioms map_encode_l
#print axioms map_step_rel_l
#print axioms map_call_rel_l
#print axioms map_extract_rel_l
#print axioms map_graph_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListMap
