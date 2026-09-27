import BMSConstructibleBridge.SecondOrderProgramAncestorTransition
import BMSConstructibleBridge.SecondOrderProgramIteration
import BMSConstructibleBridge.SecondOrderProgramListReverse
import YesMetaZFC.BMS.Reference

/-!
# 原ancestorChain的显式程序

输入 pair (pair 参数 当前列) fuel，初始化空累计表，运行同一祖先状态步fuel次，
最后反转累计表。标准端逐输入等于原Reference.ancestorChain；内部端给出同一
实际迭代图与反转图的精确调用桥。后者是程序接线，不冒充所有内部下标的链规格。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorChain

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m step_some_eval_l step_none_eval_l)
open SecondOrderProgramListReverse (reverse_m reverse_encode_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 把原参数、当前列、空表与同一fuel配成迭代输入。 -/
def start_m : code_m := .pair
  (.pair (.comp .left .left) (.pair (.comp .right .left) .zero)) .right

/-- 原祖先状态的fuel次迭代。 -/
def states_m (c : code_m) : code_m := .comp (repeat_m (step_m c)) start_m

/-- 取最终累计表再反转，恢复从直接parent开始的原顺序。 -/
def chain_m (c : code_m) : code_m :=
  .comp reverse_m (.comp (.comp .right .right) (states_m c))

/-- 标准初始化保留原fuel与当前列。 -/
theorem start_eval_l (x k n : Nat) :
    eval_l start_m (Nat.pair (Nat.pair x k) n) = Nat.pair (Nat.pair x (Nat.pair k 0)) n := by
  simp only [start_m, eval_l, Nat.unpair_pair]

private theorem fixed_eval_l (f : Nat → Nat) {s : Nat} (hs : f s = s) (n : Nat) :
    f^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, hs]

/-- 更强标准累计器身份：任意初始列表接在祖先链逆序之后。 -/
theorem accumulator_eval_l (c : code_m) (f : Nat → Option Nat) (x : Nat)
    (hc : ∀ k, eval_l c (Nat.pair x k) = Encodable.encode (f k))
    (k n : Nat) (v : List Nat) :
    ((eval_l (step_m c))^[n] (Nat.pair x (Nat.pair k (Encodable.encode v)))).unpair.2.unpair.2 =
      Encodable.encode ((BMS.ancestorChain f k n).reverse ++ v) := by
  induction n generalizing k v with
  | zero => simp only [Function.iterate_zero_apply, Nat.unpair_pair, BMS.ancestorChain,
      List.reverse_nil, List.nil_append]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases hparent : f k with
      | none =>
          have hp : eval_l c (Nat.pair x k) = 0 := by
            simpa only [hparent, Encodable.encode_none] using hc k
          have hs := step_none_eval_l c x k (Encodable.encode v) hp
          rw [hs, fixed_eval_l _ hs]
          simp only [Nat.unpair_pair, BMS.ancestorChain, hparent, List.reverse_nil, List.nil_append]
      | some p =>
          have hp : eval_l c (Nat.pair x k) = p + 1 := by
            simpa only [hparent, Encodable.encode_some, Encodable.encode_nat] using hc k
          rw [step_some_eval_l c x k (Encodable.encode v) p hp]
          have hv : Nat.succ (Nat.pair p (Encodable.encode v)) = Encodable.encode (p :: v) :=
            SecondOrderProgramListCode.cons_encode_l p v
          rw [hv, ih p (p :: v)]
          simp only [BMS.ancestorChain, hparent, List.reverse_cons, List.append_assoc,
            List.singleton_append]

/-- 标准输出就是原ancestorChain的列表码，不替换parent函数或fuel。 -/
theorem chain_encode_l (c : code_m) (f : Nat → Option Nat) (x : Nat)
    (hc : ∀ k, eval_l c (Nat.pair x k) = Encodable.encode (f k)) (k n : Nat) :
    eval_l (chain_m c) (Nat.pair (Nat.pair x k) n) =
      Encodable.encode (BMS.ancestorChain f k n) := by
  change eval_l reverse_m ((eval_l (repeat_m (step_m c))
    (eval_l start_m (Nat.pair (Nat.pair x k) n))).unpair.2.unpair.2) = _
  rw [start_eval_l, repeat_eval_l]
  have h := accumulator_eval_l c f x hc k n []
  change ((eval_l (step_m c))^[n] (Nat.pair x (Nat.pair k 0))).unpair.2.unpair.2 = _ at h
  rw [h, List.append_nil, reverse_encode_l, List.reverse_reverse]

/-- 任意内部参数、当前列和fuel的初始化接线。 -/
theorem start_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m start_m) I) (x k n y : num_l ℳ) :
    relation_l I (value_l (value_l x k) n) y ↔ value_l (value_l x (value_l k (zero_l ℳ))) n = y := by
  have h := (pair_value_l hℳ
    (pair_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ))
      (pair_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (left_value_l hℳ)) (zero_value_l hℳ)))
    (right_value_l hℳ)) hI (value_l (value_l x k) n) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 内部状态调用就是同一原step的同一fuel次迭代。 -/
theorem states_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {S R : set_l ℳ}
    (hS : graph_semantics_l (graph_m (states_m c)) S)
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R) (x k n y : num_l ℳ) :
    relation_l S (value_l (value_l x k) n) y ↔
      relation_l R (value_l (value_l x (value_l k (zero_l ℳ))) n) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ start_m
  rw [comp_rel_l hℳ (graph_m (repeat_m (step_m c))) (graph_m start_m) R I hR hI hS]
  simp only [start_rel_l hℳ hI, exists_eq_left']

/-- 原链图精确读取同一迭代状态的累计坐标，并调用同一反转图。 -/
theorem chain_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {A R T : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hT : graph_semantics_l (graph_m reverse_m) T) (x k n y : num_l ℳ) :
    relation_l A (value_l (value_l x k) n) y ↔ ∃ s,
      relation_l R (value_l (value_l x (value_l k (zero_l ℳ))) n) s ∧
        relation_l T (SecondOrderUnpairing.value_l hℳ (SecondOrderUnpairing.value_l hℳ s).2).2 y := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (states_m c)
  obtain ⟨V, _, hV⟩ := graph_total_l hℳ (.comp .right .right)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (.comp (.comp .right .right) (states_m c))
  have hv (s z : num_l ℳ) : relation_l V s z ↔
      (SecondOrderUnpairing.value_l hℳ (SecondOrderUnpairing.value_l hℳ s).2).2 = z :=
    (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) hV s z
  rw [comp_rel_l hℳ (graph_m reverse_m) (graph_m (.comp (.comp .right .right) (states_m c)))
    T P hT hP hA]
  simp only [comp_rel_l hℳ (graph_m (.comp .right .right)) (graph_m (states_m c))
    V S hV hS hP, states_rel_l hℳ c hS hR, hv]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, ht⟩
    exact ⟨s, hs, ht⟩
  · rintro ⟨s, hs, ht⟩
    exact ⟨_, ⟨s, hs, rfl⟩, ht⟩

#print axioms start_m
#print axioms states_m
#print axioms chain_m
#print axioms start_eval_l
#print axioms accumulator_eval_l
#print axioms chain_encode_l
#print axioms start_rel_l
#print axioms states_rel_l
#print axioms chain_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorChain
