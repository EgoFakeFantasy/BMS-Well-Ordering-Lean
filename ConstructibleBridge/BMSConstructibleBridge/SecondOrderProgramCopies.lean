import BMSConstructibleBridge.SecondOrderProgramCopyBlock
import BMSConstructibleBridge.SecondOrderProgramListAppend

/-!
# 按原复制次数顺序拼接块

参数q为pair块(pair A末列)，A为pair数组(pair最大父行父列)。输入pair q count，
依次追加copyBlock的第0至count-1份。用原prec的当前步号作复制次数，故不需先构造
range列表；标准身份直接对应原range.flatMap，内部递推仍是原图的零/后继方程。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopies

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRecurrence SecondOrderProgramValue
open SecondOrderProgramCallbackValue
open SecondOrderProgramCopyBlock (copy_m copy_encode_l)
open SecondOrderProgramListAppend (append_m append_encode_l)
open SecondOrderProgramTrimHeight (array_encode_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 递归步的下标是当前复制次数，累计块不作copyBlock的原块输入。 -/
def copy_call_m : code_m := .pair (.comp .left .left)
  (.pair (.comp (.comp .left .right) .left)
    (.pair (.comp .left .right) (.comp (.comp .right .right) .left)))

/-- 已生成部分在左，新副本在右，保持原range.flatMap顺序。 -/
def step_m : code_m := .comp append_m
  (.pair (.comp .right .right) (.comp copy_m copy_call_m))

/-- 输入pair参数count；count为内部运行时数，不是外部编译界。 -/
def copies_m : code_m := .prec .zero step_m

/-- 当前复制次数和固定原块的标准接线。 -/
theorem copy_call_eval_l (b A l k v : Nat) :
    eval_l copy_call_m (Nat.pair (Nat.pair b (Nat.pair A l)) (Nat.pair k v)) =
      Nat.pair b (Nat.pair A (Nat.pair k l)) := by
  simp only [copy_call_m, eval_l, Nat.unpair_pair]

/-- 同一拼接程序也直接保持原嵌套数组编码。 -/
theorem append_array_encode_l (a b : BMSArray) :
    eval_l append_m (Nat.pair (Encodable.encode a) (Encodable.encode b)) =
      Encodable.encode (a ++ b) := by
  rw [array_encode_l a, array_encode_l b, append_encode_l, array_encode_l (a ++ b), List.map_append]

/-- 一步追加恰为原copyBlock的第k份，不以累计部分代替原块。 -/
theorem step_encode_l (a b s : BMSArray) (m p k : Nat) (l : List Nat) :
    eval_l step_m (Nat.pair
      (Nat.pair (Encodable.encode b) (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p)) (Encodable.encode l)))
      (Nat.pair k (Encodable.encode s))) = Encodable.encode (s ++ BMS.copyBlock a b m p k l) := by
  let q := Nat.pair
    (Nat.pair (Encodable.encode b) (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p)) (Encodable.encode l)))
    (Nat.pair k (Encodable.encode s))
  change eval_l append_m (Nat.pair q.unpair.2.unpair.2 (eval_l copy_m (eval_l copy_call_m q))) = _
  rw [copy_call_eval_l, copy_encode_l]
  simp only [q, Nat.unpair_pair, append_array_encode_l]

/-- 标准输出等于原range.flatMap全部副本，任意次数及原参数都覆盖。 -/
theorem copies_encode_l (a b : BMSArray) (m p count : Nat) (l : List Nat) :
    eval_l copies_m (Nat.pair
      (Nat.pair (Encodable.encode b) (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p)) (Encodable.encode l)))
      count) = Encodable.encode ((List.range count).flatMap (fun k => BMS.copyBlock a b m p k l)) := by
  rw [copies_m, PrimitiveProgram.prec_l]
  induction count with
  | zero => rfl
  | succ n ih =>
      simp only [PrimitiveHistory.run_l] at ih ⊢
      rw [ih, step_encode_l]
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- 任意内部步号的一步图，只调用同一copyBlock图和拼接图。 -/
theorem step_rel_l (hℳ : Theory.Models ℳ theory_m) {S C P : set_l ℳ}
    (hS : graph_semantics_l (graph_m step_m) S)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hP : graph_semantics_l (graph_m append_m) P) (b A l k v y : num_l ℳ) :
    relation_l S (value_l (value_l b (value_l A l)) (value_l k v)) y ↔
      ∃ s, relation_l C (value_l b (value_l A (value_l k l))) s ∧ relation_l P (value_l v s) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ copy_m hC
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ append_m hP
  have hb : value_spec_l (.comp .left .left) _ := comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ)
  have hA : value_spec_l (.comp (.comp .left .right) .left) _ :=
    comp_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)) (left_value_l hℳ)
  have hl : value_spec_l (.comp (.comp .right .right) .left) _ :=
    comp_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (left_value_l hℳ)
  have hk : value_spec_l (.comp .left .right) _ := comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)
  have hi : value_spec_l copy_call_m _ := pair_value_l hℳ hb (pair_value_l hℳ hA (pair_value_l hℳ hk hl))
  have hs := (comp_value_l hℳ hg (pair_value_l hℳ
    (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (comp_value_l hℳ hf hi)))
    hS (value_l (value_l b (value_l A l)) (value_l k v)) y
  simp only [SecondOrderUnpairing.unpair_l] at hs
  rw [hs]
  simp only [hf hC, hg hP, exists_eq_left']

/-- 原递归的零次数返回空数组码。 -/
theorem copies_zero_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R) (q y : num_l ℳ) :
    relation_l R (value_l q (zero_l ℳ)) y ↔ zero_l ℳ = y := by
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ step_m
  rw [prec_graph_zero_l hℳ (graph_m .zero) (graph_m step_m) Z S hZ hS R hR, zero_rel_l hℳ hZ]

/-- 原递归后继步保留任意内部次数，并按同一追加顺序展开。 -/
theorem copies_succ_l (hℳ : Theory.Models ℳ theory_m) {R C P : set_l ℳ}
    (hR : graph_semantics_l (graph_m copies_m) R)
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hP : graph_semantics_l (graph_m append_m) P) (b A l k y : num_l ℳ) :
    relation_l R (value_l (value_l b (value_l A l)) (succ_l k)) y ↔ ∃ v s,
      relation_l R (value_l (value_l b (value_l A l)) k) v ∧
      relation_l C (value_l b (value_l A (value_l k l))) s ∧ relation_l P (value_l v s) y := by
  obtain ⟨Z, hZf, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, hSf, hS⟩ := graph_total_l hℳ step_m
  rw [prec_graph_succ_l hℳ (graph_m .zero) (graph_m step_m) Z S hZ hS R hR hZf hSf]
  simp only [step_rel_l hℳ hS hC hP]
  constructor
  · rintro ⟨v, hv, s, hc, hp⟩
    exact ⟨v, s, hv, hc, hp⟩
  · rintro ⟨v, s, hv, hc, hp⟩
    exact ⟨v, hv, s, hc, hp⟩

#print axioms copy_call_m
#print axioms step_m
#print axioms copies_m
#print axioms copy_call_eval_l
#print axioms append_array_encode_l
#print axioms step_encode_l
#print axioms copies_encode_l
#print axioms step_rel_l
#print axioms copies_zero_l
#print axioms copies_succ_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopies
