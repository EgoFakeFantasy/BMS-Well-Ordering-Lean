import BMSConstructibleBridge.SecondOrderProgramCallbackValue
import BMSConstructibleBridge.SecondOrderProgramListCode
import YesMetaZFC.BMS.Generation

/-!
# 原初始数组的显式程序

原seed有两列，分别为同一高度的全零列与全一列。先用原prec重复首部添项，
再构造两个嵌套列表码；高度仍是运行时输入，不是外部选定的编译参数。
标准端精确连接原seed，内部端仅断言同一程序的递推图与接线，不预支生成不变量。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSeed

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRecurrence SecondOrderProgramValue
open SecondOrderProgramCallbackValue
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原递归输入pair条目(pair步号累计码)，把固定条目加在累计列表首部。 -/
def replicate_step_m : code_m := .comp .succ (.pair .left (.comp .right .right))

/-- 输入pair条目次数，零次为空列表。 -/
def replicate_m : code_m := .prec .zero replicate_step_m

/-- 初始数组第一列：高度个零。 -/
def zeros_m : code_m := .comp replicate_m (.pair .zero PrimitiveProgram.id_m)

/-- 初始数组第二列：高度个一。 -/
def ones_m : code_m := .comp replicate_m (.pair (PrimitiveProgram.const_m 1) PrimitiveProgram.id_m)

/-- 原两列顺序保持为零列、一列；外层尾表为空。 -/
def seed_m : code_m := .comp .succ
  (.pair zeros_m (.comp .succ (.pair ones_m .zero)))

/-- 同一重复程序在标准次数上产生原Encodable列表码。 -/
theorem replicate_encode_l (v n : Nat) :
    eval_l replicate_m (Nat.pair v n) = Encodable.encode (List.replicate n v) := by
  rw [replicate_m, PrimitiveProgram.prec_l]
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [PrimitiveHistory.run_l, replicate_step_m, eval_l, Nat.unpair_pair,
        List.replicate_succ, Encodable.encode_list_cons, Encodable.encode_nat] using
        congrArg (fun s => Nat.succ (Nat.pair v s)) ih

/-- 单一原程序逐高度等于原seed；未替换初始数组定义。 -/
theorem seed_encode_l (n : Nat) :
    eval_l seed_m n = Encodable.encode (BMS.seed n) := by
  change Nat.succ (Nat.pair (eval_l replicate_m (Nat.pair 0 (eval_l PrimitiveProgram.id_m n)))
    (Nat.succ (Nat.pair (eval_l replicate_m
      (Nat.pair (eval_l (PrimitiveProgram.const_m 1) n) (eval_l PrimitiveProgram.id_m n))) 0))) = _
  rw [PrimitiveProgram.id_l, PrimitiveProgram.const_l, replicate_encode_l, replicate_encode_l]
  simp only [BMS.seed, Encodable.encode_list_cons, Encodable.encode_list_nil]

/-- 任意内部输入的添项图，不从标准次数结论外推。 -/
theorem replicate_step_rel_l (hℳ : Theory.Models ℳ theory_m) {S : set_l ℳ}
    (hS : graph_semantics_l (graph_m replicate_step_m) S) (v k s y : num_l ℳ) :
    relation_l S (value_l v (value_l k s)) y ↔ succ_l (value_l v s) = y := by
  have hs : value_spec_l replicate_step_m _ := comp_value_l hℳ (succ_value_l hℳ)
    (pair_value_l hℳ (left_value_l hℳ)
      (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)))
  simpa only [SecondOrderUnpairing.unpair_l] using hs hS (value_l v (value_l k s)) y

/-- 内部零次数的重复码为空。 -/
theorem replicate_zero_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m replicate_m) R) (v y : num_l ℳ) :
    relation_l R (value_l v (zero_l ℳ)) y ↔ zero_l ℳ = y := by
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ replicate_step_m
  rw [prec_graph_zero_l hℳ (graph_m .zero) (graph_m replicate_step_m) Z S hZ hS R hR,
    zero_rel_l hℳ hZ]

/-- 任意内部后继次数恰在上一步输出首部添同一固定条目。 -/
theorem replicate_succ_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m replicate_m) R) (v k y : num_l ℳ) :
    relation_l R (value_l v (succ_l k)) y ↔
      ∃ s, relation_l R (value_l v k) s ∧ succ_l (value_l v s) = y := by
  obtain ⟨Z, hZf, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, hSf, hS⟩ := graph_total_l hℳ replicate_step_m
  rw [prec_graph_succ_l hℳ (graph_m .zero) (graph_m replicate_step_m) Z S hZ hS R hR hZf hSf]
  simp only [replicate_step_rel_l hℳ hS]

/-- 任意内部高度的原seed图由同一重复图产生两列，不假定高度标准。 -/
theorem seed_rel_l (hℳ : Theory.Models ℳ theory_m) {S R : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hR : graph_semantics_l (graph_m replicate_m) R) (n y : num_l ℳ) :
    relation_l S n y ↔ ∃ a b,
      relation_l R (value_l (zero_l ℳ) n) a ∧
      relation_l R (value_l (succ_l (zero_l ℳ)) n) b ∧
      succ_l (value_l a (succ_l (value_l b (zero_l ℳ)))) = y := by
  obtain ⟨r, hr, _⟩ := value_exists_l hℳ replicate_m hR
  have hz : value_spec_l zeros_m _ := comp_value_l hℳ hr
    (pair_value_l hℳ (zero_value_l hℳ) (id_value_l hℳ))
  have h1 : value_spec_l (PrimitiveProgram.const_m 1) (fun _ : num_l ℳ => succ_l (zero_l ℳ)) :=
    comp_value_l hℳ (succ_value_l hℳ) (zero_value_l hℳ)
  have ho : value_spec_l ones_m _ := comp_value_l hℳ hr (pair_value_l hℳ h1 (id_value_l hℳ))
  have hs : value_spec_l seed_m _ := comp_value_l hℳ (succ_value_l hℳ)
    (pair_value_l hℳ hz (comp_value_l hℳ (succ_value_l hℳ) (pair_value_l hℳ ho (zero_value_l hℳ))))
  rw [hs hS]
  simp only [hr hR]
  constructor
  · intro hy
    exact ⟨r (value_l (zero_l ℳ) n), r (value_l (succ_l (zero_l ℳ)) n), rfl, rfl, hy⟩
  · rintro ⟨a, b, rfl, rfl, hy⟩
    exact hy

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSeed
