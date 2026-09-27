import BMSConstructibleBridge.SecondOrderProgramArithmetic
import Mathlib.Logic.Equiv.List

/-!
# 原配对列表码的程序与内部规格

沿用 `Encodable (List Nat)` 的编码：空表为零，`a :: s` 为
`succ (pair a (encode s))`。前驱、头、尾均是原七构造 `code_m` 的显式程序，
不改变原编译器或 BM4 的编码。标准求值证明只用于确认算法身份；任意 Z₂ 模型中的
图规格独立使用原 `prec` 方程和图总性，保留所有非标准内部输入。

最后的严格缩小界是模型内部的一步不等式，不是外部良基性，也不是完整列表解码或
BM4 良序证明。后续迭代终止仍须使用实际公式的模型内部归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListCode

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRecurrence
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 同一七构造程序的标准求值 -/

/-- 在递归输入 `pair x (pair k u)` 上读取步号 `k`，忽略上一步的值。 -/
def pred_step_m : code_m := .comp .left .right

/-- 递归辅助程序：零步返回零，后继步返回先前步号。 -/
def pred_rec_m : code_m := .prec .zero pred_step_m

/-- 把一元输入变成固定参数为零的递归输入。 -/
def pred_input_m : code_m := .pair .zero PrimitiveProgram.id_m

/-- 截断前驱的显式程序，不使用最小化指令。 -/
def pred_m : code_m := .comp pred_rec_m pred_input_m

/-- 构造非空列表码；输入已经是头码与尾码的配对。 -/
def cons_m : code_m := .succ

/-- 空表取零，否则读取原配对码的第一坐标。 -/
def head_m : code_m := .comp .left pred_m

/-- 空表取零，否则读取原配对码的第二坐标。 -/
def tail_m : code_m := .comp .right pred_m

/-- 标准求值的前驱规格；此证明不用于推出非标准模型规格。 -/
theorem pred_eval_l (n : Nat) : eval_l pred_m n = n.pred := by
  change eval_l pred_rec_m (Nat.pair 0 (eval_l PrimitiveProgram.id_m n)) = n.pred
  rw [PrimitiveProgram.id_l, pred_rec_m, PrimitiveProgram.prec_l]
  cases n with
  | zero => rfl
  | succ n =>
      simp only [PrimitiveHistory.run_l, pred_step_m, eval_l, Nat.unpair_pair,
        Nat.pred_succ]

/-- 非空编码使用原 `List.encodable`，没有另选编码等价。 -/
theorem cons_encode_l (a : Nat) (s : List Nat) :
    eval_l cons_m (Nat.pair a (Encodable.encode s)) = Encodable.encode (a :: s) := by
  simp only [cons_m, eval_l, Encodable.encode_list_cons, Encodable.encode_nat]

/-- 原列表编码上的首项读取，空表返回零。 -/
theorem head_encode_l (s : List Nat) :
    eval_l head_m (Encodable.encode s) = s.head?.getD 0 := by
  change (eval_l pred_m (Encodable.encode s)).unpair.1 = _
  rw [pred_eval_l]
  cases s <;> simp [Encodable.encode_list_cons, Nat.unpair_pair]

/-- 原列表编码上的尾表读取，输出仍是同一编码。 -/
theorem tail_encode_l (s : List Nat) :
    eval_l tail_m (Encodable.encode s) = Encodable.encode s.tail := by
  change (eval_l pred_m (Encodable.encode s)).unpair.2 = _
  rw [pred_eval_l]
  cases s <;> simp [Encodable.encode_list_cons, Nat.unpair_pair]

/-! ## 原前驱图在全部内部输入上的零与后继方程 -/

/-- 递归步图确实返回步号，而不是上一步的值或外层参数。 -/
theorem pred_step_rel_l (hℳ : Theory.Models ℳ theory_m) {S : set_l ℳ}
    (hS : graph_semantics_l (graph_m pred_step_m) S) (x k v y : num_l ℳ) :
    relation_l S (value_l x (value_l k v)) y ↔ k = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  rw [comp_rel_l hℳ (graph_m .left) (graph_m .right) L R hL hR hS]
  simp only [right_rel_l hℳ hR, left_rel_l hℳ hL,
    SecondOrderUnpairing.unpair_l, exists_eq_left']

/-- 递归辅助图的零方程直接来自原 `prec` 图，不引入新的递归解释。 -/
theorem pred_rec_zero_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m pred_rec_m) R) (x y : num_l ℳ) :
    relation_l R (value_l x (zero_l ℳ)) y ↔ zero_l ℳ = y := by
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ pred_step_m
  rw [prec_graph_zero_l hℳ (graph_m .zero) (graph_m pred_step_m) Z S hZ hS R hR,
    zero_rel_l hℳ hZ]

/-- 后继步忽略上一步的结果；其存在由原程序总性提供，不对内部步号作外部归纳。 -/
theorem pred_rec_succ_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m pred_rec_m) R) (x k y : num_l ℳ) :
    relation_l R (value_l x (succ_l k)) y ↔ k = y := by
  obtain ⟨Z, hZf, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, hSf, hS⟩ := graph_total_l hℳ pred_step_m
  rw [prec_graph_succ_l hℳ (graph_m .zero) (graph_m pred_step_m)
    Z S hZ hS R hR hZf hSf]
  constructor
  · rintro ⟨v, _, hv⟩
    exact (pred_step_rel_l hℳ hS x k v y).mp hv
  · intro hky
    obtain ⟨v, hv, _⟩ := function_of_semantics_l hℳ pred_rec_m hR (value_l x k)
    exact ⟨v, hv, (pred_step_rel_l hℳ hS x k v y).mpr hky⟩

/-- 前驱输入图先保留原一元输入，再与零配对。 -/
theorem pred_input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m pred_input_m) I) (x y : num_l ℳ) :
    relation_l I x y ↔ value_l (zero_l ℳ) x = y := by
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  rw [pair_rel_l hℳ (graph_m .zero) (graph_m PrimitiveProgram.id_m) Z D hZ hD hI]
  simp only [zero_rel_l hℳ hZ, id_spec_l hℳ hD]
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    rwa [← ha, ← hb] at hab
  · intro hxy
    exact ⟨zero_l ℳ, x, rfl, rfl, hxy⟩

/-- 一元前驱图和原二元递归图的逐点桥。两图都使用原编译公式。 -/
theorem pred_bridge_l (hℳ : Theory.Models ℳ theory_m) {R P : set_l ℳ}
    (hR : graph_semantics_l (graph_m pred_rec_m) R)
    (hP : graph_semantics_l (graph_m pred_m) P) (x y : num_l ℳ) :
    relation_l P x y ↔ relation_l R (value_l (zero_l ℳ) x) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ pred_input_m
  rw [comp_rel_l hℳ (graph_m pred_rec_m) (graph_m pred_input_m) R I hR hI hP]
  simp only [pred_input_rel_l hℳ hI, exists_eq_left']

/-- 零的内部前驱仍为零，规格双向且无需额外函数性假设。 -/
theorem pred_zero_l (hℳ : Theory.Models ℳ theory_m) {P : set_l ℳ}
    (hP : graph_semantics_l (graph_m pred_m) P) (y : num_l ℳ) :
    relation_l P (zero_l ℳ) y ↔ zero_l ℳ = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ pred_rec_m
  rw [pred_bridge_l hℳ hR hP, pred_rec_zero_l hℳ hR]

/-- 每个内部后继的前驱都是原数，包含全部非标准内部数。 -/
theorem pred_succ_l (hℳ : Theory.Models ℳ theory_m) {P : set_l ℳ}
    (hP : graph_semantics_l (graph_m pred_m) P) (k y : num_l ℳ) :
    relation_l P (succ_l k) y ↔ k = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ pred_rec_m
  rw [pred_bridge_l hℳ hR hP, pred_rec_succ_l hℳ hR]

/-! ## 非空构造与首尾读取 -/

/-- 内部非空构造正是同一配对值的后继。 -/
theorem cons_rel_l (hℳ : Theory.Models ℳ theory_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m cons_m) C) (a t y : num_l ℳ) :
    relation_l C (value_l a t) y ↔ succ_l (value_l a t) = y :=
  succ_rel_l hℳ hC _ _

/-- 任意后继码的头是其前驱码的第一坐标。 -/
theorem head_succ_l (hℳ : Theory.Models ℳ theory_m) {H : set_l ℳ}
    (hH : graph_semantics_l (graph_m head_m) H) (k y : num_l ℳ) :
    relation_l H (succ_l k) y ↔ (SecondOrderUnpairing.value_l hℳ k).1 = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ pred_m
  rw [comp_rel_l hℳ (graph_m .left) (graph_m pred_m) L P hL hP hH]
  simp only [pred_succ_l hℳ hP, left_rel_l hℳ hL, exists_eq_left']

/-- 任意后继码的尾是其前驱码的第二坐标。 -/
theorem tail_succ_l (hℳ : Theory.Models ℳ theory_m) {T : set_l ℳ}
    (hT : graph_semantics_l (graph_m tail_m) T) (k y : num_l ℳ) :
    relation_l T (succ_l k) y ↔ (SecondOrderUnpairing.value_l hℳ k).2 = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ pred_m
  rw [comp_rel_l hℳ (graph_m .right) (graph_m pred_m) R P hR hP hT]
  simp only [pred_succ_l hℳ hP, right_rel_l hℳ hR, exists_eq_left']

/-- 从非空构造码精确读回头码，不要求它来自外部标准列表。 -/
theorem head_cons_l (hℳ : Theory.Models ℳ theory_m) {H : set_l ℳ}
    (hH : graph_semantics_l (graph_m head_m) H) (a t y : num_l ℳ) :
    relation_l H (succ_l (value_l a t)) y ↔ a = y := by
  rw [head_succ_l hℳ hH, SecondOrderUnpairing.unpair_l]

/-- 从非空构造码精确读回尾码，输出仍属于同一内部数域。 -/
theorem tail_cons_l (hℳ : Theory.Models ℳ theory_m) {T : set_l ℳ}
    (hT : graph_semantics_l (graph_m tail_m) T) (a t y : num_l ℳ) :
    relation_l T (succ_l (value_l a t)) y ↔ t = y := by
  rw [tail_succ_l hℳ hT, SecondOrderUnpairing.unpair_l]

/-- 内部零的反配对也是零对，来自原配对算术而非标准模型计算。 -/
theorem unpair_zero_l (hℳ : Theory.Models ℳ theory_m) :
    SecondOrderUnpairing.value_l hℳ (zero_l ℳ) = (zero_l ℳ, zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hzero : value_l (zero_l ℳ) (zero_l ℳ) = zero_l ℳ := by
    change value_l (0 : num_l ℳ) 0 = 0
    rw [SecondOrderPairingBounds.value_eq_l hℳ, if_neg (lt_irrefl _)]
    simp only [mul_zero, add_zero]
  exact (congrArg (SecondOrderUnpairing.value_l hℳ) hzero).symm.trans
    (SecondOrderUnpairing.unpair_l hℳ (zero_l ℳ) (zero_l ℳ))

/-- 空码的头读取总化为零。 -/
theorem head_zero_l (hℳ : Theory.Models ℳ theory_m) {H : set_l ℳ}
    (hH : graph_semantics_l (graph_m head_m) H) (y : num_l ℳ) :
    relation_l H (zero_l ℳ) y ↔ zero_l ℳ = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ pred_m
  rw [comp_rel_l hℳ (graph_m .left) (graph_m pred_m) L P hL hP hH]
  simp only [pred_zero_l hℳ hP, left_rel_l hℳ hL, exists_eq_left', unpair_zero_l]

/-- 空码的尾读取总化为零。 -/
theorem tail_zero_l (hℳ : Theory.Models ℳ theory_m) {T : set_l ℳ}
    (hT : graph_semantics_l (graph_m tail_m) T) (y : num_l ℳ) :
    relation_l T (zero_l ℳ) y ↔ zero_l ℳ = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ pred_m
  rw [comp_rel_l hℳ (graph_m .right) (graph_m pred_m) R P hR hP hT]
  simp only [pred_zero_l hℳ hP, right_rel_l hℳ hR, exists_eq_left', unpair_zero_l]

/-! ## 非零码的内部严格缩小界 -/

/-- 内部自然数满足 `n ≤ n²`。只分零与后继，不作外部归纳。 -/
theorem le_square_l (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    n ≤ n * n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  rcases predecessor_l hℳ n with hn | ⟨k, hk⟩
  · change n = 0 at hn
    simp only [hn, mul_zero, le_refl]
  · have hOne : (1 : num_l ℳ) ≤ n := by
      rw [hk, succ_eq_l hℳ]
      simpa only [zero_add] using add_le_add_left (zero_le_l hℳ k) (1 : num_l ℳ)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne (zero_le_l hℳ n)

/-- 原配对值同时界住两坐标，供头尾及后续内部迭代复用。 -/
theorem coordinates_le_pair_l (hℳ : Theory.Models ℳ theory_m) (a t : num_l ℳ) :
    letI := order_l hℳ
    a ≤ value_l a t ∧ t ≤ value_l a t := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hmax : max a t ≤ value_l a t :=
    (le_square_l hℳ (max a t)).trans (SecondOrderPairingBounds.interval_l hℳ a t).1
  exact ⟨(le_max_left a t).trans hmax, (le_max_right a t).trans hmax⟩

/-- 配对的两坐标均严格小于对应非空列表码。 -/
theorem coordinates_lt_cons_l (hℳ : Theory.Models ℳ theory_m) (a t : num_l ℳ) :
    SecondOrderOrder.lt_l a (succ_l (value_l a t)) ∧
      SecondOrderOrder.lt_l t (succ_l (value_l a t)) := by
  letI := order_l hℳ
  have hb := coordinates_le_pair_l hℳ a t
  exact ⟨lt_of_le_of_lt hb.1 (lt_own_succ_l hℳ _),
    lt_of_le_of_lt hb.2 (lt_own_succ_l hℳ _)⟩

/-- 任意非零内部输入的尾码严格缩小；不是对内部序作外部良基递归。 -/
theorem tail_lt_l (hℳ : Theory.Models ℳ theory_m) {T : set_l ℳ}
    (hT : graph_semantics_l (graph_m tail_m) T) {x y : num_l ℳ}
    (hx : x ≠ zero_l ℳ) (hxy : relation_l T x y) : SecondOrderOrder.lt_l y x := by
  rcases predecessor_l hℳ x with hzero | ⟨k, rfl⟩
  · exact False.elim (hx hzero)
  · have hy := (tail_succ_l hℳ hT k y).mp hxy
    have hb := (coordinates_lt_cons_l hℳ (SecondOrderUnpairing.value_l hℳ k).1
      (SecondOrderUnpairing.value_l hℳ k).2).2
    rwa [SecondOrderUnpairing.pair_l, hy] at hb

/-! ## 全部新公开声明的内核依赖审计 -/

#print axioms pred_step_m
#print axioms pred_rec_m
#print axioms pred_input_m
#print axioms pred_m
#print axioms cons_m
#print axioms head_m
#print axioms tail_m
#print axioms pred_eval_l
#print axioms cons_encode_l
#print axioms head_encode_l
#print axioms tail_encode_l
#print axioms pred_step_rel_l
#print axioms pred_rec_zero_l
#print axioms pred_rec_succ_l
#print axioms pred_input_rel_l
#print axioms pred_bridge_l
#print axioms pred_zero_l
#print axioms pred_succ_l
#print axioms cons_rel_l
#print axioms head_succ_l
#print axioms tail_succ_l
#print axioms head_cons_l
#print axioms tail_cons_l
#print axioms unpair_zero_l
#print axioms head_zero_l
#print axioms tail_zero_l
#print axioms le_square_l
#print axioms coordinates_le_pair_l
#print axioms coordinates_lt_cons_l
#print axioms tail_lt_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListCode
