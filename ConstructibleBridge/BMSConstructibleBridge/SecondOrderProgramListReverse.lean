import BMSConstructibleBridge.SecondOrderProgramListFold

/-!
# 任务33 阶段A：原列表反转程序与 fold 递推

`SecondOrderProgramListFold.fold_m c` 以 `pair 列表码 累计值` 为输入，在同一实际折叠图上按
`List.foldl (fun w a => eval c (pair w a)) v` 从左到右更新累计值。本模块取
`reverse_step_m = .comp .succ (.pair .right .left)`：内部输入 `pair 累计列表码 当前项`，先
`.right` 取当前项、`.left` 取累计列表码，`.pair` 得 `pair 当前项 累计列表码`，再 `.succ` 接入
为原 cons 码（`encode (a :: t) = succ (pair (encode a) (encode t))`）。因此从空码 `0` 起对该
步折叠即把输入表逆序累到首端，得到反转。程序只用原七构造与已验折叠图，不新增列表递归指令、
不把标准 `eval` 直接推广为非标准规格。

阶段A交付：

* 标准端更强折叠身份 `reverse_fold_encode_l`：`fold reverse_step` 在 `pair (encode s) (encode t)`
  上输出 `encode (s.reverse ++ t)`；特化 `t = []` 得 `reverse_m (encode s) = encode s.reverse`。
* 内部端复用已验 `fold_zero_l / fold_cons_l`，在同一实际 `fold_m reverse_step_m` 折叠图上给出
  空码、非空 cons 递推式（累计值可任意非标准），并以 `reverse_bridge_l` 把 `reverse_m` 的图桥
  接到该折叠从零初值的调用。

本任务不是列表长度／下标对应（阶段B）、不是裁剪／展开算法，也不是最终 Z₂ 良序／保守传输闭合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListReverse

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListCode
open SecondOrderProgramListFold
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 反转步与程序定义 -/

/-- 折叠步：内部输入 `pair 累计列表码 当前项`，输出把当前项 cons 到累计列表码首端。
`.right` 取当前项、`.left` 取累计列表码，`.pair` 得 `pair 当前项 累计列表码`，`.succ` 即原
cons 码。 -/
def reverse_step_m : code_m := .comp .succ (.pair .right .left)

/-- 一元反转程序的输入：把待反转列表码与空初值 `0` 配成折叠输入。 -/
def reverse_input_m : code_m := .pair PrimitiveProgram.id_m .zero

/-- 原列表反转程序：从空码起对 `reverse_step_m` 折叠，只用已验证的折叠图。 -/
def reverse_m : code_m := .comp (fold_m reverse_step_m) reverse_input_m

/-! ## 标准端：更强折叠身份与反转正确性 -/

/-- 反转步在标准码上的原列身份：`eval reverse_step_m (pair v a) = succ (pair a v)`。 -/
theorem reverse_step_eval_l (v a : Nat) :
    eval_l reverse_step_m (Nat.pair v a) = Nat.succ (Nat.pair a v) := by
  simp only [reverse_step_m, eval_l, Nat.unpair_pair]

/-- 标准折叠恒等式（辅助归纳）：把 `fun w a => succ (pair a w)` 从左到右折叠进 `encode t`，
结果恰为 `encode (s.reverse ++ t)`，即累计器始终以原列表码保持逆序前缀接在 `t` 之前。 -/
theorem reverse_foldl_succ_l (s t : List Nat) :
    s.foldl (fun w a => Nat.succ (Nat.pair a w)) (Encodable.encode t) =
      Encodable.encode (s.reverse ++ t) := by
  induction s generalizing t with
  | nil => rfl
  | cons a s ih =>
      -- 累加器 `succ (pair a (encode t))` 就是原 cons 码 `encode (a :: t)`。
      have hstep : Nat.succ (Nat.pair a (Encodable.encode t)) = Encodable.encode (a :: t) := by
        show eval_l cons_m (Nat.pair a (Encodable.encode t)) = _
        exact cons_encode_l a t
      rw [List.foldl_cons, hstep, ih (a :: t), List.reverse_cons, List.append_assoc,
        List.singleton_append]

/-- 更强折叠身份：`fold reverse_step` 在 `pair (encode s) (encode t)` 上输出
`encode (s.reverse ++ t)`。逐点复用 `fold_encode_l` 把步替换为标准逆序累加，再由
`reverse_foldl_succ_l` 收口。 -/
theorem reverse_fold_encode_l (s t : List Nat) :
    eval_l (fold_m reverse_step_m) (Nat.pair (Encodable.encode s) (Encodable.encode t)) =
      Encodable.encode (s.reverse ++ t) := by
  rw [fold_encode_l]
  have h : s.foldl (fun w a => eval_l reverse_step_m (Nat.pair w a)) (Encodable.encode t) =
      s.foldl (fun w a => Nat.succ (Nat.pair a w)) (Encodable.encode t) := by
    congr 1
    · funext w a
      exact reverse_step_eval_l w a
  rw [h, reverse_foldl_succ_l]

/-- 标准端反转正确性：`reverse_m` 在 `encode s` 上等于 `encode s.reverse`，即空初值特化。 -/
theorem reverse_encode_l (s : List Nat) :
    eval_l reverse_m (Encodable.encode s) = Encodable.encode s.reverse := by
  change eval_l (fold_m reverse_step_m)
    (Nat.pair (eval_l PrimitiveProgram.id_m (Encodable.encode s)) 0) = _
  rw [PrimitiveProgram.id_l]
  have hnil : (0 : Nat) = Encodable.encode ([] : List Nat) := rfl
  rw [hnil, reverse_fold_encode_l, List.append_nil]

/-! ## 内部端：实际折叠图上的步、桥与零/cons 递推 -/

/-- 任意内部输入上，原反转步图把当前项接到累计列表码首端：
`relation (reverse_step 图) (pair 累计码 当前项) y ↔ succ (pair 当前项 累计码) = y`。
逐构造展开 `.comp .succ (.pair .right .left)`，与 `SecondOrderProgramReplicate.step_rel_l` 同构。 -/
theorem reverse_step_rel_l (hℳ : Theory.Models ℳ theory_m) {S : set_l ℳ}
    (hS : graph_semantics_l (graph_m reverse_step_m) S) (v a y : num_l ℳ) :
    relation_l S (value_l v a) y ↔ succ_l (value_l a v) = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (.pair .right .left)
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ .succ
  have hp (z : num_l ℳ) : relation_l P (value_l v a) z ↔ value_l a v = z := by
    rw [pair_rel_l hℳ (graph_m .right) (graph_m .left) R L hR hL hP]
    simp only [right_rel_l hℳ hR, left_rel_l hℳ hL, SecondOrderUnpairing.unpair_l]
    constructor
    · rintro ⟨b, w, rfl, rfl, hz⟩
      exact hz
    · intro hz
      exact ⟨a, v, rfl, rfl, hz⟩
  rw [comp_rel_l hℳ (graph_m .succ) (graph_m (.pair .right .left)) U P hU hP hS]
  simp only [hp, succ_rel_l hℳ hU, exists_eq_left']

/-- 折叠图空码递推：输入列表码为 `0` 时任意内部初值原样保持。直接复用已验 `fold_zero_l`。 -/
theorem reverse_fold_zero_l (hℳ : Theory.Models ℳ theory_m) {F : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m reverse_step_m)) F) (v y : num_l ℳ) :
    relation_l F (value_l (zero_l ℳ) v) y ↔ v = y :=
  fold_zero_l hℳ reverse_step_m hF v y

/-- 折叠图非空 cons 递推：把表头 `a` 从累计器上逆序累加，累计值更新为 `succ (pair a v)`。
由 `fold_cons_l` 展开内部步，再用 `reverse_step_rel_l` 消去步图。累计值、头、尾均可非标准。 -/
theorem reverse_fold_cons_l (hℳ : Theory.Models ℳ theory_m) {F C : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m reverse_step_m)) F)
    (hC : graph_semantics_l (graph_m reverse_step_m) C) (a t v y : num_l ℳ) :
    relation_l F (value_l (succ_l (value_l a t)) v) y ↔
      relation_l F (value_l t (succ_l (value_l a v))) y := by
  rw [fold_cons_l hℳ reverse_step_m hF hC]
  constructor
  · rintro ⟨w, hw, hy⟩
    have hwm : succ_l (value_l a v) = w := (reverse_step_rel_l hℳ hC v a w).mp hw
    rwa [← hwm] at hy
  · intro hy
    refine ⟨succ_l (value_l a v), ?_, hy⟩
    exact (reverse_step_rel_l hℳ hC v a _).mpr rfl

/-- 反转图桥：`reverse_m` 在任意内部列表码 `a` 上的输出，等于同一实际折叠图在零初值
`value_l a (zero_l ℳ)` 上的输出。逐构造展开 `.comp (fold reverse_step) (.pair id zero)`。 -/
theorem reverse_bridge_l (hℳ : Theory.Models ℳ theory_m) {T F : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hF : graph_semantics_l (graph_m (fold_m reverse_step_m)) F) (a y : num_l ℳ) :
    relation_l T a y ↔ relation_l F (value_l a (zero_l ℳ)) y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ reverse_input_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  rw [comp_rel_l hℳ (graph_m (fold_m reverse_step_m)) (graph_m reverse_input_m) F D hF hD hT]
  simp only [pair_rel_l hℳ (graph_m PrimitiveProgram.id_m) (graph_m .zero) A Z hA hZ hD,
    id_spec_l hℳ hA, zero_rel_l hℳ hZ]
  constructor
  · rintro ⟨p, ⟨x, z, rfl, rfl, rfl⟩, hy⟩
    exact hy
  · intro hy
    exact ⟨value_l a (zero_l ℳ), ⟨a, zero_l ℳ, rfl, rfl, rfl⟩, hy⟩

/-- 程序空码：空表的反转为空码。由桥接折叠零递推得到。 -/
theorem reverse_zero_l (hℳ : Theory.Models ℳ theory_m) {T F : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hF : graph_semantics_l (graph_m (fold_m reverse_step_m)) F) (y : num_l ℳ) :
    relation_l T (zero_l ℳ) y ↔ zero_l ℳ = y := by
  rw [reverse_bridge_l hℳ hT hF]
  rw [reverse_fold_zero_l hℳ hF (zero_l ℳ) y]

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），无新增公理，
亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListReverse
