import BMSConstructibleBridge.SecondOrderPairingBounds
import BMSConstructibleBridge.SecondOrderProgramMapLookup
import BMSConstructibleBridge.SecondOrderProgramAncestorStep
import BMSConstructibleBridge.SecondOrderProgramParentZero
import BMSConstructibleBridge.SecondOrderProgramRuntimeParent
import BMSConstructibleBridge.SecondOrderProgramParentRow
import BMSConstructibleBridge.SecondOrderProgramParentRowState
import BMSConstructibleBridge.SecondOrderProgramUniformParent
import BMSConstructibleBridge.SecondOrderProgramUniformParentState
import BMSConstructibleBridge.SecondOrderProgramUniformParentRecurrence
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListLookup

/-!
# 统一父查询与真实行表的逐内部下标双向连接

零行表 `zero_table_m` 与后继行表 `next_table_m` 都是
`map_m (query_m c)` 再配对自己的输入码，即"以实际父查询程序 `c` 为回调、对数组 `x` 逐项映射"。
于是行表第 `t` 位的读取就是回调该位源码项的结果；统一父程序 `parent_m` 又通过原 `run_m`
的状态把行表接回父查询。本模块把这两条通道对齐，得到四个双向规格：

- `zero_table_lookup_l`：零行表逐项读取 ↔ 原零父查询 `parent_zero_m`；
- `next_table_lookup_l`：后继行表逐项读取 ↔ 原运行父查询 `next_m`；
- `parent_zero_l`：统一父图在第 `zero` 行 ↔ 零父查询；
- `parent_succ_l`：统一父图在 `succ r` 行 ↔ 该行实际运行父查询。

全程在任意 `ℳ ⊨ theory_m` 上陈述：行号 `r`、下标 `t`、长度 `n` 与各行码都可以是非标准元素，
下标合法界只由 `SecondOrderOrder.lt_l t n` 的内部正差见证给出，不使用任何外部归纳、外部有限性
或以抽象父关系替换实际程序图。比较两张表时使用同一 `run_m` 图的函数性与内部配对码单射，
只消去源码项的存在见证；越界（`n ≤ t`）读取不在本模块陈述，它属于有界查询层的 `some`/`none` 边界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentLookup

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramParentRow (zero_table_m next_table_m)
open SecondOrderProgramParentRowState (zero_table_rel_l next_table_rel_l zero_width_l next_width_l)
open SecondOrderProgramAncestorStep (query_m query_rel_l)
open SecondOrderProgramParentZero (parent_zero_m)
open SecondOrderProgramRuntimeParent (next_m)
open SecondOrderProgramListMap (map_m)
open SecondOrderProgramMapLookup (map_lookup_lt_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramUniformParent (parent_m run_m)
open SecondOrderProgramUniformParentState (parent_table_l)
open SecondOrderProgramUniformParentRecurrence (zero_table_l succ_table_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 内部配对码等式消去第二分量，用于比较同一 `run_m` 输入下的两个行码。 -/
private theorem pair_cancel_l (hℳ : Theory.Models ℳ theory_m) {a b c d : num_l ℳ}
    (h : value_l a b = value_l c d) : b = d :=
  (SecondOrderPairingBounds.injective_l hℳ a b c d h).2

/-- 零行表的逐项读取规格：行码 `Z x v`、数组长 `L x n` 与内部界 `lt_l t n` 时，
`E (pair v t) = y ↔ P (pair x t) = y`，左侧是实际行表逐位查询，右侧是实际零父查询程序
`parent_zero_m` 的图。中间 map 图与查询图在证明内由 `graph_total_l` 取得；源码项存在见证
由 `map_lookup_lt_l` 给出、经 `query_rel_l` 消去，反向用 `lookup_m` 图的函数性补足该见证。 -/
theorem zero_table_lookup_l (hℳ : Theory.Models ℳ theory_m) {Z E P L : set_l ℳ}
    (hZ : graph_semantics_l (graph_m zero_table_m) Z)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hP : graph_semantics_l (graph_m parent_zero_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (x v n t y : num_l ℳ) (hv : relation_l Z x v) (hn : relation_l L x n)
    (ht : SecondOrderOrder.lt_l t n) :
    relation_l E (value_l v t) y ↔ relation_l P (value_l x t) y := by
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m (query_m parent_zero_m))
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ (query_m parent_zero_m)
  have hmap : relation_l E (value_l v t) y ↔
      ∃ e : num_l ℳ, relation_l E (value_l x t) e ∧
        relation_l Q (value_l x (value_l t e)) y :=
    map_lookup_lt_l hℳ (query_m parent_zero_m) hM hQ hL hE x x v n t y
      ((zero_table_rel_l hℳ hZ hM x v).mp hv) hn ht
  constructor
  · intro hy
    obtain ⟨e, _, hq⟩ := hmap.mp hy
    exact (query_rel_l hℳ parent_zero_m hQ hP x t e y).mp hq
  · intro hp
    let hEf := function_of_semantics_l hℳ lookup_m hE
    obtain ⟨e, he, _⟩ := hEf (value_l x t)
    exact hmap.mpr ⟨e, he, (query_rel_l hℳ parent_zero_m hQ hP x t e y).mpr hp⟩

/-- 后继行表的逐项读取规格：行码 `N (pair x (pair r v)) = w`、数组长 `L x n` 与 `lt_l t n` 时，
`E (pair w t) = y ↔ P (pair (pair x (pair r v)) t) = y`，右侧是实际运行父查询程序 `next_m`
在同一上下文上的图。接线与消去方式同零行表。 -/
theorem next_table_lookup_l (hℳ : Theory.Models ℳ theory_m) {N E P L : set_l ℳ}
    (hN : graph_semantics_l (graph_m next_table_m) N)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hP : graph_semantics_l (graph_m next_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (x r v w n t y : num_l ℳ) (hw : relation_l N (value_l x (value_l r v)) w)
    (hn : relation_l L x n) (ht : SecondOrderOrder.lt_l t n) :
    relation_l E (value_l w t) y ↔
      relation_l P (value_l (value_l x (value_l r v)) t) y := by
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m (query_m next_m))
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ (query_m next_m)
  have hmap : relation_l E (value_l w t) y ↔
      ∃ e : num_l ℳ, relation_l E (value_l x t) e ∧
        relation_l Q (value_l (value_l x (value_l r v)) (value_l t e)) y :=
    map_lookup_lt_l hℳ (query_m next_m) hM hQ hL hE (value_l x (value_l r v)) x w n t y
      ((next_table_rel_l hℳ hN hM x r v w).mp hw) hn ht
  constructor
  · intro hy
    obtain ⟨e, _, hq⟩ := hmap.mp hy
    exact (query_rel_l hℳ next_m hQ hP (value_l x (value_l r v)) t e y).mp hq
  · intro hp
    let hEf := function_of_semantics_l hℳ lookup_m hE
    obtain ⟨e, he, _⟩ := hEf (value_l x t)
    exact hmap.mpr ⟨e, he, (query_rel_l hℳ next_m hQ hP (value_l x (value_l r v)) t e y).mpr hp⟩

/-- 统一父图在第 `zero` 行等于实际零父查询：`L x n` 与 `lt_l t n` 时
`P (pair (pair x zero) t) = y ↔ P0 (pair x t) = y`。正向由 `parent_table_l` 取出该行行码，
用 `zero_table_l` 与内部配对码单射把行码认成零行表值，再走 `zero_table_lookup_l`；
反向先取零行表值，经 `zero_table_l` 还原 `run_m` 的该行状态、`zero_width_l` 补行码长度，
再由 `parent_table_l` 组装。 -/
theorem parent_zero_l (hℳ : Theory.Models ℳ theory_m) {P P0 L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hP0 : graph_semantics_l (graph_m parent_zero_m) P0)
    (hL : graph_semantics_l (graph_m length_m) L)
    (x n t y : num_l ℳ) (hn : relation_l L x n) (ht : SecondOrderOrder.lt_l t n) :
    relation_l P (value_l (value_l x (zero_l ℳ)) t) y ↔ relation_l P0 (value_l x t) y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ run_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ zero_table_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  constructor
  · intro hy
    obtain ⟨v, hvR, _, hEt⟩ :=
      (parent_table_l hℳ hP hR hE hL hn (zero_l ℳ) t y).mp hy
    obtain ⟨v', hZv', heq⟩ :=
      (zero_table_l hℳ hR hZ x (value_l x (value_l (succ_l (zero_l ℳ)) v))).mp hvR
    have hv'v : v' = v := pair_cancel_l hℳ (pair_cancel_l hℳ heq)
    have hZv : relation_l Z x v := by
      rw [← hv'v]
      exact hZv'
    exact (zero_table_lookup_l hℳ hZ hE hP0 hL x v n t y hZv hn ht).mp hEt
  · intro hp0
    obtain ⟨v, hZv, _⟩ := function_of_semantics_l hℳ zero_table_m hZ x
    have hEt : relation_l E (value_l v t) y :=
      (zero_table_lookup_l hℳ hZ hE hP0 hL x v n t y hZv hn ht).mpr hp0
    refine (parent_table_l hℳ hP hR hE hL hn (zero_l ℳ) t y).mpr
      ⟨v, (zero_table_l hℳ hR hZ x _).mpr ⟨v, hZv, rfl⟩, zero_width_l hℳ hZ hL hZv hn, hEt⟩

/-- 统一父图在 `succ r` 行等于该行的实际运行父查询：给定真实 `run_m` 后继状态
`R (pair x r) = pair x (pair (succ r) v)`、`L x n` 与 `lt_l t n` 时
`P (pair (pair x (succ r)) t) = y ↔ PN (pair (pair x (pair (succ r) v)) t) = y`。
两张行码由同一 `run_m` 图的函数性与 `succ_table_l` 的等式经内部配对码单射认成同一个，
长度由 `next_width_l` 补齐；不以外部归纳或以抽象父关系替换实际图。 -/
theorem parent_succ_l (hℳ : Theory.Models ℳ theory_m) {P R PN L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hR : graph_semantics_l (graph_m run_m) R)
    (hPN : graph_semantics_l (graph_m next_m) PN)
    (hL : graph_semantics_l (graph_m length_m) L)
    (x r v n t y : num_l ℳ)
    (hv : relation_l R (value_l x r) (value_l x (value_l (succ_l r) v)))
    (hn : relation_l L x n) (ht : SecondOrderOrder.lt_l t n) :
    relation_l P (value_l (value_l x (succ_l r)) t) y ↔
      relation_l PN (value_l (value_l x (value_l (succ_l r) v)) t) y := by
  obtain ⟨N, _, hN⟩ := graph_total_l hℳ next_table_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  let hRf := function_of_semantics_l hℳ run_m hR
  constructor
  · intro hy
    obtain ⟨w, hwR, _, hEt⟩ := (parent_table_l hℳ hP hR hE hL hn (succ_l r) t y).mp hy
    obtain ⟨v', w', hRv', hNw', heq⟩ :=
      (succ_table_l hℳ hR hN x r (value_l x (value_l (succ_l (succ_l r)) w))).mp hwR
    have hv'v : v' = v :=
      pair_cancel_l hℳ (pair_cancel_l hℳ (function_value_unique_l hRf hRv' hv))
    have hw'w : w' = w := pair_cancel_l hℳ (pair_cancel_l hℳ heq)
    have hNw : relation_l N (value_l x (value_l (succ_l r) v)) w := by
      rw [← hv'v, ← hw'w]
      exact hNw'
    exact (next_table_lookup_l hℳ hN hE hPN hL x (succ_l r) v w n t y hNw hn ht).mp hEt
  · intro hpn
    obtain ⟨w, hNw, _⟩ := function_of_semantics_l hℳ next_table_m hN
      (value_l x (value_l (succ_l r) v))
    have hEt : relation_l E (value_l w t) y :=
      (next_table_lookup_l hℳ hN hE hPN hL x (succ_l r) v w n t y hNw hn ht).mpr hpn
    refine (parent_table_l hℳ hP hR hE hL hn (succ_l r) t y).mpr
      ⟨w, (succ_table_l hℳ hR hN x r _).mpr ⟨v, w, hv, hNw, rfl⟩,
        next_width_l hℳ hN hL hNw hn, hEt⟩

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），无新增公理，
亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentLookup
