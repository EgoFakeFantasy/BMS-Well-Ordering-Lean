import BMSConstructibleBridge.SecondOrderProgramListMap
import BMSConstructibleBridge.SecondOrderProgramListMapEntries
import BMSConstructibleBridge.SecondOrderProgramListMapFront
import BMSConstructibleBridge.SecondOrderProgramListReverse
import BMSConstructibleBridge.SecondOrderProgramListReverseIndices
import BMSConstructibleBridge.SecondOrderProgramLength
import BMSConstructibleBridge.SecondOrderProgramListLength
import BMSConstructibleBridge.SecondOrderProgramListIteration
import BMSConstructibleBridge.SecondOrderProgramListFold
import BMSConstructibleBridge.SecondOrderProgramListLookup

/-!
# `map_m c` 的全部内部有效下标双向规格

`map_m c` 把「以回调程序 `c` 逐项映射一个内部列表码」实现为
`reverse ∘ extract ∘ fold (map_step c) ∘ call`。本模块只给出这条程序的逐位读取规格，
不新增公式、语言检查或列表归纳，结论全部由逐层桥接拼接：

- `map_graph_rel_l` 在实际图上拆出折叠、提取、反转三段；
- `map_extract_rel_l` 与 `fold_length_l` 在零初始累计码上给出提取码长等于源码长；
- `reverse_indices_l` 把输出位换到累计码位，`fold_front_l` 再把累计码位读成源码位上的回调值。

公开签名只带结论中出现的四张图：`M`（map 图）、`C`（回调图）、`L`（长度图）、`K`（读取图）；
折叠、提取、调用、反转与迭代五张中间图在证明内部由 `graph_total_l` 取得，不外露给调用者。

全程在任意 `ℳ ⊨ theory_m` 上陈述：内部长度 `n` 与内部下标 `i` 都可以是非标准元素，界只由
`SecondOrderOrder.lt_l i n` 的内部正差见证给出，不假设任何外部标准性或有限性。结论保留原参数
`p` 与实际回调图 `C`（`relation_l C (value_l p (pair i e)) w`），不以宿主语言的函数值替代。
越界读取（`n ≤ i`）刻意不在此陈述：那需要消费实际 `map_length_l`，且不得写成「输出为零当且仅当
越界」——有界读取与越界补零的 `some`/`none` 边界只属于有界查询层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMapLookup

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListCode
open SecondOrderProgramListFold SecondOrderProgramListMap
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListReverse (reverse_m reverse_step_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- `map_m c` 在任意模型上的逐内部下标读取规格：`M (pair p x) = y`、`L x = n` 且 `lt_l i n` 时，
输出第 `i` 位等于某个源码第 `i` 项经回调图 `C` 得到的值：
`K (pair y i) = w ↔ ∃ e, K (pair x i) = e ∧ C (pair p (pair i e)) = w`。

五张中间图由 `graph_total_l` 在证明内取得；`lt_l` 的正差见证 `i + succ k = n` 经
`succ_add_l`／`add_succ_l`／`add_comm_l` 对齐成 `succ i + k = n` 与 `succ k + i = n` 两个换位界，
反转桥把输出位 `i` 接到累计码位 `k`，前段桥在起始下标 `0` 处把累计码位 `k` 归约到源码位 `i`
上的回调值，最后 `zero_add_l` 与配对槽见证代入消去收成单存在式。 -/
theorem map_lookup_lt_l (hℳ : Theory.Models ℳ theory_m) (c : code_m)
    {M C L K : set_l ℳ}
    (hM : graph_semantics_l (graph_m (map_m c)) M)
    (hC : graph_semantics_l (graph_m c) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hK : graph_semantics_l (graph_m lookup_m) K)
    (p x y n i w : num_l ℳ) (hm : relation_l M (value_l p x) y)
    (hxn : relation_l L x n) (hit : SecondOrderOrder.lt_l i n) :
    relation_l K (value_l y i) w ↔
      ∃ e : num_l ℳ, relation_l K (value_l x i) e ∧
        relation_l C (value_l p (value_l i e)) w := by
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m (map_step_m c))
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ map_extract_m
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ map_call_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ reverse_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨RF, _, hRF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨v, s, hFv, hEs, hRy⟩ := (map_graph_rel_l hℳ c hM hF hE hB R hR p x y).mp hm
  obtain ⟨k, hk⟩ := hit
  have h00 : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (SecondOrderProgramLength.length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
      ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  have hinit : relation_l E (value_l p (value_l (zero_l ℳ) (zero_l ℳ))) (zero_l ℳ) :=
    (map_extract_rel_l hℳ hE p (zero_l ℳ) (zero_l ℳ) (zero_l ℳ)).mpr rfl
  have hsn : relation_l L s n := by
    rw [← add_zero_l hℳ n]
    exact SecondOrderProgramListMapEntries.fold_length_l hℳ c hC hF hL hE hI x
      (value_l p (value_l (zero_l ℳ) (zero_l ℳ))) v n (zero_l ℳ) (zero_l ℳ) s
      hFv hinit hxn h00 hEs
  have hik : add_l (succ_l i) k = n :=
    (SecondOrderNumbers.succ_add_l hℳ i k).trans ((add_succ_l hℳ i k).symm.trans hk)
  have hcomm : succ_l (add_l k i) = succ_l (add_l i k) :=
    congrArg succ_l (SecondOrderNumbers.add_comm_l hℳ k i)
  have hfk : add_l (succ_l k) i = n :=
    (SecondOrderNumbers.succ_add_l hℳ k i).trans (hcomm.trans ((add_succ_l hℳ i k).symm.trans hk))
  have hrv : relation_l K (value_l y i) w ↔ relation_l K (value_l s k) w :=
    SecondOrderProgramListReverseIndices.reverse_indices_l hℳ hR hRF hL hK hI s y n i k w hRy hsn hik
  have hfr : relation_l K (value_l s k) w ↔
      ∃ e u : num_l ℳ, relation_l K (value_l x i) e ∧
        value_l (add_l (zero_l ℳ) i) e = u ∧ relation_l C (value_l p u) w :=
    SecondOrderProgramListMapFront.fold_front_l hℳ c hC hF hL hE hK hI x
      (value_l p (value_l (zero_l ℳ) (zero_l ℳ))) v n (zero_l ℳ) (zero_l ℳ) s p (zero_l ℳ)
      (value_l (zero_l ℳ) (zero_l ℳ)) k i w hFv hinit hxn h00 hEs rfl rfl hfk
  refine (hrv.trans hfr).trans ?_
  constructor
  · rintro ⟨e, u, he, hru, hCu⟩
    rw [SecondOrderNumbers.zero_add_l hℳ i] at hru
    subst hru
    exact ⟨e, he, hCu⟩
  · rintro ⟨e, he, hCu⟩
    refine ⟨e, value_l i e, he, ?_, hCu⟩
    rw [SecondOrderNumbers.zero_add_l hℳ i]

/-- given-source-entry 便利定理：源码第 `i` 项的读取见证 `e` 已给定时消去存在量词，
输出位与回调值双向等价：`K (pair y i) = w ↔ C (pair p (pair i e)) = w`。正向从 `map_lookup_lt_l`
取出见证，`graph_m lookup_m` 的图函数性（`function_of_semantics_l` 加 `function_value_unique_l`）
把存在见证钉回给定的 `e`；反向直接代入。 -/
theorem map_lookup_entry_l (hℳ : Theory.Models ℳ theory_m) (c : code_m)
    {M C L K : set_l ℳ}
    (hM : graph_semantics_l (graph_m (map_m c)) M)
    (hC : graph_semantics_l (graph_m c) C)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hK : graph_semantics_l (graph_m lookup_m) K)
    (p x y n i e w : num_l ℳ) (hm : relation_l M (value_l p x) y)
    (hxn : relation_l L x n) (hit : SecondOrderOrder.lt_l i n)
    (he : relation_l K (value_l x i) e) :
    relation_l K (value_l y i) w ↔ relation_l C (value_l p (value_l i e)) w := by
  let hKf := function_of_semantics_l hℳ lookup_m hK
  have hspec := map_lookup_lt_l hℳ c hM hC hL hK p x y n i w hm hxn hit
  constructor
  · intro hy
    obtain ⟨e', he', hCw⟩ := hspec.mp hy
    have hee : e = e' := function_value_unique_l hKf he he'
    rw [← hee] at hCw
    exact hCw
  · intro hCw
    exact hspec.mpr ⟨e, he, hCw⟩

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），无新增公理，
亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

#print axioms map_lookup_lt_l
#print axioms map_lookup_entry_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMapLookup
