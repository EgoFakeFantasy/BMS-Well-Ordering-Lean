import BMSConstructibleBridge.SecondOrderProgramAncestorChain
import BMSConstructibleBridge.SecondOrderProgramAncestorMembership
import BMSConstructibleBridge.SecondOrderProgramAncestorIterationCongruence

/-!
# 祖先链与成员查询在不同参数上下文中的合同

父查询图在两个上下文逐点一致（每列取值经 `hparent` 互通）时，实际祖先链程序 `chain_m`
与成员程序 `member_m` 在两个不同的外层参数上给出完全相同的输出。链的一致性来自：
同燃料的两次实际迭代在每步保留共同的当前列与累计表码，且两侧调用同一个反转图；
成员一致性则完全消费共同的链输出与同一个 contains 图，是逐输出值的双向等价，
不仅是"非零一致"。全程只谈任意模型上的实际程序图：无 `c = d`、无 `x = z` 假设、
无宿主自然数归纳、不以抽象祖先关系替换实际图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorChain (chain_m chain_rel_l)
open SecondOrderProgramAncestorMembership (member_m member_rel_of_value_l)
open SecondOrderProgramAncestorIterationCongruence (common_state_l)
open SecondOrderProgramListReverse (reverse_m)
open SecondOrderProgramListContains (contains_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 迭代状态码 `pair 参数 (pair 列 累计码)` 的二次右投影就是内部累计表码，
在任意模型上由原配对单射直接归约，不需要任何标准性。 -/
private theorem state_acc_l (hℳ : Theory.Models ℳ theory_m) (a b c : num_l ℳ) :
    (SecondOrderUnpairing.value_l hℳ
      (SecondOrderUnpairing.value_l hℳ (value_l a (value_l b c))).2).2 = c := by
  simp only [SecondOrderUnpairing.unpair_l]

/-- 父查询逐点一致时，两个不同外层参数的实际祖先链图同燃料、同列给出同一输出：
`A (pair (pair x k) n) = y ↔ B (pair (pair z k) n) = y`。两侧各取实际迭代图，
用零累计初值的共同状态存在与迭代图函数性把链读法归约到同一累计表码上的同一个
反转图取值；不假设 `c = d` 或 `x = z`。 -/
theorem chain_congr_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m)
    {C D A B : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hB : graph_semantics_l (graph_m (chain_m d)) B) (x z : num_l ℳ)
    (hparent : ∀ j q : num_l ℳ, relation_l C (value_l x j) q ↔ relation_l D (value_l z j) q)
    (k n y : num_l ℳ) :
    relation_l A (value_l (value_l x k) n) y ↔
      relation_l B (value_l (value_l z k) n) y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (step_m c))
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ (repeat_m (step_m d))
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨a, b, hRa, hUb⟩ :=
    common_state_l hℳ c d hC hD hR hU x z hparent k (zero_l ℳ) n
  constructor
  · intro hy
    obtain ⟨s, hs, ht⟩ := (chain_rel_l hℳ c hA hR hT x k n y).mp hy
    have hse : value_l x (value_l a b) = s :=
      function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m c)) hR) hRa hs
    rw [← hse, state_acc_l hℳ x a b] at ht
    exact (chain_rel_l hℳ d hB hU hT z k n y).mpr
      ⟨value_l z (value_l a b), hUb, by rw [state_acc_l hℳ z a b]; exact ht⟩
  · intro hy
    obtain ⟨s, hs, ht⟩ := (chain_rel_l hℳ d hB hU hT z k n y).mp hy
    have hse : value_l z (value_l a b) = s :=
      function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m d)) hU) hUb hs
    rw [← hse, state_acc_l hℳ z a b] at ht
    exact (chain_rel_l hℳ c hA hR hT x k n y).mpr
      ⟨value_l x (value_l a b), hRa, by rw [state_acc_l hℳ x a b]; exact ht⟩

/-- 父查询逐点一致时，两个实际成员程序在同一候选列上完全同值：
`M (pair (pair x t) i) = y ↔ N (pair (pair z t) i) = y`，对任意内部输出 `y`
成立而非只断言非零一致。两侧链图由 `chain_congr_l` 给出同一个实际链输出码，
再接同一个 contains 图的 `member_rel_of_value_l` 双向桥。 -/
theorem member_congr_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m)
    {C D M N : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hN : graph_semantics_l (graph_m (member_m d)) N) (x z : num_l ℳ)
    (hparent : ∀ j q : num_l ℳ, relation_l C (value_l x j) q ↔ relation_l D (value_l z j) q)
    (t i y : num_l ℳ) :
    relation_l M (value_l (value_l x t) i) y ↔
      relation_l N (value_l (value_l z t) i) y := by
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ (chain_m c)
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ (chain_m d)
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ contains_m
  obtain ⟨v, hv, _⟩ :=
    function_of_semantics_l hℳ (chain_m c) hA (value_l (value_l x t) t)
  have hv' : relation_l B (value_l (value_l z t) t) v :=
    (chain_congr_l hℳ c d hC hD hA hB x z hparent t t v).mp hv
  exact (member_rel_of_value_l hℳ c hM hA hK hv i y).trans
    (member_rel_of_value_l hℳ d hN hB hK hv' i y).symm

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），无新增公理，
亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorCongruence
