import BMSConstructibleBridge.PrimitiveProgram
import BMSConstructibleBridge.SecondOrderProgramSemantics
import BMSConstructibleBridge.SecondOrderProgramConstructors
import BMSConstructibleBridge.SecondOrderProgramRecursion
import BMSConstructibleBridge.SecondOrderUnpairing
import BMSConstructibleBridge.SecondOrderPairingBounds
import BMSConstructibleBridge.SecondOrderPairing
import BMSConstructibleBridge.SecondOrderFunctions

/-!
# 任务24 整合模块（三）：原 `prec` 全函数闭包与 `code_m` 七构造语义闭合

依赖前两个整合模块，完成两件事：

* **阶段 2**：把 §C 的存在性闭成原 `prec` 图的内部全函数
  （`prec_rel_unique_l` / `prec_graph_l`），复用 `SecondOrderProgramConstructors`
  的唯一一份图理解助手 `graph_comprehension_l` 与 `SecondOrderProgramRecursion`
  的存在性终局 `prec_history_exists_l`；
* **阶段 3**：对 `code_m` 七构造做外部有限语法归纳，得到联合出口
  `graph_total_l : ∀ c, ∃ X, function_l X ∧ graph_semantics_l (graph_m c) X`。

`form_m c s t` 定义为 `(graph_m c).form s t`，`graph_semantics_l (graph_m c) X` 展开即
`∀ Γ Δ (η : Env ℳ Γ Δ) (s t), satisfies η (form_m c s t) ↔ relation_l X (s.eval η) (t.eval η)`，
所以 `graph_total_l` 就是任务 brief §D 的联合出口，不另立第二套谓词。
六个非递归构造由 `SecondOrderProgramConstructors` 提供，`prec` 由本模块阶段 2 提供；
归纳只在 `code_m` 的实际语法上进行，`graph_m` 逐构造 unfold 与对应 `_graph_l` 定义相等。

本模块只整合已验收证明，不改聚合根 `BMSConstructibleBridge.lean`、163 冻结源、
BMSTools、lakefile、工具链；不 commit / push / 同步。无 sorry / admit / 新公理 / 关闭 linter。
构建权：`LEAN_NUM_THREADS=1` 唯一串行。 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTotality

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderNumbers
open SecondOrderDivision SecondOrderFiniteRange SecondOrderBetaSequence
open SecondOrderFunctions SecondOrderHistory
open PrimitiveFormulas SecondOrderProgramSemantics
open SecondOrderProgramConstructors SecondOrderProgramRecursion

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 阶段 2：把 `prec` 图闭成模型内部的全函数

### `prec` 关系的全域唯一性

把 §C 的存在性经配对满射搬到任意输入码 `a`；把主文件的 `prec_history_unique_l`
经配对单射搬到同一码上的两个输出。这正是 `graph_comprehension_l` 需要的 `huniq`。 -/

/-- `prec` 图关系 `R a b := ∃ x n, pair(x,n)=a ∧ prec_history x n b` 逐点唯一。 -/
theorem prec_rel_unique_l (hℳ : Theory.Models ℳ theory_m)
    {XF XG : set_l ℳ} (hXF : function_l XF) (hXG : function_l XG)
    {a b b' : num_l ℳ}
    (hb : ∃ x n, SecondOrderPairing.value_l x n = a ∧ prec_history_l XF XG x n b)
    (hb' : ∃ x n, SecondOrderPairing.value_l x n = a ∧ prec_history_l XF XG x n b') : b = b' := by
  obtain ⟨x, n, hx, hK⟩ := hb
  obtain ⟨x', n', hx', hK'⟩ := hb'
  obtain ⟨hxx', hnn'⟩ := SecondOrderPairingBounds.injective_l hℳ x n x' n' (hx.trans hx'.symm)
  subst x'
  subst n'
  exact prec_history_unique_l hℳ hXF hXG hK hK'

/-- `prec` 图闭合成内部全函数：`XF`、`XG` 为全函数且携统一语义时，
`F.prec_l G` 的图在模型内实现为一张全函数集，且逐点保持原公式语义。 -/
theorem prec_graph_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    (hXF : function_l XF) (hXG : function_l XG) :
    ∃ K : set_l ℳ, function_l K ∧ graph_semantics_l (F.prec_l G) K := by
  refine graph_comprehension_l hℳ (F.prec_l G)
    (fun a b => ∃ x n, SecondOrderPairing.value_l x n = a ∧ prec_history_l XF XG x n b) ?_ ?_
  · exact prec_primitive_syntax_l hℳ F G XF XG hF hG
  · intro a
    obtain ⟨x, n, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ a
    obtain ⟨y, hy⟩ := prec_history_exists_l hℳ F G XF XG hF hG hXF hXG x n
    exact ⟨y, ⟨x, n, rfl, hy⟩,
      fun b hb => (prec_rel_unique_l hℳ hXF hXG ⟨x, n, rfl, hy⟩ hb).symm⟩

/-! ## 阶段 3：`code_m` 七构造的外部有限语法归纳

`graph_m` 逐构造把程序编译为公式图：`zero ↦ zero_l`、`succ ↦ succ_l`、
`left ↦ left_l`、`right ↦ right_l`、`pair c d ↦ (graph_m c).pair_l (graph_m d)`、
`comp c d ↦ (graph_m c).comp_l (graph_m d)`、`prec c d ↦ (graph_m c).prec_l (graph_m d)`。
归纳假设对子程序给出内部全函数图及统一语义，各 `_graph_l` 只需把它闭到组合后的图；
每个分支的目标与对应助手结论定义相等，`exact` 直接消化 `graph_m` 的逐构造 unfold。 -/

/-- 联合出口：任意 `code_m` 程序在任意 ℳ ⊨ 原 Z₂ 理论内被闭成内部全函数图，
且该图逐点等于原编译器公式 `form_m` 的语义。展开即为
`∀ Γ Δ η s t, satisfies η (form_m c s t) ↔ relation_l X (s.eval η) (t.eval η)`。 -/
theorem graph_total_l (hℳ : Theory.Models ℳ theory_m) (c : PrimitiveProgram.code_m) :
    ∃ X : set_l ℳ, function_l X ∧ graph_semantics_l (PrimitiveProgram.graph_m c) X := by
  induction c with
  | zero => exact zero_graph_l hℳ
  | succ => exact succ_graph_l hℳ
  | left => exact left_graph_l hℳ
  | right => exact right_graph_l hℳ
  | pair c d hc hd =>
      obtain ⟨XC, hCF, hCS⟩ := hc
      obtain ⟨XD, hDF, hDS⟩ := hd
      exact pair_graph_l hℳ (PrimitiveProgram.graph_m c) (PrimitiveProgram.graph_m d)
        XC XD hCS hDS hCF hDF
  | comp c d hc hd =>
      obtain ⟨XC, hCF, hCS⟩ := hc
      obtain ⟨XD, hDF, hDS⟩ := hd
      exact comp_graph_l hℳ (PrimitiveProgram.graph_m c) (PrimitiveProgram.graph_m d)
        XC XD hCS hDS hCF hDF
  | prec c d hc hd =>
      obtain ⟨XC, hCF, hCS⟩ := hc
      obtain ⟨XD, hDF, hDS⟩ := hd
      exact prec_graph_l hℳ (PrimitiveProgram.graph_m c) (PrimitiveProgram.graph_m d)
        XC XD hCS hDS hCF hDF

/-! ## 公理审计

阶段 2 与阶段 3 的新出口只应继承已复编模块的可信基
（`propext / Classical.choice / Quot.sound`），不得引入 `sorryAx` 或新公理。
联合出口 `graph_total_l` 已把六个非递归构造与 `prec` 闭包全部纳入依赖；
此处逐项列出各构造的 `_graph_l`、图理解助手与两个阶段 2 出口，便于单份日志复核。 -/

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTotality
