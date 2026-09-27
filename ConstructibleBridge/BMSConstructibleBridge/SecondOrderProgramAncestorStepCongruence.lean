import BMSConstructibleBridge.SecondOrderPairingBounds
import BMSConstructibleBridge.SecondOrderProgramArithmetic
import BMSConstructibleBridge.SecondOrderProgramAncestorStep
import BMSConstructibleBridge.SecondOrderProgramAncestorTransition

/-!
# 祖先单步在父查询逐点一致下的跨上下文合同

两个原 parent 程序 `c`、`d` 各自的单步状态转换图 `step_m c`、`step_m d` 只在一步内查询
parent 一次，其余动作全由选择器按查询结果决定：none 保持整个状态，some p 精确生成
`pair p (succ (pair p v))`。因此只要两条 parent 图在两个不同上下文码 `x`、`z` 上逐点一致
（`hparent : C (pair x j) = q ↔ D (pair z j) = q`，对所有内部 `j q`），两步图在各自上下文上
携带同一当前列 `b`、同一累计器 `v` 时的单步输出就双向等价。

`step_congr_l` 只组合已验接口：`C` 图的函数性给出实际唯一父值 `q`，模型 `predecessor`
把 `q` 二分为 `zero` 或 `succ p`（任意内部数，不做外部标准归纳），`hparent` 把该值传到
`D`，再分别套用 `step_none_l`／`step_some_l`；两侧输出等式用内部配对码单射消去不同的外层
上下文参数、保留相同的当前列与累计器形状。假设不是 `c = d` 也不是 `x = z`，结论也不
经过宿主 `Nat` 迭代。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorStepCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramArithmetic
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l step_some_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 内部配对码等式消去外层上下文槽：`value x u = value x u' ↔ u = u'`，
正向取配对单射的第二投影，反向是求值的同余性。 -/
private theorem outer_cancel_l (hℳ : Theory.Models ℳ theory_m) (x : num_l ℳ)
    (u u' : num_l ℳ) : value_l x u = value_l x u' ↔ u = u' :=
  ⟨fun h => (SecondOrderPairingBounds.injective_l hℳ x u x u' h).2, congrArg (value_l x)⟩

/-- 祖先单步的跨上下文合同：parent 图 `C`／`D` 在 `x`、`z` 上逐点一致时，单步图
`S (pair x (pair b v)) = pair x (pair t w) ↔ T (pair z (pair b v)) = pair z (pair t w)`
对任意内部行号 `b`、累计码 `v`、输出列 `t` 与输出值 `w` 双向成立。
两分支各自把整步规格化约为纯配对码等式，再由配对单射跨上下文传递。 -/
theorem step_congr_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m)
    {C D S T : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C)
    (hD : graph_semantics_l (graph_m d) D)
    (hS : graph_semantics_l (graph_m (step_m c)) S)
    (hT : graph_semantics_l (graph_m (step_m d)) T)
    (x z : num_l ℳ)
    (hparent : ∀ j q : num_l ℳ, relation_l C (value_l x j) q ↔ relation_l D (value_l z j) q)
    (b v t w : num_l ℳ) :
    relation_l S (value_l x (value_l b v)) (value_l x (value_l t w)) ↔
      relation_l T (value_l z (value_l b v)) (value_l z (value_l t w)) := by
  obtain ⟨q, hq, _⟩ := (function_of_semantics_l hℳ c hC) (value_l x b)
  rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
  · have hd : relation_l D (value_l z b) (zero_l ℳ) := (hparent b (zero_l ℳ)).mp hq
    have hs := step_none_l hℳ c hS hC hq v (value_l x (value_l t w))
    have ht := step_none_l hℳ d hT hD hd v (value_l z (value_l t w))
    exact hs.trans ((outer_cancel_l hℳ x _ _).trans
      ((outer_cancel_l hℳ z _ _).symm.trans ht.symm))
  · have hd : relation_l D (value_l z b) (succ_l p) := (hparent b (succ_l p)).mp hq
    have hs := step_some_l hℳ c hS hC hq v (value_l x (value_l t w))
    have ht := step_some_l hℳ d hT hD hd v (value_l z (value_l t w))
    exact hs.trans ((outer_cancel_l hℳ x _ _).trans
      ((outer_cancel_l hℳ z _ _).symm.trans ht.symm))

/-! ## 公理审计

本模块公共声明仅允许既有标准公理集合（propext/Quot.sound/Classical.choice），无新增公理，
亦不得有 `sorryAx`。审计置于命名空间内、`end` 之前。 -/

#print axioms step_congr_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorStepCongruence
