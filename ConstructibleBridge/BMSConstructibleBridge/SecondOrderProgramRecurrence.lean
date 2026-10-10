import BMSConstructibleBridge.SecondOrderProgramSemantics
import BMSConstructibleBridge.SecondOrderProgramRecursion
import BMSConstructibleBridge.SecondOrderProgramConstructors
import BMSConstructibleBridge.SecondOrderHistory
import BMSConstructibleBridge.SecondOrderFunctions
import BMSConstructibleBridge.SecondOrderRelations

/-!
# 任务25：原 `prec` 图（K）的内部零方程与后继方程

按 Codex #1316 / #1382，在任务24（三整合模块，#1350 窄验收）之后，证明原 `prec` 历史语义
`prec_history_l`（Codex 规格中的 K）在**任意** ℳ ⊨ 原 Z₂ 理论内满足原始递归的两条特征方程：

* 零方程：`prec_history_l XF XG x 0 y ↔ XF x y`；
* 后继方程：`prec_history_l XF XG x (succ k) y ↔
  ∃ u, prec_history_l XF XG x k u ∧ XG (pair x (pair k u)) y`。

对应宿主 `run_l f g x 0 = f x`、`run_l f g x (succ n) = g (pair x (pair n (run_l f g x n)))`，
但全程在模型内部量词上成立，保留全部非标准内部 `k`，不对宿主 `Nat` 递归。

**复用不重写**（Codex #1350）：零方程反向只用已验的 `base_l` + `beta_sequence_iff_l`；
后继方程反向复用 `SecondOrderProgramRecursion.prec_history_succ_l` 加 `prec_history_unique_l`
与后继方程正向，绝不复制一遍追加构造的证明体。

本模块只新增独立文件，直接 import 已验收三模块及稳定的 `SecondOrderProgramSemantics`，
不改聚合根 / 旧 A-B / 原 code / 配置；不 commit / push / 同步主树。
无 sorry / admit / 新公理 / 关闭 linter。构建权：`LEAN_NUM_THREADS=1` 唯一串行。 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRecurrence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderNumbers
open SecondOrderDivision SecondOrderFiniteRange SecondOrderBetaSequence
open SecondOrderFunctions SecondOrderHistory
open PrimitiveFormulas SecondOrderProgramSemantics SecondOrderProgramRecursion
open SecondOrderProgramConstructors

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 零方程 -/

/-- 内部零方程：`x` 处长度 `0` 的 `prec` 历史恰取 `XF` 在 `x` 的值。
正向只靠 β 读取唯一性把端点 `y` 与初值 `a₀` 对齐；反向用 `base_l` 造一格历史，
再经 `beta_sequence_iff_l` 在长度 `succ 0` 上编码出配对码 `b`、`c`。 -/
theorem prec_history_zero_l (hℳ : Theory.Models ℳ theory_m)
    {XF XG : set_l ℳ} {x y : num_l ℳ} :
    prec_history_l XF XG x (zero_l ℳ) y ↔ relation_l XF x y := by
  constructor
  · rintro ⟨b, c, ⟨a₀, ha₀, hβ0⟩, hβy, _steps⟩
    have : a₀ = y := beta_rel_unique_l hℳ hβ0 hβy
    subst this
    exact ha₀
  · intro hxy
    letI := semiring_l hℳ
    letI := order_l hℳ
    letI := ordered_l hℳ
    -- 一格内部历史 `H`，在索引 `0` 读到目标值 `y`。
    obtain ⟨H, hH⟩ := base_l hℳ XF y
    obtain ⟨b, c, hbiff⟩ := beta_sequence_iff_l hℳ H (succ_l (zero_l ℳ)) hH.1
    have hz : SecondOrderOrder.lt_l (zero_l ℳ) (succ_l (zero_l ℳ)) :=
      lt_own_succ_l hℳ (zero_l ℳ)
    have hβ0y : beta_rel_l b c (zero_l ℳ) y := (hbiff (zero_l ℳ) hz y).mpr hH.2.1
    refine ⟨b, c, ⟨y, hxy, hβ0y⟩, hβ0y, ?_⟩
    intro i hi
    exact False.elim (not_lt_of_ge (zero_le_l hℳ i) hi)

/-! ## 后继方程 -/

/-- 内部后继方程正向：长度 `succ k` 的历史，其末步恰好把 `XF`-历史在 `k` 处的值 `u`
经 `XG` 在 `pair x (pair k u)` 处转移到输出 `y`。只用末步 β 分解与唯一性，不需要 `XG` 全函数。 -/
theorem prec_history_succ_forward_l (hℳ : Theory.Models ℳ theory_m)
    {XF XG : set_l ℳ} {x k y : num_l ℳ}
    (h : prec_history_l XF XG x (succ_l k) y) :
    ∃ u : num_l ℳ, prec_history_l XF XG x k u ∧
      relation_l XG (value_l x (value_l k u)) y := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨b, c, hbase, hβy, hsteps⟩ := h
  -- 末步 `k < succ k` 给出 `k` 处值 `u`、`succ k` 处值 `v` 及 `XG` 转移。
  obtain ⟨u, v, hu, hv, hxg⟩ := hsteps k (lt_own_succ_l hℳ k)
  have hvy : v = y := beta_rel_unique_l hℳ hv hβy
  subst hvy
  refine ⟨u, ⟨b, c, hbase, hu, ?_⟩, hxg⟩
  intro i hi
  exact hsteps i (SecondOrderOrder.trans_l hℳ hi (lt_own_succ_l hℳ k))

/-- 内部后继方程反向：给定 `k` 处历史值 `u` 与 `XG` 在 `pair x (pair k u)` 处的输出 `y`，
构造 `succ k` 处历史。复用已验收的追加步 `prec_history_succ_l`（它取 `XG` 的唯一值），
再以 `prec_history_unique_l` 与后继方程正向把所取的 `y'` 对齐回给定的 `y`，
不重复一遍重编码构造。 -/
theorem prec_history_succ_backward_l (hℳ : Theory.Models ℳ theory_m)
    {XF XG : set_l ℳ} (hXF : function_l XF) (hXG : function_l XG) {x k y : num_l ℳ}
    (hu : ∃ u, prec_history_l XF XG x k u ∧
      relation_l XG (value_l x (value_l k u)) y) :
    prec_history_l XF XG x (succ_l k) y := by
  obtain ⟨u, hhu, hy⟩ := hu
  obtain ⟨y', hhy'⟩ := prec_history_succ_l hℳ hXG ⟨u, hhu⟩
  -- 后继方程正向把 `succ k` 历史拆成某个 `u''` 处的 `k` 历史加 `XG` 转移到 `y'`。
  obtain ⟨u'', hhu'', hxy'⟩ := prec_history_succ_forward_l hℳ hhy'
  -- `k` 处历史值唯一：`u'' = u`；代回转移式。
  have hu2u : u'' = u := prec_history_unique_l hℳ hXF hXG hhu'' hhu
  rw [hu2u] at hxy'
  -- 于是 `XG` 在同一点 `pair x (pair k u)` 上给出 `y'` 与 `y`；由全函数唯一性 `y' = y`。
  obtain ⟨_, _, huniq⟩ := hXG (value_l x (value_l k u))
  have hyy' : y' = y := (huniq y' hxy').trans (huniq y hy).symm
  exact hyy' ▸ hhy'

/-- 内部后继方程（双向）。 -/
theorem prec_history_succ_eq_l (hℳ : Theory.Models ℳ theory_m)
    {XF XG : set_l ℳ} (hXF : function_l XF) (hXG : function_l XG) {x k y : num_l ℳ} :
    prec_history_l XF XG x (succ_l k) y ↔
      ∃ u : num_l ℳ, prec_history_l XF XG x k u ∧
        relation_l XG (value_l x (value_l k u)) y :=
  ⟨prec_history_succ_forward_l hℳ, prec_history_succ_backward_l hℳ hXF hXG⟩

/-! ## 原 XR 图桥与图层面方程

上面两条方程作用在内部历史 `prec_history_l`（K）上。任务25 的第三项把同一结论抬到
原 `prec` 图 `XR`：先用 `prec_primitive_syntax_l` 按自由槽 `[input, output]` 实例、与
`hXR` 在同一 `pushFree` 环境相接，得到 `XR` 逐点等价于 `prec_history_l` 的**图桥**；
再在图桥上传输零方程与后继方程。 -/

/-- **原 XR 图桥**：设 `XF`、`XG` 分别是子程序 `F`、`G` 的任意模型图，`XR` 满足
`F.prec_l G` 的统一值语义。则 `XR` 在配对码 `value_l x n` 处的输出恰等于内部 `prec` 历史
`prec_history_l XF XG x n y`。图桥本身**不需要** `XR`、`XF`、`XG` 的函数性假设：只用
`prec_primitive_syntax_l` 与 `hXR` 同环境相接，配对码相等 `value_l x' n' = value_l x n`
由 `SecondOrderPairingBounds.injective_l` 消去。 -/
theorem prec_graph_bridge_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    (XR : set_l ℳ) (hXR : graph_semantics_l (F.prec_l G) XR)
    (x n y : num_l ℳ) :
    relation_l XR (value_l x n) y ↔ prec_history_l XF XG x n y := by
  -- 在 `[input, output]` 两自由槽上把 `hXR` 与 `prec_primitive_syntax_l` 相接。
  have key : relation_l XR (value_l x n) y ↔
      ∃ x' n' : num_l ℳ, value_l x' n' = value_l x n ∧ prec_history_l XF XG x' n' y := by
    have hL : Formula.satisfies (((Env.empty (M := ℳ)).pushFree y).pushFree (value_l x n))
        ((F.prec_l G).form (.fvar .here) (.fvar (.there .here))) ↔
        relation_l XR (value_l x n) y := by
      simpa only [Term.eval, Env.pushFree, Assignment.push] using
        hXR (((Env.empty (M := ℳ)).pushFree y).pushFree (value_l x n))
        (.fvar .here) (.fvar (.there .here))
    have hR : Formula.satisfies (((Env.empty (M := ℳ)).pushFree y).pushFree (value_l x n))
        ((F.prec_l G).form (.fvar .here) (.fvar (.there .here))) ↔
        ∃ x' n' : num_l ℳ, value_l x' n' = value_l x n ∧
          prec_history_l XF XG x' n' y := by
      simpa only [Term.eval, Env.pushFree, Assignment.push] using
        prec_primitive_syntax_l hℳ F G XF XG hF hG
        (((Env.empty (M := ℳ)).pushFree y).pushFree (value_l x n))
        (.fvar .here) (.fvar (.there .here))
    exact hL.symm.trans hR
  rw [key]
  constructor
  · rintro ⟨x', n', hval, hhist⟩
    obtain ⟨hx, hn⟩ := SecondOrderPairingBounds.injective_l hℳ x' n' x n hval
    exact hx ▸ hn ▸ hhist
  · intro hh
    exact ⟨x, n, rfl, hh⟩

/-- 图层面的零方程：`XR` 在 `value_l x 0` 处取值 `y` 当且仅当 `XF x y`。
由图桥把左侧换成 `prec_history_l ... (zero_l ℳ) y`，再接 K 层零方程。 -/
theorem prec_graph_zero_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    (XR : set_l ℳ) (hXR : graph_semantics_l (F.prec_l G) XR)
    (x y : num_l ℳ) :
    relation_l XR (value_l x (zero_l ℳ)) y ↔ relation_l XF x y := by
  rw [prec_graph_bridge_l hℳ F G XF XG hF hG XR hXR x (zero_l ℳ) y]
  exact prec_history_zero_l hℳ

/-- 图层面的后继方程：`XR` 在 `value_l x (succ k)` 处取值 `y` 当且仅当存在 `u`，
使 `XR` 在 `value_l x k` 处取值 `u` 且 `XG` 在 `value_l x (value_l k u)` 处取值 `y`。
与 K 层后继方程一样需要 `XF`、`XG` 的函数性（后继方程反向用到历史值唯一）。 -/
theorem prec_graph_succ_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    (XR : set_l ℳ) (hXR : graph_semantics_l (F.prec_l G) XR)
    (hXF : function_l XF) (hXG : function_l XG) (x k y : num_l ℳ) :
    relation_l XR (value_l x (succ_l k)) y ↔
      ∃ u : num_l ℳ, relation_l XR (value_l x k) u ∧
        relation_l XG (value_l x (value_l k u)) y := by
  simp only [prec_graph_bridge_l hℳ F G XF XG hF hG XR hXR]
  exact prec_history_succ_eq_l hℳ hXF hXG

/-! ## 公理审计

任务25 的新出口只应继承已复编模块的可信基（`propext / Classical.choice / Quot.sound`），
不得引入 `sorryAx` 或新公理。 -/

#print axioms prec_history_zero_l
#print axioms prec_history_succ_forward_l
#print axioms prec_history_succ_backward_l
#print axioms prec_history_succ_eq_l
#print axioms prec_graph_bridge_l
#print axioms prec_graph_zero_l
#print axioms prec_graph_succ_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRecurrence
