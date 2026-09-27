import BMSConstructibleBridge.SecondOrderProgramSemantics
import BMSConstructibleBridge.SecondOrderHistory
import BMSConstructibleBridge.SecondOrderFunctions
import BMSConstructibleBridge.SecondOrderRelations

/-!
# 任务24 整合模块（二）：原 `prec` 历史语义的 §C 存在性

本模块整理已验收的 §C 独立草稿（`ProgramSemanticsPrecExistence` 的检查点 1–4），
只证明「对每个内部 `x n`，存在 `y` 使 `prec_history_l XF XG x n y`」，覆盖全部非标准内部 `n`。
按 Codex #1318 / #1334 的最小模块方案，这里是可导入的整合模块，不是重写：

* 复用已稳定、**不修改**的主文件 `SecondOrderProgramSemantics`（A/B：`prec_history_l`、
  `graph_semantics_l`、`prec_primitive_syntax_l`、`prec_history_unique_l`）；
* 不重复图理解助手（`graph_comprehension_l`）——它只存在于 `SecondOrderProgramConstructors`；
* 阶段 2 的 `prec` 全函数闭包（`prec_rel_unique` / `prec_graph_l`）随存在性出口交给
  `SecondOrderProgramTotality`，本模块只留纯粹的 §C 存在性。

存在性全程在对象语言 `succ` 上归纳（`SecondOrderModel.induct_l`），不对宿主 `Nat` 递归，
不对外部 `Prop` 裸归纳。无 sorry / admit / 新公理 / 关闭 linter。
构建权：`LEAN_NUM_THREADS=1` 唯一串行。 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRecursion

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderNumbers
open SecondOrderDivision SecondOrderFiniteRange SecondOrderBetaSequence
open SecondOrderFunctions SecondOrderHistory
open PrimitiveFormulas SecondOrderProgramSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 检查点 1：基例（`n = 0`）

内部长度为 `0` 时，历史只需承载 `XF` 在 `x` 处的单个取值：
它既是第 0 项（初值），又是末项（输出），`i < 0` 的相邻步条件空真。
构造用 `SecondOrderHistory.base_l` 得到一格内部实数历史 `H`，
再用 `beta_sequence_iff_l` 在长度 `succ 0` 上把 `H` 编码为同一对 `b`、`c`。 -/

/-- 基例：`XF` 全域时，对每个内部 `x` 存在长度 `0` 的 `prec` 历史输出。 -/
theorem prec_history_exists_zero_l (hℳ : Theory.Models ℳ theory_m)
    {XF XG : set_l ℳ} (hXF : function_l XF) (x : num_l ℳ) :
    ∃ y : num_l ℳ, prec_history_l XF XG x (zero_l ℳ) y := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  -- 取 `XF` 在 `x` 处的唯一取值。
  obtain ⟨a₀, ha₀, _⟩ := hXF x
  -- 一格内部历史：`H 0 a₀`，且在 `i < succ 0` 上逐点唯一。
  obtain ⟨H, hH⟩ := base_l hℳ XF a₀
  have hfun : ∀ i, SecondOrderOrder.lt_l i (succ_l (zero_l ℳ)) →
      ∃! a, relation_l H i a := hH.1
  -- 长度 `succ 0` 上的 β 编码：第 0 项读到 `H 0`。
  obtain ⟨b, c, hbiff⟩ := beta_sequence_iff_l hℳ H (succ_l (zero_l ℳ)) hfun
  have hzero_lt : SecondOrderOrder.lt_l (zero_l ℳ) (succ_l (zero_l ℳ)) :=
    lt_own_succ_l hℳ (zero_l ℳ)
  have hβ0 : beta_rel_l b c (zero_l ℳ) a₀ :=
    ((hbiff (zero_l ℳ) hzero_lt a₀).mpr hH.2.1)
  refine ⟨a₀, b, c, ⟨a₀, ha₀, hβ0⟩, hβ0, ?_⟩
  -- `i < 0` 无实例：正差序下每个数不小于 `0`。
  intro i hi
  exact False.elim (not_lt_of_ge (zero_le_l hℳ i) hi)

/-! ## 检查点 2 前置：把 β 读取恢复为内部实数图

追加一步的路线是「恢复旧历史的图 → 末项加一格 → 用更长的长度重新 β 编码」。
`beta_sequence_iff_l` 需要一个真正的内部实数图 `H` 作输入，因此先把已有码 `b`、`c`
的读取关系 `beta_rel_l b c i a` 用理解公理实现为内部图。这正是内部实数分离，
不把外部集合强塞进 Henkin 域。 -/

/-- 给定一对内部数 `b`、`c`，β 读取关系在模型内实现为一张二元图。 -/
theorem beta_graph_l (hℳ : Theory.Models ℳ theory_m) (b c : num_l ℳ) :
    ∃ H : set_l ℳ, ∀ i a, relation_l H i a ↔ beta_rel_l b c i a := by
  -- 自由槽依次为 `i`（首）、`a`（次）、`b`、`c`（参数）。
  let φ : Formula signature_m [] (.num :: .num :: [.num, .num]) :=
    beta_template_m (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there .here))
  let η : Env ℳ [] [.num, .num] := ((Env.empty (M := ℳ)).pushFree c).pushFree b
  obtain ⟨H, hH⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl) η
  refine ⟨H, fun i a => (hH i a).trans ?_⟩
  rw [beta_template_syntax_l hℳ]
  exact Iff.rfl

/-! ## 检查点 2：末项追加一格

追加步是纯外部的单步推理（一次前驱分案），不涉及内部归纳，因此可对任意
非标准 `n` 直接成立。它把长度 `n` 的历史延长到 `succ n`：
先用 `beta_graph_l` 把旧码 `b`、`c` 的读取恢复成内部图 `H`，
再用 `SecondOrderHistory.extend_l` 把新值 `y'` 追加到索引 `succ n`，
最后在长度 `succ (succ n)` 上用 `beta_sequence_iff_l` 重新编码。 -/

/-- `i < succ j` 精确分成 `i < j` 或 `i = j`。 -/
theorem lt_succ_cases_l (hℳ : Theory.Models ℳ theory_m) {i j : num_l ℳ}
    (h : SecondOrderOrder.lt_l i (succ_l j)) : SecondOrderOrder.lt_l i j ∨ i = j := by
  obtain ⟨k, hk⟩ := h
  rcases predecessor_l hℳ k with rfl | ⟨m, rfl⟩
  · right
    rw [add_succ_l hℳ, add_zero_l hℳ] at hk
    exact injective_l hℳ hk
  · left
    rw [add_succ_l hℳ] at hk
    exact ⟨m, injective_l hℳ hk⟩

/-- 追加步：长度 `n` 的历史输出存在时，长度 `succ n` 的历史输出也存在。 -/
theorem prec_history_succ_l (hℳ : Theory.Models ℳ theory_m)
    {XF XG : set_l ℳ} (hXG : function_l XG) {x n : num_l ℳ}
    (h : ∃ y, prec_history_l XF XG x n y) :
    ∃ y', prec_history_l XF XG x (succ_l n) y' := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨y, b, c, ⟨a₀, ha₀, hβ0⟩, hβn, hsteps⟩ := h
  -- 末项的下一步取值：`XG` 在 `pair x (pair n y)` 处的唯一输出。
  obtain ⟨y', hy', _uq⟩ := hXG (value_l x (value_l n y))
  obtain ⟨H, hH⟩ := beta_graph_l hℳ b c
  obtain ⟨K, hK⟩ := extend_l hℳ H n y'
  -- 旧图在 `i < succ n` 上逐点唯一（存在来自旧历史，唯一来自余数唯一性）。
  have hval : ∀ i, SecondOrderOrder.lt_l i (succ_l n) → ∃! a, beta_rel_l b c i a := by
    intro i hi
    rcases lt_succ_cases_l hℳ hi with hlt | heq
    · obtain ⟨u, _v, hu, _hv, _hx⟩ := hsteps i hlt
      exact ⟨u, hu, fun z hz => beta_rel_unique_l hℳ hz hu⟩
    · subst heq
      exact ⟨y, hβn, fun z hz => beta_rel_unique_l hℳ hz hβn⟩
  -- 新图 `K` 在 `i < succ (succ n)` 上逐点唯一。
  have hKfun : ∀ i, SecondOrderOrder.lt_l i (succ_l (succ_l n)) →
      ∃! a, relation_l K i a := by
    intro i hi
    rcases lt_succ_cases_l hℳ hi with hlt | heq
    · obtain ⟨a, ha, hau⟩ := hval i hlt
      refine ⟨a, (hK i a).mpr (Or.inl ⟨hlt, (hH i a).mpr ha⟩), ?_⟩
      intro z hz
      rcases (hK i z).mp hz with ⟨_, hHiz⟩ | ⟨heq', _⟩
      · exact hau z ((hH i z).mp hHiz)
      · exact absurd (heq' ▸ hlt) (SecondOrderOrder.irrefl_l hℳ (succ_l n))
    · subst heq
      refine ⟨y', (hK (succ_l n) y').mpr (Or.inr ⟨rfl, rfl⟩), ?_⟩
      intro z hz
      rcases (hK (succ_l n) z).mp hz with ⟨hirrefl, _⟩ | ⟨_, rfl⟩
      · exact absurd hirrefl (SecondOrderOrder.irrefl_l hℳ (succ_l n))
      · rfl
  obtain ⟨b', c', hbiff⟩ := beta_sequence_iff_l hℳ K (succ_l (succ_l n)) hKfun
  -- 把「β 读取 ↔ `K`」和「`K` ↔ 旧图或末项」组合成对新码 `b'`、`c'` 的读取。
  have hbiffK (i : num_l ℳ) (hi : SecondOrderOrder.lt_l i (succ_l (succ_l n))) (a : num_l ℳ) :
      beta_rel_l b' c' i a ↔ relation_l K i a := hbiff i hi a
  refine ⟨y', b', c', ⟨a₀, ha₀, ?_⟩, ?_, ?_⟩
  · -- 初值：`0 < succ n`，第 0 项与旧历史一致。
    exact (hbiffK (zero_l ℳ) (SecondOrderOrder.zero_succ_l hℳ (succ_l n)) a₀).mpr
      ((hK (zero_l ℳ) a₀).mpr
        (Or.inl ⟨SecondOrderOrder.zero_succ_l hℳ n, (hH (zero_l ℳ) a₀).mpr hβ0⟩))
  · -- 输出：新码在 `succ n` 处读到追加值 `y'`。
    exact (hbiffK (succ_l n) (lt_own_succ_l hℳ (succ_l n)) y').mpr
      ((hK (succ_l n) y').mpr (Or.inr ⟨rfl, rfl⟩))
  · -- 相邻步：`i < succ n` 时沿用旧历史，或跨接末尾追加的那一步。
    intro i hi
    rcases lt_succ_cases_l hℳ hi with hlt | heq
    · obtain ⟨u, v, hu, hv, hx⟩ := hsteps i hlt
      have hilt : SecondOrderOrder.lt_l i (succ_l n) :=
        SecondOrderOrder.trans_l hℳ hlt (lt_own_succ_l hℳ n)
      have hisucc : SecondOrderOrder.lt_l (succ_l i) (succ_l n) :=
        (SecondOrderOrder.succ_iff_l hℳ i n).mpr hlt
      refine ⟨u, v,
        (hbiffK i (SecondOrderOrder.trans_l hℳ hilt (lt_own_succ_l hℳ (succ_l n))) u).mpr
          ((hK i u).mpr (Or.inl ⟨hilt, (hH i u).mpr hu⟩)),
        (hbiffK (succ_l i)
          (SecondOrderOrder.trans_l hℳ hisucc (lt_own_succ_l hℳ (succ_l n))) v).mpr
          ((hK (succ_l i) v).mpr (Or.inl ⟨hisucc, (hH (succ_l i) v).mpr hv⟩)), hx⟩
    · subst heq
      refine ⟨y, y',
        (hbiffK i (SecondOrderOrder.trans_l hℳ (lt_own_succ_l hℳ i)
          (lt_own_succ_l hℳ (succ_l i))) y).mpr
          ((hK i y).mpr (Or.inl ⟨lt_own_succ_l hℳ i, (hH i y).mpr hβn⟩)),
        (hbiffK (succ_l i) (lt_own_succ_l hℳ (succ_l i)) y').mpr
          ((hK (succ_l i) y').mpr (Or.inr ⟨rfl, rfl⟩)), hy'⟩

/-! ## 检查点 3：实际归纳公式与逐点桥

内部长度归纳必须对一个**实际纯公式**做，不能对宿主 `Nat` 递归或任意外部 `Prop` 裸归纳。
这里按 Codex #1260 采用编译器原 `prec` 公式作为归纳公式：
自由槽依次为 `n`（归纳）、`x`（参数），外层绑定 `q`（配对码），内层绑定 `y`（输出），
正文为 `pair_m x n q ∧ (F.prec_l G).form q y`。逐点桥把它对应到 `∃ y, prec_history_l`：
`prec_primitive_syntax_l` 给出 `.form` 的历史语义，配对单射性把 `q` 对齐回 `(x, n)`。 -/

/-- 存在性归纳用的实际原 `prec` 公式：`∃ q y, pair(x, n) = q ∧ prec_form(q, y)`。 -/
def prec_exists_m {f g : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    (G : PrimitiveFormulas.graph_l g) : Formula signature_m [] [.num, .num] :=
  .existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there .here)))
    ((F.prec_l G).form (.bvar (.there .here)) (.bvar .here))))

/-- `prec_exists_m` 仍是纯算术公式：先对 `pure_m` 逐层判定，再经 `pure_language_m` 升级。
`.form` 的纯度来自图携带的 `pure` 字段，配对图的纯度来自 `pair_pure_l`。 -/
theorem prec_exists_language_m {f g : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    (G : PrimitiveFormulas.graph_l g) : language_m (prec_exists_m F G) = true := by
  refine pure_language_m _ ?_
  show SecondOrderSyntax.pure_m (prec_exists_m F G) = true
  -- 逐层展开 `pure_m`，两个合取支各自用图携带的纯度；`s t u` 由具体子目标固定上下文。
  simp only [prec_exists_m, SecondOrderSyntax.pure_m, Bool.and_eq_true]
  refine ⟨pair_pure_l _ _ _ ?_ ?_ ?_, (F.prec_l G).pure _ _ ?_ ?_⟩ <;>
    simp only [SecondOrderSyntax.pure_term_m]

/-- 逐点桥：`prec_exists_m` 在 `(n, x)` 上的真值等价于「`x` 处存在长度 `n` 的历史输出」。
两个嵌套绑定量词先各自把配对图与 `prec` 图的求值降为 `q`、`y`，再用配对单射性把外层
`q` 对齐回 `(x, k)`。 -/
theorem prec_exists_iff_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    (x k : num_l ℳ) :
    Formula.satisfies (((Env.empty (M := ℳ)).pushFree x).pushFree k)
        (prec_exists_m F G) ↔
      ∃ y, prec_history_l XF XG x k y := by
  -- 内层绑定 `q`、`y` 压入后，配对图与 `prec` 图的求值分别化为 `value_l x k = q` 与历史语义。
  have hpair (q y : num_l ℳ) : Formula.satisfies
      ((((((Env.empty (M := ℳ)).pushFree x).pushFree k).pushBound q).pushBound y))
      (PrimitiveFormulas.pair_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there .here))) ↔
      SecondOrderPairing.value_l x k = q := by
    simp only [SecondOrderPairing.formula_l, Term.eval, Env.pushBound,
      Env.pushFree, Assignment.push]
  have hform (q y : num_l ℳ) : Formula.satisfies
      ((((((Env.empty (M := ℳ)).pushFree x).pushFree k).pushBound q).pushBound y))
      ((F.prec_l G).form (.bvar (.there .here)) (.bvar .here)) ↔
      ∃ x' n', SecondOrderPairing.value_l x' n' = q ∧ prec_history_l XF XG x' n' y := by
    have h := prec_primitive_syntax_l hℳ F G XF XG hF hG
      (((((Env.empty (M := ℳ)).pushFree x).pushFree k).pushBound q).pushBound y)
      (.bvar (.there .here)) (.bvar .here)
    simpa only [Term.eval, Env.pushBound, Env.pushFree, Assignment.push] using h
  simp only [prec_exists_m, Formula.satisfies]
  constructor
  · rintro ⟨q, y, hA, hB⟩
    have hq : SecondOrderPairing.value_l x k = q := (hpair q y).mp hA
    obtain ⟨x', n', hp', hh⟩ := (hform q y).mp hB
    obtain ⟨hx', hn'⟩ :=
      SecondOrderPairingBounds.injective_l hℳ x' n' x k (hp'.trans hq.symm)
    rw [hx', hn'] at hh
    exact ⟨y, hh⟩
  · rintro ⟨y, hh⟩
    refine ⟨SecondOrderPairing.value_l x k, y, ?_, ?_⟩
    · exact (hpair (SecondOrderPairing.value_l x k) y).mpr rfl
    · exact (hform (SecondOrderPairing.value_l x k) y).mpr ⟨x, k, rfl, hh⟩

/-! ## 检查点 4：内部归纳闭合存在性

基例用 `prec_history_exists_zero_l`（长度 `0`），后继步用 `prec_history_succ_l`
（追加一格）；两者经逐点桥装入 `SecondOrderModel.induct_l`，`x` 作单一参数。
结论覆盖全部内部 `n`，包括非标准 `n`：归纳发生在对象语言的 `succ` 上。 -/

/-- 存在性终局：`XF`、`XG` 为内部全函数时，任意内部 `x`、`n` 都有 `prec` 历史输出。 -/
theorem prec_history_exists_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    (hXF : function_l XF) (hXG : function_l XG) (x : num_l ℳ) :
    ∀ n : num_l ℳ, ∃ y, prec_history_l XF XG x n y := by
  apply induct_l hℳ (prec_exists_m F G) (prec_exists_language_m F G)
    ((Env.empty (M := ℳ)).pushFree x)
    (fun n => ∃ y, prec_history_l XF XG x n y)
    (fun k => prec_exists_iff_l hℳ F G XF XG hF hG x k)
  · exact prec_history_exists_zero_l hℳ hXF x
  · intro k ih
    exact prec_history_succ_l hℳ hXG ih

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRecursion
