import BMSConstructibleBridge.PrimitiveProgram
import BMSConstructibleBridge.SecondOrderBetaSequence
import BMSConstructibleBridge.SecondOrderUnpairing

/-!
# 原 PrimitiveProgram 编译器在任意 Z₂ 模型内的语义

`PrimitiveProgram.form_m c s t` 是原编译器递归程序 `c` 得到的**实际纯算术公式**。
原 `PrimitiveProgram.sound_m` 只对标准模型 `structure_l` 给出语义，
而 `PrimitiveFormulas.graph_l f` 的 `sound` 字段同样只约束 `structure_l`，
因此不能据此假定任意模型上的上下文无关性。

本模块研究任意 ℳ ⊨ 原 `SecondOrderArithmetic.theory_m` 上的语义。
当前已完成 §A 与 §B；下面 §C、§D 是尚待完成的任务目标，不是已有出口：

* §A 给出原 `prec` 的精确历史语义 `prec_history_l`（Codex 规格中的 K），
  并把它与原公式在任意上下文、环境、数项上的满足关系精确对齐；
* §B 证明该历史语义的输出唯一（一次实际公式归纳，不要求候选 `c` 正、
  不要求两份 `b,c` 相同、不对非标准 `n` 使用宿主 `Nat.rec`）；
* §C 用内部迭代与 β 编码给出存在性（每个 `x` 单独取历史，不收集内部实数族）；
* §D 对 `code_m` 七构造做外部有限语法归纳，得到联合出口
  `∃ X, function_l X ∧ ∀ Γ Δ η s t, satisfies η (form_m c s t) ↔ relation_l X (s.eval η) (t.eval η)`。

**技术前提**：`PrimitiveFormulas` 的 `initial` / `transition` / `steps` /
`recursion` / `iteration` 以及项记法 `zero/succ/add/mul/twice/v₀/v₁` 都是该文件内的
**私有定义**，本模块无法按名展开它们。因此这里用本模块自己的公开 `_m` 记法
重述同一棵 AST，并用一次 `rfl` 把公开入口 `(F.prec_l G).form` 与重述模板
逐层核对（见 `prec_form_eq_m`）。这与 `SecondOrderBetaSequence.beta_template_eq_m`
的做法相同，不是注释层面的声称。

本模块只新增独立文件，不让原 `PrimitiveFormulas` 反向导入 β 文件，无循环依赖。
完成本模块只消去"原编译程序在任意 Z₂ 模型内全域唯一"的缺口，
**不等于** BM4 算法在非标准模型内的规格正确性，也不是最终固定高度 Z₂ 良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSemantics

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderNumbers
open SecondOrderDivision SecondOrderFiniteRange SecondOrderBetaSequence
open PrimitiveFormulas

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 项记法与提升

与 `PrimitiveFormulas` 的私有记法同形，但全部公开，可被 `simp` 展开。 -/

/-- 穿过一个数变量绑定后提升一层。 -/
abbrev shift_m {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m (.num :: Γ) Δ .num :=
  t.weakenBound sort_m.num

/-- 穿过两个数变量绑定后提升两层。 -/
abbrev twice_m {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m (.num :: .num :: Γ) Δ .num :=
  (t.weakenBound sort_m.num).weakenBound sort_m.num

/-- 两个数量词绑定下的外层变量（先绑定者）。 -/
abbrev v₁_m {Γ Δ : SortContext signature_m} : Term signature_m (.num :: .num :: Γ) Δ .num :=
  .bvar (.there .here)

/-- 两个数量词绑定下的内层变量（后绑定者）。 -/
abbrev v₀_m {Γ Δ : SortContext signature_m} : Term signature_m (.num :: .num :: Γ) Δ .num :=
  .bvar .here

/-- 一个数量词绑定下的变量。 -/
abbrev u₀_m {Γ Δ : SortContext signature_m} : Term signature_m (.num :: Γ) Δ .num :=
  .bvar .here

/-! ## 原 prec 各层模板的公开重述

以下五个模板逐层对应 `PrimitiveFormulas` 的 `iteration` / `transition` /
`initial` / `steps` / `recursion`，再由 `prec_form_m` 组装成
`(F.prec_l G).form` 的同形副本。全部使用本模块的公开记法。 -/

/-- 一步迭代模板：`R_G(pair(x, pair(i,u)), v)`，中间配对结果由两个数量词承载。 -/
def iteration_m {f : Nat → Nat} (G : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (x i u v : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (twice_m i) (twice_m u) v₁_m)
    (.conj (PrimitiveFormulas.pair_m (twice_m x) v₁_m v₀_m) (G.form v₀_m (twice_m v)))))

/-- 第 `i` 步转移模板：`β(b,c,i,u) ∧ β(b,c,i+1,v) ∧ R_G(pair(x,pair(i,u)),v)`。 -/
def transition_m {f : Nat → Nat} (G : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (b c x i : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (beta_template_m (twice_m b) (twice_m c) (twice_m i) v₁_m)
    (.conj (beta_template_m (twice_m b) (twice_m c) (succ_m (twice_m i)) v₀_m)
      (iteration_m G (twice_m x) (twice_m i) v₁_m v₀_m))))

/-- 初值模板：`∃ a, R_F(x,a) ∧ β(b,c,0,a)`。 -/
def initial_m {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (b c x : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.conj (F.form (shift_m x) u₀_m)
    (beta_template_m (shift_m b) (shift_m c) zero_m u₀_m))

/-- 全部相邻步模板：`∀ i < n, transition(b,c,x,i)`。 -/
def steps_m {f : Nat → Nat} (G : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (b c x n : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .forallE .num (.imp (PrimitiveFormulas.lt_m u₀_m (shift_m n))
    (transition_m G (shift_m b) (shift_m c) (shift_m x) u₀_m))

/-- 历史模板：`∃ b c, 初值 ∧ β(b,c,n,y) ∧ 全部相邻步`。 -/
def recursion_m {f g : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    (G : PrimitiveFormulas.graph_l g)
    {Γ Δ : SortContext signature_m} (x n y : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (initial_m F v₁_m v₀_m (twice_m x))
    (.conj (beta_template_m v₁_m v₀_m (twice_m n) (twice_m y))
      (steps_m G v₁_m v₀_m (twice_m x) (twice_m n)))))

/-- 原 `prec` 公式的同形副本：`∃ x n, pair(x,n)=s ∧ 历史(x,n,t)`。 -/
def prec_form_m {f g : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    (G : PrimitiveFormulas.graph_l g)
    {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m v₁_m v₀_m (twice_m s))
    (recursion_m F G v₁_m v₀_m (twice_m t))))

/-- **公开入口与原模板的逐层核对**：本模块重述的 `prec_form_m` 与
`PrimitiveFormulas.graph_l.prec_l` 给出的 `form` 定义相等。
这一条 `rfl` 同时核对了 `iteration` / `transition` / `initial` / `steps` /
`recursion` 五层私有模板以及私有项记法，是"两个模板可连接"的实际证据，
不是注释层面的声称。 -/
theorem prec_form_eq_m {f g : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    (G : PrimitiveFormulas.graph_l g) {Γ Δ : SortContext signature_m}
    (s t : Term signature_m Γ Δ .num) :
    (F.prec_l G).form s t = prec_form_m F G s t := rfl

/-! ## §A 原 prec 的精确历史语义

`prec_history_l XF XG x n y`（Codex 规格中的 K）声明：存在同一对内部数 `b`、`c`，
使得 `b` 在模数族 `m_i = 1 + (i+1)c` 下的第 0 项读到 `XF` 在 `x` 处的取值，
第 `n` 项读到 `y`，且每个 `i < n` 的相邻两项满足 `XG` 的一步转移。

配对一律使用模型自身的 `SecondOrderPairing.value_l`，与 `relation_l` 的定义一致。 -/

/-- 原 prec 的历史语义（K 规格）。 -/
def prec_history_l (XF XG : set_l ℳ) (x n y : num_l ℳ) : Prop :=
  ∃ b c : num_l ℳ,
    (∃ a : num_l ℳ, relation_l XF x a ∧ beta_rel_l b c (zero_l ℳ) a) ∧
    beta_rel_l b c n y ∧
    ∀ i : num_l ℳ, SecondOrderOrder.lt_l i n →
      ∃ u v : num_l ℳ,
        beta_rel_l b c i u ∧ beta_rel_l b c (succ_l i) v ∧
        relation_l XG (SecondOrderPairing.value_l x (SecondOrderPairing.value_l i u)) v

/-! ### 子图在任意模型上的语义假设

归纳时子程序 `F`、`G` 的任意模型语义由归纳假设给出。这里把它封装为一个命题，
避免每个引理都重复四个参数。 -/

/-- 一张原图在任意模型、任意上下文/环境/数项上的统一值语义。 -/
def graph_semantics_l {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f) (X : set_l ℳ) : Prop :=
  ∀ {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num),
    Formula.satisfies η (F.form s t) ↔ relation_l X (s.eval η) (t.eval η)

/-- 一步迭代模板在任意模型上的语义：两次配对后查 `XG`。 -/
theorem iteration_syntax_l {f : Nat → Nat} (G : PrimitiveFormulas.graph_l f)
    (XG : set_l ℳ) (hG : graph_semantics_l G XG)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (x i u v : Term signature_m Γ Δ .num) :
    Formula.satisfies η (iteration_m G x i u v) ↔
      ∃ w₁ w₀ : num_l ℳ,
        SecondOrderPairing.value_l (i.eval η) (u.eval η) = w₁ ∧
        SecondOrderPairing.value_l (x.eval η) w₁ = w₀ ∧
        relation_l XG w₀ (v.eval η) := by
  -- 注意：不要把 `Env.pushBound` 放进 simp 列表，否则环境被展开成字面量 record，
  -- `Term.eval_weakenBound` 就匹配不上了（与 β 模块同一处坑）。
  simp only [iteration_m, Formula.satisfies, SecondOrderPairing.formula_l,
    Term.eval, Term.eval_weakenBound]
  constructor
  · rintro ⟨w₁, w₀, h₁, h₀, hg⟩
    refine ⟨w₁, w₀, h₁, h₀, ?_⟩
    -- 先把绑定变量求值化简掉，再单独用 `Term.eval_weakenBound` 消去两次提升；
    -- 两步必须分开：若在同一次 simp 里展开 `Env.pushBound`，
    -- `Term.eval_weakenBound` 就匹配不上（与 β 模块同一处坑）。
    have hg₁ : relation_l XG w₀
        (Term.eval (Env.pushBound (Env.pushBound η w₁) w₀) (twice_m v)) := by
      simpa [Term.eval, Assignment.push, Env.pushBound] using
        (hG (Env.pushBound (Env.pushBound η w₁) w₀) v₀_m (twice_m v)).mp hg
    simpa [Term.eval_weakenBound] using hg₁
  · rintro ⟨w₁, w₀, h₁, h₀, hg⟩
    refine ⟨w₁, w₀, h₁, h₀, ?_⟩
    have hg₁ : relation_l XG w₀
        (Term.eval (Env.pushBound (Env.pushBound η w₁) w₀) (twice_m v)) := by
      simpa [Term.eval_weakenBound] using hg
    simpa [Term.eval, Assignment.push, Env.pushBound] using
      (hG (Env.pushBound (Env.pushBound η w₁) w₀) v₀_m (twice_m v)).mpr hg₁

/-! ### 求值辅助

下面几条把"提升过的项在压入环境中的求值"写成可直接被 `simp` 使用的等式。
关键是不要把 `Env.pushBound` 与 `Term.eval_weakenBound` 放进同一次 `simp`：
前者会把环境展开成字面量 record，后者就匹配不上（与 β 模块同一处坑）。
因此这里把两条路径分开，各自单独成一条引理。 -/

/-- 零项的求值就是模型自身的零。 -/
theorem eval_zero_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) :
    Term.eval η (zero_m : Term signature_m Γ Δ .num) = zero_l ℳ := rfl

/-- 后继项的求值就是模型自身的后继。 -/
theorem eval_succ_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (t : Term signature_m Γ Δ .num) :
    Term.eval η (succ_m t) = succ_l (t.eval η) := rfl

/-- 提升一层的项在压入一个绑定后的求值不变。 -/
theorem eval_shift_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (a : num_l ℳ) (t : Term signature_m Γ Δ .num) :
    Term.eval (Env.pushBound η a) (shift_m t) = t.eval η := by
  simpa [shift_m] using (Term.eval_weakenBound η a t)

/-- 提升两层的项在压入两个绑定后的求值不变。 -/
theorem eval_twice_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (a b : num_l ℳ) (t : Term signature_m Γ Δ .num) :
    Term.eval (Env.pushBound (Env.pushBound η a) b) (twice_m t) = t.eval η := by
  calc
    Term.eval (Env.pushBound (Env.pushBound η a) b) (twice_m t)
        = Term.eval (Env.pushBound (Env.pushBound η a) b)
            ((t.weakenBound sort_m.num).weakenBound sort_m.num) := rfl
    _ = Term.eval (Env.pushBound η a) (t.weakenBound sort_m.num) :=
        Term.eval_weakenBound (Env.pushBound η a) b (t.weakenBound sort_m.num)
    _ = t.eval η := Term.eval_weakenBound η a t

/-- 一个数量词下的绑定变量取值就是压入的那个值。 -/
theorem eval_u₀_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (a : num_l ℳ) :
    Term.eval (Env.pushBound η a) (u₀_m : Term signature_m (.num :: Γ) Δ .num) = a := by
  simp [Term.eval, Env.pushBound, Assignment.push]

/-- 两个数量词下的内层变量取值。 -/
theorem eval_v₀_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (a b : num_l ℳ) :
    Term.eval (Env.pushBound (Env.pushBound η a) b)
      (v₀_m : Term signature_m (.num :: .num :: Γ) Δ .num) = b := by
  simp [Term.eval, Env.pushBound, Assignment.push]

/-- 两个数量词下的外层变量取值。 -/
theorem eval_v₁_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (a b : num_l ℳ) :
    Term.eval (Env.pushBound (Env.pushBound η a) b)
      (v₁_m : Term signature_m (.num :: .num :: Γ) Δ .num) = a := by
  simp [Term.eval, Env.pushBound, Assignment.push]

/-! ### β 模板在任意模型上的语义

`beta_template_m` 是 `PrimitiveFormulas.beta_m` 的同形副本（`beta_template_eq_m`
用定义相等核对过），所以任意模型/任意环境上的语义直接由
`SecondOrderBetaSequence.beta_primitive_syntax_l` 搬过来，不需要重做一遍 β 编码的展开。 -/

/-- 同形 β 模板在任意模型、任意环境、任意数项上的语义。 -/
theorem beta_template_syntax_l (hℳ : Theory.Models ℳ theory_m)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (b c i v : Term signature_m Γ Δ .num) :
    Formula.satisfies η (beta_template_m b c i v) ↔
      beta_rel_l (b.eval η) (c.eval η) (i.eval η) (v.eval η) := by
  rw [← beta_template_eq_m b c i v]
  exact beta_primitive_syntax_l hℳ η b c i v

/-! ### 第 `i` 步转移的语义 -/

/-- 一步转移模板在任意模型上的语义：两步 β 读取加一次 `XG` 的一步关系。 -/
theorem transition_syntax_l (hℳ : Theory.Models ℳ theory_m) {g : Nat → Nat}
    (G : PrimitiveFormulas.graph_l g) (XG : set_l ℳ) (hG : graph_semantics_l G XG)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (b c x i : Term signature_m Γ Δ .num) :
    Formula.satisfies η (transition_m G b c x i) ↔
      ∃ u v : num_l ℳ,
        beta_rel_l (b.eval η) (c.eval η) (i.eval η) u ∧
        beta_rel_l (b.eval η) (c.eval η) (succ_l (i.eval η)) v ∧
        relation_l XG (SecondOrderPairing.value_l (x.eval η)
          (SecondOrderPairing.value_l (i.eval η) u)) v := by
  simp only [transition_m, Formula.satisfies]
  constructor
  · rintro ⟨u, v, hu, hv, hi⟩
    let η₂ := Env.pushBound (Env.pushBound η u) v
    refine ⟨u, v, ?_, ?_, ?_⟩
    · have h := (beta_template_syntax_l hℳ η₂ (twice_m b) (twice_m c) (twice_m i) v₁_m).mp hu
      simpa [η₂, eval_twice_m, eval_v₁_m] using h
    · have h := (beta_template_syntax_l hℳ η₂ (twice_m b) (twice_m c)
        (succ_m (twice_m i)) v₀_m).mp hv
      simpa [η₂, eval_twice_m, eval_succ_m, eval_v₀_m] using h
    · have h := (iteration_syntax_l G XG hG η₂ (twice_m x) (twice_m i) v₁_m v₀_m).mp hi
      rcases h with ⟨w₁, w₀, h₁, h₀, hg⟩
      have h₁' : SecondOrderPairing.value_l (i.eval η) u = w₁ := by
        simpa [η₂, eval_twice_m, eval_v₁_m] using h₁
      have h₀' : SecondOrderPairing.value_l (x.eval η) w₁ = w₀ := by
        simpa [η₂, eval_twice_m] using h₀
      have hg' : relation_l XG w₀ v := by
        simpa [η₂, eval_v₀_m] using hg
      simpa [← h₀', ← h₁'] using hg'
  · rintro ⟨u, v, hu, hv, hi⟩
    let η₂ := Env.pushBound (Env.pushBound η u) v
    refine ⟨u, v, ?_, ?_, ?_⟩
    · exact (beta_template_syntax_l hℳ η₂ (twice_m b) (twice_m c) (twice_m i) v₁_m).mpr
        (by simpa [η₂, eval_twice_m, eval_v₁_m] using hu)
    · exact (beta_template_syntax_l hℳ η₂ (twice_m b) (twice_m c)
        (succ_m (twice_m i)) v₀_m).mpr
        (by simpa [η₂, eval_twice_m, eval_succ_m, eval_v₀_m] using hv)
    · apply (iteration_syntax_l G XG hG η₂ (twice_m x) (twice_m i) v₁_m v₀_m).mpr
      let w₁ := SecondOrderPairing.value_l (i.eval η) u
      let w₀ := SecondOrderPairing.value_l (x.eval η) w₁
      refine ⟨w₁, w₀, ?_, ?_, ?_⟩
      · simp [w₁, η₂, eval_twice_m, eval_v₁_m]
      · simp [w₀, η₂, eval_twice_m]
      · simpa [w₀, w₁, η₂, eval_v₀_m] using hi

/-! ### 初值的语义 -/

/-- 初值模板在任意模型上的语义：`XF` 在 `x` 处的取值就是 β 序列的第 0 项。 -/
theorem initial_syntax_l (hℳ : Theory.Models ℳ theory_m) {f : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (XF : set_l ℳ) (hF : graph_semantics_l F XF)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (b c x : Term signature_m Γ Δ .num) :
    Formula.satisfies η (initial_m F b c x) ↔
      ∃ a : num_l ℳ,
        relation_l XF (x.eval η) a ∧ beta_rel_l (b.eval η) (c.eval η) (zero_l ℳ) a := by
  simp only [initial_m, Formula.satisfies]
  constructor
  · rintro ⟨a, hF', hβ⟩
    let η₁ := Env.pushBound η a
    refine ⟨a, ?_, ?_⟩
    · have h := (hF η₁ (shift_m x) u₀_m).mp hF'
      simpa [η₁, eval_shift_m, eval_u₀_m] using h
    · have h := (beta_template_syntax_l hℳ η₁ (shift_m b) (shift_m c)
        (zero_m : Term signature_m (.num :: Γ) Δ .num) u₀_m).mp hβ
      simpa [η₁, eval_shift_m, eval_zero_m, eval_u₀_m] using h
  · rintro ⟨a, hF', hβ⟩
    let η₁ := Env.pushBound η a
    refine ⟨a, ?_, ?_⟩
    · exact (hF η₁ (shift_m x) u₀_m).mpr
        (by simpa [η₁, eval_shift_m, eval_u₀_m] using hF')
    · exact (beta_template_syntax_l hℳ η₁ (shift_m b) (shift_m c)
        (zero_m : Term signature_m (.num :: Γ) Δ .num) u₀_m).mpr
        (by simpa [η₁, eval_shift_m, eval_zero_m, eval_u₀_m] using hβ)

/-! ### 全部相邻步的语义 -/

/-- 相邻步模板在任意模型上的语义：对所有模型内部 `i < n` 成立。 -/
theorem steps_syntax_l (hℳ : Theory.Models ℳ theory_m) {g : Nat → Nat}
    (G : PrimitiveFormulas.graph_l g) (XG : set_l ℳ) (hG : graph_semantics_l G XG)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (b c x n : Term signature_m Γ Δ .num) :
    Formula.satisfies η (steps_m G b c x n) ↔
      ∀ i : num_l ℳ, SecondOrderOrder.lt_l i (n.eval η) →
        ∃ u v : num_l ℳ,
          beta_rel_l (b.eval η) (c.eval η) i u ∧
          beta_rel_l (b.eval η) (c.eval η) (succ_l i) v ∧
          relation_l XG (SecondOrderPairing.value_l (x.eval η)
            (SecondOrderPairing.value_l i u)) v := by
  simp only [steps_m, Formula.satisfies]
  constructor
  · intro h i hi
    let η₁ := Env.pushBound η i
    have hlt : Formula.satisfies η₁ (PrimitiveFormulas.lt_m u₀_m (shift_m n)) := by
      exact (SecondOrderOrder.formula_l η₁ u₀_m (shift_m n)).mpr
        (by simpa [η₁, eval_u₀_m, eval_shift_m] using hi)
    have ht := (transition_syntax_l hℳ G XG hG η₁
      (shift_m b) (shift_m c) (shift_m x) u₀_m).mp (h i hlt)
    simpa [η₁, eval_shift_m, eval_u₀_m] using ht
  · intro h i hlt
    let η₁ := Env.pushBound η i
    have hi : SecondOrderOrder.lt_l i (n.eval η) := by
      have h := (SecondOrderOrder.formula_l η₁ u₀_m (shift_m n)).mp hlt
      simpa [η₁, eval_u₀_m, eval_shift_m] using h
    exact (transition_syntax_l hℳ G XG hG η₁
      (shift_m b) (shift_m c) (shift_m x) u₀_m).mpr
      (by simpa [η₁, eval_shift_m, eval_u₀_m] using h i hi)

/-! ### 历史的语义 -/

/-- 历史模板在任意模型上的语义就是 `prec_history_l`（K 规格）。 -/
theorem recursion_syntax_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (x n y : Term signature_m Γ Δ .num) :
    Formula.satisfies η (recursion_m F G x n y) ↔
      prec_history_l XF XG (x.eval η) (n.eval η) (y.eval η) := by
  simp only [recursion_m, Formula.satisfies, prec_history_l]
  constructor
  · rintro ⟨b, c, hi, hb, hs⟩
    let η₂ := Env.pushBound (Env.pushBound η b) c
    refine ⟨b, c, ?_, ?_, ?_⟩
    · have h := (initial_syntax_l hℳ F XF hF η₂ v₁_m v₀_m (twice_m x)).mp hi
      simpa [η₂, eval_twice_m, eval_v₁_m, eval_v₀_m] using h
    · have h := (beta_template_syntax_l hℳ η₂ v₁_m v₀_m (twice_m n) (twice_m y)).mp hb
      simpa [η₂, eval_twice_m, eval_v₁_m, eval_v₀_m] using h
    · have h := (steps_syntax_l hℳ G XG hG η₂ v₁_m v₀_m (twice_m x) (twice_m n)).mp hs
      simpa [η₂, eval_twice_m, eval_v₁_m, eval_v₀_m] using h
  · rintro ⟨b, c, hi, hb, hs⟩
    let η₂ := Env.pushBound (Env.pushBound η b) c
    refine ⟨b, c, ?_, ?_, ?_⟩
    · exact (initial_syntax_l hℳ F XF hF η₂ v₁_m v₀_m (twice_m x)).mpr
        (by simpa [η₂, eval_twice_m, eval_v₁_m, eval_v₀_m] using hi)
    · exact (beta_template_syntax_l hℳ η₂ v₁_m v₀_m (twice_m n) (twice_m y)).mpr
        (by simpa [η₂, eval_twice_m, eval_v₁_m, eval_v₀_m] using hb)
    · exact (steps_syntax_l hℳ G XG hG η₂ v₁_m v₀_m (twice_m x) (twice_m n)).mpr
        (by simpa [η₂, eval_twice_m, eval_v₁_m, eval_v₀_m] using hs)

/-! ### 最外层 prec 的语义 -/

/-- 最外层 prec 模板在任意模型上的语义：先按模型自身配对拆出 `x`、`n`，再要求历史。 -/
theorem prec_syntax_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (prec_form_m F G s t) ↔
      ∃ x n : num_l ℳ,
        SecondOrderPairing.value_l x n = s.eval η ∧
        prec_history_l XF XG x n (t.eval η) := by
  simp only [prec_form_m, Formula.satisfies]
  constructor
  · rintro ⟨x, n, hp, hr⟩
    let η₂ := Env.pushBound (Env.pushBound η x) n
    refine ⟨x, n, ?_, ?_⟩
    · have h := (SecondOrderPairing.formula_l η₂ v₁_m v₀_m (twice_m s)).mp hp
      simpa [η₂, eval_v₁_m, eval_v₀_m, eval_twice_m] using h
    · have h := (recursion_syntax_l hℳ F G XF XG hF hG η₂ v₁_m v₀_m (twice_m t)).mp hr
      simpa [η₂, eval_v₁_m, eval_v₀_m, eval_twice_m] using h
  · rintro ⟨x, n, hp, hr⟩
    let η₂ := Env.pushBound (Env.pushBound η x) n
    refine ⟨x, n, ?_, ?_⟩
    · exact (SecondOrderPairing.formula_l η₂ v₁_m v₀_m (twice_m s)).mpr
        (by simpa [η₂, eval_v₁_m, eval_v₀_m, eval_twice_m] using hp)
    · exact (recursion_syntax_l hℳ F G XF XG hF hG η₂ v₁_m v₀_m (twice_m t)).mpr
        (by simpa [η₂, eval_v₁_m, eval_v₀_m, eval_twice_m] using hr)

/-- **公开入口版**：原 `PrimitiveFormulas.graph_l.prec_l` 给出的 `form` 本身，
在任意模型、任意上下文、任意环境、任意数项上，正好表达"存在模型内部的一对
`x`、`n` 使得 `pair(x,n) = s`，且 `prec_history_l` 在 `x,n,t` 上成立"。

这一条把 `prec_form_eq_m` 的定义相等核对与上面的语义引理接起来，因此
"原编译器实际生成的公式"与"K 规格"的对齐不是注释层面的声称。 -/
theorem prec_primitive_syntax_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η ((F.prec_l G).form s t) ↔
      ∃ x n : num_l ℳ,
        SecondOrderPairing.value_l x n = s.eval η ∧
        prec_history_l XF XG x n (t.eval η) := by
  rw [prec_form_eq_m F G s t]
  exact prec_syntax_l hℳ F G XF XG hF hG η s t

/-! ## §B 两份内部 β 历史的输出唯一

归纳式的六个自由数槽依次为 `i,n,b,c,b',c'`。它没有集合参数：
子图的函数性只在基例和后继步中使用。数量词 `∀u∀v` 之下，
`u` 为绑定槽 1，`v` 为绑定槽 0；自由槽不随绑定数量词移动。 -/

/-- 实际归纳公式：在 `i < succ n` 内，两份 β 读取若同时存在则相等。 -/
def history_agree_m : Formula signature_m [] [.num, .num, .num, .num, .num, .num] :=
  .imp (PrimitiveFormulas.lt_m (.fvar .here) (succ_m (.fvar (.there .here))))
    (.forallE .num (.forallE .num (.imp
      (.conj
        (PrimitiveFormulas.beta_m (.fvar (.there (.there .here)))
          (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar (.there .here)))
        (PrimitiveFormulas.beta_m (.fvar (.there (.there (.there (.there .here)))))
          (.fvar (.there (.there (.there (.there (.there .here))))))
          (.fvar .here) (.bvar .here)))
      (.equal (.bvar (.there .here)) (.bvar .here)))))

/-- 归纳矩阵只用原纯算术语言；此检查直接归约实际 AST。 -/
theorem history_agree_language_m : language_m history_agree_m = true := rfl

/-- 六个自由槽及两个绑定槽的逐环境语义核对。 -/
theorem history_agree_syntax_l (hℳ : Theory.Models ℳ theory_m)
    (n b c b' c' i : num_l ℳ) :
    Formula.satisfies
      (((((((Env.empty (M := ℳ)).pushFree c').pushFree b').pushFree c).pushFree b).pushFree n).pushFree i)
      history_agree_m ↔
      (SecondOrderOrder.lt_l i (succ_l n) → ∀ u v : num_l ℳ,
        beta_rel_l b c i u ∧ beta_rel_l b' c' i v → u = v) := by
  simp only [history_agree_m, Formula.satisfies, SecondOrderOrder.formula_l,
    beta_primitive_syntax_l hℳ, eval_succ_m]
  rfl

/-- 内部函数图的任意两条同输入边具有相同输出。 -/
theorem function_value_unique_l {X : set_l ℳ} (hX : SecondOrderFunctions.function_l X)
    {x a b : num_l ℳ} (ha : relation_l X x a) (hb : relation_l X x b) : a = b := by
  obtain ⟨v, _hv, huniq⟩ := hX x
  exact (huniq a ha).trans (huniq b hb).symm

/-- 正差序中每个内部数严格小于自身后继，无需任何标准性。 -/
theorem lt_own_succ_l (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) :
    SecondOrderOrder.lt_l n (succ_l n) := by
  refine ⟨zero_l ℳ, ?_⟩
  rw [add_succ_l hℳ, add_zero_l hℳ]

/-- 原 K 历史的输出唯一。两份历史可使用不同的 `b,c`，且均不要求 `c > 0`。
唯一一次对模型数的归纳显式使用 `history_agree_m` 及其语言、语义证明。 -/
theorem prec_history_unique_l (hℳ : Theory.Models ℳ theory_m)
    {XF XG : set_l ℳ} (hXF : SecondOrderFunctions.function_l XF)
    (hXG : SecondOrderFunctions.function_l XG) {x n y y' : num_l ℳ}
    (hy : prec_history_l XF XG x n y) (hy' : prec_history_l XF XG x n y') : y = y' := by
  obtain ⟨b, c, ⟨a, hFa, hβa⟩, hβy, hsteps⟩ := hy
  obtain ⟨b', c', ⟨a', hFa', hβa'⟩, hβy', hsteps'⟩ := hy'
  let η : Env ℳ [] [.num, .num, .num, .num, .num] :=
    (((((Env.empty (M := ℳ)).pushFree c').pushFree b').pushFree c).pushFree b).pushFree n
  have hP : ∀ i : num_l ℳ, SecondOrderOrder.lt_l i (succ_l n) →
      ∀ u v : num_l ℳ, beta_rel_l b c i u ∧ beta_rel_l b' c' i v → u = v := by
    apply induct_l hℳ history_agree_m history_agree_language_m η
      (fun i => SecondOrderOrder.lt_l i (succ_l n) →
        ∀ u v : num_l ℳ, beta_rel_l b c i u ∧ beta_rel_l b' c' i v → u = v)
      (history_agree_syntax_l hℳ n b c b' c')
    · intro _hi u v hβ
      exact (beta_rel_unique_l hℳ hβ.1 hβa).trans
        ((function_value_unique_l hXF hFa hFa').trans (beta_rel_unique_l hℳ hβ.2 hβa').symm)
    · intro i hIH hi u v hβ
      have hin : SecondOrderOrder.lt_l i n := (SecondOrderOrder.succ_iff_l hℳ i n).mp hi
      have hi' := SecondOrderOrder.trans_l hℳ hin (lt_own_succ_l hℳ n)
      obtain ⟨u₀, u₁, h₀, h₁, hG⟩ := hsteps i hin
      obtain ⟨v₀, v₁, h₀', h₁', hG'⟩ := hsteps' i hin
      have hprev : u₀ = v₀ := hIH hi' u₀ v₀ ⟨h₀, h₀'⟩
      have hnext : u₁ = v₁ := function_value_unique_l hXG hG (by simpa only [hprev] using hG')
      exact (beta_rel_unique_l hℳ hβ.1 h₁).trans
        (hnext.trans (beta_rel_unique_l hℳ hβ.2 h₁').symm)
  exact hP n (lt_own_succ_l hℳ n) y y' ⟨hβy, hβy'⟩

/-- 原 prec 公式对同一输入的两个输出值相等；任意上下文和实际输出项均保留。
此处只是唯一性，尚未声称历史存在或整个程序为全函数。 -/
theorem prec_primitive_unique_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    (hXF : SecondOrderFunctions.function_l XF) (hXG : SecondOrderFunctions.function_l XG)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (s t t' : Term signature_m Γ Δ .num)
    (ht : Formula.satisfies η ((F.prec_l G).form s t))
    (ht' : Formula.satisfies η ((F.prec_l G).form s t')) : t.eval η = t'.eval η := by
  obtain ⟨x, n, hp, hK⟩ := (prec_primitive_syntax_l hℳ F G XF XG hF hG η s t).mp ht
  obtain ⟨x', n', hp', hK'⟩ := (prec_primitive_syntax_l hℳ F G XF XG hF hG η s t').mp ht'
  obtain ⟨hx, hn⟩ := SecondOrderPairingBounds.injective_l hℳ x n x' n' (hp.trans hp'.symm)
  subst x'
  subst n'
  exact prec_history_unique_l hℳ hXF hXG hK hK'

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSemantics
