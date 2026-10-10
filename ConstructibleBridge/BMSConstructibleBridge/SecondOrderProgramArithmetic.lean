import BMSConstructibleBridge.SecondOrderProgramSemantics
import BMSConstructibleBridge.SecondOrderProgramConstructors
import BMSConstructibleBridge.SecondOrderProgramRecursion
import BMSConstructibleBridge.SecondOrderProgramTotality
import BMSConstructibleBridge.SecondOrderProgramRecurrence
import BMSConstructibleBridge.SecondOrderModel
import BMSConstructibleBridge.SecondOrderUnpairing
import BMSConstructibleBridge.SecondOrderSyntax
import BMSConstructibleBridge.PrimitiveProgram

/-!
# 任务26：`id_m` / `const_m` / `add_m` / `mul_m` 的任意模型内部规格

按 Codex #1412 / #1438 的完整任务26，在独立新模块 `SecondOrderProgramArithmetic.lean` 中，
对**原**编译器 AST `PrimitiveProgram.id_m` / `const_m` / `add_m` / `mul_m` 证明它们在任意
ℳ ⊨ 原 Z₂ 理论内的真实内部算法规格。所有出口默认 `hℳ`，只谈具有原 `graph_m` 统一值语义的
内部图 `X`，覆盖全部非标准内部输入；不从只约束标准 `structure_l` 的 `PrimitiveProgram.*_l` /
`F.sound` 搬运结论，也不把程序换成标准等价新代码。

**复用不重建**（Codex #1412 / 任务24 #1350 / 任务25 #1412）：图的存在性与函数性一律由已验收的
`SecondOrderProgramTotality.graph_total_l` 提供；`add`/`mul` 的零/后继方程直接消费任务25 的
`prec_graph_zero_l` / `prec_graph_succ_l`，`mul` 步进复用已证的 `add_spec_l`。逐点关系由
`graph_semantics_l` 在两自由槽 `[input, output]` 上具体化（`graph_point_l`）。
最终规格的反方向需要图函数性，但任务26 合同禁止把四程序自身总性再作为未证前提，故本模块
先证通用 `function_of_semantics_l`：任一携带 `graph_m c` 统一语义的图都与 `graph_total_l`
所取的函数图 `X0` 逐点等价，从而导出 `function_l`；`add_spec_l` / `mul_spec_l` 不再额外要求
`hAf` / `hBf`。

`numeral_val_l k` 是任意模型 `Env.empty` 对**原** `SecondOrderSyntax.numeral_m k` 的求值，
非只对标准结构成立的 `numeral_l`。不 commit / push / 同步；`LEAN_NUM_THREADS=1` 唯一串行。 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramArithmetic

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderNumbers
open SecondOrderDivision SecondOrderFiniteRange SecondOrderBetaSequence
open SecondOrderFunctions SecondOrderHistory SecondOrderUnpairing
open PrimitiveFormulas SecondOrderProgramSemantics SecondOrderProgramConstructors
open SecondOrderProgramRecursion SecondOrderProgramRecurrence SecondOrderProgramTotality

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 任意模型数码 ν(k)

`ν k` 严格定义为任意模型空环境对**原** `numeral_m k`（纯零与后继项）的求值，
不使用只对标准结构成立的 `SecondOrderSyntax.numeral_l`。零/后继方程由求值定义直接得到。 -/

/-- 数码 `k` 在任意模型中的解释：原 `numeral_m k` 项在空环境上的求值。 -/
def numeral_val_l (k : Nat) : num_l ℳ :=
  (numeral_m (Γ := []) (Δ := []) k).eval (Env.empty (M := ℳ))

@[simp] theorem numeral_val_zero_l : numeral_val_l 0 = zero_l ℳ := rfl

theorem numeral_val_succ_l (k : Nat) :
    (numeral_val_l (k + 1) : num_l ℳ) = succ_l (numeral_val_l k) := rfl

/-! ## 逐点关系助手

把 `graph_semantics_l`（任意上下文/环境/项）在具体化的 `[input, output]` 两自由槽环境上
变成 `relation_l X a b` 与一条算术等式之间的等价。这些助手只重组已验收的构造语义，不新增假设。 -/

/-- 统一值语义在两自由槽 `[input, output]` 上的逐点形式。 -/
theorem graph_point_l {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f) (X : set_l ℳ)
    (hX : graph_semantics_l F X) (a b : num_l ℳ) :
    relation_l X a b ↔
      Formula.satisfies (((Env.empty (M := ℳ)).pushFree b).pushFree a)
        (F.form (.fvar .here : Term signature_m [] [.num, .num] .num)
          (.fvar (.there .here) : Term signature_m [] [.num, .num] .num)) := by
  simpa only [Term.eval, Env.pushFree, Assignment.push] using (hX (((Env.empty (M := ℳ)).pushFree b).pushFree a)
    (.fvar .here) (.fvar (.there .here))).symm

/-- 零图逐点关系。 -/
theorem zero_rel_l (_hℳ : Theory.Models ℳ theory_m) {X : set_l ℳ}
    (hX : graph_semantics_l PrimitiveFormulas.zero_l X) (a b : num_l ℳ) :
    relation_l X a b ↔ zero_l ℳ = b := by
  rw [graph_point_l PrimitiveFormulas.zero_l X hX a b]
  simpa only [Term.eval, Env.pushFree, Assignment.push] using zero_semantics_l _hℳ
    (((Env.empty (M := ℳ)).pushFree b).pushFree a) (.fvar .here) (.fvar (.there .here))

/-- 后继图逐点关系。 -/
theorem succ_rel_l (_hℳ : Theory.Models ℳ theory_m) {X : set_l ℳ}
    (hX : graph_semantics_l PrimitiveFormulas.succ_l X) (a b : num_l ℳ) :
    relation_l X a b ↔ succ_l a = b := by
  rw [graph_point_l PrimitiveFormulas.succ_l X hX a b]
  simpa only [Term.eval, Env.pushFree, Assignment.push] using succ_semantics_l _hℳ
    (((Env.empty (M := ℳ)).pushFree b).pushFree a) (.fvar .here) (.fvar (.there .here))

/-- 第一投影图逐点关系：读取模型反配对的第一坐标。 -/
theorem left_rel_l (hℳ : Theory.Models ℳ theory_m) {X : set_l ℳ}
    (hX : graph_semantics_l PrimitiveFormulas.left_l X) (a b : num_l ℳ) :
    relation_l X a b ↔ (value_l hℳ a).1 = b := by
  rw [graph_point_l PrimitiveFormulas.left_l X hX a b]
  simpa only [Term.eval, Env.pushFree, Assignment.push] using left_semantics_l hℳ
    (((Env.empty (M := ℳ)).pushFree b).pushFree a) (.fvar .here) (.fvar (.there .here))

/-- 第二投影图逐点关系：读取模型反配对的第二坐标。 -/
theorem right_rel_l (hℳ : Theory.Models ℳ theory_m) {X : set_l ℳ}
    (hX : graph_semantics_l PrimitiveFormulas.right_l X) (a b : num_l ℳ) :
    relation_l X a b ↔ (value_l hℳ a).2 = b := by
  rw [graph_point_l PrimitiveFormulas.right_l X hX a b]
  simpa only [Term.eval, Env.pushFree, Assignment.push] using right_semantics_l hℳ
    (((Env.empty (M := ℳ)).pushFree b).pushFree a) (.fvar .here) (.fvar (.there .here))

/-- 配对图逐点关系：两子图各自读值后按原顺序配对。 -/
theorem pair_rel_l (_hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    {X : set_l ℳ} (hX : graph_semantics_l (F.pair_l G) X) (a b : num_l ℳ) :
    relation_l X a b ↔
      ∃ u v : num_l ℳ, relation_l XF a u ∧ relation_l XG a v ∧ value_l u v = b := by
  rw [graph_point_l (F.pair_l G) X hX a b]
  simpa only [Term.eval, Env.pushFree, Assignment.push] using pair_semantics_l _hℳ F G XF XG hF hG
    (((Env.empty (M := ℳ)).pushFree b).pushFree a) (.fvar .here) (.fvar (.there .here))

/-- 复合图逐点关系：先经内层图 `G`、再经外层图 `F`。 -/
theorem comp_rel_l (_hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    {X : set_l ℳ} (hX : graph_semantics_l (F.comp_l G) X) (a b : num_l ℳ) :
    relation_l X a b ↔ ∃ m : num_l ℳ, relation_l XG a m ∧ relation_l XF m b := by
  rw [graph_point_l (F.comp_l G) X hX a b]
  simpa only [Term.eval, Env.pushFree, Assignment.push] using comp_semantics_l _hℳ F G XF XG hF hG
    (((Env.empty (M := ℳ)).pushFree b).pushFree a) (.fvar .here) (.fvar (.there .here))

/-! ## 由统一语义导出函数性（Codex #1438(2) / #1442(A)）

规格 (3)(4) 的反方向需要图的 `function_l`。任务26 合同禁止把四程序自身总性再作为未证前提，
所以不额外要求 `hAf`。这里用任务24 的 `graph_total_l hℳ c` 先取到一个真正带 `∃!` 的图 `X0`，
再用 `graph_point_l` 在**同一**两自由槽环境把任意 `A` 与 `X0` 的逐点关系连成等价，
最后逐输入转移存在唯一性。全程不选新集合、不加新公理。 -/

/-- 任一具有原 `graph_m c` 统一值语义的图都自动是函数：与任务24 所取 `X0` 逐点等价，
`X0` 的逐输入 `∃!` 按 `graph_point_l` 桥到该图。 -/
theorem function_of_semantics_l (hℳ : Theory.Models ℳ theory_m) (c : PrimitiveProgram.code_m)
    {A : set_l ℳ} (hA : graph_semantics_l (PrimitiveProgram.graph_m c) A) :
    SecondOrderFunctions.function_l A := by
  obtain ⟨X0, hX0fun, hX0⟩ := graph_total_l hℳ c
  intro a
  -- 同一 `graph_m c` 在两自由槽环境上把 `A` 与 `X0` 的关系逐点连起来。
  have key : ∀ b : num_l ℳ, relation_l A a b ↔ relation_l X0 a b :=
    fun b => (graph_point_l (PrimitiveProgram.graph_m c) A hA a b).trans
      (graph_point_l (PrimitiveProgram.graph_m c) X0 hX0 a b).symm
  -- `X0` 在输入 `a` 处有唯一值，按 key 逐点搬到 `A`。
  obtain ⟨b, hb0, hu0⟩ := hX0fun a
  refine ⟨b, (key b).mpr hb0, ?_⟩
  intro b' hb'
  exact hu0 b' ((key b').mp hb')

/-! ## 规格 (1)：`id_m = .pair .left .right`，`relation X a b ↔ a = b` -/

/-- 恒等程序在任意模型的规格：其图把每个数送到自身。左右图读模型反配对，`pair_l`
把两坐标按原顺序重组回输入，故配对输出恰等于输入。 -/
theorem id_spec_l (hℳ : Theory.Models ℳ theory_m) {X : set_l ℳ}
    (hX : graph_semantics_l (PrimitiveProgram.graph_m PrimitiveProgram.id_m) X)
    (a b : num_l ℳ) : relation_l X a b ↔ a = b := by
  obtain ⟨XL, _, hXL⟩ := left_graph_l hℳ
  obtain ⟨XR, _, hXR⟩ := right_graph_l hℳ
  constructor
  · intro h
    obtain ⟨u, v, hu, hv, hab⟩ :=
      (pair_rel_l hℳ PrimitiveFormulas.left_l PrimitiveFormulas.right_l XL XR hXL hXR hX a b).mp h
    have hu' : (value_l hℳ a).1 = u := (left_rel_l hℳ hXL a u).mp hu
    have hv' : (value_l hℳ a).2 = v := (right_rel_l hℳ hXR a v).mp hv
    have h : SecondOrderPairing.value_l u v = a := by rw [← hu', ← hv']; exact pair_l hℳ a
    exact h.symm.trans hab
  · intro hab
    subst hab
    refine (pair_rel_l hℳ PrimitiveFormulas.left_l PrimitiveFormulas.right_l XL XR hXL hXR hX a a).mpr
      ⟨(value_l hℳ a).1, (value_l hℳ a).2,
        (left_rel_l hℳ hXL _ _).mpr rfl, (right_rel_l hℳ hXR _ _).mpr rfl, pair_l hℳ a⟩

/-! ## 规格 (2)：`const_m k`，`relation X a b ↔ b = ν k`

对外部固定 `k` 结构归纳；`const_m (k+1) = .comp .succ (const_m k)`，其图先经内层 `const_m k`
图（归纳假设给 `m = ν k`）再经后继图（`succ m = b`），于是 `b = succ (ν k) = ν (k+1)`。
内层图的存在与语义由 `graph_total_l` 提供，不新证总性。保留任意输入 `a`。 -/

/-- 常函数程序在任意模型的规格：输出恒为数码 `ν k`，与输入无关。 -/
theorem const_spec_l (hℳ : Theory.Models ℳ theory_m) :
    ∀ (k : Nat) {X : set_l ℳ},
      graph_semantics_l (PrimitiveProgram.graph_m (PrimitiveProgram.const_m k)) X →
      ∀ (a b : num_l ℳ), relation_l X a b ↔ b = numeral_val_l k := by
  intro k
  induction k with
  | zero =>
      intro X hX a b
      rw [zero_rel_l hℳ hX, numeral_val_zero_l]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
  | succ k ih =>
      intro X hX a b
      obtain ⟨Xc, _, hXc⟩ := graph_total_l hℳ (PrimitiveProgram.const_m k)
      obtain ⟨Xs, _, hXs⟩ := succ_graph_l hℳ
      rw [comp_rel_l hℳ PrimitiveFormulas.succ_l
          (PrimitiveProgram.graph_m (PrimitiveProgram.const_m k)) Xs Xc hXs hXc hX a b]
      constructor
      · rintro ⟨m, hc, hs⟩
        have hm : m = numeral_val_l k := (ih hXc a m).mp hc
        subst hm
        have hs' : succ_l (numeral_val_l k) = b := (succ_rel_l hℳ hXs _ _).mp hs
        rw [numeral_val_succ_l]
        exact hs'.symm
      · intro hb
        refine ⟨numeral_val_l k, (ih hXc a _).mpr rfl, ?_⟩
        exact (succ_rel_l hℳ hXs _ _).mpr ((numeral_val_succ_l k).symm.trans hb.symm)

/-! ## 规格 (3)：`add_m`，`relation A (value x n) z ↔ add x n = z`

`add_m = .prec id_m (succ ∘ right ∘ right)`。其图 `A` 是 `prec` 图，故用任务25 的
`prec_graph_zero_l` / `prec_graph_succ_l`（初值经 `id` 图、步进经 `succ∘right∘right` 图），
再对**内部**第二参数 `n` 用 `SecondOrderModel.induct_l` 归纳——归纳变量落在公式头部自由槽，
`x`、集合 `A` 作参数留在环境中，覆盖全部非标准 `n`，不做宿主 `Nat` 递归。 -/

/-- 模型加法项：把签名自身的 `.add` 函数符号用于两数项，供归纳公式使用。 -/
def add_term_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

/-- 加法项在任意环境的求值就是模型自身的 `add_l`。 -/
theorem eval_add_term_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (s t : Term signature_m Γ Δ .num) :
    Term.eval η (add_term_m s t) = add_l (s.eval η) (t.eval η) := rfl

/-- `add_m` 的步进程序 `succ ∘ right ∘ right`（原 `add_m` 用它做 `prec` 的转移函数）。 -/
def add_step_m : PrimitiveProgram.code_m := .comp .succ (.comp .right .right)

/-- 步进程序 `succ ∘ right ∘ right` 的逐点关系：把输入 `⟨x, ⟨k, u⟩⟩` 送到 `succ u`。
逐层拆 `comp`／`succ`／`right` 图，投影坐标读模型反配对。 -/
theorem add_step_rel_l (hℳ : Theory.Models ℳ theory_m) {XS : set_l ℳ}
    (hXS : graph_semantics_l (PrimitiveProgram.graph_m add_step_m) XS)
    (x k u : num_l ℳ) :
    relation_l XS (value_l x (value_l k u)) (succ_l u) := by
  -- step = succ_l.comp_l (right_l.comp_l right_l)
  obtain ⟨Xi, _, hXi⟩ := graph_total_l hℳ (.comp .right .right : PrimitiveProgram.code_m)
  obtain ⟨Xs, _, hXs⟩ := succ_graph_l hℳ
  obtain ⟨Xr, _, hXr⟩ := right_graph_l hℳ
  have hstep : PrimitiveProgram.graph_m add_step_m
      = PrimitiveFormulas.succ_l.comp_l (PrimitiveFormulas.right_l.comp_l
        PrimitiveFormulas.right_l) := rfl
  -- 内层 `right ∘ right`：输入 ⟨x, ⟨k, u⟩⟩ 读两次反配对第二坐标得 u。
  have hi : relation_l Xi (value_l x (value_l k u)) u :=
    (comp_rel_l hℳ PrimitiveFormulas.right_l PrimitiveFormulas.right_l Xr Xr hXr hXr hXi
      (value_l x (value_l k u)) u).mpr
      ⟨value_l k u,
        (right_rel_l hℳ hXr _ _).mpr (congrArg Prod.snd
          (SecondOrderUnpairing.unpair_l hℳ x (value_l k u))),
        (right_rel_l hℳ hXr _ _).mpr (congrArg Prod.snd
          (SecondOrderUnpairing.unpair_l hℳ k u))⟩
  -- 外层 `succ ∘ 内层`：先经内层得 u，再经后继得 succ u。
  exact (comp_rel_l hℳ PrimitiveFormulas.succ_l
      (PrimitiveFormulas.right_l.comp_l PrimitiveFormulas.right_l) Xs Xi hXs hXi
      ((by rwa [← hstep]) : graph_semantics_l
        (PrimitiveFormulas.succ_l.comp_l (PrimitiveFormulas.right_l.comp_l
          PrimitiveFormulas.right_l)) XS)
      (value_l x (value_l k u)) (succ_l u)).mpr
    ⟨u, hi, (succ_rel_l hℳ hXs u (succ_l u)).mpr rfl⟩

/-- `add_m` 的初值图是 `id` 图，输出恒等；步进图把 `⟨x,⟨k,u⟩⟩` 送到 `succ u`。
`graph_m add_m` 恰为 `(graph_m id).prec_l (graph_m step)`。 -/
theorem add_prec_eq_m : PrimitiveProgram.graph_m PrimitiveProgram.add_m
    = (PrimitiveProgram.graph_m PrimitiveProgram.id_m).prec_l
      (PrimitiveProgram.graph_m add_step_m) := rfl

/-- 归纳公式：头部自由槽为被归纳数 `n`，参数 `x`（数）、`A`（集合）随后。 -/
def add_phi_m : Formula signature_m [] [.num, .num, .set] :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here)
      (add_term_m (.fvar (.there .here)) (.fvar .here))))

/-- 归纳公式属纯二阶算术语言；直接归约实际 AST。 -/
theorem add_phi_language_m : SecondOrderArithmetic.language_m add_phi_m = true := by
  unfold add_phi_m
  simp only [SecondOrderArithmetic.language_m, GraphSyntax.edge_m, PrimitiveFormulas.pair_m,
    PrimitiveFormulas.lt_m, SecondOrderSyntax.pure_args_m, SecondOrderSyntax.pure_term_m, add_term_m]
  rfl

/-- 归纳公式的逐模型语义：`x`、`A` 由环境提供，头部槽 `n` 由 `pushFree` 压入。 -/
theorem add_phi_syntax_l (A : set_l ℳ) (x : num_l ℳ) (n : num_l ℳ) :
    Formula.satisfies
        ((((Env.empty (M := ℳ)).pushFree A).pushFree x).pushFree n) add_phi_m ↔
      relation_l A (value_l x n) (add_l x n) := by
  -- formula_l / edge_l 在最外层抽象掉内部提升，避免与 pushBound 的 simp 冲突。
  simp only [add_phi_m, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l,
    eval_add_term_l]
  -- 具体环境 ((empty.pushFree A).pushFree x).pushFree n 上的自由变量求值。
  simp only [Term.eval, Env.pushFree, Env.pushBound, Env.empty, Assignment.push]
  constructor
  · rintro ⟨q, hp, he⟩
    rw [← hp] at he
    exact he
  · intro h
    exact ⟨value_l x n, rfl, h⟩

/-- 加法程序在任意模型的完整规格：图 `A` 把配对码 `⟨x, n⟩` 送到内部加法 `add x n`，
且该输出唯一。对内 `n` 用 `induct_l` 证存在方向，反方向的函数性不额外假设，
由 `function_of_semantics_l` 从统一语义 `hA` 自身导出。 -/
theorem add_spec_l (hℳ : Theory.Models ℳ theory_m) {A : set_l ℳ}
    (hA : graph_semantics_l (PrimitiveProgram.graph_m PrimitiveProgram.add_m) A)
    (x : num_l ℳ) (n : num_l ℳ) (z : num_l ℳ) :
    relation_l A (value_l x n) z ↔ add_l x n = z := by
  obtain ⟨XF, hXF, hXF'⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨XG, hXG, hXG'⟩ := graph_total_l hℳ add_step_m
  -- 函数性由统一语义导出，不作为未证前提。
  have hAf : SecondOrderFunctions.function_l A := function_of_semantics_l hℳ PrimitiveProgram.add_m hA
  -- 存在方向：对内部 `n` 归纳 `relation A (value x n) (add x n)`。
  have hex : ∀ m : num_l ℳ, relation_l A (value_l x m) (add_l x m) := by
    refine induct_l hℳ add_phi_m add_phi_language_m
      (((Env.empty (M := ℳ)).pushFree A).pushFree x)
      (fun m => relation_l A (value_l x m) (add_l x m))
      (fun m => ?_) ?_ ?_
    · exact add_phi_syntax_l A x m
    · -- 基例 n = 0：add x 0 = x，初值经 id 图。
      show relation_l A (value_l x (zero_l ℳ)) (add_l x (zero_l ℳ))
      rw [add_zero_l hℳ]
      exact (prec_graph_zero_l hℳ (PrimitiveProgram.graph_m PrimitiveProgram.id_m)
        (PrimitiveProgram.graph_m add_step_m) XF XG hXF' hXG' A
        (by rw [← add_prec_eq_m]; exact hA) x x).mpr
          ((id_spec_l hℳ hXF' x x).mpr rfl)
    · -- 后继步：add x (succ k) = succ (add x k)，步进图把 ⟨x,⟨k,add x k⟩⟩ 送 succ (add x k)。
      intro k ih
      show relation_l A (value_l x (succ_l k)) (add_l x (succ_l k))
      rw [add_succ_l hℳ]
      refine (prec_graph_succ_l hℳ (PrimitiveProgram.graph_m PrimitiveProgram.id_m)
        (PrimitiveProgram.graph_m add_step_m) XF XG hXF' hXG' A
        (by rw [← add_prec_eq_m]; exact hA) hXF hXG x k (succ_l (add_l x k))).mpr
        ⟨add_l x k, ih, add_step_rel_l hℳ hXG' x k (add_l x k)⟩
  -- 反方向：图 `A` 是函数，正确输出与任意输出在同一输入处相等。
  constructor
  · intro h
    exact (function_value_unique_l hAf h (hex n)).symm
  · intro h
    exact h ▸ hex n

/-! ## 规格 (4)：`mul_m`，`relation B (value x n) z ↔ mul x n = z`

`mul_m = .prec zero_m (add_m ∘ (right∘right ⊳ , left))`：初值图取零，步进图先把
`⟨x,⟨k,u⟩⟩` 重排为 `⟨u,x⟩`（`right∘right` 读内层第二坐标 `u`、`left` 读外层第一坐标 `x`），
再经**已证的 `add_m` 图**取 `add u x`。与加法同样对内 `n` 用 `induct_l`，零/后继方程走
`prec_graph_zero_l` / `prec_graph_succ_l`，反方向用 `function_l B`。 -/

/-- 模型乘法项：把签名自身的 `.mul` 函数符号用于两数项，供归纳公式使用。 -/
def mul_term_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .mul (.cons s (.cons t .nil))

/-- 乘法项在任意环境的求值就是模型自身的 `mul_l`。 -/
theorem eval_mul_term_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (s t : Term signature_m Γ Δ .num) :
    Term.eval η (mul_term_m s t) = mul_l (s.eval η) (t.eval η) := rfl

/-- `mul_m` 步进重排子程序 `right∘right ⊳ , left`。 -/
def mul_inner_m : PrimitiveProgram.code_m := .pair (.comp .right .right) .left

/-- `mul_m` 步进程序 `add_m ∘ mul_inner_m`。 -/
def mul_step_m : PrimitiveProgram.code_m := .comp PrimitiveProgram.add_m mul_inner_m

/-- 步进重排子图 `mul_inner_m` 把 `⟨x,⟨k,u⟩⟩` 送到配对码 `⟨u,x⟩`：内层 `right∘right` 读 `u`、
`left` 读 `x`，配对按 `u` 前 `x` 后重组。 -/
theorem mul_inner_rel_l (hℳ : Theory.Models ℳ theory_m) {XI : set_l ℳ}
    (hXI : graph_semantics_l (PrimitiveProgram.graph_m mul_inner_m) XI)
    (x k u : num_l ℳ) :
    relation_l XI (value_l x (value_l k u)) (value_l u x) := by
  obtain ⟨Xrr, _, hXrr⟩ := graph_total_l hℳ (.comp .right .right : PrimitiveProgram.code_m)
  obtain ⟨Xl, _, hXl⟩ := left_graph_l hℳ
  obtain ⟨Xs, _, hXs⟩ := right_graph_l hℳ
  have hgraph : PrimitiveProgram.graph_m mul_inner_m
      = (PrimitiveFormulas.right_l.comp_l PrimitiveFormulas.right_l).pair_l
        PrimitiveFormulas.left_l := rfl
  -- 内层 `right∘right`：输入 ⟨x,⟨k,u⟩⟩ 读两次反配对第二坐标得 u。
  have hrr : relation_l Xrr (value_l x (value_l k u)) u :=
    (comp_rel_l hℳ PrimitiveFormulas.right_l PrimitiveFormulas.right_l Xs Xs hXs hXs hXrr
      (value_l x (value_l k u)) u).mpr
      ⟨value_l k u,
        (right_rel_l hℳ hXs _ _).mpr (congrArg Prod.snd
          (SecondOrderUnpairing.unpair_l hℳ x (value_l k u))),
        (right_rel_l hℳ hXs _ _).mpr (congrArg Prod.snd
          (SecondOrderUnpairing.unpair_l hℳ k u))⟩
  -- 外层配对：第一坐标取 u、第二坐标取 x，重组回 value u x。
  refine ((pair_rel_l hℳ (PrimitiveFormulas.right_l.comp_l PrimitiveFormulas.right_l)
      PrimitiveFormulas.left_l Xrr Xl hXrr hXl
      ((by rwa [← hgraph]) : graph_semantics_l
        ((PrimitiveFormulas.right_l.comp_l PrimitiveFormulas.right_l).pair_l
          PrimitiveFormulas.left_l) XI)
      (value_l x (value_l k u)) (value_l u x)).mpr)
    ⟨u, x, hrr,
      (left_rel_l hℳ hXl _ _).mpr (congrArg Prod.fst
        (SecondOrderUnpairing.unpair_l hℳ x (value_l k u))), rfl⟩

/-- 步进程序 `add_m ∘ mul_inner_m` 把 `⟨x,⟨k,u⟩⟩` 送到 `add u x`，复用已证的 `add_m` 图规格。 -/
theorem mul_step_rel_l (hℳ : Theory.Models ℳ theory_m) {XS : set_l ℳ}
    (hXS : graph_semantics_l (PrimitiveProgram.graph_m mul_step_m) XS)
    (x k u : num_l ℳ) :
    relation_l XS (value_l x (value_l k u)) (add_l u x) := by
  obtain ⟨XA, _, hXA⟩ := graph_total_l hℳ PrimitiveProgram.add_m
  obtain ⟨XI, _, hXI⟩ := graph_total_l hℳ mul_inner_m
  have hstep : PrimitiveProgram.graph_m mul_step_m
      = (PrimitiveProgram.graph_m PrimitiveProgram.add_m).comp_l
        (PrimitiveProgram.graph_m mul_inner_m) := rfl
  refine ((comp_rel_l hℳ (PrimitiveProgram.graph_m PrimitiveProgram.add_m)
      (PrimitiveProgram.graph_m mul_inner_m) XA XI hXA hXI
      ((by rwa [← hstep]) : graph_semantics_l
        ((PrimitiveProgram.graph_m PrimitiveProgram.add_m).comp_l
          (PrimitiveProgram.graph_m mul_inner_m)) XS)
      (value_l x (value_l k u)) (add_l u x)).mpr)
    ⟨value_l u x, mul_inner_rel_l hℳ hXI x k u,
      (add_spec_l hℳ hXA u x (add_l u x)).mpr rfl⟩

/-- `mul_m` 恰为 `zero` 初值图配 `mul_step_m` 步进图的 `prec`。 -/
theorem mul_prec_eq_m : PrimitiveProgram.graph_m PrimitiveProgram.mul_m
    = (PrimitiveProgram.graph_m .zero).prec_l (PrimitiveProgram.graph_m mul_step_m) := rfl

/-- 乘法归纳公式：头部自由槽为被归纳数 `n`，参数 `x`（数）、`B`（集合）随后。 -/
def mul_phi_m : Formula signature_m [] [.num, .num, .set] :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here)
      (mul_term_m (.fvar (.there .here)) (.fvar .here))))

/-- 乘法归纳公式属纯二阶算术语言；直接归约实际 AST。 -/
theorem mul_phi_language_m : SecondOrderArithmetic.language_m mul_phi_m = true := by
  unfold mul_phi_m
  simp only [SecondOrderArithmetic.language_m, GraphSyntax.edge_m, PrimitiveFormulas.pair_m,
    PrimitiveFormulas.lt_m, SecondOrderSyntax.pure_args_m, SecondOrderSyntax.pure_term_m, mul_term_m]
  rfl

/-- 乘法归纳公式的逐模型语义：`x`、`B` 由环境提供，头部槽 `n` 由 `pushFree` 压入。 -/
theorem mul_phi_syntax_l (B : set_l ℳ) (x : num_l ℳ) (n : num_l ℳ) :
    Formula.satisfies
        ((((Env.empty (M := ℳ)).pushFree B).pushFree x).pushFree n) mul_phi_m ↔
      relation_l B (value_l x n) (mul_l x n) := by
  -- formula_l / edge_l 在最外层抽象掉内部提升，避免与 pushBound 的 simp 冲突。
  simp only [mul_phi_m, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l,
    eval_mul_term_l]
  -- 具体环境 ((empty.pushFree B).pushFree x).pushFree n 上的自由变量求值。
  simp only [Term.eval, Env.pushFree, Env.pushBound, Env.empty, Assignment.push]
  constructor
  · rintro ⟨q, hp, he⟩
    rw [← hp] at he
    exact he
  · intro h
    exact ⟨value_l x n, rfl, h⟩

/-- 乘法程序在任意模型的完整规格：图 `B` 把配对码 `⟨x, n⟩` 送到内部乘法 `mul x n`，
且该输出唯一。对内 `n` 用 `induct_l` 证存在方向，反方向的函数性不额外假设，
由 `function_of_semantics_l` 从统一语义 `hB` 自身导出。 -/
theorem mul_spec_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    (hB : graph_semantics_l (PrimitiveProgram.graph_m PrimitiveProgram.mul_m) B)
    (x : num_l ℳ) (n : num_l ℳ) (z : num_l ℳ) :
    relation_l B (value_l x n) z ↔ mul_l x n = z := by
  obtain ⟨XF, hXF, hXF'⟩ := zero_graph_l hℳ
  obtain ⟨XG, hXG, hXG'⟩ := graph_total_l hℳ mul_step_m
  -- 函数性由统一语义导出，不作为未证前提。
  have hBf : SecondOrderFunctions.function_l B := function_of_semantics_l hℳ PrimitiveProgram.mul_m hB
  -- 存在方向：对内部 `n` 归纳 `relation B (value x n) (mul x n)`。
  have hex : ∀ m : num_l ℳ, relation_l B (value_l x m) (mul_l x m) := by
    refine induct_l hℳ mul_phi_m mul_phi_language_m
      (((Env.empty (M := ℳ)).pushFree B).pushFree x)
      (fun m => relation_l B (value_l x m) (mul_l x m))
      (fun m => ?_) ?_ ?_
    · exact mul_phi_syntax_l B x m
    · -- 基例 n = 0：mul x 0 = 0，初值经 zero 图。
      show relation_l B (value_l x (zero_l ℳ)) (mul_l x (zero_l ℳ))
      rw [mul_zero_l hℳ]
      exact (prec_graph_zero_l hℳ (PrimitiveProgram.graph_m .zero) (PrimitiveProgram.graph_m mul_step_m)
        XF XG hXF' hXG' B (by rw [← mul_prec_eq_m]; exact hB) x (zero_l ℳ)).mpr
          ((zero_rel_l hℳ hXF' x (zero_l ℳ)).mpr rfl)
    · -- 后继步：mul x (succ k) = add (mul x k) x，步进图把 ⟨x,⟨k,mul x k⟩⟩ 送 add (mul x k) x。
      intro k ih
      show relation_l B (value_l x (succ_l k)) (mul_l x (succ_l k))
      rw [mul_succ_l hℳ]
      refine (prec_graph_succ_l hℳ (PrimitiveProgram.graph_m .zero) (PrimitiveProgram.graph_m mul_step_m)
        XF XG hXF' hXG' B (by rw [← mul_prec_eq_m]; exact hB) hXF hXG x k
        (add_l (mul_l x k) x)).mpr
        ⟨mul_l x k, ih, mul_step_rel_l hℳ hXG' x k (mul_l x k)⟩
  -- 反方向：图 `B` 是函数，正确输出与任意输出在同一输入处相等。
  constructor
  · intro h
    exact (function_value_unique_l hBf h (hex n)).symm
  · intro h
    exact h ▸ hex n

/-! ## 公理审计

任务26 的新出口只应继承已复编模块的可信基（`propext / Classical.choice / Quot.sound`），
不得引入 `sorryAx` 或新公理。以下逐一打印本模块全部公开出口的公理依赖。 -/

-- 数码与逐点关系助手
#print axioms numeral_val_l
#print axioms numeral_val_zero_l
#print axioms numeral_val_succ_l
#print axioms graph_point_l
#print axioms zero_rel_l
#print axioms succ_rel_l
#print axioms left_rel_l
#print axioms right_rel_l
#print axioms pair_rel_l
#print axioms comp_rel_l
-- 由语义导出函数性
#print axioms function_of_semantics_l
-- 规格 (1)(2)
#print axioms id_spec_l
#print axioms const_spec_l
-- 规格 (3) add
#print axioms add_term_m
#print axioms eval_add_term_l
#print axioms add_step_m
#print axioms add_step_rel_l
#print axioms add_prec_eq_m
#print axioms add_phi_m
#print axioms add_phi_language_m
#print axioms add_phi_syntax_l
#print axioms add_spec_l
-- 规格 (4) mul
#print axioms mul_term_m
#print axioms eval_mul_term_l
#print axioms mul_inner_m
#print axioms mul_step_m
#print axioms mul_inner_rel_l
#print axioms mul_step_rel_l
#print axioms mul_prec_eq_m
#print axioms mul_phi_m
#print axioms mul_phi_language_m
#print axioms mul_phi_syntax_l
#print axioms mul_spec_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramArithmetic
