import BMSConstructibleBridge.FixedHeightSecondOrder
import BMSConstructibleBridge.PureSecondOrder
import BMSConstructibleBridge.PrimitiveCoding
import BMSConstructibleBridge.PrimitiveProgram

/-!
# 当前高度有界目标的纯二阶算术矩阵（任务2 第 2 步 / 第 3 步）

`FixedHeightSecondOrder` 只给出宿主层规格；本模块把该规格**真正编译成**
`signature_m` 中的纯算术公式：高度上界用解码后的当前高度图 `h` 表达
（不是另造关系符号），矩阵其余部分沿用原 `PureSecondOrder` 的图编译器。

与旧 `PureSecondOrder.formula_l` 的区别只在起点前提：旧链要求"第 n 个种子
出现在 `X` 中"，本模块要求"`X` 的**全部取值**解码后当前高度不超过自由参数 `N`"。
因此终点是 `FixedHeightSecondOrder.sentence_l N` 而不是 `SeedReflection.sentence_l n`。

## 任务7-A：程序来源保留

原 `formula_l` 经 `PrimitiveFormulas.primrec_l` 只取到**存在性**的 `graph_l h`，
其 `sound` 又只约束标准结构 `structure_l`，于是"这个公式从哪个程序编译来"这条
信息在出口处丢失了。本模块现在把图参数**一般化**为 `graph_l f` / `graph_l g`，
公开程序参数化的 `compiled_matrix_m (cH cE)`：

* `m_graph`（无图参数）/ `m_allBounds F` / `m_stop G` / `matrix_m F G` —— 对**任意**
  图参数成立，纯性相应一般化；
* `compiled_matrix_m cH cE` —— AST 直接由 `PrimitiveProgram.graph_m cH` /
  `graph_m cE` 生成，因此编译来源在类型里可见，不必回头查私有名；
* `complete_m` 从 `h_prim` / `edge_prim` 取出**程序见证** `cH` / `cE`，给出
  `eval_l cH = h`、`eval_l cE = edge` 的等式；
* `formula_l` / `closed_l` **保留为推论**（取 `f := h`、`g := edge`），不是新增出口。

关键观察：`matrix_sound` 的结论是**参数化的** `sentence_general f g N`，
其中 `f`、`g` 就是该矩阵所用图证书的图函数。故一般化版本比旧版本**更强**：
对任意一对程序 `cH`、`cE`，编译矩阵的语义由 `sentence_general` 在该程序所
求值出的 `f`、`g` 处实例给出。这正是"编译来源保留"的实质内容 —— 编译来源
进入**前提与类型**，而语义结论**随参数变化**；只有再取 `f := h`、`g := edge`
（经 `sentence_general_h`）才回到 `FixedHeightSecondOrder.sentence_l N`。

闭句仍走 `PureSecondOrder.closed_m` 的同一数码替换：`closed_l` 用的 `φ` 就是
`formula_l` 给出的那个矩阵，**不为每个 `N` 另选标准等价公式**。

本模块**不**使用旧 `formula_l` / `closed_formula_l`（那两个的终点才是旧种子目标），
也**不**修改旧模块：`PureSecondOrder` 中的 `member`/`ternary`/`graph`/`stop` 是 `private`，
此处按必要范围重做小模板。

仍然只是宿主层 AST 与标准语义的对应：不声称任意非标准 Z₂ 模型中的算法总性、
Collection 转移或最终良序推导；**也不声称已经给出某个具体 BM4 可执行程序**——
本批只保留"今后可按七种程序构造作归纳"的来源。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.FixedHeightPureFormula

open Logic FirstOrder SecondOrderSyntax

set_option autoImplicit false

private abbrev term (Γ Δ : SortContext signature_m) := Term signature_m Γ Δ .num

private def zero {Γ Δ : SortContext signature_m} : term Γ Δ :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : term Γ Δ) : term Γ Δ :=
  Term.app (σ := signature_m) .succ (.cons s .nil)

/-! ## 高度图

`h` 就是 `HeightDescent.height_l ∘ ArithmeticPresentation.decode_l` 在自然数码上的
取值：`trimHeight ((decode_l a).1.raw)`。高度是**可计算**的，所以直接来自
`PrimitiveCoding` 的原语证书，而不是新增一个算法原语。 -/

private def h (a : Nat) : Nat := trimHeight ((ArithmeticPresentation.decode_l a).1.raw)

/-- `HeightDescent.height_l` 在解码结果上与该函数定义相同。 -/
private theorem h_eq (a : Nat) :
    h a = HeightDescent.height_l (ArithmeticPresentation.decode_l a).1 := rfl

private theorem h_prim : Nat.Primrec h := by
  show Nat.Primrec (fun a => trimHeight ((ArithmeticPresentation.decode_l a).1.raw))
  exact Primrec.nat_iff.mp (PrimitiveCoding.height_l.comp PrimitiveCoding.decode_l)

/-- 高度图的**程序见证**：`h` 确由七种原始递归构造编译而来。 -/
private theorem h_complete : ∃ c : PrimitiveProgram.code_m, PrimitiveProgram.eval_l c = h :=
  PrimitiveProgram.complete_m h_prim

/-! ## 高度上界模板

`bound F a N := ∃u (F.form a↑ u ∧ ¬ lt_m N↑ u)`，即 `h a = u` 且 `¬ N < u`，
合起来正是 `h a ≤ N`。只用到图 `F` 的纯性与语义，不新增布尔特征函数。

任务7-A 把参数从具体的 `graph_l h` 推广为**任意** `graph_l f`：
`bound` 本身只用到 `F.form` / `F.pure` / `F.sound`，与 `f` 的具体取值无关。 -/

def bound {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f) {Γ Δ : SortContext signature_m}
    (a N : term Γ Δ) : Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (F.form (a.weakenBound sort_m.num) (.bvar .here))
    (.neg (PrimitiveFormulas.lt_m (N.weakenBound sort_m.num) (.bvar .here))))

theorem bound_pure {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (a N : term Γ Δ)
    (ha : pure_term_m a = true) (hN : pure_term_m N = true) : pure_m (bound F a N) = true := by
  simp only [bound, pure_m, Bool.and_eq_true]
  refine ⟨F.pure _ _ (by simpa only [PrimitiveFormulas.weaken_l] using ha) rfl, ?_⟩
  exact PrimitiveFormulas.lt_pure_l _ _
    (by simpa only [PrimitiveFormulas.weaken_l] using hN) rfl

theorem bound_sound {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ) (a N : term Γ Δ) :
    Formula.satisfies η (bound F a N) ↔ f (a.eval η) ≤ N.eval η := by
  simp only [bound, Formula.satisfies, F.sound, PrimitiveFormulas.lt_l, Term.eval_weakenBound,
    Term.eval]
  change (∃ u : Nat, f (a.eval η) = u ∧ ¬ N.eval η < u) ↔ f (a.eval η) ≤ N.eval η
  constructor
  · rintro ⟨u, hu, hnu⟩
    exact hu.trans_le (Nat.le_of_not_lt hnu)
  · intro hle
    exact ⟨f (a.eval η), rfl, Nat.not_lt.mpr hle⟩

/-- 高度专用形态：特化 `f := h` 后即"解码后当前高度 ≤ N"。
    证明走一般化版本，避免维护两份。 -/
theorem bound_sound_h {Γ Δ : SortContext signature_m} (F : PrimitiveFormulas.graph_l h)
    (η : Env structure_l Γ Δ) (a N : term Γ Δ) :
    Formula.satisfies η (bound F a N) ↔
      HeightDescent.height_l (ArithmeticPresentation.decode_l (a.eval η)).1 ≤ N.eval η := by
  simpa only [h, HeightDescent.height_l] using bound_sound F η a N

/-! ## 公式模板（沿用原图编译器的形状） -/

private def member {Γ Δ : SortContext signature_m} (s t : term Γ Δ)
    (X : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (s.weakenBound sort_m.num) (t.weakenBound sort_m.num) (.bvar .here))
    (.rel .mem (.cons (.bvar .here) (.cons (X.weakenBound sort_m.num) .nil))))

private theorem member_sound {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ)
    (s t : term Γ Δ) (X : Term signature_m Γ Δ .set) :
    Formula.satisfies η (member s t X) ↔ Nat.pair (s.eval η) (t.eval η) ∈ X.eval η := by
  simp only [member, Formula.satisfies, PrimitiveFormulas.pair_l,
    Term.eval_weakenBound, Term.eval, Arguments.eval]
  change (∃ p : Nat, Nat.pair (s.eval η) (t.eval η) = p ∧ p ∈ X.eval η) ↔ _
  simp

private abbrev twice {Γ Δ : SortContext signature_m} (s : term Γ Δ) :
    term (.num :: .num :: Γ) Δ :=
  (s.weakenBound sort_m.num).weakenBound sort_m.num

private def ternary {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (s t u : term Γ Δ) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (twice t) (twice u) (.bvar (.there .here)))
    (.conj (PrimitiveFormulas.pair_m (twice s) (.bvar (.there .here)) (.bvar .here))
      (F.form (.bvar .here) (succ zero)))))

private theorem ternary_pure {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (s t u : term Γ Δ)
    (hs : pure_term_m s = true) (ht : pure_term_m t = true) (hu : pure_term_m u = true) :
    pure_m (ternary F s t u) = true := by
  simp only [ternary, pure_m, Bool.and_eq_true]
  exact ⟨PrimitiveFormulas.pair_pure_l _ _ _
      (by simpa only [twice, PrimitiveFormulas.weaken_l] using ht)
      (by simpa only [twice, PrimitiveFormulas.weaken_l] using hu) rfl,
    PrimitiveFormulas.pair_pure_l _ _ _
      (by simpa only [twice, PrimitiveFormulas.weaken_l] using hs) rfl rfl,
    F.pure _ _ rfl rfl⟩

private theorem ternary_sound {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ) (s t u : term Γ Δ) :
    Formula.satisfies η (ternary F s t u) ↔
    f (Nat.pair (s.eval η) (Nat.pair (t.eval η) (u.eval η))) = 1 := by
  simp only [ternary, Formula.satisfies, PrimitiveFormulas.pair_l, F.sound,
    twice, Term.eval_weakenBound, succ, zero, Term.eval, Arguments.eval]
  change (∃ p q : Nat, Nat.pair (t.eval η) (u.eval η) = p ∧
    Nat.pair (s.eval η) p = q ∧ f q = 1) ↔ _
  simp

/-- 检查器判定函数：`check_l` 的三个参数由 `Nat.pair` 三编码展开。 -/
private def edge (n : Nat) : Nat :=
  cond (ArithmeticPresentation.check_l n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2) 1 0

private theorem edge_prim : Nat.Primrec edge := by
  have h₀ : Primrec (fun n : Nat => n.unpair.1) := Primrec.nat_iff.mpr .left
  have h₁ : Primrec (fun n : Nat => n.unpair.2) := Primrec.nat_iff.mpr .right
  have h₂ : Primrec (fun n : Nat =>
      (n.unpair.1, n.unpair.2.unpair.1, n.unpair.2.unpair.2)) :=
    Primrec.pair h₀ (Primrec.pair (h₀.comp h₁) (h₁.comp h₁))
  have h₃ := PrimitiveCoding.check_l.comp h₂
  have h₄ := (Primrec.dom_bool (fun b => cond b (1 : Nat) 0)).comp h₃
  apply Primrec.nat_iff.mp
  apply h₄.of_eq
  intro n
  rfl

/-- 检查器的**程序见证**：`edge` 确由七种原始递归构造编译而来。 -/
theorem edge_complete : ∃ c : PrimitiveProgram.code_m, PrimitiveProgram.eval_l c = edge :=
  PrimitiveProgram.complete_m edge_prim

private theorem edge_pair (b a k : Nat) : edge (Nat.pair b (Nat.pair a k)) = 1 ↔
    ArithmeticPresentation.check_l b a k = true := by
  cases h : ArithmeticPresentation.check_l b a k <;> simp [edge, h]

/-- 不再给出下降见证的两种写法等价：`edge _ ≠ 1` 与 `check_l _ ≠ true`。 -/
private theorem edge_ne_one (b a k : Nat) :
    (edge (Nat.pair b (Nat.pair a k)) ≠ 1) ↔ (ArithmeticPresentation.check_l b a k ≠ true) :=
  not_congr (edge_pair b a k)

/-! ## 三个合取块（任务7-A：图参数一般化）

三块在**绑定/自由上下文**上与旧 `PureSecondOrder.graph` / `start` / `stop` 逐字一致
（上下文是 `Formula signature_m [.set] [.num]`：绑定 `.set` 是目标集合 `X`，
自由 `.num` 是高度上界 `N`），只把图参数从写死的 `graph_l h` / `graph_l edge`
换成自由的 `graph_l f` / `graph_l g`。 -/

/-- 全域单值函数图，与原 `PureSecondOrder.graph` 逐字相同（无图参数）。 -/
def m_graph : Formula signature_m [.set] [.num] :=
  .forallE .num (.existsE .num (.conj
    (member (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))
    (.forallE .num (.imp
      (member (.bvar (.there (.there .here))) (.bvar .here)
        (.bvar (.there (.there (.there .here)))))
      (.equal (.bvar .here) (.bvar (.there .here)))))))

theorem m_graph_pure : pure_m m_graph = true := by
  decide

/-- 取代旧 `start` 的前提：`X` 的**全部取值**解码后当前高度 ≤ `N`。

    旧链只要求"第 n 个种子在 `X` 中"，这里对每个 `i a` 若 `pair i a ∈ X`
    就要求 `bound F a N`，即不限定起点，但限制全部取值。
    **图参数 `F` 是自由的** —— 这正是任务7-A 要保留的编译来源。

    上下文核算：外层 `Formula signature_m [.set] [.num]` 中绑定 `.set`（`X`）是
    `.bvar .here`。两个 `.forallE .num` 之后绑定为 `[.num, .num, .set]`：
    `i` 在索引 1、`a` 在索引 0、`X` 在索引 2；自由 `.num`（`N`）仍是 `.fvar .here`。 -/
def m_allBounds {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f) :
    Formula signature_m [.set] [.num] :=
  .forallE .num (.forallE .num (.imp
    (member (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))
    (bound F (.bvar .here) (.fvar .here))))

theorem m_allBounds_pure {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f) :
    pure_m (m_allBounds F) = true := by
  simp only [m_allBounds, pure_m, Bool.and_eq_true]
  exact ⟨by decide, bound_pure F _ _ rfl rfl⟩

/-- 终点块：存在相邻两步，使检查器不给出下降见证，与原 `PureSecondOrder.stop` 逐字相同。
    **图参数 `G` 自由**，同样保留编译来源。 -/
def m_stop {g : Nat → Nat} (G : PrimitiveFormulas.graph_l g) : Formula signature_m [.set] [.num] :=
  .existsE .num (.existsE .num (.existsE .num (.conj
    (member (.bvar (.there (.there .here))) (.bvar (.there .here))
      (.bvar (.there (.there (.there .here)))))
    (.conj (member (succ (.bvar (.there (.there .here)))) (.bvar .here)
      (.bvar (.there (.there (.there .here)))))
      (.forallE .num (.neg (ternary G (.bvar (.there .here))
        (.bvar (.there (.there .here))) (.bvar .here))))))))

theorem m_stop_pure {g : Nat → Nat} (G : PrimitiveFormulas.graph_l g) :
    pure_m (m_stop G) = true := by
  simp only [m_stop, pure_m, Bool.and_eq_true]
  exact ⟨by decide, by decide, ternary_pure G _ _ _ rfl rfl rfl⟩

/-! ## 目标矩阵与标准语义 -/

/-- **程序参数化的目标矩阵**：`graph → (allBounds → stop)`。

    `F` / `G` 是两个**任意**的图证书，因此该矩阵对任意程序成立。 -/
def matrix_m {f g : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    (G : PrimitiveFormulas.graph_l g) : Formula signature_m [.set] [.num] :=
  .imp m_graph (.imp (m_allBounds F) (m_stop G))

theorem matrix_pure {f g : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    (G : PrimitiveFormulas.graph_l g) : pure_m (matrix_m F G) = true := by
  simp only [matrix_m, pure_m, Bool.and_eq_true]
  exact ⟨m_graph_pure, m_allBounds_pure F, m_stop_pure G⟩

/-! ### 一般化语义句

把 `FixedHeightSecondOrder.sentence_l` 里写死的高度谓词
`HeightDescent.height_l ∘ decode_l` 与检查器 `check_l` 换成**参数** `f`、`g`。
这样 `matrix_sound` 对任意图证书都成立（`rfl` 即可）。取 `f := h`、`g := edge`
时，经 `sentence_general_h` 得到 `FixedHeightSecondOrder.sentence_l`：
高度部分由 `h` 的定义化简，检查器部分由 `edge_ne_one` 把 `edge _ = 1`
等价换成 `check_l _ = true`（**这一步是等价改写，不是定义相等**）。

这正是任务7-A 的实质：编译来源（`graph_l f` / `graph_l g`）进入前提，
语义结论随 `f`、`g` 参数化；旧 `formula_l` 是 `f := h`、`g := edge` 的特例。 -/

/-- 参数化的"高度有界 ⇒ 有非下降步"句；`f` 是高度谓词，`g` 是检查器判定函数。 -/
def sentence_general (f g : Nat → Nat) (N : Nat) : Prop :=
  ∀ X : Set Nat, SecondOrderPresentation.function_l X →
    (∀ i a, Nat.pair i a ∈ X → f a ≤ N) →
      ∃ i a b, Nat.pair i a ∈ X ∧ Nat.pair (i + 1) b ∈ X ∧
        ∀ k, g (Nat.pair b (Nat.pair a k)) ≠ 1

/-- **核心语义定理**：任意一对图证书给出的矩阵，其 `∀X` 语义恰是
    参数化句 `sentence_general f g N`。 -/
theorem matrix_sound {f g : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    (G : PrimitiveFormulas.graph_l g) (N : Nat) :
    Formula.satisfies (PureSecondOrder.environment_l N) (.forallE .set (matrix_m F G)) ↔
      sentence_general f g N := by
  simp only [matrix_m, sentence_general, m_graph, m_allBounds, m_stop,
    Formula.satisfies, member_sound, bound_sound, ternary_sound,
    PureSecondOrder.environment_l, succ, Term.eval, Arguments.eval,
    Env.pushBound, Assignment.push]
  rfl

/-- 与 `FixedHeightSecondOrder.sentence_l` 的衔接：`f := h`、`g := edge` 时，
    参数化句经 `edge_ne_one` 与原句**等价**（高度部分由 `h` 的定义化简，
    检查器部分把 `edge _ = 1` 等价换成 `check_l _ = true`）。 -/
theorem sentence_general_h (N : Nat) :
    sentence_general h edge N ↔ FixedHeightSecondOrder.sentence_l N := by
  simp only [sentence_general, FixedHeightSecondOrder.sentence_l, h,
    HeightDescent.height_l, edge_ne_one]

/-- 高度图 + 检查器专用形态：直接给出旧出口的语义。 -/
theorem matrix_sound_h (F : PrimitiveFormulas.graph_l h) (G : PrimitiveFormulas.graph_l edge)
    (N : Nat) :
    Formula.satisfies (PureSecondOrder.environment_l N) (.forallE .set (matrix_m F G)) ↔
      FixedHeightSecondOrder.sentence_l N :=
  (matrix_sound F G N).trans (sentence_general_h N)

/-! ## 程序见证出口（任务7-A 的核心） -/

/-- 高度程序与检查器程序的存在性，连同 `eval_l` 等式。 -/
theorem programs_exist :
    (∃ cH : PrimitiveProgram.code_m, PrimitiveProgram.eval_l cH = h) ∧
    (∃ cE : PrimitiveProgram.code_m, PrimitiveProgram.eval_l cE = edge) :=
  ⟨h_complete, edge_complete⟩

/-- **公开的程序参数化矩阵**：AST 直接由 `PrimitiveProgram.graph_m cH` /
    `graph_m cE` 生成，编译来源在类型中可见，无需回查私有名。

    纯性对**任意** `cH` / `cE` 成立（不依赖具体程序）。 -/
def compiled_matrix_m (cH cE : PrimitiveProgram.code_m) : Formula signature_m [.set] [.num] :=
  matrix_m (PrimitiveProgram.graph_m cH) (PrimitiveProgram.graph_m cE)

theorem compiled_matrix_pure (cH cE : PrimitiveProgram.code_m) :
    pure_m (compiled_matrix_m cH cE) = true :=
  matrix_pure (PrimitiveProgram.graph_m cH) (PrimitiveProgram.graph_m cE)

/-- 程序见证确实把 `compiled_matrix_m` 与我们想要的矩阵连起来：
    取到 `eval_l cH = h`、`eval_l cE = edge` 的见证后，编译矩阵的 `∀N` 标准语义
    就是 `FixedHeightSecondOrder.sentence_l N`。

    证明把 `matrix_sound` 的结论 `sentence_general (eval_l cH) (eval_l cE) N`
    的**两个参数**用 `eval_l` 等式重写成 `sentence_general h edge N`
    （这一步在**结果命题**上做，不需要对 `graph_m` 的排序索引重写），
    再经 `sentence_general_h` 换成高度/检查器专用形态。
    `eval_l` 等式用于**指明** `cH` / `cE` 是高度图与检查器的程序。 -/
theorem compiled_matrix_sound {cH cE : PrimitiveProgram.code_m}
    (hH : PrimitiveProgram.eval_l cH = h) (hE : PrimitiveProgram.eval_l cE = edge) (N : Nat) :
    Formula.satisfies (PureSecondOrder.environment_l N) (.forallE .set (compiled_matrix_m cH cE)) ↔
      FixedHeightSecondOrder.sentence_l N := by
  have h₁ := matrix_sound (PrimitiveProgram.graph_m cH) (PrimitiveProgram.graph_m cE) N
  rw [compiled_matrix_m]
  refine h₁.trans ?_
  rw [hH, hE]
  exact sentence_general_h N

/-- 有见证程序的存在性出口：存在一对程序，其编译矩阵的 `∀N` 标准语义
    恰是 `FixedHeightSecondOrder.sentence_l N`。 -/
theorem compiled_matrix_exists :
    ∃ cH cE : PrimitiveProgram.code_m,
      PrimitiveProgram.eval_l cH = h ∧ PrimitiveProgram.eval_l cE = edge ∧
      ∀ N, Formula.satisfies (PureSecondOrder.environment_l N)
        (.forallE .set (compiled_matrix_m cH cE)) ↔
        FixedHeightSecondOrder.sentence_l N := by
  obtain ⟨cH, hH⟩ := h_complete
  obtain ⟨cE, hE⟩ := edge_complete
  exact ⟨cH, cE, hH, hE, fun N => compiled_matrix_sound hH hE N⟩

/-! ## 推论出口（保留旧名，语义不变） -/

/-- 当前高度有界的纯二阶目标在 `signature_m` 中具有真实纯算术矩阵：
    自由参数是高度上界 `N`，最外层是一个全称集合量词，
    矩阵只含零、后继、加乘、数等式、成员与数量词。

    任务9-A1 之后，本定理从 `compiled_matrix_exists` 取**固定**的程序见证
    `cH`、`cE`，并以 `compiled_matrix_m cH cE` 作为同一见证矩阵；
    不再另取匿名图 `PrimitiveFormulas.primrec_l`。
    需要编译来源时用 `compiled_matrix_m` / `compiled_matrix_pure`
    / `compiled_matrix_exists` / `compiled_closed_l`。 -/
theorem formula_l : ∃ φ : Formula signature_m [.set] [.num], pure_m φ = true ∧
    ∀ N, Formula.satisfies (PureSecondOrder.environment_l N) (.forallE .set φ) ↔
      FixedHeightSecondOrder.sentence_l N := by
  obtain ⟨cH, cE, _, _, hspec⟩ := compiled_matrix_exists
  exact ⟨compiled_matrix_m cH cE, compiled_matrix_pure cH cE, hspec⟩

/-- 同一矩阵按数码替换后得到的闭句，仍保有当前高度有界的标准语义。

    直接实例化 `PureSecondOrder` 的公共闭句接口，不重做替换，
    也不使用旧 `formula_l` / `closed_formula_l`（那两个的终点是旧种子目标）。
    `φ` 就是 `formula_l` 给出的那一个矩阵，**不为每个 `N` 另选等价公式**。 -/
theorem closed_l : ∃ φ : Formula signature_m [.set] [.num], pure_m φ = true ∧
    ∀ N,
      (∃ ψ : Formula signature_m [.set] [],
        PureSecondOrder.closed_m φ N = .forallE .set ψ ∧ pure_m ψ = true) ∧
      (Formula.satisfies (Env.empty (M := structure_l)) (PureSecondOrder.closed_m φ N) ↔
        FixedHeightSecondOrder.sentence_l N) := by
  obtain ⟨cH, cE, _, _, hspec⟩ := compiled_matrix_exists
  exact ⟨compiled_matrix_m cH cE, compiled_matrix_pure cH cE, fun N =>
    ⟨PureSecondOrder.closed_pure_m _ (compiled_matrix_pure cH cE) N,
      (PureSecondOrder.closed_l _ N).trans (hspec N)⟩⟩

/-- **任务9-A1 的公开见证接口**：编译来源完整保留到闭句层。

    存在**固定**的程序 `cH`、`cE`（高度图与检查器），连同 `eval_l` 等式，
    使同一 `compiled_matrix_m cH cE` 满足：其数码闭句对**所有**外部 `N`
    既保有纯性，又具有原当前高度有界句 `FixedHeightSecondOrder.sentence_l N`
    的标准语义。**不为每个 `N` 另选程序或公式。**

    与 `formula_l` / `closed_l` 的关系：后两者是**存在式**出口（只给"存在某个 φ"），
    本定理把那个 φ 的具体程序来源与 `eval_l` 等式一并公开。 -/
theorem compiled_closed_l :
    ∃ cH cE : PrimitiveProgram.code_m,
      PrimitiveProgram.eval_l cH = h ∧ PrimitiveProgram.eval_l cE = edge ∧
      pure_m (compiled_matrix_m cH cE) = true ∧
      ∀ N,
        (∃ ψ : Formula signature_m [.set] [],
          PureSecondOrder.closed_m (compiled_matrix_m cH cE) N = .forallE .set ψ ∧
            pure_m ψ = true) ∧
        (Formula.satisfies (Env.empty (M := structure_l))
            (PureSecondOrder.closed_m (compiled_matrix_m cH cE) N) ↔
          FixedHeightSecondOrder.sentence_l N) := by
  obtain ⟨cH, cE, hH, hE, hspec⟩ := compiled_matrix_exists
  refine ⟨cH, cE, hH, hE, compiled_matrix_pure cH cE, fun N => ?_⟩
  exact ⟨PureSecondOrder.closed_pure_m _ (compiled_matrix_pure cH cE) N,
    (PureSecondOrder.closed_l _ N).trans (hspec N)⟩

end YesMetaZFC.BMS.ConstructibleBridge.FixedHeightPureFormula
