import BMSConstructibleBridge.SecondOrderSyntax

/-!
# 原始递归函数的纯算术图编译

各编译构造实际返回现有语法核中的公式，同时验证纯语言检查和全环境语义。
不得把 `Primrec` 证书直接当作一个新的算术关系符号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PrimitiveFormulas

open Logic FirstOrder SecondOrderSyntax

set_option autoImplicit false

private abbrev term (Γ Δ : SortContext signature_m) := Term signature_m Γ Δ .num

private def zero {Γ Δ : SortContext signature_m} : term Γ Δ :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : term Γ Δ) : term Γ Δ :=
  Term.app (σ := signature_m) .succ (.cons s .nil)

private def add {Γ Δ : SortContext signature_m} (s t : term Γ Δ) : term Γ Δ :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

private def mul {Γ Δ : SortContext signature_m} (s t : term Γ Δ) : term Γ Δ :=
  Term.app (σ := signature_m) .mul (.cons s (.cons t .nil))

private abbrev shift {Γ Δ : SortContext signature_m} (s : term Γ Δ) : term (.num :: Γ) Δ :=
  s.weakenBound sort_m.num

private abbrev twice {Γ Δ : SortContext signature_m} (s : term Γ Δ) :
    term (.num :: .num :: Γ) Δ := shift (shift s)

private def v₀ {Γ Δ : SortContext signature_m} : term (.num :: Γ) Δ := .bvar .here

private def v₁ {Γ Δ : SortContext signature_m} : term (.num :: .num :: Γ) Δ :=
  .bvar (.there .here)

mutual
  /-- 纯项穿过一个数变量绑定后保持纯语言检查结果。 -/
  theorem weaken_l {Γ Δ : SortContext signature_m} {s : sort_m}
      (t : Term signature_m Γ Δ s) :
      pure_term_m (t.weakenBound sort_m.num) = pure_term_m t :=
    match t with
    | .bvar _ => rfl
    | .fvar _ => rfl
    | .app f s => by
        change (if f = func_m.pair then false else pure_args_m (s.weakenBound sort_m.num)) =
          (if f = func_m.pair then false else pure_args_m s)
        rw [pure_args_weaken s]

  private theorem pure_args_weaken {Γ Δ : SortContext signature_m} {s : List sort_m}
      (t : Arguments signature_m Γ Δ s) :
      pure_args_m (t.weakenBound sort_m.num) = pure_args_m t :=
    match t with
    | .nil => rfl
    | .cons t s => by
        change (pure_term_m (t.weakenBound sort_m.num) &&
          pure_args_m (s.weakenBound sort_m.num)) = (pure_term_m t && pure_args_m s)
        rw [weaken_l t, pure_args_weaken s]
end

private theorem lt_iff (a b : Nat) : (∃ d, a + (d + 1) = b) ↔ a < b := by
  constructor
  · rintro ⟨d, h⟩; omega
  · intro h; exact ⟨b - a - 1, by omega⟩

/-- 小于关系的纯加乘公式；差值见证也只量化自然数。 -/
def lt_m {Γ Δ : SortContext signature_m} (s t : term Γ Δ) :
    Formula signature_m Γ Δ :=
  .existsE .num (.equal (add (s.weakenBound sort_m.num) (succ (.bvar .here)))
    (t.weakenBound sort_m.num))

/-- 小于模板不引入额外函数或关系。 -/
theorem lt_pure_l {Γ Δ : SortContext signature_m} (s t : term Γ Δ)
    (hs : pure_term_m s = true) (ht : pure_term_m t = true) : pure_m (lt_m s t) = true := by
  simp [lt_m, pure_m, pure_term_m, pure_args_m, add, succ, weaken_l, hs, ht]

/-- 小于模板在所有标准数值环境中正确。 -/
theorem lt_l {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ) (s t : term Γ Δ) :
    Formula.satisfies η (lt_m s t) ↔ Term.eval η s < Term.eval η t := by
  change (∃ d : Nat, (s.weakenBound sort_m.num).eval (η.pushBound d) + (d + 1) =
    (t.weakenBound sort_m.num).eval (η.pushBound d)) ↔ _
  simp only [Term.eval_weakenBound]
  change (∃ d : Nat, (s.eval η : Nat) + (d + 1) = (t.eval η : Nat)) ↔
    (s.eval η : Nat) < (t.eval η : Nat)
  exact lt_iff (s.eval η) (t.eval η)

/-- 与实际 `Nat.pair` 两分支一致的纯算术图。 -/
def pair_m {Γ Δ : SortContext signature_m} (s t u : term Γ Δ) :
    Formula signature_m Γ Δ :=
  .disj (.conj (lt_m s t) (.equal (add (mul t t) s) u))
    (.conj (.neg (lt_m s t)) (.equal (add (add (mul s s) s) t) u))

/-- 配对图消去配对函数符号。 -/
theorem pair_pure_l {Γ Δ : SortContext signature_m} (s t u : term Γ Δ)
    (hs : pure_term_m s = true) (ht : pure_term_m t = true) (hu : pure_term_m u = true) :
    pure_m (pair_m s t u) = true := by
  simp [pair_m, pure_m, lt_pure_l s t hs ht, pure_term_m, pure_args_m, add, mul, hs, ht, hu]

/-- 配对图的语义连接库中实际配对函数，而非另选一个编码。 -/
theorem pair_l {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ)
    (s t u : term Γ Δ) : Formula.satisfies η (pair_m s t u) ↔
    Nat.pair (Term.eval η s) (Term.eval η t) = Term.eval η u := by
  simp only [pair_m, Formula.satisfies, lt_l]
  change ((s.eval η < t.eval η ∧ t.eval η * t.eval η + s.eval η = u.eval η) ∨
    (¬s.eval η < t.eval η ∧ s.eval η * s.eval η + s.eval η + t.eval η = u.eval η)) ↔ _
  by_cases h : s.eval η < t.eval η <;> simp [Nat.pair, h]

/-- 图编译器保存真实公式、纯语言证据以及全部环境中的语义规格。 -/
structure graph_l (f : Nat → Nat) where
  form : {Γ Δ : SortContext signature_m} → term Γ Δ → term Γ Δ → Formula signature_m Γ Δ
  pure : ∀ {Γ Δ} (s t : term Γ Δ), pure_term_m s = true → pure_term_m t = true →
    pure_m (form s t) = true
  sound : ∀ {Γ Δ} (η : Env structure_l Γ Δ) (s t : term Γ Δ),
    Formula.satisfies η (form s t) ↔ f (Term.eval η s) = Term.eval η t

/-- 零函数的纯算术图。 -/
def zero_l : graph_l (fun _ => 0) where
  form _ t := .equal zero t
  pure _ t _ ht := by simp [pure_m, zero, pure_term_m, pure_args_m, ht]
  sound _ _ _ := Iff.rfl

/-- 后继函数的纯算术图。 -/
def succ_l : graph_l Nat.succ where
  form s t := .equal (succ s) t
  pure s t hs ht := by simp [pure_m, succ, pure_term_m, pure_args_m, hs, ht]
  sound _ _ _ := Iff.rfl

namespace graph_l

/-- 复合通过一个数量词连接两张图，不新增复合函数符号。 -/
def comp_l {f g : Nat → Nat} (F : graph_l f) (G : graph_l g) : graph_l (fun n => f (g n)) where
  form s t := .existsE .num (.conj
    (G.form (s.weakenBound sort_m.num) (.bvar .here))
    (F.form (.bvar .here) (t.weakenBound sort_m.num)))
  pure s t hs ht := by
    simp only [pure_m, Bool.and_eq_true]
    exact ⟨G.pure _ _ (by simpa only [weaken_l] using hs) rfl,
      F.pure _ _ rfl (by simpa only [weaken_l] using ht)⟩
  sound η s t := by
    simp only [Formula.satisfies, G.sound, F.sound, Term.eval_weakenBound, Term.eval]
    dsimp only [Env.pushBound, Assignment.push]
    simp

end graph_l

/-- 配对第一投影通过配对图存在量化另一坐标。 -/
def left_l : graph_l (fun n => n.unpair.1) where
  form s t := .existsE .num (pair_m (t.weakenBound sort_m.num) (.bvar .here)
    (s.weakenBound sort_m.num))
  pure s t hs ht := by
    change pure_m (pair_m (t.weakenBound sort_m.num) (.bvar .here)
      (s.weakenBound sort_m.num)) = true
    exact pair_pure_l _ _ _ (by simpa only [weaken_l] using ht) rfl
      (by simpa only [weaken_l] using hs)
  sound η s t := by
    simp only [Formula.satisfies, pair_l, Term.eval_weakenBound, Term.eval]
    change (∃ u : Nat, Nat.pair (t.eval η) u = s.eval η) ↔ _
    constructor
    · rintro ⟨u, h⟩
      rw [← h, Nat.unpair_pair]
    · intro h
      exact ⟨(s.eval η).unpair.2, by rw [← h, Nat.pair_unpair]⟩

/-- 配对第二投影不调用算术语言以外的开方函数。 -/
def right_l : graph_l (fun n => n.unpair.2) where
  form s t := .existsE .num (pair_m (.bvar .here) (t.weakenBound sort_m.num)
    (s.weakenBound sort_m.num))
  pure s t hs ht := by
    change pure_m (pair_m (.bvar .here) (t.weakenBound sort_m.num)
      (s.weakenBound sort_m.num)) = true
    exact pair_pure_l _ _ _ rfl (by simpa only [weaken_l] using ht)
      (by simpa only [weaken_l] using hs)
  sound η s t := by
    simp only [Formula.satisfies, pair_l, Term.eval_weakenBound, Term.eval]
    change (∃ u : Nat, Nat.pair u (t.eval η) = s.eval η) ↔ _
    constructor
    · rintro ⟨u, h⟩
      rw [← h, Nat.unpair_pair]
    · intro h
      exact ⟨(s.eval η).unpair.1, by rw [← h, Nat.pair_unpair]⟩

/-- β 读取图在任意上下文、任意纯数项上的实例化。 -/
def beta_m {Γ Δ : SortContext signature_m} (b c i v : term Γ Δ) :
    Formula signature_m Γ Δ :=
  let m := succ (mul (succ (twice i)) (twice c))
  .existsE .num (.existsE .num (.conj
    (.equal (twice b) (add (mul v₁ m) (twice v)))
    (.equal (add (twice v) (succ v₀)) m)))

/-- β 图中的每个量词仍是数量词，且没有未消去的计算符号。 -/
theorem beta_pure_l {Γ Δ : SortContext signature_m} (b c i v : term Γ Δ)
    (hb : pure_term_m b = true) (hc : pure_term_m c = true)
    (hi : pure_term_m i = true) (hv : pure_term_m v = true) :
    pure_m (beta_m b c i v) = true := by
  simp [beta_m, pure_m, pure_term_m, pure_args_m, add, mul, succ, v₀, v₁,
    twice, shift, weaken_l, hb, hc, hi, hv]

/-- 通用 β 模板的语义恰好连接有限历史的纯算术读取规格。 -/
theorem beta_l {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ)
    (b c i v : term Γ Δ) : Formula.satisfies η (beta_m b c i v) ↔
    PrimitiveHistory.beta_l (b.eval η) (c.eval η) (i.eval η) (v.eval η) := by
  simp only [beta_m, Formula.satisfies, add, mul, succ, v₀, v₁, twice, shift,
    Term.eval, Arguments.eval, Term.eval_weakenBound]
  change (∃ q d : Nat, b.eval η = q * ((i.eval η + 1) * c.eval η + 1) + v.eval η ∧
    v.eval η + (d + 1) = (i.eval η + 1) * c.eval η + 1) ↔ _
  rfl

namespace graph_l

/-- 两张图的配对构造，两个中间结果均由数量词绑定。 -/
def pair_l {f g : Nat → Nat} (F : graph_l f) (G : graph_l g) :
    graph_l (fun n => Nat.pair (f n) (g n)) where
  form s t := .existsE .num (.existsE .num (.conj (F.form (twice s) v₁)
    (.conj (G.form (twice s) v₀) (PrimitiveFormulas.pair_m v₁ v₀ (twice t)))))
  pure s t hs ht := by
    simp only [pure_m, Bool.and_eq_true]
    exact ⟨F.pure _ _ (by simpa only [twice, shift, weaken_l] using hs) rfl,
      G.pure _ _ (by simpa only [twice, shift, weaken_l] using hs) rfl,
      pair_pure_l _ _ _ rfl rfl (by simpa only [twice, shift, weaken_l] using ht)⟩
  sound η s t := by
    simp only [Formula.satisfies, F.sound, G.sound, PrimitiveFormulas.pair_l,
      twice, shift, Term.eval_weakenBound, v₀, v₁, Term.eval]
    change (∃ u v : Nat, f (s.eval η) = u ∧ g (s.eval η) = v ∧
      Nat.pair u v = t.eval η) ↔ _
    simp

end graph_l

private def iteration {g : Nat → Nat} (G : graph_l g) {Γ Δ : SortContext signature_m}
    (x i u v : term Γ Δ) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj (pair_m (twice i) (twice u) v₁)
    (.conj (pair_m (twice x) v₁ v₀) (G.form v₀ (twice v)))))

private theorem iteration_pure {g : Nat → Nat} (G : graph_l g)
    {Γ Δ : SortContext signature_m} (x i u v : term Γ Δ)
    (hx : pure_term_m x = true) (hi : pure_term_m i = true)
    (hu : pure_term_m u = true) (hv : pure_term_m v = true) :
    pure_m (iteration G x i u v) = true := by
  simp only [iteration, pure_m, Bool.and_eq_true]
  exact ⟨pair_pure_l _ _ _ (by simpa only [twice, shift, weaken_l] using hi)
      (by simpa only [twice, shift, weaken_l] using hu) rfl,
    pair_pure_l _ _ _ (by simpa only [twice, shift, weaken_l] using hx) rfl rfl,
    G.pure _ _ rfl (by simpa only [twice, shift, weaken_l] using hv)⟩

private theorem iteration_sound {g : Nat → Nat} (G : graph_l g)
    {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ) (x i u v : term Γ Δ) :
    Formula.satisfies η (iteration G x i u v) ↔
    g (Nat.pair (x.eval η) (Nat.pair (i.eval η) (u.eval η))) = v.eval η := by
  simp only [iteration, Formula.satisfies, pair_l, G.sound, twice, shift,
    Term.eval_weakenBound, v₀, v₁, Term.eval]
  change (∃ p q : Nat, Nat.pair (i.eval η) (u.eval η) = p ∧
    Nat.pair (x.eval η) p = q ∧ g q = v.eval η) ↔ _
  simp

private def transition {g : Nat → Nat} (G : graph_l g) {Γ Δ : SortContext signature_m}
    (b c x i : term Γ Δ) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj (beta_m (twice b) (twice c) (twice i) v₁)
    (.conj (beta_m (twice b) (twice c) (succ (twice i)) v₀)
      (iteration G (twice x) (twice i) v₁ v₀))))

private theorem transition_pure {g : Nat → Nat} (G : graph_l g)
    {Γ Δ : SortContext signature_m} (b c x i : term Γ Δ)
    (hb : pure_term_m b = true) (hc : pure_term_m c = true)
    (hx : pure_term_m x = true) (hi : pure_term_m i = true) :
    pure_m (transition G b c x i) = true := by
  have hb : pure_term_m (twice b) = true := by simpa only [twice, shift, weaken_l] using hb
  have hc : pure_term_m (twice c) = true := by simpa only [twice, shift, weaken_l] using hc
  have hx : pure_term_m (twice x) = true := by simpa only [twice, shift, weaken_l] using hx
  have hi : pure_term_m (twice i) = true := by simpa only [twice, shift, weaken_l] using hi
  simp only [transition, pure_m, Bool.and_eq_true]
  exact ⟨beta_pure_l _ _ _ _ hb hc hi rfl,
    beta_pure_l _ _ _ _ hb hc (by simp [succ, pure_term_m, pure_args_m, hi]) rfl,
    iteration_pure G _ _ _ _ hx hi rfl rfl⟩

private theorem transition_sound {g : Nat → Nat} (G : graph_l g)
    {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ) (b c x i : term Γ Δ) :
    Formula.satisfies η (transition G b c x i) ↔
    ∃ u v, PrimitiveHistory.beta_l (b.eval η) (c.eval η) (i.eval η) u ∧
      PrimitiveHistory.beta_l (b.eval η) (c.eval η) (i.eval η + 1) v ∧
      g (Nat.pair (x.eval η) (Nat.pair (i.eval η) u)) = v := by
  simp only [transition, Formula.satisfies, beta_l, iteration_sound, twice, shift,
    Term.eval_weakenBound, succ, v₀, v₁, Term.eval, Arguments.eval]
  rfl

private def initial {f : Nat → Nat} (F : graph_l f) {Γ Δ : SortContext signature_m}
    (b c x : term Γ Δ) : Formula signature_m Γ Δ :=
  .existsE .num (.conj (F.form (shift x) v₀) (beta_m (shift b) (shift c) zero v₀))

private theorem initial_pure {f : Nat → Nat} (F : graph_l f)
    {Γ Δ : SortContext signature_m} (b c x : term Γ Δ)
    (hb : pure_term_m b = true) (hc : pure_term_m c = true) (hx : pure_term_m x = true) :
    pure_m (initial F b c x) = true := by
  simp only [initial, pure_m, Bool.and_eq_true]
  exact ⟨F.pure _ _ (by simpa only [shift, weaken_l] using hx) rfl,
    beta_pure_l _ _ _ _ (by simpa only [shift, weaken_l] using hb)
      (by simpa only [shift, weaken_l] using hc) rfl rfl⟩

private theorem initial_sound {f : Nat → Nat} (F : graph_l f)
    {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ) (b c x : term Γ Δ) :
    Formula.satisfies η (initial F b c x) ↔
    PrimitiveHistory.beta_l (b.eval η) (c.eval η) 0 (f (x.eval η)) := by
  simp only [initial, Formula.satisfies, F.sound, beta_l, shift,
    Term.eval_weakenBound, zero, v₀, Term.eval, Arguments.eval]
  change (∃ a : Nat, f (x.eval η) = a ∧
    PrimitiveHistory.beta_l (b.eval η) (c.eval η) 0 a) ↔ _
  simp

private def steps {g : Nat → Nat} (G : graph_l g) {Γ Δ : SortContext signature_m}
    (b c x n : term Γ Δ) : Formula signature_m Γ Δ :=
  .forallE .num (.imp (lt_m v₀ (shift n)) (transition G (shift b) (shift c) (shift x) v₀))

private theorem steps_pure {g : Nat → Nat} (G : graph_l g)
    {Γ Δ : SortContext signature_m} (b c x n : term Γ Δ)
    (hb : pure_term_m b = true) (hc : pure_term_m c = true)
    (hx : pure_term_m x = true) (hn : pure_term_m n = true) :
    pure_m (steps G b c x n) = true := by
  simp only [steps, pure_m, Bool.and_eq_true]
  exact ⟨lt_pure_l _ _ rfl (by simpa only [shift, weaken_l] using hn),
    transition_pure G _ _ _ _ (by simpa only [shift, weaken_l] using hb)
      (by simpa only [shift, weaken_l] using hc)
      (by simpa only [shift, weaken_l] using hx) rfl⟩

private theorem steps_sound {g : Nat → Nat} (G : graph_l g)
    {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ) (b c x n : term Γ Δ) :
    Formula.satisfies η (steps G b c x n) ↔
    ∀ i < n.eval η, ∃ u v, PrimitiveHistory.beta_l (b.eval η) (c.eval η) i u ∧
      PrimitiveHistory.beta_l (b.eval η) (c.eval η) (i + 1) v ∧
      g (Nat.pair (x.eval η) (Nat.pair i u)) = v := by
  simp only [steps, Formula.satisfies, lt_l, transition_sound, shift,
    Term.eval_weakenBound, v₀, Term.eval]
  rfl

private def recursion {f g : Nat → Nat} (F : graph_l f) (G : graph_l g)
    {Γ Δ : SortContext signature_m} (x n y : term Γ Δ) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj (initial F v₁ v₀ (twice x))
    (.conj (beta_m v₁ v₀ (twice n) (twice y)) (steps G v₁ v₀ (twice x) (twice n)))))

private theorem recursion_pure {f g : Nat → Nat} (F : graph_l f) (G : graph_l g)
    {Γ Δ : SortContext signature_m} (x n y : term Γ Δ)
    (hx : pure_term_m x = true) (hn : pure_term_m n = true) (hy : pure_term_m y = true) :
    pure_m (recursion F G x n y) = true := by
  have hx : pure_term_m (twice x) = true := by simpa only [twice, shift, weaken_l] using hx
  have hn : pure_term_m (twice n) = true := by simpa only [twice, shift, weaken_l] using hn
  have hy : pure_term_m (twice y) = true := by simpa only [twice, shift, weaken_l] using hy
  simp only [recursion, pure_m, Bool.and_eq_true]
  exact ⟨initial_pure F _ _ _ rfl rfl hx, beta_pure_l _ _ _ _ rfl rfl hn hy,
    steps_pure G _ _ _ _ rfl rfl hx hn⟩

private theorem recursion_sound {f g : Nat → Nat} (F : graph_l f) (G : graph_l g)
    {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ) (x n y : term Γ Δ) :
    Formula.satisfies η (recursion F G x n y) ↔
    PrimitiveHistory.run_l f g (x.eval η) (n.eval η) = y.eval η := by
  simp only [recursion, Formula.satisfies, initial_sound, beta_l, steps_sound,
    twice, shift, Term.eval_weakenBound, v₀, v₁, Term.eval]
  change PrimitiveHistory.history_l f g (x.eval η) (n.eval η) (y.eval η) ↔ _
  exact PrimitiveHistory.history_iff_l f g _ _ _

namespace graph_l

/-- 原始递归通过有限 β 历史编译；无限语义递归不进入目标公式。 -/
def prec_l {f g : Nat → Nat} (F : graph_l f) (G : graph_l g) :
    graph_l (Nat.unpaired (PrimitiveHistory.run_l f g)) where
  form s t := .existsE .num (.existsE .num (.conj (pair_m v₁ v₀ (twice s))
    (recursion F G v₁ v₀ (twice t))))
  pure s t hs ht := by
    simp only [pure_m, Bool.and_eq_true]
    exact ⟨pair_pure_l _ _ _ rfl rfl (by simpa only [twice, shift, weaken_l] using hs),
      recursion_pure F G _ _ _ rfl rfl (by simpa only [twice, shift, weaken_l] using ht)⟩
  sound η s t := by
    simp only [Formula.satisfies, PrimitiveFormulas.pair_l, recursion_sound,
      twice, shift, Term.eval_weakenBound, v₀, v₁, Term.eval]
    change (∃ x n : Nat, Nat.pair x n = s.eval η ∧
      PrimitiveHistory.run_l f g x n = t.eval η) ↔ _
    constructor
    · rintro ⟨x, n, h, h₀⟩
      simpa only [Nat.unpaired, ← h, Nat.unpair_pair] using h₀
    · intro h
      exact ⟨(s.eval η).unpair.1, (s.eval η).unpair.2, Nat.pair_unpair _, h⟩

end graph_l

/-- 每个库中原始递归函数都有经过纯语言检查且逐环境正确的实际公式图。 -/
theorem primrec_l {f : Nat → Nat} (h : Nat.Primrec f) : Nonempty (graph_l f) := by
  induction h with
  | zero => exact ⟨zero_l⟩
  | succ => exact ⟨succ_l⟩
  | left => exact ⟨left_l⟩
  | right => exact ⟨right_l⟩
  | pair _ _ hᵢ hⱼ =>
      obtain ⟨F⟩ := hᵢ
      obtain ⟨G⟩ := hⱼ
      exact ⟨F.pair_l G⟩
  | comp _ _ hᵢ hⱼ =>
      obtain ⟨F⟩ := hᵢ
      obtain ⟨G⟩ := hⱼ
      exact ⟨F.comp_l G⟩
  | prec _ _ hᵢ hⱼ =>
      obtain ⟨F⟩ := hᵢ
      obtain ⟨G⟩ := hⱼ
      exact ⟨F.prec_l G⟩

end YesMetaZFC.BMS.ConstructibleBridge.PrimitiveFormulas
