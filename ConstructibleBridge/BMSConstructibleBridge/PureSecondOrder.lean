import BMSConstructibleBridge.PrimitiveFormulas

/-!
# 原 BM4 目标的纯二阶算术公式

实际消去配对、起点和一步算法符号。输出公式只有零、后继、加乘、数等式、
集合成员关系和数量词，外加最外层的一个全称集合量词。图编译器由已经核验的
原算法原始递归证书产生；没有假定 BM4 良基性、模型可靠性或对象理论可证性。

本文件证明公式存在及标准语义正确性，不生成 `Z₂` 的良序推导代码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PureSecondOrder

open Logic FirstOrder SecondOrderSyntax

set_option autoImplicit false

private def beg (n : Nat) : Nat :=
  cond (decide ((ArithmeticPresentation.decode_l n.unpair.2).1.raw = seed n.unpair.1)) 1 0

private def edge (n : Nat) : Nat :=
  cond (ArithmeticPresentation.check_l n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2) 1 0

private theorem beg_prim : Nat.Primrec beg := by
  have h₀ : Primrec (fun n : Nat => n.unpair.1) := Primrec.nat_iff.mpr .left
  have h₁ : Primrec (fun n : Nat => n.unpair.2) := Primrec.nat_iff.mpr .right
  exact Primrec.nat_iff.mp ((Primrec.dom_bool (fun b => cond b 1 0)).comp
    ((Primrec.eq.comp (PrimitiveCoding.decode_l.comp h₁)
      (PrimitiveCoding.seed_l.comp h₀)).decide))

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

private theorem beg_pair (n a : Nat) : beg (Nat.pair n a) = 1 ↔
    (ArithmeticPresentation.decode_l a).1.raw = seed n := by
  by_cases h : (ArithmeticPresentation.decode_l a).1.raw = seed n <;> simp [beg, h]

private theorem edge_pair (b a k : Nat) : edge (Nat.pair b (Nat.pair a k)) = 1 ↔
    ArithmeticPresentation.check_l b a k = true := by
  cases h : ArithmeticPresentation.check_l b a k <;> simp [edge, h]

private abbrev term (Γ Δ : SortContext signature_m) := Term signature_m Γ Δ .num

private def zero {Γ Δ : SortContext signature_m} : term Γ Δ :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : term Γ Δ) : term Γ Δ :=
  Term.app (σ := signature_m) .succ (.cons s .nil)

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

private def binary {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (s t : term Γ Δ) : Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (s.weakenBound sort_m.num) (t.weakenBound sort_m.num) (.bvar .here))
    (F.form (.bvar .here) (succ zero)))

private theorem binary_pure {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (s t : term Γ Δ)
    (hs : pure_term_m s = true) (ht : pure_term_m t = true) : pure_m (binary F s t) = true := by
  simp only [binary, pure_m, Bool.and_eq_true]
  exact ⟨PrimitiveFormulas.pair_pure_l _ _ _
      (by simpa only [PrimitiveFormulas.weaken_l] using hs)
      (by simpa only [PrimitiveFormulas.weaken_l] using ht) rfl,
    F.pure _ _ rfl rfl⟩

private theorem binary_sound {f : Nat → Nat} (F : PrimitiveFormulas.graph_l f)
    {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ) (s t : term Γ Δ) :
    Formula.satisfies η (binary F s t) ↔ f (Nat.pair (s.eval η) (t.eval η)) = 1 := by
  simp only [binary, Formula.satisfies, PrimitiveFormulas.pair_l, F.sound,
    Term.eval_weakenBound, succ, zero, Term.eval, Arguments.eval]
  change (∃ p : Nat, Nat.pair (s.eval η) (t.eval η) = p ∧ f p = 1) ↔ _
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

private def graph : Formula signature_m [.set] [.num] :=
  .forallE .num (.existsE .num (.conj
    (member (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))
    (.forallE .num (.imp
      (member (.bvar (.there (.there .here))) (.bvar .here)
        (.bvar (.there (.there (.there .here)))))
      (.equal (.bvar .here) (.bvar (.there .here)))))))

private def start (F : PrimitiveFormulas.graph_l beg) : Formula signature_m [.set] [.num] :=
  .existsE .num (.conj (member zero (.bvar .here) (.bvar (.there .here)))
    (binary F (.fvar .here) (.bvar .here)))

private def stop (G : PrimitiveFormulas.graph_l edge) : Formula signature_m [.set] [.num] :=
  .existsE .num (.existsE .num (.existsE .num (.conj
    (member (.bvar (.there (.there .here))) (.bvar (.there .here))
      (.bvar (.there (.there (.there .here)))))
    (.conj (member (succ (.bvar (.there (.there .here)))) (.bvar .here)
      (.bvar (.there (.there (.there .here)))))
      (.forallE .num (.neg (ternary G (.bvar (.there .here))
        (.bvar (.there (.there .here))) (.bvar .here))))))))

private def body (F : PrimitiveFormulas.graph_l beg) (G : PrimitiveFormulas.graph_l edge) :
    Formula signature_m [.set] [.num] := .imp graph (.imp (start F) (stop G))

private theorem body_pure (F : PrimitiveFormulas.graph_l beg) (G : PrimitiveFormulas.graph_l edge) :
    pure_m (body F G) = true := by
  simp only [body, start, stop, pure_m, Bool.and_eq_true]
  exact ⟨rfl, ⟨rfl, binary_pure F _ _ rfl rfl⟩,
    rfl, rfl, ternary_pure G _ _ _ rfl rfl rfl⟩

/-- 纯目标的高度参数环境。 -/
def environment_l (n : Nat) : Env structure_l [] [.num] where
  boundVal := Assignment.empty
  freeVal := Assignment.push (M := structure_l) (sort := .num) n Assignment.empty

private theorem body_sound (F : PrimitiveFormulas.graph_l beg) (G : PrimitiveFormulas.graph_l edge)
    (n : Nat) : Formula.satisfies (environment_l n) (.forallE .set (body F G)) ↔
    SeedReflection.sentence_l n := by
  simp only [body, graph, start, stop, Formula.satisfies, member_sound, binary_sound,
    ternary_sound, beg_pair, edge_pair, zero, succ, Term.eval, Arguments.eval]
  rfl

/-- 原 BM4 逐高度目标在纯二阶算术语言中具有精确的 Π¹₁ 公式。
    没有未消去的配对、seed 或展开函数符号，也没有额外的良基性前提。 -/
theorem formula_l : ∃ φ : Formula signature_m [.set] [.num], pure_m φ = true ∧
    ∀ n, Formula.satisfies (environment_l n) (.forallE .set φ) ↔ SeedReflection.sentence_l n := by
  obtain ⟨F⟩ := PrimitiveFormulas.primrec_l beg_prim
  obtain ⟨G⟩ := PrimitiveFormulas.primrec_l edge_prim
  exact ⟨body F G, body_pure F G, body_sound F G⟩

/-- 纯目标的闭句生成器；参数是同一个矩阵，而非另选一个语义等价公式。 -/
def closed_m (φ : Formula signature_m [.set] [.num]) (n : Nat) :
    Sentence signature_m :=
  (Formula.forallE (σ := signature_m) sort_m.set φ).instantiateFreeTop (numeral_m n)

/-- 闭句逐字是原矩阵的捕获避免数码替换再加原集合全称前束。 -/
theorem closed_eq_m (φ : Formula signature_m [.set] [.num]) (n : Nat) :
    closed_m φ n = .forallE .set (φ.instantiateFreeTop (numeral_m n)) := by
  simp only [closed_m, Formula.instantiateFreeTop_forallE, numeral_weaken_m]

/-- 数码闭包仍有纯算术矩阵，不遗留 start、step 或配对函数符号。 -/
theorem closed_pure_m (φ : Formula signature_m [.set] [.num])
    (h : pure_m φ = true) (n : Nat) :
    ∃ ψ : Formula signature_m [.set] [],
      closed_m φ n = .forallE .set ψ ∧ pure_m ψ = true :=
  ⟨φ.instantiateFreeTop (numeral_m n), closed_eq_m φ n, by rwa [formula_numeral_m]⟩

/-- 同一纯目标及其数码闭句的标准语义精确对应。 -/
theorem closed_l (φ : Formula signature_m [.set] [.num]) (n : Nat) :
    Formula.satisfies (Env.empty (M := structure_l)) (closed_m φ n) ↔
      Formula.satisfies (environment_l n) (.forallE .set φ) := by
  rw [closed_m, Formula.satisfies_instantiateFreeTop, numeral_l]
  rfl

/-- 选定一个纯 BM4 矩阵后，所有闭句均由该矩阵数码替换生成且具有原逐高度语义。
    本定理只连接 AST 和标准语义，不声称已经生成其对象证明或数值 quotation。 -/
theorem closed_formula_l : ∃ φ : Formula signature_m [.set] [.num],
    pure_m φ = true ∧ ∀ n,
      (∃ ψ : Formula signature_m [.set] [],
        closed_m φ n = .forallE .set ψ ∧ pure_m ψ = true) ∧
      (Formula.satisfies (Env.empty (M := structure_l)) (closed_m φ n) ↔
        SeedReflection.sentence_l n) := by
  obtain ⟨φ, h, hφ⟩ := formula_l
  exact ⟨φ, h, fun n => ⟨closed_pure_m φ h n, (closed_l φ n).trans (hφ n)⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PureSecondOrder
