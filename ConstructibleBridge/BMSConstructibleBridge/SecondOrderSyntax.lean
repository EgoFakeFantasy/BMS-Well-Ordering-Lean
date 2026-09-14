import BMSConstructibleBridge.SeedReflection
import BMSConstructibleBridge.PrimitiveHistory
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Semantics

/-!
# 逐高度目标的有类型二阶算术语法

复用项目的一阶多排序语法核，以数和集合为两个排序。目标有一个全称集合量词，
矩阵只含数量词。有限签名中的配对、起点和一步关系均由实际原始递归算法解释。
这属于原始递归符号的定义扩张；本文件尚未提供到纯加乘语言的公式消去和对象
总性证明，也没有把标准结构中的满足关系冒充 `Z₂` 可证性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSyntax

open Logic FirstOrder

set_option autoImplicit false

/-- 二阶算术的两个排序。 -/
inductive sort_m where
  | num
  | set
  deriving DecidableEq

/-- 有限函数签名；配对为原始递归定义扩张。 -/
inductive func_m where
  | zero
  | succ
  | add
  | mul
  | pair
  deriving DecidableEq

/-- 集合成员关系，以及两个具有独立算法证书的算术关系。 -/
inductive rel_m where
  | mem
  | start
  | step
  deriving DecidableEq

/-- 保留纯算术核心的有限双排序签名；不允许任意宿主谓词进入语法。 -/
abbrev signature_m : Signature where
  SortSymbol := sort_m
  FuncSymbol := func_m
  RelSymbol := rel_m
  funcDomain
    | .zero => []
    | .succ => [.num]
    | .add | .mul | .pair => [.num, .num]
  funcCodomain _ := .num
  relDomain
    | .mem => [.num, .set]
    | .start => [.num, .num]
    | .step => [.num, .num, .num]

private abbrev carrier : sort_m → Type
  | .num => Nat
  | .set => Set Nat

/-- 标准全二阶结构；集合域遍历全部实数，而非仅可构造或可计算实数。 -/
abbrev structure_l : FirstOrder.Structure signature_m where
  Carrier := carrier
  nonempty
    | .num => ⟨0⟩
    | .set => ⟨∅⟩
  funcInterp
    | .zero, .nil => (0 : Nat)
    | .succ, .cons n .nil => (n + 1 : Nat)
    | .add, .cons n (.cons m .nil) => n + m
    | .mul, .cons n (.cons m .nil) => n * m
    | .pair, .cons n (.cons m .nil) => Nat.pair n m
  relInterp
    | .mem, .cons n (.cons X .nil) => n ∈ X
    | .start, .cons n (.cons a .nil) =>
        (ArithmeticPresentation.decode_l a).1.raw = seed n
    | .step, .cons b (.cons a (.cons k .nil)) =>
        ArithmeticPresentation.check_l b a k = true

/-- 起点关系的实际原始递归证书；不只检查符号个数。 -/
theorem start_l : PrimrecRel (fun n a =>
    (ArithmeticPresentation.decode_l a).1.raw = seed n) :=
  Primrec.eq.comp (PrimitiveCoding.decode_l.comp Primrec.snd)
    (PrimitiveCoding.seed_l.comp Primrec.fst)

/-- 一步关系的实际原始递归证书。 -/
theorem step_l : PrimrecPred (fun p : Nat × Nat × Nat =>
    ArithmeticPresentation.check_l p.1 p.2.1 p.2.2 = true) :=
  Primrec.eq.comp PrimitiveCoding.check_l (Primrec.const true)

private def member {Γ Δ : SortContext signature_m}
    (s t : Term signature_m Γ Δ .num) (X : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .rel .mem (.cons (Term.app (σ := signature_m) .pair (.cons s (.cons t .nil)))
    (.cons X .nil))

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons t .nil)

private def add {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

private def mul {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .mul (.cons s (.cons t .nil))

/-- 函数图的全域性和唯一性公式；外部绑定变量是集合，唯一自由变量是高度。 -/
def graph_m : Formula signature_m [.set] [.num] :=
  .forallE .num (.existsE .num (.conj
    (member (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))
    (.forallE .num (.imp
      (member (.bvar (.there (.there .here))) (.bvar .here)
        (.bvar (.there (.there (.there .here)))))
      (.equal (.bvar .here) (.bvar (.there .here)))))))

/-- 起点必须解码为原种子，不能换成任意同高度数组。 -/
def start_m : Formula signature_m [.set] [.num] :=
  .existsE .num (.conj
    (member zero (.bvar .here) (.bvar (.there .here)))
    (.rel .start (.cons (.fvar .here) (.cons (.bvar .here) .nil))))

/-- 存在断点；三个存在数变量依次为位置、前项和后项。 -/
def break_m : Formula signature_m [.set] [.num] :=
  .existsE .num (.existsE .num (.existsE .num (.conj
    (member (.bvar (.there (.there .here))) (.bvar (.there .here))
      (.bvar (.there (.there (.there .here)))))
    (.conj
      (member (succ (.bvar (.there (.there .here)))) (.bvar .here)
        (.bvar (.there (.there (.there .here)))))
      (.forallE .num (.neg (.rel .step
        (.cons (.bvar (.there .here))
          (.cons (.bvar (.there (.there .here))) (.cons (.bvar .here) .nil))))))))))

/-- 只有一个自由数变量的真实公式 AST，而非用宿主函数参数定义的谓词。 -/
def sentence_m : Formula signature_m [] [.num] :=
  .forallE .set (.imp graph_m (.imp start_m break_m))

/-- 算术矩阵检查：不允许任何集合量词，等式只允许数项。 -/
def arithmetic_m {Γ Δ : SortContext signature_m} : Formula signature_m Γ Δ → Bool
  | .falsum | .truth | .rel _ _ => true
  | @Formula.equal _ _ _ .num _ _ => true
  | @Formula.equal _ _ _ .set _ _ => false
  | .neg φ => arithmetic_m φ
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ => arithmetic_m φ && arithmetic_m ψ
  | .forallE .num φ | .existsE .num φ => arithmetic_m φ
  | .forallE .set _ | .existsE .set _ => false

/-- 单集合全称前束片段检查；不声称判定所有等价于 Π¹₁ 的公式。 -/
def pi11_m {Γ Δ : SortContext signature_m} : Formula signature_m Γ Δ → Bool
  | .forallE .set φ => arithmetic_m φ
  | _ => false

/-- 实际 AST 属于有限原始递归签名的 Π¹₁ 前束片段。 -/
theorem pi11_l : pi11_m sentence_m = true := rfl

private def environment (n : Nat) : Env structure_l [] [.num] where
  boundVal := Assignment.empty
  freeVal := Assignment.push (M := structure_l) (sort := .num) n Assignment.empty

/-- 标准满足关系与之前的逐高度句精确一致，包括图唯一性和起点条件。 -/
theorem realizes_l (n : Nat) : Formula.satisfies (environment n) sentence_m ↔
    SeedReflection.sentence_l n := Iff.rfl

/-- 语法目标的意义仍是原始 BM4 种子的可达性。 -/
theorem acc_iff_l (n : Nat) : Formula.satisfies (environment n) sentence_m ↔
    Acc Step (validSeed n) := (realizes_l n).trans (SeedReflection.acc_iff_l n)

/-- 纯零与后继构成的数码项；不把宿主自然数直接当作对象常量。 -/
def numeral_m {Γ Δ : SortContext signature_m} : Nat → Term signature_m Γ Δ .num
  | 0 => zero
  | n + 1 => succ (numeral_m n)

/-- 数码在任意标准数值环境中返回该自然数。 -/
theorem numeral_l {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ)
    (n : Nat) : Term.eval η (numeral_m n) = n := by
  induction n with
  | zero => rfl
  | succ n hᵢ =>
      change (Term.eval η (numeral_m n) : Nat) + 1 = n + 1
      rw [hᵢ]

/-- 按高度实际生成无自由变量的闭句，采用语法核的捕获避免替换。 -/
def closed_m (n : Nat) : Formula signature_m [] [] :=
  sentence_m.instantiateFreeTop (numeral_m n)

/-- 替换任意数码后仍是单集合全称加算术矩阵；不是只检查几个高度。 -/
theorem closed_pi11_l (n : Nat) : pi11_m (closed_m n) = true := rfl

/-- 实际生成的每个闭句均具有规定的种子无下降链语义。 -/
theorem closed_l (n : Nat) : Formula.satisfies (Env.empty (M := structure_l))
    (closed_m n) ↔ SeedReflection.sentence_l n := by
  rw [closed_m, Formula.satisfies_instantiateFreeTop, numeral_l]
  exact realizes_l n

mutual
  /-- 纯数项检查；明确拒绝尚未消去的配对函数符号。 -/
  def pure_term_m {Γ Δ : SortContext signature_m} :
      {s : sort_m} → Term signature_m Γ Δ s → Bool
    | _, .bvar _ | _, .fvar _ => true
    | _, .app f s => if (f : func_m) = .pair then false else pure_args_m s

  /-- 参数列逐项使用纯算术项。 -/
  def pure_args_m {Γ Δ : SortContext signature_m} :
      {s : List sort_m} → Arguments signature_m Γ Δ s → Bool
    | _, .nil => true
    | _, .cons t s => pure_term_m t && pure_args_m s
end

/-- 纯算术公式检查：只允许零、后继、加乘、数等式、成员关系和数量词。 -/
def pure_m {Γ Δ : SortContext signature_m} : Formula signature_m Γ Δ → Bool
  | .falsum | .truth => true
  | .rel .mem s => pure_args_m s
  | .rel .start _ | .rel .step _ => false
  | @Formula.equal _ _ _ .num s t => pure_term_m s && pure_term_m t
  | @Formula.equal _ _ _ .set _ _ => false
  | .neg φ => pure_m φ
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ => pure_m φ && pure_m ψ
  | .forallE .num φ | .existsE .num φ => pure_m φ
  | .forallE .set _ | .existsE .set _ => false

/-- 数码不含配对等定义扩张符号。 -/
theorem numeral_pure_m {Γ Δ : SortContext signature_m} (n : Nat) :
    pure_term_m (numeral_m (Γ := Γ) (Δ := Δ) n) = true := by
  induction n with
  | zero => rfl
  | succ n hᵢ =>
      change (pure_term_m (numeral_m n) && true) = true
      simpa only [Bool.and_true] using hᵢ

/-- 数码没有绑定变量，穿过任意排序的量词时保持同一个数码。 -/
theorem numeral_weaken_m {Γ Δ : SortContext signature_m} (s : sort_m) (n : Nat) :
    (numeral_m (Γ := Γ) (Δ := Δ) n).weakenBound s = numeral_m n := by
  induction n with
  | zero => rfl
  | succ n hᵢ =>
      simp only [numeral_m, succ, Term.weakenBound_app, Arguments.weakenBound_cons,
        Arguments.weakenBound_nil, hᵢ]

mutual
  /-- 捕获避免的数码替换保留每个项的纯语言检查结果。 -/
  theorem term_numeral_m {Γ Δ : SortContext signature_m} {s : sort_m}
      (t : Term signature_m Γ (.num :: Δ) s) (n : Nat) :
      pure_term_m (t.instantiateFreeTop (numeral_m n)) = pure_term_m t :=
    match t with
    | .bvar _ => rfl
    | .fvar .here => numeral_pure_m n
    | .fvar (.there _) => rfl
    | .app f a => by
        rw [Term.instantiateFreeTop_app]
        simp only [pure_term_m, args_numeral_m a n]

  /-- 参数列中的数码替换逐项保持纯语言检查。 -/
  theorem args_numeral_m {Γ Δ : SortContext signature_m} {s : List sort_m}
      (a : Arguments signature_m Γ (.num :: Δ) s) (n : Nat) :
      pure_args_m (a.instantiateFreeTop (numeral_m n)) = pure_args_m a :=
    match a with
    | .nil => rfl
    | .cons t a => by
        rw [Arguments.instantiateFreeTop_cons]
        simp only [pure_args_m, term_numeral_m t n, args_numeral_m a n]
end

/-- 替换任意数码不改变矩阵的纯算术分类；数量词和集合绑定均按原语法核处理。 -/
theorem formula_numeral_m {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m Γ (.num :: Δ)) (n : Nat) :
    pure_m (φ.instantiateFreeTop (numeral_m n)) = pure_m φ :=
  match φ with
  | .falsum | .truth => rfl
  | .rel r a => by
      cases r <;> simp only [Formula.instantiateFreeTop_rel, pure_m, args_numeral_m a n]
  | @Formula.equal _ _ _ s t u => by
      cases s <;> simp only [Formula.instantiateFreeTop_equal, pure_m, term_numeral_m]
  | .neg φ => by
      simp only [Formula.instantiateFreeTop_neg, pure_m, formula_numeral_m φ n]
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ => by
      simp only [Formula.instantiateFreeTop_conj, Formula.instantiateFreeTop_disj,
        Formula.instantiateFreeTop_imp, Formula.instantiateFreeTop_iff, pure_m,
        formula_numeral_m φ n, formula_numeral_m ψ n]
  | .forallE .num φ | .existsE .num φ => by
      simp only [Formula.instantiateFreeTop_forallE, Formula.instantiateFreeTop_existsE,
        numeral_weaken_m, pure_m, formula_numeral_m φ n]
  | .forallE .set _ | .existsE .set _ => by
      simp only [Formula.instantiateFreeTop_forallE, Formula.instantiateFreeTop_existsE, pure_m]
termination_by φ.size
decreasing_by all_goals simp only [Formula.size]; omega

/-- β 读取的纯算术 AST，四个自由数参数依次为 b、c、i、v。 -/
def beta_m : Formula signature_m [] [.num, .num, .num, .num] :=
  let b : Term signature_m [.num, .num] [.num, .num, .num, .num] .num := .fvar .here
  let c : Term signature_m [.num, .num] [.num, .num, .num, .num] .num := .fvar (.there .here)
  let i : Term signature_m [.num, .num] [.num, .num, .num, .num] .num :=
    .fvar (.there (.there .here))
  let v : Term signature_m [.num, .num] [.num, .num, .num, .num] .num :=
    .fvar (.there (.there (.there .here)))
  let m := succ (mul (succ i) c)
  .existsE .num (.existsE .num (.conj
    (.equal b (add (mul (.bvar (.there .here)) m) v))
    (.equal (add v (succ (.bvar .here))) m)))

/-- β 模板不含任何新增算法关系或配对函数符号。 -/
theorem beta_pure_l : pure_m beta_m = true := rfl

private def beta_env (b c i v : Nat) : Env structure_l [] [.num, .num, .num, .num] where
  boundVal := Assignment.empty
  freeVal := Assignment.push (M := structure_l) (sort := .num) b
    (Assignment.push (M := structure_l) (sort := .num) c
      (Assignment.push (M := structure_l) (sort := .num) i
        (Assignment.push (M := structure_l) (sort := .num) v Assignment.empty)))

/-- 纯算术模板与实际有限历史读取精确一致。 -/
theorem beta_l (b c i v : Nat) : Formula.satisfies (beta_env b c i v) beta_m ↔
    Nat.beta (Nat.pair b c) i = v := PrimitiveHistory.beta_iff_l b c i v

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSyntax
