import BMSConstructibleBridge.SecondOrderInternalFormulaCompilation

/-! # 全内部长度的有限相等析取码

在原求值器的编码中，第 n 行为 v₀ = v₁ ∨ … ∨ v₀ = vₙ，零行为假。
长度属于模型数域；构造使用原 Z₂ 的内部关系递归和可定义归纳，不以宿主
Nat 递归枚举公式。本模块交付唯一递归图及其全域性，合法性与求值另行验证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteDisjunctionSyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) : Term signature_m (.num :: Γ) Δ s :=
  t.weakenBound sort_m.num

private def succ_m {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons t .nil)

def node_m {Γ Δ : SortContext signature_m} (k : Nat) (p q : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := SecondOrderFormulaCode.formula_m (numeral_m k) p q

def binary_m {Γ Δ : SortContext signature_m} (k : Nat) (p q r : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.conj (PrimitiveFormulas.pair_m (up p) (up q) (.bvar .here))
    (node_m k (.bvar .here) (up r)))

def disjunction_m {Γ Δ : SortContext signature_m} (p q r : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.existsE .num
    (.conj (node_m 2 (up (up (up p))) (.bvar (.there (.there .here))))
      (.conj (node_m 2 (up (up (up q))) (.bvar (.there .here)))
        (.conj (binary_m 3 (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
          (node_m 2 (.bvar .here) (up (up (up r)))))))))

def step_m {Γ Δ : SortContext signature_m} (n p q : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.conj (binary_m 0 (numeral_m 0) (succ_m (up n)) (.bvar .here))
    (disjunction_m (up p) (.bvar .here) (up q)))

/-- 纯规范构造子组合；不从存在命题抽取公式码。 -/
noncomputable def next_l (n p : num_l ℳ) : num_l ℳ :=
  SecondOrderFormulaCompilation.disjunction_l p
    (SecondOrderEvaluationEquations.node_l 0 (value_l (zero_l ℳ) (succ_l n)))

theorem node_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (k : Nat) (p q : Term signature_m Γ Δ .num) :
    (node_m k p q).satisfies η ↔ SecondOrderEvaluationEquations.node_l k (p.eval η) = q.eval η := by
  have h (i : Nat) : (numeral_m i).eval η = SecondOrderEvaluationRule.numeral_l ℳ i := by
    induction i with
    | zero => rfl
    | succ i ih =>
        change succ_l ((numeral_m i).eval η) = succ_l (SecondOrderEvaluationRule.numeral_l ℳ i)
        rw [ih]
  rw [node_m, SecondOrderFormulaCode.formula_l, h]
  rfl

theorem binary_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (k : Nat) (p q r : Term signature_m Γ Δ .num) :
    (binary_m k p q r).satisfies η ↔
      SecondOrderEvaluationEquations.node_l k (value_l (p.eval η) (q.eval η)) = r.eval η := by
  simp only [binary_m, Formula.satisfies, SecondOrderPairing.formula_l,
    node_formula_l, up, Term.eval_weakenBound, Term.eval]
  constructor
  · rintro ⟨a, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

theorem disjunction_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (p q r : Term signature_m Γ Δ .num) :
    (disjunction_m p q r).satisfies η ↔
      SecondOrderFormulaCompilation.disjunction_l (p.eval η) (q.eval η) = r.eval η := by
  simp only [disjunction_m, Formula.satisfies, node_formula_l, binary_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  change (∃ a b c, SecondOrderEvaluationEquations.node_l 2 (p.eval η) = a ∧
    SecondOrderEvaluationEquations.node_l 2 (q.eval η) = b ∧
    SecondOrderEvaluationEquations.node_l 3 (value_l a b) = c ∧
    SecondOrderEvaluationEquations.node_l 2 c = r.eval η) ↔ _
  constructor
  · rintro ⟨a, b, c, rfl, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, _, rfl, rfl, rfl, h⟩

theorem step_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (n p q : Term signature_m Γ Δ .num) :
    (step_m n p q).satisfies η ↔ next_l (n.eval η) (p.eval η) = q.eval η := by
  simp only [step_m, Formula.satisfies, binary_formula_l, disjunction_formula_l,
    up, succ_m, Term.eval_weakenBound, Term.eval, Arguments.eval]
  change (∃ a, SecondOrderEvaluationEquations.node_l 0
    (value_l (zero_l ℳ) (succ_l (n.eval η))) = a ∧
    SecondOrderFormulaCompilation.disjunction_l (p.eval η) a = q.eval η) ↔ _
  constructor
  · rintro ⟨a, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

def rule_l (S : set_l ℳ) (n p : num_l ℳ) : Prop :=
  (n = zero_l ℳ ∧ p = zero_l ℳ) ∨
    ∃ i q, succ_l i = n ∧ relation_l S i q ∧ next_l i q = p

def rule_m {Γ Δ : SortContext signature_m} (S : Term signature_m Γ Δ .set)
    (n p : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .disj (.conj (.equal n (numeral_m 0)) (.equal p (numeral_m 0)))
    (.existsE .num (.existsE .num
      (.conj (.equal (succ_m (.bvar (.there .here))) (up (up n)))
        (.conj (GraphSyntax.edge_m (up (up S)) (.bvar (.there .here)) (.bvar .here))
          (step_m (.bvar (.there .here)) (.bvar .here) (up (up p)))))))

theorem rule_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (S : Term signature_m Γ Δ .set) (n p : Term signature_m Γ Δ .num) :
    (rule_m S n p).satisfies η ↔ rule_l (S.eval η) (n.eval η) (p.eval η) := by
  simp only [rule_m, Formula.satisfies, SecondOrderPairing.edge_l, step_formula_l,
    up, succ_m, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m : Formula signature_m [] [.num, .num, .set] :=
  rule_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

def spec_l (S : set_l ℳ) : Prop := ∀ n p, relation_l S n p ↔ rule_l S n p

theorem local_l (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) (n p : num_l ℳ)
    (h : SecondOrderInitialAgreement.agree_l X Y n) : rule_l X n p ↔ rule_l Y n p := by
  apply or_congr Iff.rfl
  apply exists_congr
  intro i
  apply exists_congr
  intro q
  apply and_congr_right
  intro hi
  have hi' : SecondOrderOrder.lt_l i n := by
    rw [← hi]
    exact ⟨zero_l ℳ, by rw [add_succ_l hℳ, add_zero_l hℳ]⟩
  exact and_congr (h i hi' q) Iff.rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) : ∃! S : set_l ℳ, spec_l S := by
  have h (S : set_l ℳ) (n p : num_l ℳ) :
      SecondOrderRecursiveRelation.rule_l formula_m Env.empty S n p ↔ rule_l S n p :=
    rule_formula_l _ _ _ _
  obtain ⟨S, hS, hU⟩ := SecondOrderRecursiveRelation.exists_l hℳ formula_m pure_m Env.empty
    (fun X Y n hn p => (h X n p).trans ((local_l hℳ X Y n p hn).trans (h Y n p).symm))
  exact ⟨S, fun n p => (hS n p).trans (h S n p),
    fun W hW => hU W (fun n p => (hW n p).trans (h W n p).symm)⟩

theorem base_l (hℳ : Theory.Models ℳ theory_m) {S : set_l ℳ} (hS : spec_l S)
    (p : num_l ℳ) : relation_l S (zero_l ℳ) p ↔ p = zero_l ℳ := by
  rw [hS]
  constructor
  · rintro (⟨_, hp⟩ | ⟨i, q, hi, _, _⟩)
    · exact hp
    · exact False.elim (SecondOrderModel.nonzero_l hℳ _ hi)
  · intro hp
    exact Or.inl ⟨rfl, hp⟩

theorem successor_l (hℳ : Theory.Models ℳ theory_m) {S : set_l ℳ} (hS : spec_l S)
    (n p : num_l ℳ) : relation_l S (succ_l n) p ↔
      ∃ q, relation_l S n q ∧ next_l n q = p := by
  rw [hS]
  constructor
  · rintro (⟨hn, _⟩ | ⟨i, q, hi, hq, hp⟩)
    · exact False.elim (SecondOrderModel.nonzero_l hℳ _ hn)
    · obtain rfl := SecondOrderModel.injective_l hℳ hi
      exact ⟨q, hq, hp⟩
  · rintro ⟨q, hq, hp⟩
    exact Or.inr ⟨n, q, rfl, hq, hp⟩

theorem total_l (hℳ : Theory.Models ℳ theory_m) {S : set_l ℳ} (hS : spec_l S) :
    ∀ n : num_l ℳ, ∃ p, relation_l S n p := by
  let φ : Formula signature_m [] [.num, .set] :=
    .existsE .num (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
  apply induct_l hℳ φ (pure_language_m _ rfl) ((Env.empty (M := ℳ)).pushFree S)
    (fun n => ∃ p, relation_l S n p) ?_ ?_ ?_
  · intro n
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
    rfl
  · exact ⟨zero_l ℳ, (hS _ _).mpr (Or.inl ⟨rfl, rfl⟩)⟩
  · rintro n ⟨p, hp⟩
    exact ⟨next_l n p, (hS _ _).mpr (Or.inr ⟨n, p, rfl, hp, rfl⟩)⟩

def fixed_m {Γ Δ : SortContext signature_m} (S : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .forallE .num (.forallE .num (.iff
    (GraphSyntax.edge_m (up (up S)) (.bvar (.there .here)) (.bvar .here))
    (rule_m (up (up S)) (.bvar (.there .here)) (.bvar .here))))

def total_m {Γ Δ : SortContext signature_m} (S : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .forallE .num (.existsE .num
    (GraphSyntax.edge_m (up (up S)) (.bvar (.there .here)) (.bvar .here)))

theorem fixed_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (S : Term signature_m Γ Δ .set) : (fixed_m S).satisfies η ↔ spec_l (S.eval η) := by
  simp only [fixed_m, Formula.satisfies, SecondOrderPairing.edge_l, rule_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem total_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (S : Term signature_m Γ Δ .set) :
    (total_m S).satisfies η ↔ ∀ n, ∃ p, relation_l (S.eval η) n p := by
  simp only [total_m, Formula.satisfies, SecondOrderPairing.edge_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def sentence_m : Sentence signature_m := .existsE .set (.conj
  (fixed_m (.bvar .here)) (total_m (.bvar .here)))

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  obtain ⟨S, hS, _⟩ := exists_l hℳ
  exact ⟨S, (fixed_formula_l _ _).mpr hS, (total_formula_l _ _).mpr (total_l hℳ hS)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteDisjunctionSyntax
