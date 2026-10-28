import BMSConstructibleBridge.SecondOrderLegacyValidityBudget

/-! # 原部分翻译递归的内部二维预算唯一性

输出码仍为任意内部数字；预算只限制源码和槽数。存在子分支的槽数
增加由严格子码下降支付。通过原纯算术公式的内部强归纳比较两张
在预算内满足原部分翻译方程的图，不假定数字外部标准。

非法输入默认零的总化函数不能直接满足这里的部分图规格；后续解码
必须保留原合法性守卫。本模块不构造 Class 翻译图或统一历史界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyTranslationBudget

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderAlgebra
open SecondOrderLegacyFormulaTranslation (query_l query_m point_l point_m cases_l)
open SecondOrderLegacyFormulaTranslationLength (bound_l bound_m bound_formula_l)
open SecondOrderLegacyValidityBudget (cap_l cap_m cap_formula_l child_l existential_child_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

theorem point_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (C : Term signature_m Γ Δ .set) (n l q : Term signature_m Γ Δ .num) :
    (point_m C n l q).satisfies η ↔ point_l (C.eval η) (n.eval η) (l.eval η) (q.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, SecondOrderFormulaCode.formula_l,
    SecondOrderLegacyFormulaTranslation.cases_formula_l, Term.eval_weakenBound, Term.eval]
  rfl

theorem local_l (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) (n l q B : num_l ℳ)
    (hB : bound_l l n B)
    (h : ∀ k, SecondOrderOrder.lt_l k n → ∀ m, bound_l m k B →
      ∀ r, query_l X k m r ↔ query_l Y k m r) : point_l X n l q ↔ point_l Y n l q := by
  apply or_congr Iff.rfl
  apply exists_congr
  intro t
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  have hpLt := (SecondOrderFormulaCode.bounds_l hℳ t p).2
  rw [hp] at hpLt
  have hNeg : SecondOrderLegacyFormulaTranslation.negation_l X p l q ↔
      SecondOrderLegacyFormulaTranslation.negation_l Y p l q := by
    apply exists_congr
    intro a
    exact and_congr (h p hpLt l (child_l hℳ hpLt hB) a) Iff.rfl
  have hConj : SecondOrderLegacyFormulaTranslation.conjunction_l X p l q ↔
      SecondOrderLegacyFormulaTranslation.conjunction_l Y p l q := by
    apply exists_congr
    intro i
    apply exists_congr
    intro j
    apply exists_congr
    intro a
    apply exists_congr
    intro b
    apply exists_congr
    intro d
    apply and_congr_right
    intro hij
    have hChildren := SecondOrderFormulaCode.children_l hℳ t i j
    rw [hij, hp] at hChildren
    exact and_congr (h i hChildren.1 l (child_l hℳ hChildren.1 hB) a)
      (and_congr (h j hChildren.2 l (child_l hℳ hChildren.2 hB) b) Iff.rfl)
  have hExists : SecondOrderLegacyFormulaTranslation.existential_l X p l q ↔
      SecondOrderLegacyFormulaTranslation.existential_l Y p l q := by
    apply exists_congr
    intro a
    exact and_congr (h p hpLt (succ_l l) (existential_child_l hℳ hpLt hB) a) Iff.rfl
  exact or_congr Iff.rfl (or_congr (and_congr Iff.rfl hNeg)
    (or_congr (and_congr Iff.rfl hConj) (and_congr Iff.rfl hExists)))

def spec_l (C : set_l ℳ) (N B : num_l ℳ) : Prop :=
  ∀ n l q, cap_l n N → bound_l l n B → (query_l C n l q ↔ point_l C n l q)

def spec_m {Γ Δ : SortContext signature_m} (C : Term signature_m Γ Δ .set)
    (N B : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .forallE .num <| .forallE .num <|
    let w (t : Term signature_m Γ Δ .num) := up (up (up t))
    let n : Term signature_m (.num :: .num :: .num :: Γ) Δ .num := .bvar (.there (.there .here))
    let l : Term signature_m (.num :: .num :: .num :: Γ) Δ .num := .bvar (.there .here)
    let q : Term signature_m (.num :: .num :: .num :: Γ) Δ .num := .bvar .here
    .imp (cap_m n (w N)) <| .imp (bound_m l n (w B)) <|
      .iff (query_m (up (up (up C))) n l q) (point_m (up (up (up C))) n l q)

theorem spec_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (C : Term signature_m Γ Δ .set) (N B : Term signature_m Γ Δ .num) :
    (spec_m C N B).satisfies η ↔ spec_l (C.eval η) (N.eval η) (B.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, cap_formula_l, bound_formula_l,
    SecondOrderLegacyFormulaTranslation.query_formula_l, point_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def row_m {Γ Δ : SortContext signature_m} (X Y : Term signature_m Γ Δ .set)
    (N B n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .imp (cap_m n N) <| .forallE .num <| .forallE .num <|
    .imp (bound_m (.bvar (.there .here)) (up (up n)) (up (up B))) <|
      .iff (query_m (up (up X)) (up (up n)) (.bvar (.there .here)) (.bvar .here))
        (query_m (up (up Y)) (up (up n)) (.bvar (.there .here)) (.bvar .here))

theorem row_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (X Y : Term signature_m Γ Δ .set) (N B n : Term signature_m Γ Δ .num) :
    (row_m X Y N B n).satisfies η ↔ cap_l (n.eval η) (N.eval η) →
      ∀ l q, bound_l l (n.eval η) (B.eval η) →
        (query_l (X.eval η) (n.eval η) l q ↔ query_l (Y.eval η) (n.eval η) l q) := by
  simp only [row_m, Formula.satisfies, cap_formula_l, bound_formula_l,
    SecondOrderLegacyFormulaTranslation.query_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem agreement_l (hℳ : Theory.Models ℳ theory_m) {X Y : set_l ℳ} {N B : num_l ℳ}
    (hX : spec_l X N B) (hY : spec_l Y N B) : ∀ n, cap_l n N →
      ∀ l q, bound_l l n B → (query_l X n l q ↔ query_l Y n l q) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  let φ : Formula signature_m [] [.num, .num, .num, .set, .set] :=
    row_m (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  apply SecondOrderListInduction.strong_induct_l hℳ φ (pure_language_m _ rfl)
    ((((Env.empty.pushFree Y).pushFree X).pushFree B).pushFree N)
    (fun n => cap_l n N → ∀ l q, bound_l l n B → (query_l X n l q ↔ query_l Y n l q))
    (fun n => row_formula_l _ _ _ _ _ _) ?_
  intro n ih hn l q hl
  refine (hX n l q hn hl).trans ((local_l hℳ X Y n l q B hl ?_).trans (hY n l q hn hl).symm)
  intro k hk m hm r
  change n ≤ N at hn
  exact ih k hk (show cap_l k N from Or.inr (lt_of_lt_of_le hk hn)) m r hm

def sentence_m : Sentence signature_m := .forallE .set <| .forallE .set <|
  .forallE .num <| .forallE .num <|
    .imp (spec_m (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here)) <|
      .imp (spec_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)) <|
        .forallE .num <| row_m (.bvar (.there (.there (.there (.there .here)))))
          (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
          (.bvar (.there .here)) (.bvar .here)

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, spec_formula_l, row_formula_l, Term.eval]
  exact fun _ _ _ _ hX hY => agreement_l hℳ hX hY

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyTranslationBudget
