import BMSConstructibleBridge.SecondOrderLegacyFormulaTranslationLength

/-! # 原五标签合法性递归的内部二维预算

预算 `l+n ≤ B` 随严格子码查询保持；存在分支把长度变成 `succ l`，
其增加由子码的严格下降支付。两张在预算内满足原递归方程的表一致，
通过原算术公式的内部强归纳证明，涵盖全部非标准码与长度。

本模块尚不构造 Class 表，也不提供 Δ₀ 集合检查器或统一历史界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyValidityBudget

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderAlgebra
open SecondOrderLegacyFormulaTranslationLength (bound_l bound_m bound_formula_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

def cap_l (n N : num_l ℳ) : Prop := n = N ∨ SecondOrderOrder.lt_l n N

def cap_m {Γ Δ : SortContext signature_m} (n N : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .disj (.equal n N) (PrimitiveFormulas.lt_m n N)

theorem cap_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (n N : Term signature_m Γ Δ .num) :
    (cap_m n N).satisfies η ↔ cap_l (n.eval η) (N.eval η) := by
  simp only [cap_m, cap_l, Formula.satisfies, SecondOrderOrder.formula_l]

theorem child_l (hℳ : Theory.Models ℳ theory_m) {l n k B : num_l ℳ}
    (hk : SecondOrderOrder.lt_l k n) (hB : bound_l l n B) : bound_l l k B := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  change l + n ≤ B at hB
  change l + k ≤ B
  exact (add_le_add le_rfl (le_of_lt hk)).trans hB

theorem existential_child_l (hℳ : Theory.Models ℳ theory_m) {l n k B : num_l ℳ}
    (hk : SecondOrderOrder.lt_l k n) (hB : bound_l l n B) : bound_l (succ_l l) k B := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  change l + n ≤ B at hB
  change succ_l l + k ≤ B
  calc
    succ_l l + k = l + (k + 1) := by rw [succ_eq_l hℳ]; ac_rfl
    _ ≤ l + n := add_le_add le_rfl ((lt_iff_add_one_le_l hℳ k n).mp hk)
    _ ≤ B := hB

/-- 全预算域的平方配数坐标落入同一个内部有限初段。 -/
theorem cell_bound_l (hℳ : Theory.Models ℳ theory_m) {l n B : num_l ℳ}
    (hB : bound_l l n B) :
    SecondOrderOrder.lt_l (value_l n l) (mul_l (succ_l B) (succ_l B)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  change l + n ≤ B at hB
  have hn : n ≤ B := (le_add_of_nonneg_left (zero_le_l hℳ l)).trans hB
  have hl : l ≤ B := (le_add_of_nonneg_right (zero_le_l hℳ n)).trans hB
  have hMax : max n l + 1 ≤ B + 1 := add_le_add (max_le hn hl) le_rfl
  have hSquare := mul_self_le_mul_self (zero_le_l hℳ _) hMax
  change value_l n l < succ_l B * succ_l B
  rw [succ_eq_l hℳ]
  exact (SecondOrderPairingBounds.interval_l hℳ n l).2.trans_le hSquare

theorem local_l (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) (n l B : num_l ℳ)
    (hB : bound_l l n B)
    (h : ∀ k, SecondOrderOrder.lt_l k n → ∀ m, bound_l m k B →
      (relation_l X k m ↔ relation_l Y k m)) :
    SecondOrderInternalFormulaSyntax.rule_l X n l ↔
      SecondOrderInternalFormulaSyntax.rule_l Y n l := by
  apply or_congr Iff.rfl
  apply exists_congr
  intro t
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  have hpLt := (SecondOrderFormulaCode.bounds_l hℳ t p).2
  rw [hp] at hpLt
  have hConj : SecondOrderEvaluationRule.conjunction_l X p l ↔
      SecondOrderEvaluationRule.conjunction_l Y p l := by
    apply exists_congr
    intro i
    apply exists_congr
    intro j
    apply and_congr_right
    intro hij
    have hChildren := SecondOrderFormulaCode.children_l hℳ t i j
    rw [hij, hp] at hChildren
    exact and_congr (h i hChildren.1 l (child_l hℳ hChildren.1 hB))
      (h j hChildren.2 l (child_l hℳ hChildren.2 hB))
  exact or_congr Iff.rfl (or_congr
    (and_congr Iff.rfl (h p hpLt l (child_l hℳ hpLt hB)))
    (or_congr (and_congr Iff.rfl hConj)
      (and_congr Iff.rfl (h p hpLt (succ_l l) (existential_child_l hℳ hpLt hB)))))

def spec_l (V : set_l ℳ) (N B : num_l ℳ) : Prop :=
  ∀ n l, cap_l n N → bound_l l n B →
    (relation_l V n l ↔ SecondOrderInternalFormulaSyntax.rule_l V n l)

def spec_m {Γ Δ : SortContext signature_m} (V : Term signature_m Γ Δ .set)
    (N B : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .forallE .num <|
    .imp (cap_m (.bvar (.there .here)) (up (up N))) <|
      .imp (bound_m (.bvar .here) (.bvar (.there .here)) (up (up B))) <|
        .iff (GraphSyntax.edge_m (up (up V)) (.bvar (.there .here)) (.bvar .here))
          (SecondOrderInternalFormulaSyntax.rule_m (up (up V)) (.bvar (.there .here)) (.bvar .here))

theorem spec_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V : Term signature_m Γ Δ .set) (N B : Term signature_m Γ Δ .num) :
    (spec_m V N B).satisfies η ↔ spec_l (V.eval η) (N.eval η) (B.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, cap_formula_l, bound_formula_l,
    SecondOrderPairing.edge_l, SecondOrderInternalFormulaSyntax.rule_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def row_m {Γ Δ : SortContext signature_m} (X Y : Term signature_m Γ Δ .set)
    (N B n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .imp (cap_m n N) <| .forallE .num <|
    .imp (bound_m (.bvar .here) (up n) (up B)) <|
      .iff (GraphSyntax.edge_m (up X) (up n) (.bvar .here))
        (GraphSyntax.edge_m (up Y) (up n) (.bvar .here))

theorem row_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (X Y : Term signature_m Γ Δ .set) (N B n : Term signature_m Γ Δ .num) :
    (row_m X Y N B n).satisfies η ↔ cap_l (n.eval η) (N.eval η) →
      ∀ l, bound_l l (n.eval η) (B.eval η) →
        (relation_l (X.eval η) (n.eval η) l ↔ relation_l (Y.eval η) (n.eval η) l) := by
  simp only [row_m, Formula.satisfies, cap_formula_l, bound_formula_l,
    SecondOrderPairing.edge_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem agreement_l (hℳ : Theory.Models ℳ theory_m) {X Y : set_l ℳ} {N B : num_l ℳ}
    (hX : spec_l X N B) (hY : spec_l Y N B) : ∀ n, cap_l n N →
      ∀ l, bound_l l n B → (relation_l X n l ↔ relation_l Y n l) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  let φ : Formula signature_m [] [.num, .num, .num, .set, .set] :=
    row_m (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  apply SecondOrderListInduction.strong_induct_l hℳ φ (pure_language_m _ rfl)
    ((((Env.empty.pushFree Y).pushFree X).pushFree B).pushFree N)
    (fun n => cap_l n N → ∀ l, bound_l l n B → (relation_l X n l ↔ relation_l Y n l))
    (fun n => row_formula_l _ _ _ _ _ _) ?_
  intro n ih hn l hl
  refine (hX n l hn hl).trans ((local_l hℳ X Y n l B hl ?_).trans (hY n l hn hl).symm)
  intro k hk m hm
  change n ≤ N at hn
  exact ih k hk (show cap_l k N from Or.inr (lt_of_lt_of_le hk hn)) m hm

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
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, spec_formula_l,
    row_formula_l, Term.eval]
  exact fun _ _ _ _ hX hY => agreement_l hℳ hX hY

#print axioms local_l
#print axioms cell_bound_l
#print axioms agreement_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyValidityBudget
