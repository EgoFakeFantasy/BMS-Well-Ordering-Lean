import BMSConstructibleBridge.SecondOrderLegacyAssignmentReversal
import BMSConstructibleBridge.SecondOrderTriangularFormulaBranches

/-! # 原五标签至显式槽四标签的内部递归翻译图

翻译状态保存原赋值长度与目标码。原子反转变量槽，否定和合取转为 NAND，
原存在量词递增旧长度并在目标槽 l 更新。递归只查询严格更小的原公式码，
因此原 Z₂ 给出实际唯一递归图，包括非标准码及长度。
本模块只交付递归方程的解；合法输入上的输出总性、单值性、目标长度界、
求值保持及 Def 的双向等价仍是独立义务，不由图的唯一性自动获得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyFormulaTranslation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderEvaluationRule (numeral_l)
open SecondOrderTriangularConstructor (constructor_l constructor_m)
open SecondOrderLegacyAssignmentReversal (index_l index_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

private abbrev up₄ {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := up (up (up (up t)))

private abbrev up₅ {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := up (up₄ t)

private def succ_m {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :=
  Term.app (σ := signature_m) .succ (.cons t .nil)

def query_l (C : set_l ℳ) (n l q : num_l ℳ) : Prop := relation_l C n (value_l l q)

def query_m {Γ Δ : SortContext signature_m} (C : Term signature_m Γ Δ .set)
    (n l q : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .conj (PrimitiveFormulas.pair_m (up l) (up q) (.bvar .here))
    (GraphSyntax.edge_m (up C) (up n) (.bvar .here))

theorem query_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (C : Term signature_m Γ Δ .set) (n l q : Term signature_m Γ Δ .num) :
    (query_m C n l q).satisfies η ↔ query_l (C.eval η) (n.eval η) (l.eval η) (q.eval η) := by
  simp only [query_m, query_l, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

def atomic_l (t p l q : num_l ℳ) : Prop := ∃ i j r s,
  value_l i j = p ∧ index_l l i r ∧ index_l l j s ∧
    ((t = numeral_l ℳ 0 ∧ constructor_l (numeral_l ℳ 1) r s q) ∨
      (t = numeral_l ℳ 1 ∧ constructor_l (numeral_l ℳ 0) r s q))

def atomic_m {Γ Δ : SortContext signature_m} (t p l q : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num <| .existsE .num <| .existsE .num <| .existsE .num <|
    let i : Term signature_m (.num :: .num :: .num :: .num :: Γ) Δ .num :=
      .bvar (.there (.there (.there .here)))
    let j : Term signature_m (.num :: .num :: .num :: .num :: Γ) Δ .num := .bvar (.there (.there .here))
    let r : Term signature_m (.num :: .num :: .num :: .num :: Γ) Δ .num := .bvar (.there .here)
    let s : Term signature_m (.num :: .num :: .num :: .num :: Γ) Δ .num := .bvar .here
    .conj (PrimitiveFormulas.pair_m i j (up₄ p)) <|
      .conj (index_m (up₄ l) i r) <| .conj (index_m (up₄ l) j s) <|
        .disj (.conj (.equal (up₄ t) (numeral_m 0)) (constructor_m (numeral_m 1) r s (up₄ q)))
          (.conj (.equal (up₄ t) (numeral_m 1)) (constructor_m (numeral_m 0) r s (up₄ q)))

def negation_l (C : set_l ℳ) (p l q : num_l ℳ) : Prop :=
  ∃ a, query_l C p l a ∧ constructor_l (numeral_l ℳ 2) a a q

def negation_m {Γ Δ : SortContext signature_m} (C : Term signature_m Γ Δ .set)
    (p l q : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .conj (query_m (up C) (up p) (up l) (.bvar .here))
    (constructor_m (numeral_m 2) (.bvar .here) (.bvar .here) (up q))

def conjunction_l (C : set_l ℳ) (p l q : num_l ℳ) : Prop := ∃ i j a b d,
  value_l i j = p ∧ query_l C i l a ∧ query_l C j l b ∧
    constructor_l (numeral_l ℳ 2) a b d ∧ constructor_l (numeral_l ℳ 2) d d q

def conjunction_m {Γ Δ : SortContext signature_m} (C : Term signature_m Γ Δ .set)
    (p l q : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .existsE .num <| .existsE .num <| .existsE .num <| .existsE .num <|
    let i : Term signature_m (.num :: .num :: .num :: .num :: .num :: Γ) Δ .num :=
      .bvar (.there (.there (.there (.there .here))))
    let j : Term signature_m (.num :: .num :: .num :: .num :: .num :: Γ) Δ .num :=
      .bvar (.there (.there (.there .here)))
    let a : Term signature_m (.num :: .num :: .num :: .num :: .num :: Γ) Δ .num := .bvar (.there (.there .here))
    let b : Term signature_m (.num :: .num :: .num :: .num :: .num :: Γ) Δ .num := .bvar (.there .here)
    let d : Term signature_m (.num :: .num :: .num :: .num :: .num :: Γ) Δ .num := .bvar .here
    .conj (PrimitiveFormulas.pair_m i j (up₅ p)) <|
      .conj (query_m (up₅ C) i (up₅ l) a) <| .conj (query_m (up₅ C) j (up₅ l) b) <|
        .conj (constructor_m (numeral_m 2) a b d) (constructor_m (numeral_m 2) d d (up₅ q))

def existential_l (C : set_l ℳ) (p l q : num_l ℳ) : Prop :=
  ∃ a, query_l C p (succ_l l) a ∧ constructor_l (numeral_l ℳ 3) l a q

def existential_m {Γ Δ : SortContext signature_m} (C : Term signature_m Γ Δ .set)
    (p l q : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .conj (query_m (up C) (up p) (succ_m (up l)) (.bvar .here))
    (constructor_m (numeral_m 3) (up l) (.bvar .here) (up q))

def cases_l (C : set_l ℳ) (t p l q : num_l ℳ) : Prop := atomic_l t p l q ∨
  (t = numeral_l ℳ 2 ∧ negation_l C p l q) ∨
    (t = numeral_l ℳ 3 ∧ conjunction_l C p l q) ∨
      (t = numeral_l ℳ 4 ∧ existential_l C p l q)

def cases_m {Γ Δ : SortContext signature_m} (C : Term signature_m Γ Δ .set)
    (t p l q : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .disj (atomic_m t p l q) <|
    .disj (.conj (.equal t (numeral_m 2)) (negation_m C p l q)) <|
      .disj (.conj (.equal t (numeral_m 3)) (conjunction_m C p l q))
        (.conj (.equal t (numeral_m 4)) (existential_m C p l q))

theorem cases_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (C : Term signature_m Γ Δ .set) (t p l q : Term signature_m Γ Δ .num) :
    (cases_m C t p l q).satisfies η ↔
      cases_l (C.eval η) (t.eval η) (p.eval η) (l.eval η) (q.eval η) := by
  simp only [cases_m, cases_l, atomic_m, atomic_l, negation_m, negation_l,
    conjunction_m, conjunction_l, existential_m, existential_l, Formula.satisfies,
    SecondOrderPairing.formula_l, SecondOrderLegacyAssignmentReversal.index_formula_l,
    query_formula_l, SecondOrderTriangularConstructor.formula_l,
    up₅, up₄, up, succ_m, numeral_m, SecondOrderEvaluationRule.numeral_l,
    Term.eval_weakenBound, Term.eval, Arguments.eval]
  rfl

def point_l (C : set_l ℳ) (n l q : num_l ℳ) : Prop :=
  (n = zero_l ℳ ∧ q = zero_l ℳ) ∨
    ∃ t p, SecondOrderFormulaCode.node_l t p = n ∧ cases_l C t p l q

def point_m {Γ Δ : SortContext signature_m} (C : Term signature_m Γ Δ .set)
    (n l q : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .disj (.conj (.equal n (numeral_m 0)) (.equal q (numeral_m 0))) <|
    .existsE .num <| .existsE .num <|
      .conj (SecondOrderFormulaCode.formula_m (.bvar (.there .here)) (.bvar .here) (up (up n)))
        (cases_m (up (up C)) (.bvar (.there .here)) (.bvar .here) (up (up l)) (up (up q)))

def rule_l (C : set_l ℳ) (n s : num_l ℳ) : Prop :=
  ∃ l q, value_l l q = s ∧ point_l C n l q

def rule_m {Γ Δ : SortContext signature_m} (C : Term signature_m Γ Δ .set)
    (n s : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .existsE .num <|
    .conj (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here) (up (up s)))
      (point_m (up (up C)) (up (up n)) (.bvar (.there .here)) (.bvar .here))

def formula_m : Formula signature_m [] [.num, .num, .set] :=
  rule_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem rule_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (C : Term signature_m Γ Δ .set) (n s : Term signature_m Γ Δ .num) :
    (rule_m C n s).satisfies η ↔ rule_l (C.eval η) (n.eval η) (s.eval η) := by
  simp only [rule_m, rule_l, point_m, point_l, Formula.satisfies,
    SecondOrderPairing.formula_l, SecondOrderFormulaCode.formula_l, cases_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem local_l (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) (n s : num_l ℳ)
    (h : SecondOrderInitialAgreement.agree_l X Y n) : rule_l X n s ↔ rule_l Y n s := by
  apply exists_congr
  intro l
  apply exists_congr
  intro q
  apply and_congr Iff.rfl
  apply or_congr Iff.rfl
  apply exists_congr
  intro t
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  have hpLt := (SecondOrderFormulaCode.bounds_l hℳ t p).2
  rw [hp] at hpLt
  unfold cases_l
  apply or_congr Iff.rfl
  apply or_congr
  · apply and_congr Iff.rfl
    apply exists_congr
    intro a
    exact and_congr (h p hpLt (value_l l a)) Iff.rfl
  · apply or_congr
    · apply and_congr Iff.rfl
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
      exact and_congr (h i hChildren.1 (value_l l a))
        (and_congr (h j hChildren.2 (value_l l b)) Iff.rfl)
    · apply and_congr Iff.rfl
      apply exists_congr
      intro a
      exact and_congr (h p hpLt (value_l (succ_l l) a)) Iff.rfl

def spec_l (C : set_l ℳ) : Prop := ∀ n s, relation_l C n s ↔ rule_l C n s

def spec_m {Γ Δ : SortContext signature_m} (C : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .num <| .forallE .num <| .iff
    (GraphSyntax.edge_m (up (up C)) (.bvar (.there .here)) (.bvar .here))
    (rule_m (up (up C)) (.bvar (.there .here)) (.bvar .here))

theorem spec_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (C : Term signature_m Γ Δ .set) : (spec_m C).satisfies η ↔ spec_l (C.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, SecondOrderPairing.edge_l,
    rule_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) : ∃! C : set_l ℳ, spec_l C := by
  have h (C : set_l ℳ) (n s : num_l ℳ) :
      SecondOrderRecursiveRelation.rule_l formula_m Env.empty C n s ↔ rule_l C n s :=
    rule_formula_l _ _ _ _
  obtain ⟨C, hC, hUnique⟩ := SecondOrderRecursiveRelation.exists_l hℳ formula_m pure_m Env.empty
    (fun X Y n hn s => (h X n s).trans ((local_l hℳ X Y n s hn).trans (h Y n s).symm))
  exact ⟨C, fun n s => (hC n s).trans (h C n s),
    fun D hD => hUnique D (fun n s => (hD n s).trans (h D n s).symm)⟩

theorem equation_l (hℳ : Theory.Models ℳ theory_m) {C : set_l ℳ} (hC : spec_l C)
    (n l q : num_l ℳ) : query_l C n l q ↔ point_l C n l q := by
  rw [query_l, hC]
  constructor
  · rintro ⟨l', q', hPair, hPoint⟩
    obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ l' q' l q hPair
    exact hPoint
  · intro hPoint
    exact ⟨l, q, rfl, hPoint⟩

def sentence_m : Sentence signature_m := Metatheory.Formula.forall_close
  (SecondOrderRankedRecursionTheorem.fixed_m (SecondOrderRecursiveRelation.operator_m formula_m))

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  rw [SecondOrderRankedRecursionTheorem.fixed_l]
  have hη : SecondOrderSetIterationTheorem.parameters_l η = Env.empty := by
    apply Env.ext <;> intro s v <;> nomatch v
  rw [hη]
  have h (C : set_l ℳ) (n s : num_l ℳ) :
      SecondOrderRecursiveRelation.rule_l formula_m Env.empty C n s ↔ rule_l C n s :=
    rule_formula_l _ _ _ _
  obtain ⟨C, hC, hUnique⟩ := exists_l hℳ
  refine ⟨C, (SecondOrderRecursiveRelation.operator_l formula_m Env.empty C C).mpr
    (fun n s => (hC n s).trans (h C n s).symm), ?_⟩
  intro D hD a
  have hDC : D = C := hUnique D (fun n s =>
    ((SecondOrderRecursiveRelation.operator_l formula_m Env.empty D D).mp hD n s).trans (h D n s))
  exact hDC ▸ Iff.rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyFormulaTranslation
