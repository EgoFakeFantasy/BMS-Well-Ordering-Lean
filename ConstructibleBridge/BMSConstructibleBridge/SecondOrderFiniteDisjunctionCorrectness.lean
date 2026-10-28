import BMSConstructibleBridge.SecondOrderFiniteDisjunctionSyntax
import BMSConstructibleBridge.SecondOrderEvaluationLogic

/-! # 内部有限相等析取的合法性和实际真值

归纳变量遍历全部模型自然数，赋值也可具有非标准长度。合法性要求 n 小于
赋值长度；真值方程则读取实际有效赋值的前 n 个参数，不假定宿主有限性。
这是有限子集进入同一 Def 层的数码前置，不是完整层界或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteDisjunctionCorrectness

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderSequenceSyntax (read_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) : Term signature_m (.num :: Γ) Δ s :=
  t.weakenBound sort_m.num

private def succ_m {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons t .nil)

def legal_m {Γ Δ : SortContext signature_m} (S V : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num (.forallE .num (.imp
    (PrimitiveFormulas.lt_m (up (up n)) (.bvar (.there .here)))
    (.imp (GraphSyntax.edge_m (up (up S)) (up (up n)) (.bvar .here))
      (GraphSyntax.edge_m (up (up V)) (.bvar .here) (.bvar (.there .here))))))

theorem legal_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (S V : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num) :
    (legal_m S V n).satisfies η ↔ ∀ l, SecondOrderOrder.lt_l (n.eval η) l →
      ∀ p, relation_l (S.eval η) (n.eval η) p → relation_l (V.eval η) p l := by
  simp only [legal_m, Formula.satisfies, SecondOrderPairing.edge_l,
    SecondOrderOrder.formula_l, up, Term.eval_weakenBound, Term.eval]
  change (∀ l p, SecondOrderOrder.lt_l (n.eval η) l →
    relation_l (S.eval η) (n.eval η) p → relation_l (V.eval η) p l) ↔ _
  exact forall_congr' (fun _ => forall_comm)

theorem legal_l (hℳ : Theory.Models ℳ theory_m) {S V : set_l ℳ}
    (hS : SecondOrderFiniteDisjunctionSyntax.spec_l S)
    (hV : SecondOrderInternalFormulaSyntax.spec_l V) :
    ∀ n l, SecondOrderOrder.lt_l n l → ∀ p, relation_l S n p → relation_l V p l := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  let φ : Formula signature_m [] [.num, .set, .set] :=
    legal_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  apply induct_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree V).pushFree S)
    (fun n => ∀ l, SecondOrderOrder.lt_l n l → ∀ p, relation_l S n p → relation_l V p l)
    (fun _ => legal_formula_l _ _ _ _) ?_ ?_
  · intro l _ p hp
    obtain rfl := (SecondOrderFiniteDisjunctionSyntax.base_l hℳ hS p).mp hp
    exact SecondOrderInternalFormulaCompilation.falsum_l hV l
  · intro n ih l hn p hp
    obtain ⟨q, hq, rfl⟩ := (SecondOrderFiniteDisjunctionSyntax.successor_l hℳ hS n p).mp hp
    have hn₀ : n < succ_l n := (SecondOrderNaturalGraph.lt_succ_l hℳ n n).mpr le_rfl
    have hqV := ih l (lt_trans hn₀ hn) q hq
    have hEq : relation_l V (SecondOrderEvaluationEquations.node_l 0
        (value_l (zero_l ℳ) (succ_l n))) l :=
      SecondOrderInternalFormulaCompilation.node_l hV _ _ _
        (Or.inl ⟨Or.inl rfl, _, _, rfl, lt_of_le_of_lt (SecondOrderAlgebra.zero_le_l hℳ _) hn, hn⟩)
    exact SecondOrderInternalFormulaCompilation.negation_l hV
      (SecondOrderInternalFormulaCompilation.conjunction_l hV
        (SecondOrderInternalFormulaCompilation.negation_l hV hqV)
        (SecondOrderInternalFormulaCompilation.negation_l hV hEq))

def prefix_l (E Q : set_l ℳ) (c n : num_l ℳ) : Prop :=
  ∃ i, SecondOrderOrder.lt_l i n ∧ ∃ x y,
    read_l E c (zero_l ℳ) x ∧ read_l E c (succ_l i) y ∧ relation_l Q x y

def prefix_m {Γ Δ : SortContext signature_m} (E Q : Term signature_m Γ Δ .set)
    (c n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.conj (PrimitiveFormulas.lt_m (.bvar .here) (up n))
    (.existsE .num (.existsE .num
      (.conj (SecondOrderSequenceSyntax.formula_m (up (up (up E))) (up (up (up c)))
        (numeral_m 0) (.bvar (.there .here)))
        (.conj (SecondOrderSequenceSyntax.formula_m (up (up (up E))) (up (up (up c)))
          (succ_m (.bvar (.there (.there .here)))) (.bvar .here))
          (GraphSyntax.edge_m (up (up (up Q))) (.bvar (.there .here)) (.bvar .here)))))))

theorem prefix_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E Q : Term signature_m Γ Δ .set) (c n : Term signature_m Γ Δ .num) :
    (prefix_m E Q c n).satisfies η ↔ prefix_l (E.eval η) (Q.eval η) (c.eval η) (n.eval η) := by
  simp only [prefix_m, Formula.satisfies, SecondOrderOrder.formula_l,
    SecondOrderSequenceSyntax.raw_l, SecondOrderPairing.edge_l,
    up, succ_m, Term.eval_weakenBound, Term.eval]
  rfl

theorem prefix_successor_l (hℳ : Theory.Models ℳ theory_m) (E Q : set_l ℳ) (c n : num_l ℳ) :
    prefix_l E Q c (succ_l n) ↔ prefix_l E Q c n ∨
      ∃ x y, read_l E c (zero_l ℳ) x ∧ read_l E c (succ_l n) y ∧ relation_l Q x y := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  have hn : n < succ_l n := (SecondOrderNaturalGraph.lt_succ_l hℳ n n).mpr le_rfl
  constructor
  · rintro ⟨i, hi, h⟩
    rcases eq_or_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ i n).mp hi) with rfl | hi
    · exact Or.inr h
    · exact Or.inl ⟨i, hi, h⟩
  · rintro (⟨i, hi, h⟩ | h)
    · exact ⟨i, lt_trans hi hn, h⟩
    · exact ⟨n, hn, h⟩

def evaluation_m {Γ Δ : SortContext signature_m} (T : Term signature_m Γ Δ .set)
    (p l c : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.conj (PrimitiveFormulas.pair_m (up l) (up c) (.bvar .here))
    (GraphSyntax.edge_m (up T) (up p) (.bvar .here)))

theorem evaluation_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (T : Term signature_m Γ Δ .set) (p l c : Term signature_m Γ Δ .num) :
    (evaluation_m T p l c).satisfies η ↔
      relation_l (T.eval η) (p.eval η) (value_l (l.eval η) (c.eval η)) := by
  simp only [evaluation_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, up, Term.eval_weakenBound, Term.eval]
  constructor
  · rintro ⟨a, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

def correct_m {Γ Δ : SortContext signature_m} (S T E Q : Term signature_m Γ Δ .set)
    (c l n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num (.imp (GraphSyntax.edge_m (up S) (up n) (.bvar .here))
    (.iff (evaluation_m (up T) (.bvar .here) (up l) (up c))
      (prefix_m (up E) (up Q) (up c) (up n))))

theorem correct_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (S T E Q : Term signature_m Γ Δ .set) (c l n : Term signature_m Γ Δ .num) :
    (correct_m S T E Q c l n).satisfies η ↔ ∀ p, relation_l (S.eval η) (n.eval η) p →
      (relation_l (T.eval η) p (value_l (l.eval η) (c.eval η)) ↔
        prefix_l (E.eval η) (Q.eval η) (c.eval η) (n.eval η)) := by
  simp only [correct_m, Formula.satisfies, SecondOrderPairing.edge_l,
    evaluation_formula_l, prefix_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem correct_l (hℳ : Theory.Models ℳ theory_m) {S E D Q R T : set_l ℳ}
    (hS : SecondOrderFiniteDisjunctionSyntax.spec_l S)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)
    (c l : num_l ℳ) (hc : SecondOrderAssignmentSyntax.valid_l E c l) :
    ∀ n p, relation_l S n p → (relation_l T p (value_l l c) ↔ prefix_l E Q c n) := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  let φ : Formula signature_m [] [.num, .set, .set, .set, .set, .num, .num] :=
    correct_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar .here)
  let η : Env ℳ [] [.set, .set, .set, .set, .num, .num] :=
    (((((Env.empty.pushFree l).pushFree c).pushFree Q).pushFree E).pushFree T).pushFree S
  apply induct_l hℳ φ (pure_language_m _ rfl) η
    (fun n => ∀ p, relation_l S n p → (relation_l T p (value_l l c) ↔ prefix_l E Q c n))
    (fun _ => correct_formula_l _ _ _ _ _ _ _ _) ?_ ?_
  · intro p hp
    obtain rfl := (SecondOrderFiniteDisjunctionSyntax.base_l hℳ hS p).mp hp
    constructor
    · intro h
      exact False.elim (SecondOrderEvaluationLogic.falsum_l hℳ E D Q R T hT _ h)
    · rintro ⟨i, hi, _⟩
      exact False.elim ((not_lt_of_ge (SecondOrderAlgebra.zero_le_l hℳ i)) hi)
  · intro n ih p hp
    obtain ⟨q, hq, rfl⟩ := (SecondOrderFiniteDisjunctionSyntax.successor_l hℳ hS n p).mp hp
    rw [SecondOrderFiniteDisjunctionSyntax.next_l,
      SecondOrderEvaluationLogic.disjunction_l hℳ E D Q R T hT l c _ _ hc,
      ih q hq, SecondOrderEvaluationEquations.equality_l hℳ E D Q R T hT l c _ _ hc]
    exact (prefix_successor_l hℳ E Q c n).symm

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteDisjunctionCorrectness
