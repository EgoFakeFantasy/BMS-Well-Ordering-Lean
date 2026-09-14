import BMSConstructibleBridge.SecondOrderEvaluationCongruence

/-!
# 内部求值的构造子方程

验证相等、成员、否定、合取及存在量词的递归方程。存在量词对任意正确前插
码给出同一真值，不依赖选出的表示。源公式编译及 Def 仍是后续义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderSequenceSyntax (read_l)
open SecondOrderAssignmentSyntax (valid_l extension_l)
open SecondOrderEvaluationRule (atomic_l conjunction_l existential_l cases_l rule_l numeral_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

noncomputable def node_l (k : Nat) (p : num_l ℳ) : num_l ℳ :=
  SecondOrderFormulaCode.node_l (numeral_l ℳ k) p

def spec_l (E D Q R T : set_l ℳ) : Prop := ∀ n a, relation_l T n a ↔ rule_l E D Q R T n a

theorem numeral_eq_l (hℳ : Theory.Models ℳ theory_m) (i j : Nat) :
    numeral_l ℳ i = numeral_l ℳ j ↔ i = j := by
  constructor
  · intro h
    by_contra h₀
    exact (SecondOrderArithmetic.numeral_ne_m (Γ := []) (Δ := []) i j h₀).sound hℳ Env.empty
      (by intro φ hφ; cases hφ) h
  · rintro rfl
    rfl

theorem node_case_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (k : Nat) (p l c : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (node_l k p) (value_l l c) ↔ cases_l E D Q R T l c (numeral_l ℳ k) p (value_l l c) := by
  rw [hT, SecondOrderEvaluationCongruence.state_l hℳ, and_iff_right hc]
  constructor
  · rintro ⟨t, q, h, hq⟩
    obtain ⟨rfl, rfl⟩ := SecondOrderFormulaCode.injective_l hℳ t q (numeral_l ℳ k) p h
    exact hq
  · intro h
    exact ⟨_, p, rfl, h⟩

theorem atomic_decode_l (hℳ : Theory.Models ℳ theory_m) (E Q : set_l ℳ) (c i j : num_l ℳ) :
    atomic_l E Q c (value_l i j) ↔ ∃ x y, read_l E c i x ∧ read_l E c j y ∧ relation_l Q x y := by
  constructor
  · rintro ⟨a, b, x, y, h, hx, hy, hQ⟩
    obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ a b i j h
    exact ⟨x, y, hx, hy, hQ⟩
  · rintro ⟨x, y, hx, hy, hQ⟩
    exact ⟨i, j, x, y, rfl, hx, hy, hQ⟩

theorem equality_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (l c i j : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (node_l 0 (value_l i j)) (value_l l c) ↔
      ∃ x y, read_l E c i x ∧ read_l E c j y ∧ relation_l Q x y := by
  have h := node_case_l hℳ E D Q R T hT 0 (value_l i j) l c hc
  simp [cases_l, numeral_eq_l hℳ] at h
  exact h.trans (atomic_decode_l hℳ E Q c i j)

theorem membership_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (l c i j : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (node_l 1 (value_l i j)) (value_l l c) ↔
      ∃ x y, read_l E c i x ∧ read_l E c j y ∧ relation_l R x y := by
  have h := node_case_l hℳ E D Q R T hT 1 (value_l i j) l c hc
  simp [cases_l, numeral_eq_l hℳ] at h
  exact h.trans (atomic_decode_l hℳ E R c i j)

theorem negation_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (l c p : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (node_l 2 p) (value_l l c) ↔ ¬ relation_l T p (value_l l c) := by
  simpa [cases_l, numeral_eq_l hℳ] using node_case_l hℳ E D Q R T hT 2 p l c hc

theorem conjunction_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (l c p q : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (node_l 3 (value_l p q)) (value_l l c) ↔
      relation_l T p (value_l l c) ∧ relation_l T q (value_l l c) := by
  have h : relation_l T (node_l 3 (value_l p q)) (value_l l c) ↔
      SecondOrderEvaluationRule.conjunction_l T (value_l p q) (value_l l c) := by
    simpa [cases_l, numeral_eq_l hℳ] using node_case_l hℳ E D Q R T hT 3 (value_l p q) l c hc
  refine h.trans ?_
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ i j p q hij
    exact ⟨hi, hj⟩
  · rintro ⟨hp, hq⟩
    exact ⟨p, q, rfl, hp, hq⟩

theorem existential_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (l c p : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (node_l 4 p) (value_l l c) ↔
      ∃ x d, mem_l x D ∧ extension_l E c l d x ∧ relation_l T p (value_l (succ_l l) d) := by
  have h : relation_l T (node_l 4 p) (value_l l c) ↔ SecondOrderEvaluationRule.existential_l E D T l c p := by
    simpa [cases_l, numeral_eq_l hℳ] using node_case_l hℳ E D Q R T hT 4 p l c hc
  refine h.trans ?_
  constructor
  · rintro ⟨x, d, a, hx, hd, rfl, ha⟩
    exact ⟨x, d, hx, hd, ha⟩
  · rintro ⟨x, d, hx, hd, ha⟩
    exact ⟨x, d, _, hx, hd, rfl, ha⟩

/-- 两个正确前插码在全部内部公式上的求值相同。 -/
theorem extension_value_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (l c d e x p : num_l ℳ)
    (hd : extension_l E c l d x) (he : extension_l E c l e x) :
    relation_l T p (value_l (succ_l l) d) ↔ relation_l T p (value_l (succ_l l) e) :=
  SecondOrderEvaluationCongruence.congr_l hℳ E D Q R T hT p (succ_l l) d e
    (SecondOrderAssignmentCongruence.extension_same_l hℳ E c l d e x hd he)

/-- 存在量词可对选中域元素的任意正确前插表示求值。 -/
theorem existential_all_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (D Q R T : set_l ℳ) (hT : spec_l E D Q R T)
    (l c p : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (node_l 4 p) (value_l l c) ↔
      ∃ x, mem_l x D ∧ ∀ d, extension_l E c l d x → relation_l T p (value_l (succ_l l) d) := by
  rw [existential_l hℳ E D Q R T hT l c p hc]
  constructor
  · rintro ⟨x, d, hx, hd, h⟩
    exact ⟨x, hx, fun e he => (extension_value_l hℳ E D Q R T hT l c d e x p hd he).mp h⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l x hc
    exact ⟨x, d, hx, hd, h d hd⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationEquations
