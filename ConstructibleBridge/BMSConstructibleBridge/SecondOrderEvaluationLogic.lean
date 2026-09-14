import BMSConstructibleBridge.SecondOrderFormulaCompilation

/-! # 完整源逻辑所需的派生求值方程 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationLogic

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderAssignmentSyntax (valid_l extension_l)
open SecondOrderEvaluationEquations (spec_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem falsum_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (a : num_l ℳ) : ¬ relation_l T (zero_l ℳ) a := by
  intro h
  obtain ⟨_, _, _, _, t, p, hp, _⟩ := (hT _ _).mp h
  exact nonzero_l hℳ (value_l t p) hp

theorem disjunction_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (l c p q : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (SecondOrderFormulaCompilation.disjunction_l p q) (value_l l c) ↔
      relation_l T p (value_l l c) ∨ relation_l T q (value_l l c) := by
  have hN := SecondOrderEvaluationEquations.negation_l hℳ E D Q R T hT l c
  have hC := SecondOrderEvaluationEquations.conjunction_l hℳ E D Q R T hT l c
  change relation_l T (SecondOrderEvaluationEquations.node_l 2
    (SecondOrderEvaluationEquations.node_l 3 (value_l
      (SecondOrderEvaluationEquations.node_l 2 p) (SecondOrderEvaluationEquations.node_l 2 q)))) (value_l l c) ↔ _
  rw [hN _ hc, hC _ _ hc, hN _ hc, hN _ hc]
  tauto

theorem implication_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (l c p q : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (SecondOrderFormulaCompilation.implication_l p q) (value_l l c) ↔
      (relation_l T p (value_l l c) → relation_l T q (value_l l c)) := by
  have hN := SecondOrderEvaluationEquations.negation_l hℳ E D Q R T hT l c
  have hC := SecondOrderEvaluationEquations.conjunction_l hℳ E D Q R T hT l c
  change relation_l T (SecondOrderEvaluationEquations.node_l 2
    (SecondOrderEvaluationEquations.node_l 3 (value_l p (SecondOrderEvaluationEquations.node_l 2 q)))) (value_l l c) ↔ _
  rw [hN _ hc, hC _ _ hc, hN _ hc]
  tauto

theorem biconditional_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (l c p q : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (SecondOrderFormulaCompilation.biconditional_l p q) (value_l l c) ↔
      (relation_l T p (value_l l c) ↔ relation_l T q (value_l l c)) := by
  change relation_l T (SecondOrderEvaluationEquations.node_l 3 (value_l
    (SecondOrderFormulaCompilation.implication_l p q) (SecondOrderFormulaCompilation.implication_l q p)))
      (value_l l c) ↔ _
  rw [SecondOrderEvaluationEquations.conjunction_l hℳ E D Q R T hT l c _ _ hc,
    implication_l hℳ E D Q R T hT l c _ _ hc, implication_l hℳ E D Q R T hT l c _ _ hc]
  exact Iff.intro (fun h => ⟨h.1, h.2⟩) (fun h => ⟨h.mp, h.mpr⟩)

theorem universal_l (hℳ : Theory.Models ℳ theory_m) (E D Q R T : set_l ℳ)
    (hT : spec_l E D Q R T) (l c p : num_l ℳ) (hc : valid_l E c l) :
    relation_l T (SecondOrderFormulaCompilation.universal_l p) (value_l l c) ↔
      ∀ x, mem_l x D → ∀ d, extension_l E c l d x → relation_l T p (value_l (succ_l l) d) := by
  classical
  change relation_l T (SecondOrderEvaluationEquations.node_l 2
    (SecondOrderEvaluationEquations.node_l 4 (SecondOrderEvaluationEquations.node_l 2 p))) (value_l l c) ↔ _
  rw [SecondOrderEvaluationEquations.negation_l hℳ E D Q R T hT l c _ hc,
    SecondOrderEvaluationEquations.existential_l hℳ E D Q R T hT l c _ hc]
  constructor
  · intro h x hx d hd
    by_contra h₀
    exact h ⟨x, d, hx, hd, (SecondOrderEvaluationEquations.negation_l hℳ E D Q R T hT
      (succ_l l) d p hd.1).mpr h₀⟩
  · intro h h₀
    obtain ⟨x, d, hx, hd, hN⟩ := h₀
    exact ((SecondOrderEvaluationEquations.negation_l hℳ E D Q R T hT (succ_l l) d p hd.1).mp hN)
      (h x hx d hd)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationLogic
