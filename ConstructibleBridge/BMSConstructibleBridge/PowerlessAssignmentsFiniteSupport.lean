import BMSConstructibleBridge.PowerlessFiniteSupport
import BMSConstructibleBridge.PowerlessEvaluationOperator

/-!
# 完整有限赋值集存在性的实际有限核心支持

目标闭句保留原 omega_m 与 assignments_m；所有域和内部自然数一起量化。
所取有限支持只推出这一目标，不被声称足够解释全部层次或稳定关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentsFiniteSupport

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def sentence_m : Sentence ℒ := .forallE .set (.forallE .set (.imp
  (SecondOrderOmegaSyntax.omega_m (.bvar (.there .here)))
  (.existsE .set (PowerlessEvaluationOperator.assignments_m
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))))

theorem specification_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} :
    sentence_m.TrueIn ℳ ↔ ∀ ω A : carrier_l ℳ, omega_l ω →
      ∃ S, PowerlessEvaluationOperator.assignments_l ω A S := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l,
    PowerlessEvaluationOperator.assignments_formula_l]
  rfl

theorem sentence_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : sentence_m.TrueIn ℳ :=
  specification_l.mpr (fun _ A hω => PowerlessFiniteAssignments.all_exists_l hℳ hω A)

theorem finite_m : Nonempty (Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m) :=
  PowerlessFiniteSupport.finite_m (fun _ hℳ => sentence_l hℳ)

theorem models_l : ∃ Γ : List (Sentence ℒ), (∀ φ ∈ Γ, PowerlessTheory.theory_m φ) ∧
    Theory.SemanticallyEntails.{0, 0, 0, u} (Theory.ofList Γ) sentence_m :=
  PowerlessFiniteSupport.models_l (fun _ hℳ => sentence_l hℳ)

noncomputable def support_m : Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m :=
  Classical.choice finite_m

def theory_m : Theory ℒ := Theory.ofList support_m.sentences

theorem core_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m :=
  fun φ hφ => hℳ φ (support_m.subset φ hφ)

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (hℳ : Theory.Models ℳ theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) (A : carrier_l ℳ) :
    ∃ S, PowerlessEvaluationOperator.assignments_l ω A S :=
  (specification_l.mp (support_m.derivation.semantically_entails ℳ hℳ)) ω A hω

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentsFiniteSupport
