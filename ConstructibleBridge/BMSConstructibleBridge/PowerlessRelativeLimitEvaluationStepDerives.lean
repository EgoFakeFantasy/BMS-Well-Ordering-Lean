import BMSConstructibleBridge.PowerlessRelativeLimitEvaluationStep
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

/-! # 固定层内原求值步存在的原 Z₂ 推导

给定实际 ω、空集、全有限数值／赋值集和 ω 自映射，原求值算子的输出
仍属于同一非零极限层。参数 guard 包括历史；这是局部列存在，不是 Sat、
完整 Collection 或最终固定高度 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationStepDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def schema_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ [.set, .set, .set] Δ .set := .bvar (.there (.there .here))
    let β : Term ℒ [.set, .set, .set] Δ .set := .bvar (.there .here)
    let C : Term ℒ [.set, .set, .set] Δ .set := .bvar .here
    let w (t : Term ℒ [] Δ .set) := up (up (up t))
    .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
        .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
          .imp (parameters_m Δ C (fun v => .fvar v)) <|
            .imp (SecondOrderObjectSyntax.member_m (w S) C) <|
              .imp (SecondOrderOmegaSyntax.omega_m (w ω)) <|
                .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up (w e))))) <|
                  .imp (PowerlessFiniteSequencesSyntax.spec_m (w ω) (w ω) (w N)) <|
                    .imp (SecondOrderObjectSyntax.map_m (w T) (w ω) (w ω)) <|
                      .imp (PowerlessFiniteSequencesSyntax.spec_m (w ω) (w A) (w S)) <|
                        .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up C))
                          (PowerlessEvaluationStep.step_m (up (w ω)) (up (w e)) (up (w T)) (up (w A))
                            (up (w t₁)) (up (w t₂)) (up (w t₃)) (up (w S)) (up (w H)) (up (w n)) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω e N T A S t₁ t₂ t₃ H n)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω e N T A S t₁ t₂ t₃ H n : Term ℒ [] Δ .set) :
    (sentence_m ω e N T A S t₁ t₂ t₃ H n).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η B β C hBase hC hLimit hParams hSC hω he hN hT hS
  let ξ := ((η.pushBound B).pushBound β).pushBound C
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ξ
    (.bvar (.there (.there .here)))).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K ξ
    (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l
    (hℳ := hℳ) ξ (.bvar (.there .here))).mp hLimit
  have hParams' := (parameters_formula_l Δ ξ (.bvar .here) (fun v => .fvar v)).mp hParams
  have hω' := (omega_formula_l ξ (up (up (up ω)))).mp hω
  have hN' := (PowerlessFiniteSequencesSyntax.spec_formula_l ξ _ _ _).mp hN
  have hT' := (map_formula_l ξ _ _ _).mp hT
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l ξ _ _ _).mp hS
  have he' : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η) := by
    simpa only [PowerlessNatural.zero_l, ThirdOrderSemantics.member_l,
      Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval, up,
      Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using he
  have hSC' : mem_l hℳ ((up (up (up S))).eval ξ) C := hSC
  simp only [ξ, up, Term.eval_weakenBound] at hω' hN' hT' hS' hSC'
  have hParams'' : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C := hParams'
  obtain ⟨Y, hYC, hY⟩ := PowerlessRelativeLimitEvaluationStep.exists_l hBase' hLimit' hC'
    η ω e N T A S t₁ t₂ t₃ H n hParams'' hSC' hω' he' hN' hT' hS'
  refine ⟨Y, hYC, ?_⟩
  simpa only [PowerlessEvaluationStep.step_formula_l, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here] using hY

theorem derives_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ H n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m ω e N T A S t₁ t₂ t₃ H n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω e N T A S t₁ t₂ t₃ H n)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationStepDerives
