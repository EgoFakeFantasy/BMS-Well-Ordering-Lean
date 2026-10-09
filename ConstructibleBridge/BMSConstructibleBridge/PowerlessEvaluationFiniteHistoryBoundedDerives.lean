import BMSConstructibleBridge.PowerlessEvaluationFiniteHistoryBounded
import BMSConstructibleBridge.PowerlessRelativeHierarchyDerives

/-! # 有限历史有界化等价的原 Z₂ 推导

层界、内部有限长度及实际序列集的规格均保留为对象前提；结论是原求值
历史与纯 Δ₀ 检查的等价式。没有把局部求值检查当作完整语义正确性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFiniteHistoryBoundedDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def schema_m {Δ : SortContext ℒ} (B β C ω e N T A S t₁ t₂ t₃ F n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <|
          .imp (SecondOrderObjectSyntax.member_m ω C) <|
            .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up e)))) <|
              .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω N) <|
                .imp (SecondOrderObjectSyntax.map_m T ω ω) <|
                  .imp (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
                    .imp (SecondOrderObjectSyntax.member_m n ω) <|
                      .iff (PowerlessEvaluationFiniteHistoryBounded.formula_m C ω e N T A S t₁ t₂ t₃ F n)
                        (PowerlessEvaluationFiniteHistory.formula_m C ω e T A t₁ t₂ t₃ S F n)

def sentence_m {Δ : SortContext ℒ} (B β C ω e N T A S t₁ t₂ t₃ F n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β C ω e N T A S t₁ t₂ t₃ F n)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β C ω e N T A S t₁ t₂ t₃ F n : Term ℒ [] Δ .set) :
    (sentence_m B β C ω e N T A S t₁ t₂ t₃ F n).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hC hLimit hω hωC he hN hT hS hn
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K η B β C).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l (hℳ := hℳ) η β).mp hLimit
  have hω' := (omega_formula_l η ω).mp hω
  have hωEq := SecondOrderOmega.unique_l hℳ hω' K.omega_spec
  have hN' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω ω N).mp hN
  have hT' := (map_formula_l η T ω ω).mp hT
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω A S).mp hS
  have hωC' : SecondOrderQuotient.mem_l hℳ (ω.eval η) (C.eval η) := hωC
  have hn' : SecondOrderQuotient.mem_l hℳ (n.eval η) (ω.eval η) := hn
  have he' : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η) := by
    simpa only [PowerlessNatural.zero_l, ThirdOrderSemantics.member_l, Formula.satisfies,
      SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here] using he
  rw [hωEq] at hN' hT' hS' hωC' hn'
  apply (PowerlessEvaluationFiniteHistoryBounded.formula_l η C ω e N T A S t₁ t₂ t₃ F n).trans
  apply Iff.trans _ (PowerlessEvaluationFiniteHistory.formula_l η C ω e T A t₁ t₂ t₃ S F n).symm
  simpa only [hωEq] using
    (PowerlessEvaluationFiniteHistoryBounded.trace_iff_l K hBase' hLimit' hC' hωC' he' hN' hT' hS' hn'
      (t₁ := t₁.eval η) (t₂ := t₂.eval η) (t₃ := t₃.eval η) (F := F.eval η))

theorem derives_m {Δ : SortContext ℒ} (B β C ω e N T A S t₁ t₂ t₃ F n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B β C ω e N T A S t₁ t₂ t₃ F n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β C ω e N T A S t₁ t₂ t₃ F n)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationFiniteHistoryBoundedDerives
