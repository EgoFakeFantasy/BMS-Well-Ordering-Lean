import BMSConstructibleBridge.PowerlessFiniteEvaluationQuery
import BMSConstructibleBridge.PowerlessRelativeHierarchyDerives

/-! # 有限历史查询稳定性的原 Z₂ 对象推导

每个参数实例的闭句断言：在给定非零极限层及实际序列规格下，纯 Δ₀
查询与任一覆盖该索引的原历史查询等价。有限长度和层界全部显式保留。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationQueryDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def schema_m {Δ : SortContext ℒ} (B β C ω e N T A S t₁ t₂ t₃ Q F r k f : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <|
          .imp (SecondOrderObjectSyntax.member_m ω C) <|
            .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up e)))) <|
              .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω N) <|
                .imp (SecondOrderObjectSyntax.map_m T ω ω) <|
                  .imp (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
                    .imp (PowerlessFiniteSequencesSyntax.spec_m ω C Q) <|
                      .imp (SecondOrderObjectSyntax.member_m r ω) <|
                        .imp (PowerlessEvaluationFiniteHistory.formula_m C ω e T A t₁ t₂ t₃ S F r) <|
                          .imp (SecondOrderObjectSyntax.member_m k r) <|
                            .iff (PowerlessFiniteEvaluationQuery.formula_m C ω e N T A S t₁ t₂ t₃ Q k f)
                              (PowerlessEvaluationClause.query_m F k f)

def sentence_m {Δ : SortContext ℒ} (B β C ω e N T A S t₁ t₂ t₃ Q F r k f : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β C ω e N T A S t₁ t₂ t₃ Q F r k f)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β C ω e N T A S t₁ t₂ t₃ Q F r k f : Term ℒ [] Δ .set) :
    (sentence_m B β C ω e N T A S t₁ t₂ t₃ Q F r k f).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hC hLimit hω hωC he hN hT hS hQ hr hF hk
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K η B β C).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l (hℳ := hℳ) η β).mp hLimit
  have hω' := (omega_formula_l η ω).mp hω
  have hωEq := SecondOrderOmega.unique_l hℳ hω' K.omega_spec
  have hN' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω ω N).mp hN
  have hT' := (map_formula_l η T ω ω).mp hT
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω A S).mp hS
  have hQ' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω C Q).mp hQ
  have hF' := (PowerlessEvaluationFiniteHistory.formula_l η C ω e T A t₁ t₂ t₃ S F r).mp hF
  have hωC' : SecondOrderQuotient.mem_l hℳ (ω.eval η) (C.eval η) := hωC
  have hr' : SecondOrderQuotient.mem_l hℳ (r.eval η) (ω.eval η) := hr
  have he' : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η) := by
    simpa only [PowerlessNatural.zero_l, ThirdOrderSemantics.member_l, Formula.satisfies,
      SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here] using he
  rw [hωEq] at hN' hT' hS' hQ' hF' hωC' hr'
  apply (PowerlessFiniteEvaluationQuery.formula_l η C ω e N T A S t₁ t₂ t₃ Q k f).trans
  apply Iff.trans _ (PowerlessEvaluationClause.query_formula_l η F k f).symm
  simpa only [hωEq] using
    (PowerlessFiniteEvaluationQuery.stable_l K hBase' hLimit' hC' hωC' he' hN' hT' hS' hQ' hr' hF' hk
      (f := f.eval η))

theorem derives_m {Δ : SortContext ℒ} (B β C ω e N T A S t₁ t₂ t₃ Q F r k f : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β C ω e N T A S t₁ t₂ t₃ Q F r k f)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β C ω e N T A S t₁ t₂ t₃ Q F r k f)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationQueryDerives
