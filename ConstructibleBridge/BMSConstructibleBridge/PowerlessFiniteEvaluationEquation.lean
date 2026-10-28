import BMSConstructibleBridge.PowerlessFiniteEvaluationClause
import BMSConstructibleBridge.PowerlessEvaluationPrefixEquation

/-! # 稳定有限查询的原四分支递归方程

任一覆盖当前编号的实际有限历史都可消去：子码严格下降，查询稳定。
条件式方程是原 Z₂ 的正式推导，不是完整 Sat 或最后的良序结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationEquation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem equation_l (K : source_coding_l hℳ) {B β C e N T A S t₁ t₂ t₃ Q F r n f : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C) (hωC : mem_l hℳ K.omega C)
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) e)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega A S)
    (hQ : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega C Q)
    (hr : mem_l hℳ r K.omega)
    (hF : PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C K.omega e T A t₁ t₂ t₃ S F r) (hn : mem_l hℳ n r)
    (hBounds : ∀ t a b, PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega e T t a b n → mem_l hℳ a n ∧ mem_l hℳ b n) :
    PowerlessFiniteEvaluationQuery.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C K.omega e N T A S t₁ t₂ t₃ Q n f ↔
      mem_l hℳ f S ∧ PowerlessFiniteEvaluationClause.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        C K.omega e N T A S t₁ t₂ t₃ Q n f := by
  have hrOrdinal : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) r :=
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec).mem hr
  have hRead := PowerlessFiniteEvaluationQuery.stable_l K hBase hLimit hC hωC he hN hT hS hQ hr hF hn (f := f)
  have hClause := PowerlessFiniteEvaluationClause.congr_l (f := f) hBounds (fun k hk g =>
    (PowerlessFiniteEvaluationQuery.stable_l K hBase hLimit hC hωC he hN hT hS hQ hr hF
      (hrOrdinal.transitive n hn k hk) (f := g)).symm)
  exact hRead.trans ((PowerlessEvaluationPrefixEquation.equation_l hF hn hBounds).trans
    (and_congr Iff.rfl hClause))

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def schema_m {Δ : SortContext ℒ} (B β C ω e N T A S t₁ t₂ t₃ Q F r n f : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
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
                        .imp (PowerlessRelativeClassConstructorBounds.bounds_m ω e T) <|
                          .imp (PowerlessEvaluationFiniteHistory.formula_m C ω e T A t₁ t₂ t₃ S F r) <|
                            .imp (SecondOrderObjectSyntax.member_m n r) <|
                              .iff (PowerlessFiniteEvaluationQuery.formula_m C ω e N T A S t₁ t₂ t₃ Q n f)
                                (.conj (SecondOrderObjectSyntax.member_m f S)
                                  (PowerlessFiniteEvaluationClause.formula_m C ω e N T A S t₁ t₂ t₃ Q n f))

def sentence_m {Δ : SortContext ℒ} (B β C ω e N T A S t₁ t₂ t₃ Q F r n f : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β C ω e N T A S t₁ t₂ t₃ Q F r n f)

theorem derives_m {Δ : SortContext ℒ} (B β C ω e N T A S t₁ t₂ t₃ Q F r n f : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β C ω e N T A S t₁ t₂ t₃ Q F r n f)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hC hLimit hω hωC he hN hT hS hQ hr hBounds hF hn
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K η B β C).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l (hℳ := hℳ) η β).mp hLimit
  have hω' := (omega_formula_l η ω).mp hω
  have hωEq := SecondOrderOmega.unique_l hℳ hω' K.omega_spec
  have he' : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η) := by
    simpa only [PowerlessNatural.zero_l, ThirdOrderSemantics.member_l, Formula.satisfies,
      SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here] using he
  have hN' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω ω N).mp hN
  have hT' := (map_formula_l η T ω ω).mp hT
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω A S).mp hS
  have hQ' := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω C Q).mp hQ
  have hωC' : mem_l hℳ (ω.eval η) (C.eval η) := hωC
  have hr' : mem_l hℳ (r.eval η) (ω.eval η) := hr
  have hBounds' := (PowerlessRelativeClassConstructorBounds.bounds_formula_l η ω e T).mp hBounds
  have hF' := (PowerlessEvaluationFiniteHistory.formula_l η C ω e T A t₁ t₂ t₃ S F r).mp hF
  rw [hωEq] at hN' hT' hS' hQ' hωC' hr' hBounds' hF'
  have hEquation := equation_l K (f := f.eval η) hBase' hLimit' hC' hωC' he' hN' hT' hS' hQ' hr' hF' hn
    (fun t a b h => hBounds' t a b (n.eval η) h)
  rw [← hωEq] at hEquation
  exact (PowerlessFiniteEvaluationQuery.formula_l η C ω e N T A S t₁ t₂ t₃ Q n f).trans
    (hEquation.trans (and_congr Iff.rfl (PowerlessFiniteEvaluationClause.formula_l η C ω e N T A S t₁ t₂ t₃ Q n f).symm))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationEquation
