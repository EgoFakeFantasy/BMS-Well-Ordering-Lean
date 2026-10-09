import BMSConstructibleBridge.PowerlessRelativeClassConstructorBounds
import BMSConstructibleBridge.PowerlessEvaluationFiniteHistory
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 有限历史的原求值递归方程

严格子码界使精确前史与整张有限图在所有递归查询处相同。
本结论允许任意模型内部长度，且条件式方程有原 Z₂ 推导。
它还不是全部良构码的满足语义或无限查询图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationPrefixEquation

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem exists_congr_l {ω A H F f i b n : type_l hℳ}
    (hHistory : PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) H F n)
    (hb : mem_l hℳ b n) :
    PowerlessEvaluationClause.exists_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω A H f i b ↔
      PowerlessEvaluationClause.exists_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω A F f i b := by
  unfold PowerlessEvaluationClause.exists_l
  apply exists_congr
  intro m
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply exists_congr
  intro a
  apply and_congr Iff.rfl
  apply exists_congr
  intro g
  exact and_congr Iff.rfl (and_congr Iff.rfl (PowerlessRelativeLimitHistory.query_l hHistory hb))

theorem clause_congr_l {ω e T A t₁ t₂ t₃ H F n f : type_l hℳ}
    (hHistory : PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) H F n)
    (hBounds : ∀ t a b, PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω e T t a b n → mem_l hℳ a n ∧ mem_l hℳ b n) :
    PowerlessEvaluationClause.clause_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω e T A t₁ t₂ t₃ H n f ↔
      PowerlessEvaluationClause.clause_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω e T A t₁ t₂ t₃ F n f := by
  unfold PowerlessEvaluationClause.clause_l
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  apply or_congr
  · apply exists_congr
    intro a
    apply exists_congr
    intro b
    apply and_congr_right
    intro hConstructor
    exact not_congr (and_congr
      (PowerlessRelativeLimitHistory.query_l hHistory (hBounds t₂ a b hConstructor).1)
      (PowerlessRelativeLimitHistory.query_l hHistory (hBounds t₂ a b hConstructor).2))
  · apply exists_congr
    intro i
    apply exists_congr
    intro b
    exact and_congr_right (fun hConstructor => exists_congr_l hHistory (hBounds t₃ i b hConstructor).2)

theorem equation_l {C ω e T A t₁ t₂ t₃ S F r n f : type_l hℳ}
    (hF : PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C ω e T A t₁ t₂ t₃ S F r) (hn : mem_l hℳ n r)
    (hBounds : ∀ t a b, PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω e T t a b n → mem_l hℳ a n ∧ mem_l hℳ b n) :
    PowerlessEvaluationClause.query_l (ℳ := SecondOrderQuotient.structure_l hℳ) F n f ↔
      mem_l hℳ f S ∧ PowerlessEvaluationClause.clause_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        ω e T A t₁ t₂ t₃ F n f := by
  obtain ⟨Y, ⟨_, hY⟩, _⟩ := hF.1.2 n hn
  obtain ⟨H, hHistory, hStep⟩ := hF.2 n Y hY
  have hRead : PowerlessEvaluationClause.query_l (ℳ := SecondOrderQuotient.structure_l hℳ) F n f ↔
      mem_l hℳ f Y := by
    constructor
    · rintro ⟨Z, hZ, hf⟩
      exact (PowerlessBMSQuotientRecursion.value_unique_l hF.1 hZ hY) ▸ hf
    · exact fun hf => ⟨Y, hY, hf⟩
  exact hRead.trans ((hStep f).trans (and_congr Iff.rfl (clause_congr_l hHistory hBounds)))

def schema_m {Δ : SortContext ℒ} (C ω e T A S t₁ t₂ t₃ F r n f : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeClassConstructorBounds.bounds_m ω e T) <|
    .imp (PowerlessEvaluationFiniteHistory.formula_m C ω e T A t₁ t₂ t₃ S F r) <|
      .imp (SecondOrderObjectSyntax.member_m n r) <|
        .iff (PowerlessEvaluationClause.query_m F n f)
          (.conj (SecondOrderObjectSyntax.member_m f S)
            (PowerlessEvaluationClause.clause_m ω e T A t₁ t₂ t₃ F n f))

def sentence_m {Δ : SortContext ℒ} (C ω e T A S t₁ t₂ t₃ F r n f : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m C ω e T A S t₁ t₂ t₃ F r n f)

theorem derives_m {Δ : SortContext ℒ} (C ω e T A S t₁ t₂ t₃ F r n f : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m C ω e T A S t₁ t₂ t₃ F r n f)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBounds hF hn
  have hBounds' := (PowerlessRelativeClassConstructorBounds.bounds_formula_l η ω e T).mp hBounds
  have hF' := (PowerlessEvaluationFiniteHistory.formula_l η C ω e T A t₁ t₂ t₃ S F r).mp hF
  exact (PowerlessEvaluationClause.query_formula_l η F n f).trans
    ((equation_l hF' hn (fun t a b h => hBounds' t a b (n.eval η) h)).trans
      (and_congr Iff.rfl (PowerlessEvaluationClause.clause_formula_l η ω e T A t₁ t₂ t₃ F n f)).symm)

#print axioms clause_congr_l
#print axioms equation_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationPrefixEquation
