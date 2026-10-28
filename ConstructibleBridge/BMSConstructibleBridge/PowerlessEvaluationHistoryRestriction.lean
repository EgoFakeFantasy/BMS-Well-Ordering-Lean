import BMSConstructibleBridge.PowerlessEvaluationHistoryUniqueness
import BMSConstructibleBridge.PowerlessRelativeHierarchyDerives

/-! # 求值历史限制及共同初段相容性

传递的定义域保证限制图不改变已有列的严格前史。把较长历史限制到较短
定义域后，用原商内部的唯一性识别图；不依赖宿主归纳或外部良基性。
这里只证明历史相容，不宣称尚未构造的统一查询图已属于相对类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationHistoryRestriction

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem trace_l {C ω e T A t₁ t₂ t₃ S F G n m : type_l hℳ}
    (hm : ∀ k, mem_l hℳ k m → ∀ x, mem_l hℳ x k → mem_l hℳ x m)
    (hF : PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C ω e T A t₁ t₂ t₃ S F n)
    (hG : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) G m C)
    (hHistory : PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) G F m) :
    PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C ω e T A t₁ t₂ t₃ S G m := by
  refine ⟨hG, fun k Y hValue => ?_⟩
  obtain ⟨hk, hValueF⟩ := (PowerlessRelativeLimitHistory.value_l hHistory).mp hValue
  obtain ⟨H, hH, hStep⟩ := hF.2 k Y hValueF
  refine ⟨H, (PowerlessRelativeLimitHistory.congr_l ?_).mp hH, hStep⟩
  intro x hx W
  exact ((PowerlessRelativeLimitHistory.value_l hHistory).trans (and_iff_right (hm k hk x hx))).symm

theorem exists_l {C ω e T A t₁ t₂ t₃ S F n m : type_l hℳ}
    (hm : ∀ k, mem_l hℳ k m → ∀ x, mem_l hℳ x k → mem_l hℳ x m)
    (hF : PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C ω e T A t₁ t₂ t₃ S F n)
    (hSubset : ∀ x, mem_l hℳ x m → mem_l hℳ x n) :
    ∃ G, PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C ω e T A t₁ t₂ t₃ S G m ∧
      PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) G F m := by
  obtain ⟨G, hG, hHistory⟩ := PowerlessRelativeLimitHistory.restrict_l hF.1 hSubset
  exact ⟨G, trace_l hm hF hG hHistory, hHistory⟩

theorem agrees_l {C D ω e T A t₁ t₂ t₃ S F G n m : type_l hℳ}
    (hn : ∀ k, mem_l hℳ k n → ∀ x, mem_l hℳ x k → mem_l hℳ x n)
    (hF : PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C ω e T A t₁ t₂ t₃ S F n)
    (hG : PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      D ω e T A t₁ t₂ t₃ S G m)
    (hSubset : ∀ x, mem_l hℳ x n → mem_l hℳ x m) {k : type_l hℳ} (hk : mem_l hℳ k n) (Y : type_l hℳ) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F k Y ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G k Y := by
  obtain ⟨J, hJ, hHistory⟩ := exists_l hn hG hSubset
  have hFJ : F = J := PowerlessEvaluationHistoryUniqueness.unique_l
    (PowerlessEvaluationFiniteHistory.original_l hF) (PowerlessEvaluationFiniteHistory.original_l hJ)
  subst J
  exact (PowerlessRelativeLimitHistory.value_l hHistory).trans (and_iff_right hk)

theorem query_l {C D ω e T A t₁ t₂ t₃ S F G n m k f : type_l hℳ}
    (hn : ∀ k, mem_l hℳ k n → ∀ x, mem_l hℳ x k → mem_l hℳ x n)
    (hF : PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C ω e T A t₁ t₂ t₃ S F n)
    (hG : PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      D ω e T A t₁ t₂ t₃ S G m)
    (hSubset : ∀ x, mem_l hℳ x n → mem_l hℳ x m) (hk : mem_l hℳ k n) :
    PowerlessEvaluationClause.query_l (ℳ := SecondOrderQuotient.structure_l hℳ) F k f ↔
      PowerlessEvaluationClause.query_l (ℳ := SecondOrderQuotient.structure_l hℳ) G k f := by
  apply exists_congr
  intro Y
  exact and_congr (agrees_l hn hF hG hSubset hk Y) Iff.rfl

def schema_m {Δ : SortContext ℒ} (C D ω e T A S t₁ t₂ t₃ F G n m k f : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m n) <|
    .imp (PowerlessEvaluationFiniteHistory.formula_m C ω e T A t₁ t₂ t₃ S F n) <|
      .imp (PowerlessEvaluationFiniteHistory.formula_m D ω e T A t₁ t₂ t₃ S G m) <|
        .imp (ThirdOrderTheory.subset_m n m) <|
          .imp (SecondOrderObjectSyntax.member_m k n) <|
            .iff (PowerlessEvaluationClause.query_m F k f) (PowerlessEvaluationClause.query_m G k f)

def sentence_m {Δ : SortContext ℒ} (C D ω e T A S t₁ t₂ t₃ F G n m k f : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m C D ω e T A S t₁ t₂ t₃ F G n m k f)

theorem derives_m {Δ : SortContext ℒ} (C D ω e T A S t₁ t₂ t₃ F G n m k f : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m C D ω e T A S t₁ t₂ t₃ F G n m k f)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hn hF hG hSubset hk
  have hn' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η n).mp hn
  have hF' := (PowerlessEvaluationFiniteHistory.formula_l η C ω e T A t₁ t₂ t₃ S F n).mp hF
  have hG' := (PowerlessEvaluationFiniteHistory.formula_l η D ω e T A t₁ t₂ t₃ S G m).mp hG
  have hSubset' := (subset_formula_l η n m).mp hSubset
  exact (PowerlessEvaluationClause.query_formula_l η F k f).trans
    ((query_l hn' hF' hG' hSubset' hk).trans (PowerlessEvaluationClause.query_formula_l η G k f).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationHistoryRestriction
