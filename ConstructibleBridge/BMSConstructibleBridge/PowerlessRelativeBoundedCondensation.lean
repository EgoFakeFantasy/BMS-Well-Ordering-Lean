import BMSConstructibleBridge.PowerlessRelativeCodedHistoryCollapseCondensation
import BMSConstructibleBridge.PowerlessRelativeCodedHistoryCollapseBound
import BMSConstructibleBridge.PowerlessRelativeFiniteHullOmegaCoverage

/-! # 实际源域的有界弱凝聚存在模式

对象语言为原纯隶属语言，出口是原 Z₂ GraphTranslation 的普通 Derives。
从实际共同族消去操作闭包与 ω 覆盖守卫，在证明内构造同一 T/H/J，并取得原 T=Lⱼ[B]、
T⊆W、J⊆Ω 及各项原资格。不预供目标、坍缩图或凝聚高度；严格 J<Ω、
源 Collection 和最终 hSources 消去不在此结论中。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeBoundedCondensation

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  (((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
    SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set

def conclusion_m {Γ Δ : SortContext ℒ} (I B W ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let T := .bvar (.there (.there (.there .here)))
    let H := .bvar (.there (.there .here))
    let J := .bvar (.there .here)
    let Ω := .bvar .here
    .conj (PowerlessRelativeMembershipCollapse.spec_m (up₄ I) T H) <|
      .conj (PowerlessRelativeCodedHistoryCollapseDerives.result_m (up₄ B) T) <|
        .conj (PowerlessRelativeCollapseStageIndex.spec_m (up₄ B) T J) <|
          .conj (PowerlessRelativeHierarchySyntax.ordinal_m J) <|
            .conj (PowerlessRelativeHierarchySyntax.limit_m J) <|
              .conj (PowerlessRelativeHierarchySyntax.level_m (up₄ B) J T) <|
                .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) T) <|
                  .conj (PowerlessRelativeOrdinalCutoff.first_m (up₄ B) (up₄ ω) Ω) <|
                    .conj (PowerlessRelativeHierarchySyntax.level_m (up₄ B) Ω (up₄ W)) <|
                      .conj (ThirdOrderTheory.subset_m T (up₄ W)) (ThirdOrderTheory.subset_m J Ω)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem conclusion_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (I B W ω : Term ℒ Γ Δ .set) :
    (conclusion_m I B W ω).satisfies ζ ↔ ∃ T H J Ω : type_l hℳ,
      PowerlessRelativeMembershipCollapse.spec_l (I.eval ζ) T H ∧
      PowerlessRelativeCodedHistoryCollapseDerives.result_l (B.eval ζ) T ∧
      PowerlessRelativeCollapseStageIndex.spec_l (B.eval ζ) T J ∧
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (SecondOrderQuotient.structure_l hℳ)) J ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ J ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval ζ) J T ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) T ∧
      PowerlessRelativeOrdinalCutoff.first_l (B.eval ζ) (ω.eval ζ) Ω ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval ζ) Ω (W.eval ζ) ∧
      (∀ x, mem_l hℳ x T → mem_l hℳ x (W.eval ζ)) ∧
      ∀ a, mem_l hℳ a J → mem_l hℳ a Ω := by
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeMembershipCollapse.spec_formula_l,
    PowerlessRelativeCodedHistoryCollapseDerives.result_formula_l K,
    PowerlessRelativeCollapseStageIndex.spec_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.first_formula_l K, ThirdOrderSemantics.subset_formula_l,
    ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    up₄, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def schema_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W) <|
    .imp (ThirdOrderTheory.subset_m I W) <| .imp (parameters_m Δ I τ) <|
      .imp (SecondOrderObjectSyntax.member_m B I) <| .imp (SecondOrderObjectSyntax.member_m ω I) <|
        .imp (ThirdOrderTheory.subset_m B I) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
            .imp (PowerlessRelativeOrdinalCutoff.countable_m B ω I) <|
              .imp (PowerlessRelativeFiniteElementarity.form_m Φ I W τ) (conclusion_m I B W ω)

def sentence_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ I W B ω τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (sentence_m Φ I W B ω τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hExists := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeCodedHistoryCollapseCondensation.models_l hℳ Φ hΦ hΦ₀ I W B ω τ)
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hSource hIW hParams hB hωI hBI hClass hCount hElem
  obtain ⟨hClosed₀, hωSub₀⟩ := PowerlessRelativeFiniteHullOmegaCoverage.target_l K Φ hΦ hΦ₁
    ζ I W B ω τ hSource ((ThirdOrderSemantics.subset_formula_l ζ I W).mp hIW)
    hParams hB hωI hElem
  have hClosed := (PowerlessRelativeFiniteHullAssignments.closed_formula_l ζ I).mpr hClosed₀
  have hωSub := (ThirdOrderSemantics.subset_formula_l ζ ω I).mpr hωSub₀
  obtain ⟨T, H, hH, hS, ⟨J, hJ, hOrd, hLimit, hJT⟩, hTClass⟩ :=
    (PowerlessRelativeCodedHistoryCollapseCondensation.conclusion_formula_l K ζ I B).mp
      (hExists ζ hSource hIW hParams hB hωI hBI hωSub hClosed hClass hCount hElem)
  obtain ⟨hTW, Ω, hΩ, hΩW, hBound⟩ := PowerlessRelativeCodedHistoryCollapseBound.target_l
    K Φ hΦ ζ I W B ω τ T H hSource
    ((ThirdOrderSemantics.subset_formula_l ζ I W).mp hIW) hParams hB hωI
    ((ThirdOrderSemantics.subset_formula_l ζ B I).mp hBI)
    ((ThirdOrderSemantics.subset_formula_l ζ ω I).mp hωSub)
    ((PowerlessRelativeFiniteHullAssignments.closed_formula_l ζ I).mp hClosed) hH hElem
  exact (conclusion_formula_l K ζ I B W ω).mpr
    ⟨T, H, J, Ω, hH, hS, hJ, hOrd, hLimit, hJT, hTClass, hΩ, hΩW, hTW, hBound J hJ⟩

theorem derives_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m Φ I W B ω τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ hΦ₁ I W B ω τ)

#print axioms conclusion_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeBoundedCondensation
