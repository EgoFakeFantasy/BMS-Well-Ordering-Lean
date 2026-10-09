import BMSConstructibleBridge.PowerlessRelativeCodedHistoryCollapseDerives
import BMSConstructibleBridge.PowerlessRelativeFiniteHullExtensionality

/-! # 同一有限元素性源域的合格坍缩实际存在

对象语言及推导核仍是原纯隶属图翻译／num/set Z₂。给定原首 Ω 来源、
共同族、真实种子成员／包含和操作闭包，实际 I 的类内可数性构造同一
坍缩 T/H。源域外延性与上邻居从真实共同族及实际母层推出，不作为
新的模型假设；目标域资格再由完整前史运输取得。

出口显式保留原 I 的 Class／类内可数性及来源守卫，未声称 T 本身是
Class 集合或实际层，也不是完整源 Collection 或最终固定高度良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedHistoryCollapseExistence

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- T/H 同时存在并保持同一 I，原类与 Def 读数覆盖全部目标成员。 -/
def conclusion_m {Γ Δ : SortContext ℒ} (I B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    .conj (PowerlessRelativeMembershipCollapse.spec_m (up (up I))
      (.bvar (.there .here)) (.bvar .here))
      (PowerlessRelativeCodedHistoryCollapseDerives.result_m (up (up B)) (.bvar (.there .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem conclusion_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (I B : Term ℒ Γ Δ .set) :
    (conclusion_m I B).satisfies ζ ↔ ∃ T H : SecondOrderQuotient.type_l hℳ,
      PowerlessRelativeMembershipCollapse.spec_l (I.eval ζ) T H ∧
      PowerlessRelativeCodedHistoryCollapseDerives.result_l (B.eval ζ) T := by
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeMembershipCollapse.spec_formula_l,
    PowerlessRelativeCodedHistoryCollapseDerives.result_formula_l K,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def schema_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W B ω : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W) <|
    .imp (ThirdOrderTheory.subset_m I W) <|
      .imp (parameters_m Δ I τ) <|
        .imp (SecondOrderObjectSyntax.member_m B I) <|
          .imp (SecondOrderObjectSyntax.member_m ω I) <|
            .imp (ThirdOrderTheory.subset_m B I) <|
              .imp (ThirdOrderTheory.subset_m ω I) <|
                .imp (PowerlessRelativeFiniteHullAssignments.closed_m I) <|
                  .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
                    .imp (PowerlessRelativeOrdinalCutoff.countable_m B ω I) <|
                      .imp (PowerlessRelativeFiniteElementarity.form_m Φ I W τ) (conclusion_m I B)

def sentence_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W B ω : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ I W B ω τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (sentence_m Φ I W B ω τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hSource hIW hParams hB hωI hBI hωSub hClosed hClass hCount hElem
  obtain ⟨hBase, hω, Ω, hΩ, hLevel⟩ :=
    (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ζ B ω W).mp hSource
  have hIW₀ := (ThirdOrderSemantics.subset_formula_l ζ I W).mp hIW
  have hClosed₀ := (PowerlessRelativeFiniteHullAssignments.closed_formula_l ζ I).mp hClosed
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  have hElem₀ := PowerlessRelativeFiniteElementarity.subfamily_formula_l
    (PowerlessRelativeFiniteHullExtensionality.family_m Δ) Φ hΦ₀ ζ I W τ hElem
  obtain ⟨hExt, hUpper⟩ := PowerlessRelativeFiniteHullExtensionality.level_l
    (B := B.eval ζ) (β := Ω) (I₁ := I.eval ζ) (W₁ := W.eval ζ) (ω := ω.eval ζ)
    ζ I W τ hBase hLimit hLevel (hIW₀ (ω.eval ζ) hωI) hIW₀ rfl rfl hElem₀
  obtain ⟨T, H, hH⟩ := PowerlessRelativeMembershipCollapse.exists_l (hBase := hBase) K hω
    ((PowerlessRelativeHierarchySemantics.class_formula_l K ζ B I).mp hClass)
    ((PowerlessRelativeOrdinalCutoff.countable_formula_l K ζ B ω I).mp hCount)
    hExt hUpper ⟨B.eval ζ, hB⟩
  apply (conclusion_formula_l K ζ I B).mpr
  refine ⟨T, H, hH, ?_⟩
  exact PowerlessRelativeCodedHistoryCollapseDerives.target_l K Φ hΦ ζ I W B ω τ T H
    hSource hIW₀ hParams hB hωI
    ((ThirdOrderSemantics.subset_formula_l ζ B I).mp hBI)
    ((ThirdOrderSemantics.subset_formula_l ζ ω I).mp hωSub) hClosed₀ hH hElem

theorem derives_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ I W B ω τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ I W B ω τ)

#print axioms conclusion_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedHistoryCollapseExistence
