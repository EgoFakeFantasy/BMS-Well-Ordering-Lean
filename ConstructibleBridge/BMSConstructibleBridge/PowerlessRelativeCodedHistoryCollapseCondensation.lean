import BMSConstructibleBridge.PowerlessRelativeWeakCondensationDerives
import BMSConstructibleBridge.PowerlessRelativeCodedHistoryCollapseExistence

/-! # 实际有限元素性源域的弱凝聚坍缩

对象语言和正式推导仍为原纯隶属图翻译／num/set Z₂。沿用已证源存在
模式的全部守卫，实际构造同一 T/H，随后证明 T=Lⱼ[B] 及 T 的原相对
类资格。目标传递性、基对象成员、ω 覆盖和基础闭包从该 H 推出，不
另加目标模型、ClassT 或层资格假设。首 Ω 来源、I 的类内可数性及共同
族元素性仍保留；完整源 Collection、严格高度界和最终良序另待接通。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedHistoryCollapseCondensation

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 同一 T/H 保留原完整结果，并增加精确阶段集和目标类资格。 -/
def conclusion_m {Γ Δ : SortContext ℒ} (I B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    let T := .bvar (.there .here)
    let H := .bvar .here
    .conj (PowerlessRelativeMembershipCollapse.spec_m (up (up I)) T H) <|
      .conj (PowerlessRelativeCodedHistoryCollapseDerives.result_m (up (up B)) T) <|
        .conj (PowerlessRelativeWeakCondensationDerives.conclusion_m (up (up B)) T)
          (PowerlessRelativeHierarchySyntax.class_m (up (up B)) T)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem conclusion_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (I B : Term ℒ Γ Δ .set) :
    (conclusion_m I B).satisfies ζ ↔ ∃ T H : type_l hℳ,
      PowerlessRelativeMembershipCollapse.spec_l (I.eval ζ) T H ∧
      PowerlessRelativeCodedHistoryCollapseDerives.result_l (B.eval ζ) T ∧
      (∃ J, PowerlessRelativeCollapseStageIndex.spec_l (B.eval ζ) T J ∧
        SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
          (SecondOrderQuotient.structure_l hℳ)) J ∧
        PowerlessRelativeHierarchySemantics.limit_l hℳ J ∧
        PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval ζ) J T) ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ζ) T := by
  simp only [conclusion_m, Formula.satisfies, PowerlessRelativeMembershipCollapse.spec_formula_l,
    PowerlessRelativeCodedHistoryCollapseDerives.result_formula_l K,
    PowerlessRelativeWeakCondensationDerives.conclusion_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
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
  have hExists := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeCodedHistoryCollapseExistence.models_l hℳ Φ hΦ hΦ₀ I W B ω τ)
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hSource hIW hParams hB hωI hBI hωSub hClosed hClass hCount hElem
  obtain ⟨T, H, hH, hS⟩ :=
    (PowerlessRelativeCodedHistoryCollapseExistence.conclusion_formula_l K ζ I B).mp
      (hExists ζ hSource hIW hParams hB hωI hBI hωSub hClosed hClass hCount hElem)
  obtain ⟨hBase, hω, _, _, _⟩ :=
    (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ζ B ω W).mp hSource
  have hBI₀ := (ThirdOrderSemantics.subset_formula_l ζ B I).mp hBI
  have hωSub₀ := (ThirdOrderSemantics.subset_formula_l ζ ω I).mp hωSub
  have hClosed₀ := (PowerlessRelativeFiniteHullAssignments.closed_formula_l ζ I).mp hClosed
  have hFixedB := PowerlessRelativeMembershipCollapseBase.base_l hℳ
    (B.eval ζ) (I.eval ζ) T H hBase hBI₀ hH.2.1 hH.2.2.2.1 hB
  have hBT := (SecondOrderFunctionProperties.value_mem_l hℳ hH.2.1 hFixedB).2
  have hFixedω := PowerlessRelativeMembershipCollapseBase.fixed_l hℳ
    (ω.eval ζ) (I.eval ζ) T H
    (fun _ hx _ hy => SecondOrderOmegaTransitive.member_l hℳ hω hx hy)
    hωSub₀ hH.2.1 hH.2.2.2.1
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hωT (x : type_l hℳ) (hx : mem_l hℳ x K.omega) : mem_l hℳ x T :=
    (SecondOrderFunctionProperties.value_mem_l hℳ hH.2.1
      (hFixedω x (hωEq.symm ▸ hx))).2
  obtain ⟨J, hJ, hOrd, hLimit, hLevel⟩ := PowerlessRelativeWeakCondensation.exists_l K
    hBase hH.1 hBT hωT (PowerlessRelativeMembershipCollapseClosure.closed_l hH hClosed₀)
    (fun x hx => (hS x hx).2.1) (fun x hx => (hS x hx).2.2)
  exact (conclusion_formula_l K ζ I B).mpr ⟨T, H, hH, hS,
    ⟨J, hJ, hOrd, hLimit, hLevel⟩, PowerlessRelativeLevelClosure.class_l hℳ hBase hLevel⟩

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

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedHistoryCollapseCondensation
