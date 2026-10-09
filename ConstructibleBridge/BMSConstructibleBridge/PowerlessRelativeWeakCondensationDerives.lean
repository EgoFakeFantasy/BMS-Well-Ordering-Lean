import BMSConstructibleBridge.PowerlessRelativeWeakCondensation

/-! # 相对弱凝聚的原 Z₂ 对象推导

目标是精确阶段集 J 的存在、原序数及极限资格和同一 T=Lⱼ[B]。来源
资格不在此模式中：任意实际 T 满足传递性、真实基础闭包、基对象成员、
真实 ω 覆盖及已证完整阶段／Def 结果即可。不向原核增加凝聚公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeWeakCondensationDerives

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def conclusion_m {Γ Δ : SortContext ℒ} (B T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <|
    .conj (PowerlessRelativeCollapseStageIndex.spec_m (up B) (up T) (.bvar .here)) <|
      .conj (PowerlessRelativeHierarchySyntax.ordinal_m (.bvar .here)) <|
        .conj (PowerlessRelativeHierarchySyntax.limit_m (.bvar .here))
          (PowerlessRelativeHierarchySyntax.level_m (up B) (.bvar .here) (up T))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem conclusion_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B T : Term ℒ Γ Δ .set) :
    (conclusion_m B T).satisfies η ↔ ∃ J,
      PowerlessRelativeCollapseStageIndex.spec_l (B.eval η) (T.eval η) J ∧
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (SecondOrderQuotient.structure_l hℳ)) J ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ J ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) J (T.eval η) := by
  simp only [conclusion_m, Formula.satisfies, PowerlessRelativeCollapseStageIndex.spec_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (B T ω : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchyDerives.transitive_m T) <|
      .imp (SecondOrderObjectSyntax.member_m B T) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <|
          .imp (ThirdOrderTheory.subset_m ω T) <|
            .imp (PowerlessRelativeFiniteHullAssignments.closed_m T) <|
              .imp (PowerlessRelativeCodedHistoryCollapseDerives.result_m B T) (conclusion_m B T)

def sentence_m {Δ : SortContext ℒ} (B T ω : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B T ω)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (B T ω : Term ℒ [] Δ .set) :
    (sentence_m B T ω).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hB hT hBT hω hωT hC hS
  have hB₀ := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mp hB
  have hT₀ := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η T).mp hT
  have hω₀ := (SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω
  have hωEq := SecondOrderOmega.unique_l hℳ hω₀ K.omega_spec
  have hωT₀ := (ThirdOrderSemantics.subset_formula_l η ω T).mp hωT
  have hC₀ := (PowerlessRelativeFiniteHullAssignments.closed_formula_l η T).mp hC
  have hS₀ := (PowerlessRelativeCodedHistoryCollapseDerives.result_formula_l K η B T).mp hS
  apply (conclusion_formula_l K η B T).mpr
  exact PowerlessRelativeWeakCondensation.exists_l K hB₀ hT₀ hBT
    (fun x hx => hωT₀ x (hωEq.symm ▸ hx)) hC₀
    (fun x hx => (hS₀ x hx).2.1) (fun x hx => (hS₀ x hx).2.2)

theorem derives_m {Δ : SortContext ℒ} (B T ω : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B T ω)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B T ω)

#print axioms conclusion_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeWeakCondensationDerives
