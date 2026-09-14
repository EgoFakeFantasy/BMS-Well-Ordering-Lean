import BMSConstructibleBridge.ThirdOrderStageComprehension
import BMSConstructibleBridge.PowerlessMemberAxioms
import BMSConstructibleBridge.PowerlessProjectEnvironment

/-!
# 实际 Cκ 成员结构满足完整无幂集核心

基础公理来自传递性及极限层封闭；完整分离与收集来自初等早级。
模式逐一回接原 Project 语法桥，没有假定内部核心，也不声称任意早级满足核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageCore

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure
open SetTheory.Definitional.Project

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  FirstOrderSemantics.reduct

universe u

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)
    {hU₀ : ∃ x, member_l ℳ x U} :
    Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hUT := PowerlessStageStructure.transitive_l h₀ hω ht hT hU
  have hExt := PowerlessMemberAxioms.ext_l (hU₀ := hU₀) h₀ hUT
  have hκ₀ := ThirdOrderStageLimit.limit_l h₀ hω hκ
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  cases hψ with
  | extensionality =>
      simp only [FirstOrder.Formula.TrueIn, fo_sentence, PowerlessTheory.extensionality_m,
        SetTheory.Definitional.Project.Sentence.ofFormula, fo_formula, fo_mem, fo_term, fo_bound_variable,
        FirstOrder.Formula.satisfies, Arguments.eval, FirstOrder.Term.eval,
        SetTheory.Definitional.Project.Formula.extensionalEq,
        SetTheory.Definitional.Project.Formula.pairArguments]
      change ∀ A B : type_l U, (∀ x : type_l U, member_l ℳ x.val A.val ↔ member_l ℳ x.val B.val) → A = B
      exact hExt.eq_of_same_members
  | empty =>
      exact (PowerlessTheory.sentence_l hExt _).mpr (PowerlessMemberAxioms.empty_l h₀ hω ht hT hU hκ₀)
  | pairing =>
      exact (PowerlessTheory.sentence_l hExt _).mpr (PowerlessMemberAxioms.pairing_l h₀ hω ht hT hU hκ₀)
  | union =>
      exact (PowerlessTheory.sentence_l hExt _).mpr (PowerlessMemberAxioms.union_l h₀ hω ht hT hU hκ₀)
  | infinity =>
      exact (PowerlessTheory.sentence_l hExt _).mpr (PowerlessMemberAxioms.infinity_l h₀ hω ht hT hU
        (ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ))
  | foundation =>
      exact (PowerlessTheory.sentence_l hExt _).mpr (PowerlessMemberAxioms.foundation_l h₀ hUT)
  | separation φ =>
      apply (FirstOrderSemantics.sentence_correct hExt _).mpr
      intro f
      apply (SetTheory.Definitional.Project.Formula.satisfies_forallClosure_iff f
        (SetTheory.Axioms.Schema.separationCore φ)).mpr
      intro g
      let η : SetTheory.Env (FirstOrderSemantics.reduct (structure_l U hU₀)) _ := ⟨g, f⟩
      apply (SetTheory.Axioms.Schema.separation_sat_iff_d η φ).mpr
      intro A
      obtain ⟨B, hB⟩ := ThirdOrderStageComprehension.separation_l hℳ hω hκ ht hT hU
        (fo_formula φ.body φ.freeClosed) (PowerlessProjectEnvironment.env_l η) A
      refine ⟨B, fun x => (hB x).trans (and_congr Iff.rfl ?_)⟩
      have h := PowerlessProjectEnvironment.formula_l hExt φ.body φ.freeClosed (η.push x)
      simpa only [PowerlessProjectEnvironment.push_l] using h
  | collection φ =>
      apply (FirstOrderSemantics.sentence_correct hExt _).mpr
      intro f
      apply (SetTheory.Definitional.Project.Formula.satisfies_forallClosure_iff f
        (SetTheory.Axioms.Schema.collectionCore φ)).mpr
      intro g
      let η : SetTheory.Env (FirstOrderSemantics.reduct (structure_l U hU₀)) _ := ⟨g, f⟩
      apply (SetTheory.Axioms.Schema.collection_sat_iff_d η φ).mpr
      intro A h
      have hφ (x y : type_l U) :
          (fo_formula φ.body φ.freeClosed).satisfies
            (((PowerlessProjectEnvironment.env_l η).pushBound x).pushBound y) ↔
          SetTheory.Definitional.Project.Formula.satisfies ((η.push x).push y) φ.body := by
        simpa only [PowerlessProjectEnvironment.push_l] using
          PowerlessProjectEnvironment.formula_l hExt φ.body φ.freeClosed ((η.push x).push y)
      obtain ⟨B, hB⟩ := ThirdOrderStageComprehension.collection_l hℳ hω hκ ht hT hU
        (fo_formula φ.body φ.freeClosed) (PowerlessProjectEnvironment.env_l η) A (by
          intro x hx
          obtain ⟨y, hy⟩ := h x hx
          exact ⟨y, (hφ x y).mpr hy⟩)
      refine ⟨B, fun x hx => ?_⟩
      obtain ⟨y, hy, h⟩ := hB x hx
      exact ⟨y, hy, (hφ x y).mp h⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageCore
