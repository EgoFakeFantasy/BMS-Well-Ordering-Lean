import BMSConstructibleBridge.PowerlessClassComprehension
import BMSConstructibleBridge.PowerlessClassAxioms

/-!
# 实际层次类结构满足完整无幂集核心

基础闭句由类传递性及真实集合闭包验证；分离与收集对任意
原 Project 模式及其任意环境回接，不限制公式复杂度或参数数目。
环境模型仍满足完整核心；本定理不是 Z₂ 解释或目标保持终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassCore

open Logic FirstOrder ThirdOrderSemantics PowerlessSourceWitnessDomain PowerlessSourceClass
open SetTheory.Definitional.Project

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessSourceClass.structure_l
  PowerlessSourceClass.type_l FirstOrderSemantics.reduct

universe u

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    {hP : ∃ x, domain_l ω e T t₁ t₂ t₃ x} :
    Theory.Models (structure_l (domain_l ω e T t₁ t₂ t₃) hP) PowerlessTheory.theory_m := by
  let P := domain_l ω e T t₁ t₂ t₃
  have hExt := PowerlessClassAxioms.ext_l (hP := hP) hℳ hω ht hT
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  cases hψ with
  | extensionality =>
    simp only [FirstOrder.Formula.TrueIn, fo_sentence, PowerlessTheory.extensionality_m,
      SetTheory.Definitional.Project.Sentence.ofFormula, fo_formula, fo_mem, fo_term, fo_bound_variable,
      FirstOrder.Formula.satisfies, Arguments.eval, FirstOrder.Term.eval,
      SetTheory.Definitional.Project.Formula.extensionalEq,
      SetTheory.Definitional.Project.Formula.pairArguments]
    change ∀ A B : type_l P, (∀ x : type_l P, member_l ℳ x.val A.val ↔ member_l ℳ x.val B.val) → A = B
    exact hExt.eq_of_same_members
  | empty =>
    exact (PowerlessTheory.sentence_l hExt _).mpr (PowerlessClassAxioms.empty_l hℳ hω ht hT)
  | pairing =>
    exact (PowerlessTheory.sentence_l hExt _).mpr (PowerlessClassAxioms.pairing_l hℳ hω ht hT)
  | union =>
    exact (PowerlessTheory.sentence_l hExt _).mpr (PowerlessClassAxioms.union_l hℳ hω ht hT)
  | infinity =>
    exact (PowerlessTheory.sentence_l hExt _).mpr (PowerlessClassAxioms.infinity_l hℳ hω ht hT)
  | foundation =>
    exact (PowerlessTheory.sentence_l hExt _).mpr (PowerlessClassAxioms.foundation_l hℳ hω ht hT)
  | separation φ =>
    apply (FirstOrderSemantics.sentence_correct hExt _).mpr
    intro f
    apply (SetTheory.Definitional.Project.Formula.satisfies_forallClosure_iff f
      (SetTheory.Axioms.Schema.separationCore φ)).mpr
    intro g
    let η : SetTheory.Env (FirstOrderSemantics.reduct (structure_l P hP)) _ := ⟨g, f⟩
    apply (SetTheory.Axioms.Schema.separation_sat_iff_d η φ).mpr
    intro A
    obtain ⟨B, hB⟩ := PowerlessClassComprehension.separation_l hℳ hω ht hT
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
    let η : SetTheory.Env (FirstOrderSemantics.reduct (structure_l P hP)) _ := ⟨g, f⟩
    apply (SetTheory.Axioms.Schema.collection_sat_iff_d η φ).mpr
    intro A h
    have hφ (x y : type_l P) :
        (fo_formula φ.body φ.freeClosed).satisfies
          (((PowerlessProjectEnvironment.env_l η).pushBound x).pushBound y) ↔
        SetTheory.Definitional.Project.Formula.satisfies ((η.push x).push y) φ.body := by
      simpa only [PowerlessProjectEnvironment.push_l] using
        PowerlessProjectEnvironment.formula_l hExt φ.body φ.freeClosed ((η.push x).push y)
    obtain ⟨B, hB⟩ := PowerlessClassComprehension.collection_l hℳ hω ht hT
      (fo_formula φ.body φ.freeClosed) (PowerlessProjectEnvironment.env_l η) A (by
        intro x hx
        obtain ⟨y, hy⟩ := h x hx
        exact ⟨y, (hφ x y).mpr hy⟩)
    refine ⟨B, fun x hx => ?_⟩
    obtain ⟨y, hy, h⟩ := hB x hx
    exact ⟨y, hy, (hφ x y).mp h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassCore

