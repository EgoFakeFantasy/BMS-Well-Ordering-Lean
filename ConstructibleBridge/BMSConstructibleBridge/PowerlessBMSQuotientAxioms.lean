import BMSConstructibleBridge.PowerlessProjectEnvironment
import YesMetaZFC.SetTheory.Separation

/-!
# 原无幂集背景在 Z₂ 图商中的非收集公理

直接核验 `PowerlessTheory` 使用的 Project 公理及其原类型化翻译，不用另一套
相似公理表替代。完整分离允许任意参数和量词；唯一未在本模块证明的是 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientAxioms

open Logic FirstOrder
open SetTheory.Definitional.Project

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

theorem ext_l : SetTheory.Extensional (FirstOrderSemantics.reduct (quotient_l hℳ)) :=
  ⟨SecondOrderQuotient.ext_l hℳ⟩

/-- 绑定参数形式的分离，复用已有完整分离而不借用源 Collection。 -/
theorem separation_l {Γ : SortContext ℒ}
    (φ : FirstOrder.Formula ℒ (.set :: Γ) [])
    (η : FirstOrder.Env (quotient_l hℳ) Γ []) (A : SecondOrderQuotient.type_l hℳ) :
    ∃ B, ∀ x, SecondOrderQuotient.mem_l hℳ x B ↔
      SecondOrderQuotient.mem_l hℳ x A ∧ φ.satisfies (η.pushBound x) := by
  let σ : Substitution ℒ (.set :: Γ) [] [] (.set :: Γ) :=
    .map (fun v => .fvar v) (fun v => nomatch v)
  let θ : FirstOrder.Env (quotient_l hℳ) [] Γ := ⟨Assignment.empty, η.boundVal⟩
  obtain ⟨B, hB⟩ := (SecondOrderSeparationAxiom.schema_l hℳ (φ.substitute σ) θ).mp
    (SecondOrderSeparationAxiom.models_l hℳ (φ.substitute σ) θ) A
  refine ⟨B, fun x => (hB x).trans (and_congr Iff.rfl ?_)⟩
  refine (FirstOrder.Formula.satisfies_substitute (θ.pushFree x) σ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply FirstOrder.Env.ext
  · intro s v
    cases v <;> rfl
  · intro s v
    nomatch v

/-- 精确识别源理论所用收集实例的类型化像；不声称可判定或已经成立。 -/
def collection_m (ψ : FirstOrder.Sentence ℒ) : Prop :=
  ∃ (n : Nat) (φ : BinarySchema n), ψ = fo_sentence (SetTheory.Axioms.Schema.collection φ)

/-- 原理论的每个非收集公理均由任意原 Z₂ 模型的同一图商满足。 -/
theorem noncollection_l {ψ : FirstOrder.Sentence ℒ}
    (hψ : PowerlessTheory.theory_m ψ) (hNot : ¬ collection_m ψ) :
    ψ.TrueIn (quotient_l hℳ) := by
  obtain ⟨χ, hχ, rfl⟩ := hψ
  cases hχ with
  | extensionality =>
    simp only [FirstOrder.Formula.TrueIn, fo_sentence, PowerlessTheory.extensionality_m,
      SetTheory.Definitional.Project.Sentence.ofFormula, fo_formula, fo_mem, fo_term, fo_bound_variable,
      FirstOrder.Formula.satisfies, Arguments.eval, FirstOrder.Term.eval,
      SetTheory.Definitional.Project.Formula.extensionalEq,
      SetTheory.Definitional.Project.Formula.pairArguments]
    exact SecondOrderQuotient.ext_l hℳ
  | empty => exact (PowerlessTheory.sentence_l (ext_l hℳ) _).mpr (SecondOrderQuotient.empty_l hℳ)
  | pairing => exact (PowerlessTheory.sentence_l (ext_l hℳ) _).mpr (SecondOrderPairSet.models_l hℳ)
  | union => exact (PowerlessTheory.sentence_l (ext_l hℳ) _).mpr (SecondOrderUnion.models_l hℳ)
  | infinity => exact (PowerlessTheory.sentence_l (ext_l hℳ) _).mpr (SecondOrderInfinityAxiom.models_l hℳ)
  | foundation => exact (PowerlessTheory.sentence_l (ext_l hℳ) _).mpr (SecondOrderFoundation.models_l hℳ)
  | separation φ =>
    apply (FirstOrderSemantics.sentence_correct (ext_l hℳ) _).mpr
    intro f
    apply (SetTheory.Definitional.Project.Formula.satisfies_forallClosure_iff f
      (SetTheory.Axioms.Schema.separationCore φ)).mpr
    intro g
    let η : SetTheory.Env (FirstOrderSemantics.reduct (quotient_l hℳ)) _ := ⟨g, f⟩
    apply (SetTheory.Axioms.Schema.separation_sat_iff_d η φ).mpr
    intro A
    obtain ⟨B, hB⟩ := separation_l hℳ (fo_formula φ.body φ.freeClosed)
      (PowerlessProjectEnvironment.env_l η) A
    refine ⟨B, fun x => (hB x).trans (and_congr Iff.rfl ?_)⟩
    exact PowerlessProjectEnvironment.formula_l (ext_l hℳ) φ.body φ.freeClosed (η.push x)
  | collection φ => exact (hNot ⟨_, φ, rfl⟩).elim

/-- 支持列表的模型义务精确缩减到列表中实际出现的收集闭句。 -/
theorem finite_models_l (Γ : List (FirstOrder.Sentence ℒ))
    (hΓ : ∀ ψ ∈ Γ, PowerlessTheory.theory_m ψ)
    (hCollection : ∀ ψ ∈ Γ, collection_m ψ → ψ.TrueIn (quotient_l hℳ)) :
    Theory.Models (quotient_l hℳ) (Theory.ofList Γ) := by
  classical
  intro ψ hψ
  by_cases h : collection_m ψ
  · exact hCollection ψ hψ h
  · exact noncollection_l hℳ (hΓ ψ hψ) h

/-- 非收集原公理的图翻译具有真实 Z₂ 对象推导。 -/
theorem noncollection_derives_m {ψ : FirstOrder.Sentence ℒ}
    (hψ : PowerlessTheory.theory_m ψ) (hNot : ¬ collection_m ψ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m ψ) :=
  SecondOrderAxioms.interpretation_m ψ (fun _ hℳ => noncollection_l hℳ hψ hNot)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientAxioms
