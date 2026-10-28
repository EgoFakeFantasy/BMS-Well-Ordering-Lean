import BMSConstructibleBridge.PowerlessRelativeClassDefinableFiniteTrace
import BMSConstructibleBridge.PowerlessDefinableFiniteTraceDerives

/-! # Class 内可定义有限轨迹的原 Z₂ 对象推导

每个原有限矩阵实例都有纯隶属句及原图翻译的正式可推导性。前提只
保留传递基底、ω、空初始索引、Class 初值、Class 逐点见证与内部长度。
输出同一原矩阵的实际 Class 有限图及 Class 陪域，不新增 Collection、
Class 完整分离、共同层界或无限轨迹存在假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDefinableFiniteTraceDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessBMSQuotientSubsetImageDerives (at_m at_formula_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def total_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <|
    .imp (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
      .existsE .set <| .conj
        (PowerlessRelativeHierarchySyntax.class_m (up (up B)) (.bvar .here))
        (at_m φ (.bvar (.there .here)) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω e a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B a) <|
          .imp (total_m φ B) <| .imp (SecondOrderObjectSyntax.member_m n ω)
            (PowerlessRelativeClassDefinableFiniteTrace.finite_m φ B e a n)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω e a n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B ω e a n)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B ω e a n : Term ℒ [] Δ .set) :
    (sentence_m φ B ω e a n).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, total_m, PowerlessDefinableFiniteTraceDerives.zero_m,
    Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassDefinableFiniteTrace.finite_formula_l K,
    at_formula_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hω he haC hTotal hn
  rw [SecondOrderOmega.unique_l hℳ hω K.omega_spec] at hn
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.eval η, hn⟩
  have hi' : (numberCode_l K i).val = n.eval η := congrArg Subtype.val hi
  have he' : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    exact iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x)
  rw [← hi']
  exact PowerlessRelativeClassDefinableFiniteTrace.exists_l K φ η B e a hBase haC he' hTotal i

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω e a n : Term ℒ [] Δ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B ω e a n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ B ω e a n)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDefinableFiniteTraceDerives
