import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEvaluationCountability
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramDomainEnumeration

/-! # 从实际字母表枚举到原求值像可数性的对象推导

调用者只提供字母表的实际 Class ω 满射，不再额外提供整个程序码域的
可数性。原码域枚举与精确求值函数消去这一中间前提；原层／算子守卫
仍明确保留，不能把本模块当作最终无条件 BMS 良序闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEnumeratedEvaluation

open Logic FirstOrder StabilityFrame PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q E e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B (fun v => .fvar v)) <|
    .imp (PowerlessRelativeFiniteProgramEvaluationBounded.guard_m φ B β C W ω Q e t₀ t₁ t₂ a) <|
      .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
        .imp (SecondOrderObjectSyntax.map_m E ω Q) <|
          .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m E ω Q)
            (PowerlessRelativeFiniteProgramEvaluationCountability.conclusion_m φ B C ω Q e t₀ t₁ t₂ a P)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q E e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W ω Q E e t₀ t₁ t₂ a S P)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q E e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W ω Q E e t₀ t₁ t₂ a S P).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hParams hGuard hDomain hMap hOnto
  have hParams' := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l
    K Δ η B (fun v => .fvar v)).mp hParams
  have hTerm (t : Term ℒ [] Δ .set) :
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t.eval η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hParams' _ v
    | .app f _ => nomatch f
  obtain ⟨hBase, _, _, _, _, _, hω, _, _, _, _, _, _, _⟩ :=
    (PowerlessRelativeFiniteProgramEvaluationBounded.guard_formula_l K
      φ η B β C W ω Q e t₀ t₁ t₂ a).mp hGuard
  have hD := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeFiniteProgramDomainEnumeration.models_l hℳ B ω Q E S P) η
  simp only [PowerlessRelativeFiniteProgramDomainEnumeration.schema_m, Formula.satisfies] at hD
  have hCount := hD
    ((PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mpr hBase)
    ((SecondOrderOmegaSyntax.omega_l hℳ η ω).mpr hω)
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B ω).mpr (hTerm ω))
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B Q).mpr (hTerm Q))
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B E).mpr (hTerm E))
    hMap hOnto hDomain
  have hI := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeFiniteProgramEvaluationCountability.models_l hℳ hφ
      B β C W ω Q e t₀ t₁ t₂ a S P) η
  simp only [PowerlessRelativeFiniteProgramEvaluationCountability.schema_m, Formula.satisfies] at hI
  exact hI hParams hGuard hDomain hCount

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q E e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W ω Q E e t₀ t₁ t₂ a S P)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 hφ B β C W ω Q E e t₀ t₁ t₂ a S P)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramEnumeratedEvaluation
