import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEnumeratedEvaluation
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramAlphabetEnumeration

/-! # 从实际常量种子枚举到原求值精确像可数性

具体三类指令的枚举消去原 E:ω→Q 前提，再枚举同一原程序域，构造实际
求值函数和精确像。仍要求常量种子的实际 Class 满射及原算子／层守卫；
本模块不假定求值像属于 W，也不把这些条件当作终局已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramSeedEvaluation

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B (fun v => .fvar v)) <|
    .imp (PowerlessRelativeFiniteProgramEvaluationBounded.guard_m φ B β C W ω Q e t₀ t₁ t₂ a) <|
      .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
        .imp (SecondOrderObjectSyntax.map_m G ω C) <|
          .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
            .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q)
              (PowerlessRelativeFiniteProgramEvaluationCountability.conclusion_m φ B C ω Q e t₀ t₁ t₂ a P)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W ω Q G e t₀ t₁ t₂ a S P)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W ω Q G e t₀ t₁ t₂ a S P).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hParams hGuard hDomain hMap hOnto hAlphabet
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
  have hE := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeFiniteProgramAlphabetEnumeration.models_l hℳ B C ω G t₀ t₁ t₂ Q) η
  simp only [PowerlessRelativeFiniteProgramAlphabetEnumeration.schema_m, Formula.satisfies] at hE
  have hEnum := hE
    ((PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η B).mpr hBase)
    ((SecondOrderOmegaSyntax.omega_l hℳ η ω).mpr hω)
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B ω).mpr (hTerm ω))
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B C).mpr (hTerm C))
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B G).mpr (hTerm G))
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B t₀).mpr (hTerm t₀))
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B t₁).mpr (hTerm t₁))
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B t₂).mpr (hTerm t₂))
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B Q).mpr (hTerm Q))
    hMap hOnto hAlphabet
  obtain ⟨E, hEC, hEMap, hEOnto⟩ :=
    (PowerlessRelativeFiniteProgramAlphabetEnumeration.conclusion_l K η B ω Q).mp hEnum
  let O : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨ω.eval η, hTerm ω⟩
  let A : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨Q.eval η, hTerm Q⟩
  let F : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨E, hEC⟩
  obtain ⟨_, _, _, hCount⟩ := PowerlessRelativeFiniteProgramDomainEnumeration.exists_l
    (hBase := hBase) K
    ((PowerlessRelativeClassOmegaAbsolute.omega_l O).mpr hω)
    ((PowerlessRelativeClassFunctionAbsolute.map_l F O A).mpr hEMap)
    ((PowerlessRelativeClassFunctionAbsolute.onto_l F O A).mpr hEOnto)
    ((PowerlessRelativeFiniteProgramDomain.domain_formula_l K η B ω Q S P).mp hDomain)
  have hI := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeFiniteProgramEvaluationCountability.models_l hℳ hφ
      B β C W ω Q e t₀ t₁ t₂ a S P) η
  simp only [PowerlessRelativeFiniteProgramEvaluationCountability.schema_m, Formula.satisfies] at hI
  exact hI hParams hGuard hDomain
    ((PowerlessRelativeOrdinalCutoff.countable_formula_l K η B ω P).mpr hCount)

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W ω Q G e t₀ t₁ t₂ a S P)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 hφ B β C W ω Q G e t₀ t₁ t₂ a S P)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramSeedEvaluation
