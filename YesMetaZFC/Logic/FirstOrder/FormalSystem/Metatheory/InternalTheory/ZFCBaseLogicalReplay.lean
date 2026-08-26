import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedReplay

/-!
# 基础逻辑公理联合条件的对象层装配

本模块只处理十二类基础逻辑公理条件的嵌套析取装配。各具体公理回放模块只需
提供对应分支的对象层成员证明，避免重复展开同一段析取证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode

set_option autoImplicit false

/-- 将非空公式列表编码为右结合析取。 -/
def fs_zfc_support_raw_disj_chain : List SetFormula → SetFormula
  | [] => Formula.falsum
  | [formula] => formula
  | formula :: tail => formula ∨ₘ fs_zfc_support_raw_disj_chain tail

theorem fs_zfc_support_raw_disj_chain_admissible
    (parts : List SetFormula)
    (hParts :
      ∀ part, part ∈ parts → Formula.Admissible part) :
    Formula.Admissible (fs_zfc_support_raw_disj_chain parts) := by
  induction parts with
  | nil =>
      exact Formula.Admissible.falsum
  | cons head tail ih =>
      cases tail with
      | nil =>
          simpa [fs_zfc_support_raw_disj_chain] using
            hParts head (by simp)
      | cons second rest =>
          have hHead :
              Formula.Admissible head :=
            hParts head (by simp)
          have hTail :
              ∀ part, part ∈ second :: rest → Formula.Admissible part := by
            intro part hPart
            exact hParts part (by simp [hPart])
          have hTailAdmissible :
              Formula.Admissible
                (fs_zfc_support_raw_disj_chain (second :: rest)) :=
            ih hTail
          simpa [fs_zfc_support_raw_disj_chain] using
            Formula.Admissible.disj hHead hTailAdmissible

theorem fs_zfc_support_raw_disj_chain_of_member
    (parts : List SetFormula)
    (hParts :
      ∀ part, part ∈ parts → Formula.Admissible part)
    {part : SetFormula}
    (hPart : part ∈ parts)
    (hDerives :
      Derives fs_zfc_support_raw_theory [] part) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_support_raw_disj_chain parts) := by
  induction parts generalizing part with
  | nil =>
      simp at hPart
  | cons head tail ih =>
      cases tail with
      | nil =>
          have hEq : part = head := by
            simpa using hPart
          subst part
          simpa [fs_zfc_support_raw_disj_chain] using hDerives
      | cons second rest =>
          rcases List.mem_cons.mp hPart with hHead | hTail
          · have hEq : part = head := hHead
            subst part
            have hTailAdmissible :
                Formula.Admissible
                  (fs_zfc_support_raw_disj_chain (second :: rest)) :=
              fs_zfc_support_raw_disj_chain_admissible
                (second :: rest)
                (by
                  intro item hItem
                  exact hParts item (by simp [hItem]))
            simpa [fs_zfc_support_raw_disj_chain] using
              FirstOrder.Derives.disjIntroLeft
                hDerives
          · have hHeadAdmissible :
                Formula.Admissible head :=
              hParts head (by simp)
            have hTailDerives :
                Derives fs_zfc_support_raw_theory [] (
                  fs_zfc_support_raw_disj_chain (second :: rest)) :=
                ih
                (by
                  intro item hItem
                  exact hParts item (by simp [hItem]))
                hTail hDerives
            simpa [fs_zfc_support_raw_disj_chain] using
              FirstOrder.Derives.disjIntroRight
                hTailDerives

/-- 若每个析取分支都蕴含同一结论，则整个析取链也蕴含该结论。 -/
theorem fs_zfc_support_raw_disj_chain_imp
    (parts : List SetFormula)
    (conclusion : SetFormula)
    (hConclusion : Formula.Admissible conclusion)
    (hPart :
      ∀ part, part ∈ parts →
        Derives fs_zfc_support_raw_theory [] (part ⟶ₘ conclusion)) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_support_raw_disj_chain parts ⟶ₘ conclusion) := by
  induction parts with
  | nil =>
      change Derives fs_zfc_support_raw_theory [] (
        Formula.falsum ⟶ₘ conclusion)
      apply FirstOrder.Derives.impIntro
        (hAntecedentCheck :=
          Formula.check_admissible_complete Formula.Admissible.falsum)
      exact FirstOrder.Derives.falsumElim
        (FirstOrder.Derives.assumption
          (by simp)
          (Formula.check_admissible_complete Formula.Admissible.falsum))
        (Formula.check_admissible_complete hConclusion)
  | cons head tail ih =>
      cases tail with
      | nil =>
          simpa [fs_zfc_support_raw_disj_chain] using
            hPart head (by simp)
      | cons second rest =>
          have hHead :
              Derives fs_zfc_support_raw_theory [] (head ⟶ₘ conclusion) :=
            hPart head (by simp)
          have hTail :
              Derives fs_zfc_support_raw_theory []
                (fs_zfc_support_raw_disj_chain (second :: rest) ⟶ₘ
                  conclusion) :=
            ih (by
              intro part hMem
              exact hPart part (by simp [hMem]))
          have hHeadAdmissible : Formula.Admissible head :=
            Formula.Admissible.imp_left hHead.admissible
          have hTailAdmissible :
              Formula.Admissible
                (fs_zfc_support_raw_disj_chain (second :: rest)) :=
            Formula.Admissible.imp_left hTail.admissible
          have hDisjunctionAdmissible :
              Formula.Admissible
                (head ∨ₘ
                  fs_zfc_support_raw_disj_chain (second :: rest)) :=
            Formula.Admissible.disj hHeadAdmissible hTailAdmissible
          apply FirstOrder.Derives.impIntro
            (hAntecedentCheck :=
              Formula.check_admissible_complete
                hDisjunctionAdmissible)
          let Δ : Context signature :=
            [head ∨ₘ fs_zfc_support_raw_disj_chain (second :: rest)]
          change Δ ⊢ₘ[fs_zfc_support_raw_theory] conclusion
          apply FirstOrder.Derives.disjElim
            (FirstOrder.Derives.assumption
              (by simp [Δ])
              (Formula.check_admissible_complete
                hDisjunctionAdmissible))
          · exact FirstOrder.Derives.impElim
              (FirstOrder.Derives.context_weaken
                (Γ := [])
                (Δ := head :: Δ)
                (by simp [Δ])
                hHead)
              (FirstOrder.Derives.assumption
                (by simp [Δ])
                (Formula.check_admissible_complete
                  hHeadAdmissible))
          · exact FirstOrder.Derives.impElim
              (FirstOrder.Derives.context_weaken
                (Γ := [])
                (Δ := fs_zfc_support_raw_disj_chain (second :: rest) :: Δ)
                (by simp [Δ])
                hTail)
              (FirstOrder.Derives.assumption
                (by simp [Δ])
                (Formula.check_admissible_complete
                  hTailAdmissible))

/-- 十二类基础逻辑公理分支，顺序与 `base_logical_axiom_condition` 一致。 -/
def fs_zfc_support_raw_base_logical_axiom_branches
    (code : SetTerm) : List SetFormula :=
  [ code ∈ₘ ImpDistribAxiomsₘ,
    code ∈ₘ SelfImpAxiomsₘ,
    code ∈ₘ WeakeningAxiomsₘ,
    code ∈ₘ ContradictionAxiomsₘ,
    code ∈ₘ ClassicalAxiomsₘ,
    code ∈ₘ ExplosionAxiomsₘ,
    code ∈ₘ CaseAnalysisAxiomsₘ,
    code ∈ₘ SpecializationAxiomsₘ,
    code ∈ₘ ForallDistribAxiomsₘ,
    code ∈ₘ VacuousForallAxiomsₘ,
    code ∈ₘ EqualitySubstAxiomsₘ,
    code ∈ₘ EqualityReflAxiomsₘ ]

theorem fs_zfc_support_raw_base_logical_condition_of_member
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    {part : SetFormula}
    (hPart :
      part ∈ fs_zfc_support_raw_base_logical_axiom_branches code)
    (hDerives :
      Derives fs_zfc_support_raw_theory [] part) :
    Derives fs_zfc_support_raw_theory [] (
      base_logical_axiom_condition code) := by
  have hImplicationDistribution :
      Formula.Admissible (code ∈ₘ ImpDistribAxiomsₘ) :=
    membership_formula_admissible hCode
      implication_distribution_axiom_set_term_admissible
  have hSelfImplication :
      Formula.Admissible (code ∈ₘ SelfImpAxiomsₘ) :=
    membership_formula_admissible hCode
      self_implication_axiom_set_term_admissible
  have hWeakening :
      Formula.Admissible (code ∈ₘ WeakeningAxiomsₘ) :=
    membership_formula_admissible hCode
      weakening_axiom_set_term_admissible
  have hContradiction :
      Formula.Admissible (code ∈ₘ ContradictionAxiomsₘ) :=
    membership_formula_admissible hCode
      contradiction_axiom_set_term_admissible
  have hClassical :
      Formula.Admissible (code ∈ₘ ClassicalAxiomsₘ) :=
    membership_formula_admissible hCode
      classical_axiom_set_term_admissible
  have hExplosion :
      Formula.Admissible (code ∈ₘ ExplosionAxiomsₘ) :=
    membership_formula_admissible hCode
      explosion_axiom_set_term_admissible
  have hCaseAnalysis :
      Formula.Admissible (code ∈ₘ CaseAnalysisAxiomsₘ) :=
    membership_formula_admissible hCode
      case_analysis_axiom_set_term_admissible
  have hSpecialization :
      Formula.Admissible (code ∈ₘ SpecializationAxiomsₘ) :=
    membership_formula_admissible hCode
      specialization_axiom_set_term_admissible
  have hQuantifierDistribution :
      Formula.Admissible (code ∈ₘ ForallDistribAxiomsₘ) :=
    membership_formula_admissible hCode
      quantifier_distribution_axiom_set_term_admissible
  have hVacuousQuantifier :
      Formula.Admissible (code ∈ₘ VacuousForallAxiomsₘ) :=
    membership_formula_admissible hCode
      vacuous_quantifier_axiom_set_term_admissible
  have hEqualitySubstitution :
      Formula.Admissible (code ∈ₘ EqualitySubstAxiomsₘ) :=
    membership_formula_admissible hCode
      equality_substitution_axiom_set_term_admissible
  have hEqualityReflexivity :
      Formula.Admissible (code ∈ₘ EqualityReflAxiomsₘ) :=
    membership_formula_admissible hCode
      equality_reflexivity_axiom_set_term_admissible
  have hParts :
      ∀ item,
        item ∈ fs_zfc_support_raw_base_logical_axiom_branches code →
          Formula.Admissible item := by
    intro item hItem
    simp [fs_zfc_support_raw_base_logical_axiom_branches] at hItem
    rcases hItem with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact hImplicationDistribution
    · exact hSelfImplication
    · exact hWeakening
    · exact hContradiction
    · exact hClassical
    · exact hExplosion
    · exact hCaseAnalysis
    · exact hSpecialization
    · exact hQuantifierDistribution
    · exact hVacuousQuantifier
    · exact hEqualitySubstitution
    · exact hEqualityReflexivity
  have hChain :=
    fs_zfc_support_raw_disj_chain_of_member
      (fs_zfc_support_raw_base_logical_axiom_branches code)
      hParts hPart hDerives
  simpa [base_logical_axiom_condition,
    fs_zfc_support_raw_base_logical_axiom_branches,
    fs_zfc_support_raw_disj_chain] using hChain

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
