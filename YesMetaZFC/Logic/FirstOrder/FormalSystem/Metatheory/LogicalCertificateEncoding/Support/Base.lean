import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncodingSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedSequenceCodeSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding

/-!
# 基础逻辑证书的自由变量支持

本模块逐类封装十二种基础 Hilbert 证书的公开语法依赖。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace CertifiedProof

open Nonlogical.BasicSetTheory
open GodelQuotation
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 单公式 payload 组件只依赖公式码与其数值编码。 -/
theorem logical_formula_payload_component_condition_with_ids_freeSupport_subset
    (formulaCode numericCode : SetTerm)
    (traceId indexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_formula_payload_component_condition_with_ids
              formulaCode numericCode traceId indexId) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport numericCode := by
  intro freeVariable hMember
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formulaCode
  · exact Or.inl hFormula
  by_cases hNumeric :
      freeVariable ∈ Term.freeSupport numericCode
  · exact Or.inr hNumeric
  · exfalso
    simp_all [
      logical_formula_payload_component_condition_with_ids,
      Formula.freeSupport,
      Term.freeSupportList, List.mem_append] <;>
    grind [
      fs_formula_replay_condition_freeSupport_subset,
      nat_sequence_code_condition_with_ids_freeSupport_subset]

/-- 单公式 payload 组件的公开自由支持精确来自两个入口项。 -/
@[simp]
theorem mem_freeSupport_logical_formula_payload_component_condition_with_ids_iff
    (freeVariable : FreeVariable signature)
    (formulaCode numericCode : SetTerm)
    (traceId indexId : FreeVarId) :
    freeVariable ∈
        Formula.freeSupport
          (logical_formula_payload_component_condition_with_ids
            formulaCode numericCode traceId indexId) ↔
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport numericCode := by
  constructor
  · exact
      logical_formula_payload_component_condition_with_ids_freeSupport_subset
        formulaCode numericCode traceId indexId freeVariable
  · intro hMember
    rcases hMember with hFormula | hNumeric
    · simp [
        logical_formula_payload_component_condition_with_ids,
        Formula.freeSupport, Term.freeSupportList,
        hFormula]
    · simp [
        logical_formula_payload_component_condition_with_ids,
        Formula.freeSupport, Term.freeSupportList,
        hNumeric]

/-- 有限证书合取的自由支持来自其中某个字段。 -/
theorem logical_certificate_conjunction_freeSupport
    (formulas : List SetFormula) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_certificate_conjunction formulas) →
      ∃ formula ∈ formulas,
        freeVariable ∈ Formula.freeSupport formula := by
  induction formulas with
  | nil =>
      intro freeVariable hMember
      simp [logical_certificate_conjunction, Formula.freeSupport] at hMember
  | cons formula formulas ih =>
      cases formulas with
      | nil =>
          intro freeVariable hMember
          exact ⟨formula, by simp,
            by simpa [logical_certificate_conjunction] using hMember⟩
      | cons next rest =>
          intro freeVariable hMember
          have hSplit :
              freeVariable ∈ Formula.freeSupport formula ∨
                freeVariable ∈
                  Formula.freeSupport
                    (logical_certificate_conjunction (next :: rest)) := by
            simpa [
              logical_certificate_conjunction,
              Formula.freeSupport, Term.freeSupportList,
              List.mem_append] using hMember
          rcases hSplit with hFormula | hRest
          · exact ⟨formula, by simp, hFormula⟩
          · rcases ih freeVariable hRest with
              ⟨field, hField, hFieldSupport⟩
            exact ⟨field,
              List.mem_cons_of_mem formula hField,
              hFieldSupport⟩

/-- 单公式构造子证书只依赖结论码与证书码。 -/
theorem logical_unary_base_certificate_condition_with_ids_freeSupport_subset
    (tag : Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId componentId traceId indexId : FreeVarId)
    (hConstructor :
      ∀ component freeVariable,
        freeVariable ∈ Term.freeSupport (constructor component) ↔
          freeVariable ∈ Term.freeSupport component) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_unary_base_certificate_condition_with_ids
              tag constructor formulaCode certificate
              payloadId sequenceId componentId traceId indexId) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificate := by
  intro freeVariable hMember
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formulaCode
  · exact Or.inl hFormula
  by_cases hCertificate :
      freeVariable ∈ Term.freeSupport certificate
  · exact Or.inr hCertificate
  · exfalso
    rcases freeVariable with ⟨freeSort, freeId⟩
    have hComponentReplaySupport :
        (freeSort, freeId) ∈
            Formula.freeSupport
              (fs_formula_replay_condition (x#componentId)) →
          freeSort = SetSort.set ∧ freeId = componentId := by
      intro hReplay
      simpa [Term.freeSupport] using
        fs_formula_replay_condition_freeSupport_subset
          (x#componentId) (freeSort, freeId) hReplay
    simp_all [
      logical_unary_base_certificate_condition_with_ids,
      logical_certificate_conjunction,
      logical_formula_payload_component_condition_with_ids,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    clear hConstructor hFormula hCertificate
    grind (splits := 16)

/-- 双公式构造子证书只依赖结论码与证书码。 -/
theorem logical_binary_base_certificate_condition_with_ids_freeSupport_subset
    (tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId)
    (hConstructor :
      ∀ left right freeVariable,
        freeVariable ∈ Term.freeSupport (constructor left right) ↔
          freeVariable ∈ Term.freeSupport left ∨
            freeVariable ∈ Term.freeSupport right) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_binary_base_certificate_condition_with_ids
              tag constructor formulaCode certificate
              payloadId sequenceId leftId rightId traceId indexId) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificate := by
  intro freeVariable hMember
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formulaCode
  · exact Or.inl hFormula
  by_cases hCertificate :
      freeVariable ∈ Term.freeSupport certificate
  · exact Or.inr hCertificate
  · exfalso
    rcases freeVariable with ⟨freeSort, freeId⟩
    have hLeftReplaySupport :
        (freeSort, freeId) ∈
            Formula.freeSupport
              (fs_formula_replay_condition (x#leftId)) →
          freeSort = SetSort.set ∧ freeId = leftId := by
      intro hReplay
      simpa [Term.freeSupport] using
        fs_formula_replay_condition_freeSupport_subset
          (x#leftId) (freeSort, freeId) hReplay
    have hRightReplaySupport :
        (freeSort, freeId) ∈
            Formula.freeSupport
              (fs_formula_replay_condition (x#rightId)) →
          freeSort = SetSort.set ∧ freeId = rightId := by
      intro hReplay
      simpa [Term.freeSupport] using
        fs_formula_replay_condition_freeSupport_subset
          (x#rightId) (freeSort, freeId) hReplay
    simp_all [
      logical_binary_base_certificate_condition_with_ids,
      logical_certificate_conjunction,
      logical_formula_payload_component_condition_with_ids,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    clear hConstructor hFormula hCertificate
    grind (splits := 24)

/-- 三公式构造子证书只依赖结论码与证书码。 -/
theorem logical_ternary_base_certificate_condition_with_ids_freeSupport_subset
    (tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId firstId secondId thirdId traceId indexId :
      FreeVarId)
    (hConstructor :
      ∀ first second third freeVariable,
        freeVariable ∈
            Term.freeSupport (constructor first second third) ↔
          freeVariable ∈ Term.freeSupport first ∨
            freeVariable ∈ Term.freeSupport second ∨
              freeVariable ∈ Term.freeSupport third) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_ternary_base_certificate_condition_with_ids
              tag constructor formulaCode certificate
              payloadId sequenceId firstId secondId thirdId
              traceId indexId) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificate := by
  intro freeVariable hMember
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formulaCode
  · exact Or.inl hFormula
  by_cases hCertificate :
      freeVariable ∈ Term.freeSupport certificate
  · exact Or.inr hCertificate
  · exfalso
    rcases freeVariable with ⟨freeSort, freeId⟩
    have hFirstReplaySupport :
        (freeSort, freeId) ∈
            Formula.freeSupport
              (fs_formula_replay_condition (x#firstId)) →
          freeSort = SetSort.set ∧ freeId = firstId := by
      intro hReplay
      simpa [Term.freeSupport] using
        fs_formula_replay_condition_freeSupport_subset
          (x#firstId) (freeSort, freeId) hReplay
    have hSecondReplaySupport :
        (freeSort, freeId) ∈
            Formula.freeSupport
              (fs_formula_replay_condition (x#secondId)) →
          freeSort = SetSort.set ∧ freeId = secondId := by
      intro hReplay
      simpa [Term.freeSupport] using
        fs_formula_replay_condition_freeSupport_subset
          (x#secondId) (freeSort, freeId) hReplay
    have hThirdReplaySupport :
        (freeSort, freeId) ∈
            Formula.freeSupport
              (fs_formula_replay_condition (x#thirdId)) →
          freeSort = SetSort.set ∧ freeId = thirdId := by
      intro hReplay
      simpa [Term.freeSupport] using
        fs_formula_replay_condition_freeSupport_subset
          (x#thirdId) (freeSort, freeId) hReplay
    simp_all [
      logical_ternary_base_certificate_condition_with_ids,
      logical_certificate_conjunction,
      logical_formula_payload_component_condition_with_ids,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    clear hConstructor hFormula hCertificate
    grind (splits := 32)

/-- 等式自反基础证书只依赖结论码与证书码。 -/
theorem logical_equality_reflexivity_certificate_condition_with_id_freeSupport_subset
    (formulaCode certificate : SetTerm)
    (identifierId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_equality_reflexivity_certificate_condition_with_id
              formulaCode certificate identifierId) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificate := by
  intro freeVariable hMember
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formulaCode
  · exact Or.inl hFormula
  by_cases hCertificate :
      freeVariable ∈ Term.freeSupport certificate
  · exact Or.inr hCertificate
  · exfalso
    rcases freeVariable with ⟨freeSort, freeId⟩
    simp_all [
      logical_equality_reflexivity_certificate_condition_with_id,
      logical_certificate_conjunction,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    grind

/-- 无关全称引入基础证书只依赖结论码与证书码。 -/
theorem logical_vacuous_forall_certificate_condition_with_ids_freeSupport_subset
    (formulaCode certificate : SetTerm)
    (payloadId eigenId bodyNumericId sourceId variableId universalId
      traceId indexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_vacuous_forall_certificate_condition_with_ids
              formulaCode certificate payloadId eigenId bodyNumericId
              sourceId variableId universalId traceId indexId) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificate := by
  intro freeVariable hMember
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formulaCode
  · exact Or.inl hFormula
  by_cases hCertificate :
      freeVariable ∈ Term.freeSupport certificate
  · exact Or.inr hCertificate
  · exfalso
    rcases freeVariable with ⟨freeSort, freeId⟩
    simp_all [
      logical_vacuous_forall_certificate_condition_with_ids,
      logical_certificate_conjunction,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    have hClosureFresh :
        (freeSort, freeId) ∉
          Formula.freeSupport
            (canonical_forall_closure_code_condition
              (x#sourceId) (x#variableId) (x#universalId)) := by
      apply
        not_mem_freeSupport_canonical_forall_closure_code_condition
      all_goals
        simp_all [Term.freeSupport]
        <;> grind
    clear hFormula hCertificate
    grind (splits := 48)
      [fs_formula_replay_condition_freeSupport_subset]

/-- 全称量词分配基础证书只依赖结论码与证书码。 -/
theorem logical_forall_distribution_certificate_condition_with_ids_freeSupport_subset
    (formulaCode certificate : SetTerm)
    (payloadId eigenId leftNumericId rightNumericId leftId rightId
      variableId closedImplicationId closedLeftId closedRightId
      traceId indexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_forall_distribution_certificate_condition_with_ids
              formulaCode certificate payloadId eigenId leftNumericId
              rightNumericId leftId rightId variableId
              closedImplicationId closedLeftId closedRightId
              traceId indexId) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificate := by
  intro freeVariable hMember
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formulaCode
  · exact Or.inl hFormula
  by_cases hCertificate :
      freeVariable ∈ Term.freeSupport certificate
  · exact Or.inr hCertificate
  · exfalso
    rcases freeVariable with ⟨freeSort, freeId⟩
    simp_all [
      logical_forall_distribution_certificate_condition_with_ids,
      logical_certificate_conjunction,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    have hVariableFresh :
        (freeSort, freeId) ∉ Term.freeSupport (x#variableId) := by
      simp_all [Term.freeSupport]
    have hCanonicalFresh :
        ∀ source target : SetTerm,
          (freeSort, freeId) ∉ Term.freeSupport source →
          (freeSort, freeId) ∉ Term.freeSupport target →
          (freeSort, freeId) ∉
            Formula.freeSupport
              (canonical_forall_closure_code_condition
                source (x#variableId) target) := by
      intro source target hSource hTarget
      exact
        not_mem_freeSupport_canonical_forall_closure_code_condition
          (freeSort, freeId) source (x#variableId) target
          hSource hVariableFresh hTarget
    have hImplicationClosureFresh :
        (freeSort, freeId) ∉
          Formula.freeSupport
            (canonical_forall_closure_code_condition
              (imp_codeₘ(x#leftId, x#rightId))
              (x#variableId) (x#closedImplicationId)) := by
      apply hCanonicalFresh
      all_goals
        simp_all [Term.freeSupport, Term.freeSupportList]
        <;> grind
    have hLeftClosureFresh :
        (freeSort, freeId) ∉
          Formula.freeSupport
            (canonical_forall_closure_code_condition
              (x#leftId) (x#variableId) (x#closedLeftId)) := by
      apply hCanonicalFresh
      all_goals
        simp_all [Term.freeSupport]
        <;> grind
    have hRightClosureFresh :
        (freeSort, freeId) ∉
          Formula.freeSupport
            (canonical_forall_closure_code_condition
              (x#rightId) (x#variableId) (x#closedRightId)) := by
      apply hCanonicalFresh
      all_goals
        simp_all [Term.freeSupport]
        <;> grind
    have hLeftQuantifierFresh :
        (freeSort, freeId) ∉
          Formula.freeSupport
            (quantifier_occurs_condition
              (x#variableId) (x#leftId)) := by
      intro h
      rcases quantifier_occurs_condition_freeSupport_subset
          (x#variableId) (x#leftId) (freeSort, freeId) h with h | h
      all_goals simp_all [Term.freeSupport]
    have hRightQuantifierFresh :
        (freeSort, freeId) ∉
          Formula.freeSupport
            (quantifier_occurs_condition
              (x#variableId) (x#rightId)) := by
      intro h
      rcases quantifier_occurs_condition_freeSupport_subset
          (x#variableId) (x#rightId) (freeSort, freeId) h with h | h
      all_goals simp_all [Term.freeSupport]
    clear hFormula hCertificate hCanonicalFresh
    grind (splits := 64)
      [fs_formula_replay_condition_freeSupport_subset]

/-- 全称特化基础证书只依赖结论码与证书码。 -/
theorem logical_specialization_certificate_condition_with_ids_freeSupport_subset
    (formulaCode certificate : SetTerm)
    (payloadId eigenId bodyNumericId carrierNumericId sourceId carrierId
      termId variableId universalId resultId traceId indexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_specialization_certificate_condition_with_ids
              formulaCode certificate payloadId eigenId bodyNumericId
              carrierNumericId sourceId carrierId termId variableId
              universalId resultId traceId indexId) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificate := by
  intro freeVariable hMember
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formulaCode
  · exact Or.inl hFormula
  by_cases hCertificate :
      freeVariable ∈ Term.freeSupport certificate
  · exact Or.inr hCertificate
  · exfalso
    rcases freeVariable with ⟨freeSort, freeId⟩
    simp_all [
      logical_specialization_certificate_condition_with_ids,
      logical_certificate_conjunction,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    have hClosureFresh :
        (freeSort, freeId) ∉
          Formula.freeSupport
            (canonical_forall_closure_code_condition
              (x#sourceId) (x#variableId) (x#universalId)) := by
      apply
        not_mem_freeSupport_canonical_forall_closure_code_condition
      all_goals
        simp_all [Term.freeSupport]
        <;> grind
    have hQuantifierFresh :
        (freeSort, freeId) ∉
          Formula.freeSupport
            (quantifier_occurs_condition
              (x#variableId) (x#sourceId)) := by
      intro h
      rcases quantifier_occurs_condition_freeSupport_subset
          (x#variableId) (x#sourceId) (freeSort, freeId) h with h | h
      all_goals simp_all [Term.freeSupport]
    have hSubstitutionFresh :
        (freeSort, freeId) ∉
          Formula.freeSupport
            (code_substitution_spec
              (x#sourceId) (x#variableId)
              (x#termId) (x#resultId)) := by
      apply not_mem_freeSupport_code_substitution_spec
      all_goals
        simp_all [Term.freeSupport]
        <;> grind
    clear hFormula hCertificate
    grind (splits := 64)
      [fs_formula_replay_condition_freeSupport_subset]

/-- 等式替换基础证书只依赖结论码与证书码。 -/
theorem logical_equality_substitution_certificate_condition_with_ids_freeSupport_subset
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId bodyId resultId traceId indexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_equality_substitution_certificate_condition_with_ids
              formulaCode certificate payloadId sequenceId bodyId resultId
              traceId indexId) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificate := by
  intro freeVariable hMember
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formulaCode
  · exact Or.inl hFormula
  by_cases hCertificate :
      freeVariable ∈ Term.freeSupport certificate
  · exact Or.inr hCertificate
  · exfalso
    rcases freeVariable with ⟨freeSort, freeId⟩
    simp_all [
      logical_equality_substitution_certificate_condition_with_ids,
      logical_certificate_conjunction,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      quantifier_occurs_condition,
      universal_binder_at_condition,
      code_substring_at_condition,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    have hSubstitutionFresh :
        (freeSort, freeId) ∉
          Formula.freeSupport
            (code_substitution_spec
              (x#bodyId)
              (var_codeₘ(numₘ(2) *ₘ
                (x#sequenceId ·ₘ numₘ(0))))
              (var_codeₘ(numₘ(2) *ₘ
                (x#sequenceId ·ₘ numₘ(1))))
              (x#resultId)) := by
      intro hSubstitution
      have hSource :=
        code_substitution_spec_freeSupport_subset
          (x#bodyId)
          (var_codeₘ(numₘ(2) *ₘ
            (x#sequenceId ·ₘ numₘ(0))))
          (var_codeₘ(numₘ(2) *ₘ
            (x#sequenceId ·ₘ numₘ(1))))
          (x#resultId)
          (freeSort, freeId) hSubstitution
      simp_all [
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
      grind
    clear hFormula hCertificate
    grind (splits := 32)
      [fs_formula_replay_condition_freeSupport_subset]

/-- 十二类基础逻辑证书的自由支持只来自结论码与证书码。 -/
theorem logical_base_certificate_condition_freeSupport_subset
    (formulaCode certificate : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (logical_base_certificate_condition formulaCode certificate) →
      freeVariable ∈ Term.freeSupport formulaCode ∨
        freeVariable ∈ Term.freeSupport certificate := by
  intro freeVariable hMember
  simp only [
    logical_base_certificate_condition,
    logical_base_certificate_condition_with_base,
    Formula.freeSupport,
    List.mem_append] at hMember
  rcases hMember with
    hDistribution | hSelf | hWeakening | hContradiction |
    hClassical | hExplosion | hCases | hSpecialization |
    hForallDistribution | hVacuousForall |
    hEqualitySubstitution | hEqualityReflexivity
  · exact
      logical_ternary_base_certificate_condition_with_ids_freeSupport_subset
        0 implication_distribution_axiom_code_term
        formulaCode certificate _ _ _ _ _ _ _
        (by
          intro first second third freeVariable
          simp [Term.freeSupport, Term.freeSupportList] <;> grind)
        freeVariable hDistribution
  · exact
      logical_unary_base_certificate_condition_with_ids_freeSupport_subset
        1 self_implication_axiom_code_term
        formulaCode certificate _ _ _ _ _
        (by
          intro component freeVariable
          simp [Term.freeSupport, Term.freeSupportList] <;> grind)
        freeVariable hSelf
  · exact
      logical_binary_base_certificate_condition_with_ids_freeSupport_subset
        2 weakening_axiom_code_term
        formulaCode certificate _ _ _ _ _ _
        (by
          intro left right freeVariable
          simp [Term.freeSupport, Term.freeSupportList] <;> grind)
        freeVariable hWeakening
  · exact
      logical_binary_base_certificate_condition_with_ids_freeSupport_subset
        3 contradiction_axiom_code_term
        formulaCode certificate _ _ _ _ _ _
        (by
          intro left right freeVariable
          simp [Term.freeSupport, Term.freeSupportList] <;> grind)
        freeVariable hContradiction
  · exact
      logical_unary_base_certificate_condition_with_ids_freeSupport_subset
        4 classical_axiom_code_term
        formulaCode certificate _ _ _ _ _
        (by
          intro component freeVariable
          simp [Term.freeSupport, Term.freeSupportList] <;> grind)
        freeVariable hClassical
  · exact
      logical_binary_base_certificate_condition_with_ids_freeSupport_subset
        5 explosion_axiom_code_term
        formulaCode certificate _ _ _ _ _ _
        (by
          intro left right freeVariable
          simp [Term.freeSupport, Term.freeSupportList] <;> grind)
        freeVariable hExplosion
  · exact
      logical_binary_base_certificate_condition_with_ids_freeSupport_subset
        6 case_analysis_axiom_code_term
        formulaCode certificate _ _ _ _ _ _
        (by
          intro left right freeVariable
          simp [Term.freeSupport, Term.freeSupportList] <;> grind)
        freeVariable hCases
  · exact
      logical_specialization_certificate_condition_with_ids_freeSupport_subset
        formulaCode certificate _ _ _ _ _ _ _ _ _ _ _ _
        freeVariable hSpecialization
  · exact
      logical_forall_distribution_certificate_condition_with_ids_freeSupport_subset
        formulaCode certificate _ _ _ _ _ _ _ _ _ _ _ _
        freeVariable hForallDistribution
  · exact
      logical_vacuous_forall_certificate_condition_with_ids_freeSupport_subset
        formulaCode certificate _ _ _ _ _ _ _ _
        freeVariable hVacuousForall
  · exact
      logical_equality_substitution_certificate_condition_with_ids_freeSupport_subset
        formulaCode certificate _ _ _ _ _ _
        freeVariable hEqualitySubstitution
  · exact
      logical_equality_reflexivity_certificate_condition_with_id_freeSupport_subset
        formulaCode certificate _
        freeVariable hEqualityReflexivity

/-- 两个公开入口都新鲜时，基础逻辑证书条件不含该自由变量。 -/
theorem not_mem_freeSupport_logical_base_certificate_condition
    (freeVariable : FreeVariable signature)
    (formulaCode certificate : SetTerm)
    (hFormula :
      freeVariable ∉ Term.freeSupport formulaCode)
    (hCertificate :
      freeVariable ∉ Term.freeSupport certificate) :
    freeVariable ∉
      Formula.freeSupport
        (logical_base_certificate_condition formulaCode certificate) := by
  intro hMember
  rcases logical_base_certificate_condition_freeSupport_subset
      formulaCode certificate freeVariable hMember with
    hMember | hMember
  · exact hFormula hMember
  · exact hCertificate hMember

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
