import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution

/-!
# 基础逻辑证书条件的闭项替换

本模块把闭项替换穿过十二类基础逻辑证书的存在量词与内部 checked 关系。
公开接口只要求待替换变量避开实际使用的 binder；不把具体 ZFC 回放或固定编号
写入证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

namespace CertifiedProof

/--
闭项替换穿过一列嵌套存在 binder。

见证项在 `existsFreeAssignments` 的量词闭包一侧不参与公式构造；这里只复用该列表
记录 binder 顺序。
-/
private theorem logical_certificate_exists_substitute_fresh
    (sourceId : FreeVarId)
    (replacement : SetTerm)
    (assignments : List (FreeVarId × SetTerm))
    (body bodyResult : SetFormula)
    (hSourceFresh :
      sourceId ∉ assignments.map (fun assignment => assignment.1))
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ id,
        id ∈ assignments.map (fun assignment => assignment.1) →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hBodySubstitution :
      Formula.substituteFree SetSort.set sourceId replacement body =
        bodyResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (Formula.existsFreeAssignments
          SetSort.set assignments body) =
      Formula.existsFreeAssignments
        SetSort.set assignments bodyResult := by
  calc
    Formula.substituteFree SetSort.set sourceId replacement
        (Formula.existsFreeAssignments SetSort.set assignments body) =
      Formula.existsFreeAssignments SetSort.set assignments
        (Formula.substituteFree SetSort.set sourceId replacement body) := by
          symm
          exact Formula.existsFreeAssignments_substituteFree_comm_fresh
            SetSort.set sourceId replacement assignments body
            hSourceFresh hReplacementAdmissible.2
            hReplacementFresh
    _ =
      Formula.existsFreeAssignments
        SetSort.set assignments bodyResult :=
          congrArg
            (Formula.existsFreeAssignments SetSort.set assignments)
            hBodySubstitution

/--
对内部 binder 新鲜的替换逐公开参数穿过单公式基础证书条件。

构造器只需满足项替换同态；序列编码与公式 payload 的内部 binder 由各自的公共
替换接口处理。
-/
theorem logical_unary_base_certificate_condition_with_ids_substitute_fresh
    (tag : Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificate replacement
      formulaCodeResult certificateResult : SetTerm)
    (payloadId sequenceId componentId traceId indexId sourceId :
      FreeVarId)
    (hSourceFresh :
      sourceId ∉
        [payloadId, sequenceId, componentId, traceId, indexId])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ id,
        id ∈
            [payloadId, sequenceId, componentId, traceId, indexId] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hConstructorSubstitution :
      ∀ component,
        Term.substituteFree SetSort.set sourceId replacement
            (constructor component) =
          constructor
            (Term.substituteFree
              SetSort.set sourceId replacement component))
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaCode =
        formulaCodeResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_unary_base_certificate_condition_with_ids
          tag constructor formulaCode certificate
          payloadId sequenceId componentId traceId indexId) =
      logical_unary_base_certificate_condition_with_ids
        tag constructor formulaCodeResult certificateResult
        payloadId sequenceId componentId traceId indexId := by
  have hSourceNe
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, sequenceId, componentId, traceId, indexId]) :
      sourceId ≠ id := by
    intro hEq
    subst id
    exact hSourceFresh hId
  have hVariableFixed
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, sequenceId, componentId, traceId, indexId]) :
      Term.substituteFree SetSort.set sourceId replacement (x#id) =
        x#id := by
    have hNe := hSourceNe id hId
    simp [Term.substituteFree, set_variable, Ne.symm hNe]
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hSequenceCondition :=
    nat_sequence_code_condition_with_ids_substitute_closed
      (x#sequenceId) (x#payloadId) replacement
      (x#sequenceId) (x#payloadId)
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed sequenceId (by simp))
      (hVariableFixed payloadId (by simp))
  have hSequenceAtZero :
      Term.substituteFree SetSort.set sourceId replacement
          (x#sequenceId ·ₘ numₘ(0)) =
        x#sequenceId ·ₘ numₘ(0) := by
    simp [Term.substituteFree,
      hVariableFixed sequenceId (by simp),
      hNumeralFixed]
  have hComponentCondition :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#componentId) (x#sequenceId ·ₘ numₘ(0)) replacement
      (x#componentId) (x#sequenceId ·ₘ numₘ(0))
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed componentId (by simp))
      hSequenceAtZero
  let template
      (formulaTerm certificateTerm payloadTerm sequenceTerm
        componentTerm : SetTerm) : SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(tag), payloadTerm⟩ₘ),
      nat_sequence_code_condition_with_ids
        sequenceTerm payloadTerm traceId indexId,
      domₘ(sequenceTerm) ≐ₘ numₘ(1),
      logical_formula_payload_component_condition_with_ids
        componentTerm (sequenceTerm ·ₘ numₘ(0))
        traceId indexId,
      formulaTerm ≐ₘ constructor componentTerm]
  let body : SetFormula :=
    template formulaCode certificate
      (x#payloadId) (x#sequenceId) (x#componentId)
  let bodyResult : SetFormula :=
    template formulaCodeResult certificateResult
      (x#payloadId) (x#sequenceId) (x#componentId)
  have hBodySubstitution :
      Formula.substituteFree SetSort.set sourceId replacement body =
        bodyResult := by
    dsimp [body, bodyResult, template]
    rw [logical_certificate_conjunction_substituteFree]
    simp only [List.map]
    rw [hSequenceCondition, hComponentCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hFormulaCodeSubstitution, hCertificateSubstitution,
      hVariableFixed, hNumeralFixed, hConstructorSubstitution]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId),
    (sequenceId, x#sequenceId),
    (componentId, x#componentId)]
  have hAssignmentsFresh :
      sourceId ∉
        assignments.map (fun assignment => assignment.1) := by
    intro hMember
    have hIds :
        sourceId = payloadId ∨
          sourceId = sequenceId ∨
            sourceId = componentId := by
      simpa [assignments] using hMember
    rcases hIds with hEq | hEq | hEq
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
  have hWrapped :=
    logical_certificate_exists_substitute_fresh
      sourceId replacement assignments body bodyResult
      hAssignmentsFresh hReplacementAdmissible
      (fun id hId => by
        have hPrefix :
            id ∈ [payloadId, sequenceId, componentId] := by
          simpa [assignments] using hId
        exact hReplacementFresh id (by
          simpa using
            List.mem_append_left [traceId, indexId] hPrefix))
      hBodySubstitution
  simpa [
    logical_unary_base_certificate_condition_with_ids,
    assignments, body, bodyResult, template,
    Formula.existsFreeAssignments] using hWrapped

/-- 对内部 binder 新鲜的替换逐公开参数穿过双公式基础证书条件。 -/
theorem logical_binary_base_certificate_condition_with_ids_substitute_fresh
    (tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate replacement
      formulaCodeResult certificateResult : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId sourceId :
      FreeVarId)
    (hSourceFresh :
      sourceId ∉
        [payloadId, sequenceId, leftId, rightId, traceId, indexId])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ id,
        id ∈
            [payloadId, sequenceId, leftId, rightId, traceId, indexId] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hConstructorSubstitution :
      ∀ left right,
        Term.substituteFree SetSort.set sourceId replacement
            (constructor left right) =
          constructor
            (Term.substituteFree
              SetSort.set sourceId replacement left)
            (Term.substituteFree
              SetSort.set sourceId replacement right))
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaCode =
        formulaCodeResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_binary_base_certificate_condition_with_ids
          tag constructor formulaCode certificate
          payloadId sequenceId leftId rightId traceId indexId) =
      logical_binary_base_certificate_condition_with_ids
        tag constructor formulaCodeResult certificateResult
        payloadId sequenceId leftId rightId traceId indexId := by
  have hSourceNe
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, sequenceId, leftId, rightId, traceId, indexId]) :
      sourceId ≠ id := by
    intro hEq
    subst id
    exact hSourceFresh hId
  have hVariableFixed
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, sequenceId, leftId, rightId, traceId, indexId]) :
      Term.substituteFree SetSort.set sourceId replacement (x#id) =
        x#id := by
    have hNe := hSourceNe id hId
    simp [Term.substituteFree, set_variable, Ne.symm hNe]
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hSequenceCondition :=
    nat_sequence_code_condition_with_ids_substitute_closed
      (x#sequenceId) (x#payloadId) replacement
      (x#sequenceId) (x#payloadId)
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed sequenceId (by simp))
      (hVariableFixed payloadId (by simp))
  have hSequenceAt (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (x#sequenceId ·ₘ numₘ(value)) =
        x#sequenceId ·ₘ numₘ(value) := by
    simp [Term.substituteFree,
      hVariableFixed sequenceId (by simp),
      hNumeralFixed]
  have hLeftCondition :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#leftId) (x#sequenceId ·ₘ numₘ(0)) replacement
      (x#leftId) (x#sequenceId ·ₘ numₘ(0))
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed leftId (by simp))
      (hSequenceAt 0)
  have hRightCondition :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#rightId) (x#sequenceId ·ₘ numₘ(1)) replacement
      (x#rightId) (x#sequenceId ·ₘ numₘ(1))
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed rightId (by simp))
      (hSequenceAt 1)
  let template
      (formulaTerm certificateTerm payloadTerm sequenceTerm
        leftTerm rightTerm : SetTerm) : SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(tag), payloadTerm⟩ₘ),
      nat_sequence_code_condition_with_ids
        sequenceTerm payloadTerm traceId indexId,
      domₘ(sequenceTerm) ≐ₘ numₘ(2),
      logical_formula_payload_component_condition_with_ids
        leftTerm (sequenceTerm ·ₘ numₘ(0))
        traceId indexId,
      logical_formula_payload_component_condition_with_ids
        rightTerm (sequenceTerm ·ₘ numₘ(1))
        traceId indexId,
      formulaTerm ≐ₘ constructor leftTerm rightTerm]
  let body : SetFormula :=
    template formulaCode certificate
      (x#payloadId) (x#sequenceId) (x#leftId) (x#rightId)
  let bodyResult : SetFormula :=
    template formulaCodeResult certificateResult
      (x#payloadId) (x#sequenceId) (x#leftId) (x#rightId)
  have hBodySubstitution :
      Formula.substituteFree SetSort.set sourceId replacement body =
        bodyResult := by
    dsimp [body, bodyResult, template]
    rw [logical_certificate_conjunction_substituteFree]
    simp only [List.map]
    rw [hSequenceCondition, hLeftCondition, hRightCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hFormulaCodeSubstitution, hCertificateSubstitution,
      hVariableFixed, hNumeralFixed, hConstructorSubstitution]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId),
    (sequenceId, x#sequenceId),
    (leftId, x#leftId),
    (rightId, x#rightId)]
  have hAssignmentsFresh :
      sourceId ∉
        assignments.map (fun assignment => assignment.1) := by
    intro hMember
    have hIds :
        sourceId = payloadId ∨
          sourceId = sequenceId ∨
            sourceId = leftId ∨
              sourceId = rightId := by
      simpa [assignments] using hMember
    rcases hIds with hEq | hEq | hEq | hEq
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
  have hWrapped :=
    logical_certificate_exists_substitute_fresh
      sourceId replacement assignments body bodyResult
      hAssignmentsFresh hReplacementAdmissible
      (fun id hId => by
        have hPrefix :
            id ∈ [payloadId, sequenceId, leftId, rightId] := by
          simpa [assignments] using hId
        exact hReplacementFresh id (by
          simpa using
            List.mem_append_left [traceId, indexId] hPrefix))
      hBodySubstitution
  simpa [
    logical_binary_base_certificate_condition_with_ids,
    assignments, body, bodyResult, template,
    Formula.existsFreeAssignments] using hWrapped

/-- 对内部 binder 新鲜的替换逐公开参数穿过三公式基础证书条件。 -/
theorem logical_ternary_base_certificate_condition_with_ids_substitute_fresh
    (tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm → SetTerm)
    (formulaCode certificate replacement
      formulaCodeResult certificateResult : SetTerm)
    (payloadId sequenceId firstId secondId thirdId traceId indexId
      sourceId : FreeVarId)
    (hSourceFresh :
      sourceId ∉
        [payloadId, sequenceId, firstId, secondId, thirdId,
          traceId, indexId])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ id,
        id ∈
            [payloadId, sequenceId, firstId, secondId, thirdId,
              traceId, indexId] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hConstructorSubstitution :
      ∀ first second third,
        Term.substituteFree SetSort.set sourceId replacement
            (constructor first second third) =
          constructor
            (Term.substituteFree
              SetSort.set sourceId replacement first)
            (Term.substituteFree
              SetSort.set sourceId replacement second)
            (Term.substituteFree
              SetSort.set sourceId replacement third))
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaCode =
        formulaCodeResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_ternary_base_certificate_condition_with_ids
          tag constructor formulaCode certificate
          payloadId sequenceId firstId secondId thirdId traceId indexId) =
      logical_ternary_base_certificate_condition_with_ids
        tag constructor formulaCodeResult certificateResult
        payloadId sequenceId firstId secondId thirdId traceId indexId := by
  have hSourceNe
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, sequenceId, firstId, secondId, thirdId,
            traceId, indexId]) :
      sourceId ≠ id := by
    intro hEq
    subst id
    exact hSourceFresh hId
  have hVariableFixed
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, sequenceId, firstId, secondId, thirdId,
            traceId, indexId]) :
      Term.substituteFree SetSort.set sourceId replacement (x#id) =
        x#id := by
    have hNe := hSourceNe id hId
    simp [Term.substituteFree, set_variable, Ne.symm hNe]
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hSequenceCondition :=
    nat_sequence_code_condition_with_ids_substitute_closed
      (x#sequenceId) (x#payloadId) replacement
      (x#sequenceId) (x#payloadId)
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed sequenceId (by simp))
      (hVariableFixed payloadId (by simp))
  have hSequenceAt (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (x#sequenceId ·ₘ numₘ(value)) =
        x#sequenceId ·ₘ numₘ(value) := by
    simp [Term.substituteFree,
      hVariableFixed sequenceId (by simp),
      hNumeralFixed]
  have hFirstCondition :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#firstId) (x#sequenceId ·ₘ numₘ(0)) replacement
      (x#firstId) (x#sequenceId ·ₘ numₘ(0))
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed firstId (by simp))
      (hSequenceAt 0)
  have hSecondCondition :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#secondId) (x#sequenceId ·ₘ numₘ(1)) replacement
      (x#secondId) (x#sequenceId ·ₘ numₘ(1))
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed secondId (by simp))
      (hSequenceAt 1)
  have hThirdCondition :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#thirdId) (x#sequenceId ·ₘ numₘ(2)) replacement
      (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed thirdId (by simp))
      (hSequenceAt 2)
  let template
      (formulaTerm certificateTerm payloadTerm sequenceTerm
        firstTerm secondTerm thirdTerm : SetTerm) : SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(tag), payloadTerm⟩ₘ),
      nat_sequence_code_condition_with_ids
        sequenceTerm payloadTerm traceId indexId,
      domₘ(sequenceTerm) ≐ₘ numₘ(3),
      logical_formula_payload_component_condition_with_ids
        firstTerm (sequenceTerm ·ₘ numₘ(0))
        traceId indexId,
      logical_formula_payload_component_condition_with_ids
        secondTerm (sequenceTerm ·ₘ numₘ(1))
        traceId indexId,
      logical_formula_payload_component_condition_with_ids
        thirdTerm (sequenceTerm ·ₘ numₘ(2))
        traceId indexId,
      formulaTerm ≐ₘ constructor firstTerm secondTerm thirdTerm]
  let body : SetFormula :=
    template formulaCode certificate
      (x#payloadId) (x#sequenceId)
      (x#firstId) (x#secondId) (x#thirdId)
  let bodyResult : SetFormula :=
    template formulaCodeResult certificateResult
      (x#payloadId) (x#sequenceId)
      (x#firstId) (x#secondId) (x#thirdId)
  have hBodySubstitution :
      Formula.substituteFree SetSort.set sourceId replacement body =
        bodyResult := by
    dsimp [body, bodyResult, template]
    rw [logical_certificate_conjunction_substituteFree]
    simp only [List.map]
    rw [hSequenceCondition, hFirstCondition,
      hSecondCondition, hThirdCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hFormulaCodeSubstitution, hCertificateSubstitution,
      hVariableFixed, hNumeralFixed, hConstructorSubstitution]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId),
    (sequenceId, x#sequenceId),
    (firstId, x#firstId),
    (secondId, x#secondId),
    (thirdId, x#thirdId)]
  have hAssignmentsFresh :
      sourceId ∉
        assignments.map (fun assignment => assignment.1) := by
    intro hMember
    have hIds :
        sourceId = payloadId ∨
          sourceId = sequenceId ∨
            sourceId = firstId ∨
              sourceId = secondId ∨
                sourceId = thirdId := by
      simpa [assignments] using hMember
    rcases hIds with hEq | hEq | hEq | hEq | hEq
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
  have hWrapped :=
    logical_certificate_exists_substitute_fresh
      sourceId replacement assignments body bodyResult
      hAssignmentsFresh hReplacementAdmissible
      (fun id hId => by
        have hPrefix :
            id ∈
              [payloadId, sequenceId, firstId, secondId, thirdId] := by
          simpa [assignments] using hId
        exact hReplacementFresh id (by
          simpa using
            List.mem_append_left [traceId, indexId] hPrefix))
      hBodySubstitution
  simpa [
    logical_ternary_base_certificate_condition_with_ids,
    assignments, body, bodyResult, template,
    Formula.existsFreeAssignments] using hWrapped

/-- 对内部 binder 新鲜的替换逐公开参数穿过等式自反基础证书条件。 -/
theorem logical_equality_reflexivity_certificate_condition_with_id_substitute_fresh
    (formulaCode certificate replacement
      formulaCodeResult certificateResult : SetTerm)
    (identifierId sourceId : FreeVarId)
    (hSourceNeIdentifier : sourceId ≠ identifierId)
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      (SetSort.set, identifierId) ∉ Term.freeSupport replacement)
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaCode =
        formulaCodeResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_equality_reflexivity_certificate_condition_with_id
          formulaCode certificate identifierId) =
      logical_equality_reflexivity_certificate_condition_with_id
        formulaCodeResult certificateResult identifierId := by
  have hIdentifierFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (x#identifierId) =
        x#identifierId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeIdentifier]
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  let template
      (formulaTerm certificateTerm identifierTerm : SetTerm) :
      SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(11), identifierTerm⟩ₘ),
      identifierTerm ∈ₘ ωₘ,
      formulaTerm ≐ₘ
        eq_codeₘ(
          var_codeₘ(numₘ(2) *ₘ identifierTerm),
          var_codeₘ(numₘ(2) *ₘ identifierTerm))]
  let body : SetFormula :=
    template formulaCode certificate (x#identifierId)
  let bodyResult : SetFormula :=
    template formulaCodeResult certificateResult (x#identifierId)
  have hBodySubstitution :
      Formula.substituteFree SetSort.set sourceId replacement body =
        bodyResult := by
    dsimp [body, bodyResult, template]
    rw [logical_certificate_conjunction_substituteFree]
    simp [Formula.substituteFree, Term.substituteFree,
      hFormulaCodeSubstitution, hCertificateSubstitution,
      hIdentifierFixed, hNumeralFixed]
  let assignments : List (FreeVarId × SetTerm) := [
    (identifierId, x#identifierId)]
  have hAssignmentsFresh :
      sourceId ∉
        assignments.map (fun assignment => assignment.1) := by
    simpa [assignments] using hSourceNeIdentifier
  have hWrapped :=
    logical_certificate_exists_substitute_fresh
      sourceId replacement assignments body bodyResult
      hAssignmentsFresh hReplacementAdmissible
      (fun id hId => by
        have hEq : id = identifierId := by
          simpa [assignments] using hId
        subst id
        exact hReplacementFresh)
      hBodySubstitution
  simpa [
    logical_equality_reflexivity_certificate_condition_with_id,
    assignments, body, bodyResult, template,
    Formula.existsFreeAssignments] using hWrapped

/--
对内部 binder 新鲜的替换逐公开参数穿过等式替换基础证书条件。

除四个外层见证与 payload 序列的两个 binder 外，只需避开代码替换规格固定使用的
`310`、`311`。
-/
theorem logical_equality_substitution_certificate_condition_with_ids_substitute_fresh
    (formulaCode certificate replacement
      formulaCodeResult certificateResult : SetTerm)
    (payloadId sequenceId bodyId resultId traceId indexId sourceId :
      FreeVarId)
    (hSourceFresh :
      sourceId ∉
        [payloadId, sequenceId, bodyId, resultId,
          traceId, indexId, 310, 311])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ id,
        id ∈
            [payloadId, sequenceId, bodyId, resultId,
              traceId, indexId] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hReplacementCanonicalFresh :
      ∀ id,
        id ∈ [310, 311] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaCode =
        formulaCodeResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_equality_substitution_certificate_condition_with_ids
          formulaCode certificate payloadId sequenceId bodyId resultId
          traceId indexId) =
      logical_equality_substitution_certificate_condition_with_ids
        formulaCodeResult certificateResult
        payloadId sequenceId bodyId resultId traceId indexId := by
  have hSourceNe
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, sequenceId, bodyId, resultId,
            traceId, indexId, 310, 311]) :
      sourceId ≠ id := by
    intro hEq
    subst id
    exact hSourceFresh hId
  have hVariableFixed
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, sequenceId, bodyId, resultId,
            traceId, indexId, 310, 311]) :
      Term.substituteFree SetSort.set sourceId replacement (x#id) =
        x#id := by
    have hNe := hSourceNe id hId
    simp [Term.substituteFree, set_variable, Ne.symm hNe]
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hSequenceCondition :=
    nat_sequence_code_condition_with_ids_substitute_closed
      (x#sequenceId) (x#payloadId) replacement
      (x#sequenceId) (x#payloadId)
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed sequenceId (by simp))
      (hVariableFixed payloadId (by simp))
  have hSequenceAt (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (x#sequenceId ·ₘ numₘ(value)) =
        x#sequenceId ·ₘ numₘ(value) := by
    simp [Term.substituteFree,
      hVariableFixed sequenceId (by simp),
      hNumeralFixed]
  have hBodyCondition :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#bodyId) (x#sequenceId ·ₘ numₘ(2)) replacement
      (x#bodyId) (x#sequenceId ·ₘ numₘ(2))
      sourceId traceId indexId
      (hSourceNe traceId (by simp))
      (hSourceNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed bodyId (by simp))
      (hSequenceAt 2)
  have hFirstVariableFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (var_codeₘ(numₘ(2) *ₘ
            (x#sequenceId ·ₘ numₘ(0)))) =
        var_codeₘ(numₘ(2) *ₘ
          (x#sequenceId ·ₘ numₘ(0))) := by
    simp [Term.substituteFree,
      hVariableFixed sequenceId (by simp),
      hNumeralFixed]
  have hSecondVariableFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (var_codeₘ(numₘ(2) *ₘ
            (x#sequenceId ·ₘ numₘ(1)))) =
        var_codeₘ(numₘ(2) *ₘ
          (x#sequenceId ·ₘ numₘ(1))) := by
    simp [Term.substituteFree,
      hVariableFixed sequenceId (by simp),
      hNumeralFixed]
  have hSubstitutionCondition :=
    code_substitution_spec_substitute_fresh
      (x#bodyId)
      (var_codeₘ(numₘ(2) *ₘ
        (x#sequenceId ·ₘ numₘ(0))))
      (var_codeₘ(numₘ(2) *ₘ
        (x#sequenceId ·ₘ numₘ(1))))
      (x#resultId)
      replacement
      (x#bodyId)
      (var_codeₘ(numₘ(2) *ₘ
        (x#sequenceId ·ₘ numₘ(0))))
      (var_codeₘ(numₘ(2) *ₘ
        (x#sequenceId ·ₘ numₘ(1))))
      (x#resultId)
      sourceId
      (by
        intro hMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hMember
        rcases hMember with hEq | hEq
        · exact hSourceFresh (by simp [hEq])
        · exact hSourceFresh (by simp [hEq]))
      hReplacementAdmissible
      (fun id hId =>
        hReplacementCanonicalFresh id hId)
      (hVariableFixed bodyId (by simp))
      hFirstVariableFixed hSecondVariableFixed
      (hVariableFixed resultId (by simp))
  have hQuantifierCondition :
      Formula.substituteFree SetSort.set sourceId replacement
          (quantifier_occurs_condition
            (var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0))))
            (x#bodyId)) =
        quantifier_occurs_condition
          (var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0))))
          (x#bodyId) := by
    apply Formula.substituteFree_eq_self_of_not_mem
    intro hMember
    rcases quantifier_occurs_condition_freeSupport_subset
        _ _ _ hMember with hMember | hMember
    · apply hSourceNe sequenceId (by simp)
      simpa [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport] using hMember
    · apply hSourceNe bodyId (by simp)
      simpa [Term.freeSupport] using hMember
  let template
      (formulaTerm certificateTerm payloadTerm sequenceTerm
        bodyTerm resultTerm : SetTerm) : SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(10), payloadTerm⟩ₘ),
      nat_sequence_code_condition_with_ids
        sequenceTerm payloadTerm traceId indexId,
      domₘ(sequenceTerm) ≐ₘ numₘ(3),
      logical_formula_payload_component_condition_with_ids
        bodyTerm (sequenceTerm ·ₘ numₘ(2))
        traceId indexId,
      ¬ₘ quantifier_occurs_condition (var_codeₘ(numₘ(2) *ₘ (sequenceTerm ·ₘ numₘ(0)))) bodyTerm,
      substitutableₘ(var_codeₘ(numₘ(2) *ₘ (sequenceTerm ·ₘ numₘ(0))), var_codeₘ(numₘ(2) *ₘ (sequenceTerm ·ₘ numₘ(1))), bodyTerm),
      code_substitution_spec
        bodyTerm
        (var_codeₘ(numₘ(2) *ₘ
          (sequenceTerm ·ₘ numₘ(0))))
        (var_codeₘ(numₘ(2) *ₘ
          (sequenceTerm ·ₘ numₘ(1))))
        resultTerm,
      formulaTerm ≐ₘ
        imp_codeₘ(
          eq_codeₘ(
            var_codeₘ(numₘ(2) *ₘ
              (sequenceTerm ·ₘ numₘ(0))),
            var_codeₘ(numₘ(2) *ₘ
              (sequenceTerm ·ₘ numₘ(1)))),
          imp_codeₘ(bodyTerm, resultTerm))]
  let body : SetFormula :=
    template formulaCode certificate
      (x#payloadId) (x#sequenceId) (x#bodyId) (x#resultId)
  let bodyResult : SetFormula :=
    template formulaCodeResult certificateResult
      (x#payloadId) (x#sequenceId) (x#bodyId) (x#resultId)
  have hBodySubstitution :
      Formula.substituteFree SetSort.set sourceId replacement body =
        bodyResult := by
    dsimp [body, bodyResult, template]
    rw [logical_certificate_conjunction_substituteFree]
    simp only [List.map]
    rw [hSequenceCondition, hBodyCondition, hSubstitutionCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hQuantifierCondition,
      hFormulaCodeSubstitution, hCertificateSubstitution,
      hVariableFixed, hNumeralFixed]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId),
    (sequenceId, x#sequenceId),
    (bodyId, x#bodyId),
    (resultId, x#resultId)]
  have hAssignmentsFresh :
      sourceId ∉
        assignments.map (fun assignment => assignment.1) := by
    intro hMember
    have hIds :
        sourceId = payloadId ∨
          sourceId = sequenceId ∨
            sourceId = bodyId ∨
              sourceId = resultId := by
      simpa [assignments] using hMember
    rcases hIds with hEq | hEq | hEq | hEq
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
    · exact hSourceFresh (by simp [hEq])
  have hWrapped :=
    logical_certificate_exists_substitute_fresh
      sourceId replacement assignments body bodyResult
      hAssignmentsFresh hReplacementAdmissible
      (fun id hId => by
        have hPrefix :
            id ∈ [payloadId, sequenceId, bodyId, resultId] := by
          simpa [assignments] using hId
        exact hReplacementFresh id (by
          simpa using
            List.mem_append_left [traceId, indexId] hPrefix))
      hBodySubstitution
  simpa [
    logical_equality_substitution_certificate_condition_with_ids,
    assignments, body, bodyResult, template,
    Formula.existsFreeAssignments] using hWrapped

/-- 对内部 binder 新鲜的替换逐公开参数穿过无关全称引入基础证书条件。 -/
theorem logical_vacuous_forall_certificate_condition_with_ids_substitute_fresh
    (formulaCode certificate replacement
      formulaCodeResult certificateResult : SetTerm)
    (payloadId eigenId bodyNumericId sourceId variableId universalId
      traceId indexId parameter : FreeVarId)
    (hParameterFresh :
      parameter ∉
        [payloadId, eigenId, bodyNumericId, sourceId, variableId,
          universalId, traceId, indexId])
    (hParameterCanonicalFresh :
      parameter ∉
        [310, 311, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ id,
        id ∈
            [payloadId, eigenId, bodyNumericId, sourceId, variableId,
              universalId, traceId, indexId] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hReplacementCanonicalFresh :
      ∀ id,
        id ∈
            [310, 311, 460, 461, 462, 463, 464,
              465, 466, 467, 468, 469, 470] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set parameter replacement formulaCode =
        formulaCodeResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set parameter replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set parameter replacement
        (logical_vacuous_forall_certificate_condition_with_ids
          formulaCode certificate payloadId eigenId bodyNumericId
          sourceId variableId universalId traceId indexId) =
      logical_vacuous_forall_certificate_condition_with_ids
        formulaCodeResult certificateResult
        payloadId eigenId bodyNumericId sourceId variableId universalId
        traceId indexId := by
  have hParameterNe
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, eigenId, bodyNumericId, sourceId, variableId,
            universalId, traceId, indexId]) :
      parameter ≠ id := by
    intro hEq
    subst id
    exact hParameterFresh hId
  have hVariableFixed
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, eigenId, bodyNumericId, sourceId, variableId,
            universalId, traceId, indexId]) :
      Term.substituteFree SetSort.set parameter replacement (x#id) =
        x#id := by
    have hNe := hParameterNe id hId
    simp [Term.substituteFree, set_variable, Ne.symm hNe]
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set parameter replacement (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hBodyCondition :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#sourceId) (x#bodyNumericId) replacement
      (x#sourceId) (x#bodyNumericId)
      parameter traceId indexId
      (hParameterNe traceId (by simp))
      (hParameterNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed sourceId (by simp))
      (hVariableFixed bodyNumericId (by simp))
  have hClosureCondition :=
    canonical_forall_closure_code_condition_substitute_fresh
      (x#sourceId) (x#variableId) (x#universalId) replacement
      (x#sourceId) (x#variableId) (x#universalId)
      parameter hParameterCanonicalFresh
      hReplacementAdmissible hReplacementCanonicalFresh
      (hVariableFixed sourceId (by simp))
      (hVariableFixed variableId (by simp))
      (hVariableFixed universalId (by simp))
  let template
      (formulaTerm certificateTerm payloadTerm eigenTerm bodyNumericTerm
        sourceTerm variableTerm universalTerm : SetTerm) : SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(9), payloadTerm⟩ₘ),
      payloadTerm ≐ₘ
        godel_pairₘ(⟨eigenTerm, bodyNumericTerm⟩ₘ),
      eigenTerm ∈ₘ ωₘ,
      logical_formula_payload_component_condition_with_ids
        sourceTerm bodyNumericTerm traceId indexId,
      variableTerm ≐ₘ
        var_codeₘ(numₘ(2) *ₘ eigenTerm),
      ¬ₘ (variableTerm ∈ₘ varsₘ(sourceTerm)),
      canonical_forall_closure_code_condition
        sourceTerm variableTerm universalTerm,
      formulaTerm ≐ₘ
        imp_codeₘ(sourceTerm, universalTerm)]
  let body : SetFormula :=
    template formulaCode certificate
      (x#payloadId) (x#eigenId) (x#bodyNumericId)
      (x#sourceId) (x#variableId) (x#universalId)
  let bodyResult : SetFormula :=
    template formulaCodeResult certificateResult
      (x#payloadId) (x#eigenId) (x#bodyNumericId)
      (x#sourceId) (x#variableId) (x#universalId)
  have hBodySubstitution :
      Formula.substituteFree SetSort.set parameter replacement body =
        bodyResult := by
    dsimp [body, bodyResult, template]
    rw [logical_certificate_conjunction_substituteFree]
    simp only [List.map]
    rw [hBodyCondition, hClosureCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hFormulaCodeSubstitution, hCertificateSubstitution,
      hVariableFixed, hNumeralFixed]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId),
    (eigenId, x#eigenId),
    (bodyNumericId, x#bodyNumericId),
    (sourceId, x#sourceId),
    (variableId, x#variableId),
    (universalId, x#universalId)]
  have hAssignmentsFresh :
      parameter ∉
        assignments.map (fun assignment => assignment.1) := by
    intro hMember
    have hIds :
        parameter = payloadId ∨
          parameter = eigenId ∨
            parameter = bodyNumericId ∨
              parameter = sourceId ∨
                parameter = variableId ∨
                  parameter = universalId := by
      simpa [assignments] using hMember
    rcases hIds with hEq | hEq | hEq | hEq | hEq | hEq
    · exact hParameterFresh (by simp [hEq])
    · exact hParameterFresh (by simp [hEq])
    · exact hParameterFresh (by simp [hEq])
    · exact hParameterFresh (by simp [hEq])
    · exact hParameterFresh (by simp [hEq])
    · exact hParameterFresh (by simp [hEq])
  have hWrapped :=
    logical_certificate_exists_substitute_fresh
      parameter replacement assignments body bodyResult
      hAssignmentsFresh hReplacementAdmissible
      (fun id hId => by
        have hPrefix :
            id ∈
              [payloadId, eigenId, bodyNumericId, sourceId,
                variableId, universalId] := by
          simpa [assignments] using hId
        exact hReplacementFresh id (by
          simpa using
            List.mem_append_left [traceId, indexId] hPrefix))
      hBodySubstitution
  simpa [
    logical_vacuous_forall_certificate_condition_with_ids,
    assignments, body, bodyResult, template,
    Formula.existsFreeAssignments] using hWrapped

theorem logical_base_closure_reserved_mem
    {id : FreeVarId}
    (h :
      id ∈
        [310, 311, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470]) :
    id ∈
      [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
        465, 466, 467, 468, 469, 470] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  grind

private theorem logical_base_occurrence_reserved_mem
    {id : FreeVarId} (h : id ∈ [320, 321, 322]) :
    id ∈
      [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
        465, 466, 467, 468, 469, 470] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  grind

/-- 对内部 binder 新鲜的替换逐公开参数穿过全称特化基础证书条件。 -/
theorem logical_specialization_certificate_condition_with_ids_substitute_fresh
    (formulaCode certificate replacement
      formulaCodeResult certificateResult : SetTerm)
    (payloadId eigenId bodyNumericId carrierNumericId sourceId carrierId
      termId variableId universalId resultId traceId indexId parameter :
      FreeVarId)
    (hParameterFresh :
      parameter ∉
        [payloadId, eigenId, bodyNumericId, carrierNumericId, sourceId,
          carrierId, termId, variableId, universalId, resultId,
          traceId, indexId])
    (hParameterCanonicalFresh :
      parameter ∉
        [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ id,
        id ∈
            [payloadId, eigenId, bodyNumericId, carrierNumericId, sourceId,
              carrierId, termId, variableId, universalId, resultId,
              traceId, indexId] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hReplacementCanonicalFresh :
      ∀ id,
        id ∈
            [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
              465, 466, 467, 468, 469, 470] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set parameter replacement formulaCode =
        formulaCodeResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set parameter replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set parameter replacement
        (logical_specialization_certificate_condition_with_ids
          formulaCode certificate payloadId eigenId bodyNumericId
          carrierNumericId sourceId carrierId termId variableId
          universalId resultId traceId indexId) =
      logical_specialization_certificate_condition_with_ids
        formulaCodeResult certificateResult payloadId eigenId bodyNumericId
        carrierNumericId sourceId carrierId termId variableId universalId
        resultId traceId indexId := by
  have hParameterNe
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, eigenId, bodyNumericId, carrierNumericId, sourceId,
            carrierId, termId, variableId, universalId, resultId,
            traceId, indexId]) :
      parameter ≠ id := by
    intro hEq
    subst id
    exact hParameterFresh hId
  have hVariableFixed
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, eigenId, bodyNumericId, carrierNumericId, sourceId,
            carrierId, termId, variableId, universalId, resultId,
            traceId, indexId]) :
      Term.substituteFree SetSort.set parameter replacement (x#id) =
        x#id := by
    have hNe := hParameterNe id hId
    simp [Term.substituteFree, set_variable, Ne.symm hNe]
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set parameter replacement (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hSourcePayload :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#sourceId) (x#bodyNumericId) replacement
      (x#sourceId) (x#bodyNumericId)
      parameter traceId indexId
      (hParameterNe traceId (by simp))
      (hParameterNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed sourceId (by simp))
      (hVariableFixed bodyNumericId (by simp))
  have hCarrierPayload :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#carrierId) (x#carrierNumericId) replacement
      (x#carrierId) (x#carrierNumericId)
      parameter traceId indexId
      (hParameterNe traceId (by simp))
      (hParameterNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed carrierId (by simp))
      (hVariableFixed carrierNumericId (by simp))
  have hClosureCondition :=
    canonical_forall_closure_code_condition_substitute_fresh
      (x#sourceId) (x#variableId) (x#universalId) replacement
      (x#sourceId) (x#variableId) (x#universalId)
      parameter
      (fun h =>
        hParameterCanonicalFresh
          (logical_base_closure_reserved_mem h))
      hReplacementAdmissible
      (fun id h =>
        hReplacementCanonicalFresh id
          (logical_base_closure_reserved_mem h))
      (hVariableFixed sourceId (by simp))
      (hVariableFixed variableId (by simp))
      (hVariableFixed universalId (by simp))
  have hQuantifierCondition :=
    quantifier_occurs_condition_substituteFree
      parameter replacement (x#variableId) (x#sourceId)
      (x#variableId) (x#sourceId)
      (fun h =>
        hParameterCanonicalFresh
          (logical_base_occurrence_reserved_mem h))
      hReplacementAdmissible
      (fun id h =>
        hReplacementCanonicalFresh id
          (logical_base_occurrence_reserved_mem h))
      (hVariableFixed variableId (by simp))
      (hVariableFixed sourceId (by simp))
  have hSubstitutableCondition :
      Formula.substituteFree SetSort.set parameter replacement
          (substitutableₘ(x#variableId, x#termId, x#sourceId)) =
        substitutableₘ(x#variableId, x#termId, x#sourceId) := by
    simp [Formula.substituteFree,
      hVariableFixed variableId (by simp),
      hVariableFixed termId (by simp),
      hVariableFixed sourceId (by simp)]
  have hSubstitutionFresh :
      parameter ∉ [310, 311] := by
    intro hMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMember
    rcases hMember with hEq | hEq
    · exact hParameterCanonicalFresh (by simp [hEq])
    · exact hParameterCanonicalFresh (by simp [hEq])
  have hSubstitutionCondition :=
    code_substitution_spec_substitute_fresh
      (x#sourceId) (x#variableId) (x#termId) (x#resultId)
      replacement
      (x#sourceId) (x#variableId) (x#termId) (x#resultId)
      parameter hSubstitutionFresh
      hReplacementAdmissible
      (fun id hId =>
        hReplacementCanonicalFresh id
          (logical_base_closure_reserved_mem <| by
            simpa using
              List.mem_append_left
                [460, 461, 462, 463, 464, 465,
                  466, 467, 468, 469, 470] hId))
      (hVariableFixed sourceId (by simp))
      (hVariableFixed variableId (by simp))
      (hVariableFixed termId (by simp))
      (hVariableFixed resultId (by simp))
  let template
      (formulaTerm certificateTerm payloadTerm eigenTerm bodyNumericTerm
        carrierNumericTerm sourceTerm carrierTerm termCodeTerm variableTerm
        universalTerm resultTerm : SetTerm) : SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(7), payloadTerm⟩ₘ),
      payloadTerm ≐ₘ
        godel_pairₘ(⟨eigenTerm,
          godel_pairₘ(⟨bodyNumericTerm, carrierNumericTerm⟩ₘ)⟩ₘ),
      eigenTerm ∈ₘ ωₘ,
      logical_formula_payload_component_condition_with_ids
        sourceTerm bodyNumericTerm traceId indexId,
      logical_formula_payload_component_condition_with_ids
        carrierTerm carrierNumericTerm traceId indexId,
      term_codeₘ(termCodeTerm),
      carrierTerm ≐ₘ eq_codeₘ(termCodeTerm, termCodeTerm),
      variableTerm ≐ₘ var_codeₘ(numₘ(2) *ₘ eigenTerm),
      ¬ₘ quantifier_occurs_condition variableTerm sourceTerm,
      substitutableₘ(variableTerm, termCodeTerm, sourceTerm),
      canonical_forall_closure_code_condition
        sourceTerm variableTerm universalTerm,
      code_substitution_spec
        sourceTerm variableTerm termCodeTerm resultTerm,
      formulaTerm ≐ₘ
        specialization_axiom_code_term universalTerm resultTerm]
  let body : SetFormula :=
    template formulaCode certificate
      (x#payloadId) (x#eigenId) (x#bodyNumericId)
      (x#carrierNumericId) (x#sourceId) (x#carrierId)
      (x#termId) (x#variableId) (x#universalId) (x#resultId)
  let bodyResult : SetFormula :=
    template formulaCodeResult certificateResult
      (x#payloadId) (x#eigenId) (x#bodyNumericId)
      (x#carrierNumericId) (x#sourceId) (x#carrierId)
      (x#termId) (x#variableId) (x#universalId) (x#resultId)
  have hBodySubstitution :
      Formula.substituteFree SetSort.set parameter replacement body =
        bodyResult := by
    dsimp [body, bodyResult, template]
    rw [logical_certificate_conjunction_substituteFree]
    simp only [List.map]
    rw [hSourcePayload, hCarrierPayload,
      hSubstitutableCondition, hClosureCondition, hSubstitutionCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hQuantifierCondition,
      hFormulaCodeSubstitution, hCertificateSubstitution,
      hVariableFixed, hNumeralFixed]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId),
    (eigenId, x#eigenId),
    (bodyNumericId, x#bodyNumericId),
    (carrierNumericId, x#carrierNumericId),
    (sourceId, x#sourceId),
    (carrierId, x#carrierId),
    (termId, x#termId),
    (variableId, x#variableId),
    (universalId, x#universalId),
    (resultId, x#resultId)]
  have hAssignmentsFresh :
      parameter ∉
        assignments.map (fun assignment => assignment.1) := by
    intro hMember
    apply hParameterFresh
    have hIds :
        parameter = payloadId ∨
          parameter = eigenId ∨
            parameter = bodyNumericId ∨
              parameter = carrierNumericId ∨
                parameter = sourceId ∨
                  parameter = carrierId ∨
                    parameter = termId ∨
                      parameter = variableId ∨
                        parameter = universalId ∨
                          parameter = resultId := by
      simpa [assignments] using hMember
    rcases hIds with
      hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq
    all_goals simp [hEq]
  have hWrapped :=
    logical_certificate_exists_substitute_fresh
      parameter replacement assignments body bodyResult
      hAssignmentsFresh hReplacementAdmissible
      (fun id hId => by
        have hPrefix :
            id ∈
              [payloadId, eigenId, bodyNumericId, carrierNumericId,
                sourceId, carrierId, termId, variableId, universalId,
                resultId] := by
          simpa [assignments] using hId
        exact hReplacementFresh id (by
          simpa using
            List.mem_append_left [traceId, indexId] hPrefix))
      hBodySubstitution
  change
    Formula.substituteFree SetSort.set parameter replacement
        (Formula.existsFreeAssignments
          SetSort.set assignments body) =
      Formula.existsFreeAssignments
        SetSort.set assignments bodyResult
  exact hWrapped

/-- 对内部 binder 新鲜的替换逐公开参数穿过全称量词分配基础证书条件。 -/
theorem logical_forall_distribution_certificate_condition_with_ids_substitute_fresh
    (formulaCode certificate replacement
      formulaCodeResult certificateResult : SetTerm)
    (payloadId eigenId leftNumericId rightNumericId leftId rightId
      variableId closedImplicationId closedLeftId closedRightId
      traceId indexId parameter : FreeVarId)
    (hParameterFresh :
      parameter ∉
        [payloadId, eigenId, leftNumericId, rightNumericId, leftId, rightId,
          variableId, closedImplicationId, closedLeftId, closedRightId,
          traceId, indexId])
    (hParameterCanonicalFresh :
      parameter ∉
        [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ id,
        id ∈
            [payloadId, eigenId, leftNumericId, rightNumericId, leftId,
              rightId, variableId, closedImplicationId, closedLeftId,
              closedRightId, traceId, indexId] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hReplacementCanonicalFresh :
      ∀ id,
        id ∈
            [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
              465, 466, 467, 468, 469, 470] →
          (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set parameter replacement formulaCode =
        formulaCodeResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set parameter replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set parameter replacement
        (logical_forall_distribution_certificate_condition_with_ids
          formulaCode certificate payloadId eigenId leftNumericId
          rightNumericId leftId rightId variableId closedImplicationId
          closedLeftId closedRightId traceId indexId) =
      logical_forall_distribution_certificate_condition_with_ids
        formulaCodeResult certificateResult payloadId eigenId leftNumericId
        rightNumericId leftId rightId variableId closedImplicationId
        closedLeftId closedRightId traceId indexId := by
  have hParameterNe
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, eigenId, leftNumericId, rightNumericId, leftId,
            rightId, variableId, closedImplicationId, closedLeftId,
            closedRightId, traceId, indexId]) :
      parameter ≠ id := by
    intro hEq
    subst id
    exact hParameterFresh hId
  have hVariableFixed
      (id : FreeVarId)
      (hId :
        id ∈
          [payloadId, eigenId, leftNumericId, rightNumericId, leftId,
            rightId, variableId, closedImplicationId, closedLeftId,
            closedRightId, traceId, indexId]) :
      Term.substituteFree SetSort.set parameter replacement (x#id) =
        x#id := by
    have hNe := hParameterNe id hId
    simp [Term.substituteFree, set_variable, Ne.symm hNe]
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set parameter replacement (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hLeftPayload :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#leftId) (x#leftNumericId) replacement
      (x#leftId) (x#leftNumericId)
      parameter traceId indexId
      (hParameterNe traceId (by simp))
      (hParameterNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed leftId (by simp))
      (hVariableFixed leftNumericId (by simp))
  have hRightPayload :=
    logical_formula_payload_component_condition_with_ids_substitute_closed
      (x#rightId) (x#rightNumericId) replacement
      (x#rightId) (x#rightNumericId)
      parameter traceId indexId
      (hParameterNe traceId (by simp))
      (hParameterNe indexId (by simp))
      hReplacementAdmissible.2
      (hReplacementFresh traceId (by simp))
      (hReplacementFresh indexId (by simp))
      (hVariableFixed rightId (by simp))
      (hVariableFixed rightNumericId (by simp))
  have hLeftQuantifierCondition :=
    quantifier_occurs_condition_substituteFree
      parameter replacement (x#variableId) (x#leftId)
      (x#variableId) (x#leftId)
      (fun h =>
        hParameterCanonicalFresh
          (logical_base_occurrence_reserved_mem h))
      hReplacementAdmissible
      (fun id h =>
        hReplacementCanonicalFresh id
          (logical_base_occurrence_reserved_mem h))
      (hVariableFixed variableId (by simp))
      (hVariableFixed leftId (by simp))
  have hRightQuantifierCondition :=
    quantifier_occurs_condition_substituteFree
      parameter replacement (x#variableId) (x#rightId)
      (x#variableId) (x#rightId)
      (fun h =>
        hParameterCanonicalFresh
          (logical_base_occurrence_reserved_mem h))
      hReplacementAdmissible
      (fun id h =>
        hReplacementCanonicalFresh id
          (logical_base_occurrence_reserved_mem h))
      (hVariableFixed variableId (by simp))
      (hVariableFixed rightId (by simp))
  have hImplicationFixed :
      Term.substituteFree SetSort.set parameter replacement
          (imp_codeₘ(x#leftId, x#rightId)) =
        imp_codeₘ(x#leftId, x#rightId) := by
    simp [Term.substituteFree, hVariableFixed]
  have hImplicationClosure :=
    canonical_forall_closure_code_condition_substitute_fresh
      (imp_codeₘ(x#leftId, x#rightId))
      (x#variableId) (x#closedImplicationId) replacement
      (imp_codeₘ(x#leftId, x#rightId))
      (x#variableId) (x#closedImplicationId)
      parameter
      (fun h =>
        hParameterCanonicalFresh
          (logical_base_closure_reserved_mem h))
      hReplacementAdmissible
      (fun id h =>
        hReplacementCanonicalFresh id
          (logical_base_closure_reserved_mem h))
      hImplicationFixed
      (hVariableFixed variableId (by simp))
      (hVariableFixed closedImplicationId (by simp))
  have hLeftClosure :=
    canonical_forall_closure_code_condition_substitute_fresh
      (x#leftId) (x#variableId) (x#closedLeftId) replacement
      (x#leftId) (x#variableId) (x#closedLeftId)
      parameter
      (fun h =>
        hParameterCanonicalFresh
          (logical_base_closure_reserved_mem h))
      hReplacementAdmissible
      (fun id h =>
        hReplacementCanonicalFresh id
          (logical_base_closure_reserved_mem h))
      (hVariableFixed leftId (by simp))
      (hVariableFixed variableId (by simp))
      (hVariableFixed closedLeftId (by simp))
  have hRightClosure :=
    canonical_forall_closure_code_condition_substitute_fresh
      (x#rightId) (x#variableId) (x#closedRightId) replacement
      (x#rightId) (x#variableId) (x#closedRightId)
      parameter
      (fun h =>
        hParameterCanonicalFresh
          (logical_base_closure_reserved_mem h))
      hReplacementAdmissible
      (fun id h =>
        hReplacementCanonicalFresh id
          (logical_base_closure_reserved_mem h))
      (hVariableFixed rightId (by simp))
      (hVariableFixed variableId (by simp))
      (hVariableFixed closedRightId (by simp))
  let template
      (formulaTerm certificateTerm payloadTerm eigenTerm leftNumericTerm
        rightNumericTerm leftTerm rightTerm variableTerm
        closedImplicationTerm closedLeftTerm closedRightTerm : SetTerm) :
      SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(8), payloadTerm⟩ₘ),
      payloadTerm ≐ₘ
        godel_pairₘ(⟨eigenTerm,
          godel_pairₘ(⟨leftNumericTerm, rightNumericTerm⟩ₘ)⟩ₘ),
      eigenTerm ∈ₘ ωₘ,
      logical_formula_payload_component_condition_with_ids
        leftTerm leftNumericTerm traceId indexId,
      logical_formula_payload_component_condition_with_ids
        rightTerm rightNumericTerm traceId indexId,
      variableTerm ≐ₘ var_codeₘ(numₘ(2) *ₘ eigenTerm),
      ¬ₘ quantifier_occurs_condition variableTerm leftTerm,
      ¬ₘ quantifier_occurs_condition variableTerm rightTerm,
      canonical_forall_closure_code_condition
        (imp_codeₘ(leftTerm, rightTerm))
        variableTerm closedImplicationTerm,
      canonical_forall_closure_code_condition
        leftTerm variableTerm closedLeftTerm,
      canonical_forall_closure_code_condition
        rightTerm variableTerm closedRightTerm,
      formulaTerm ≐ₘ
        imp_codeₘ(
          closedImplicationTerm,
          imp_codeₘ(closedLeftTerm, closedRightTerm))]
  let body : SetFormula :=
    template formulaCode certificate
      (x#payloadId) (x#eigenId) (x#leftNumericId) (x#rightNumericId)
      (x#leftId) (x#rightId) (x#variableId)
      (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)
  let bodyResult : SetFormula :=
    template formulaCodeResult certificateResult
      (x#payloadId) (x#eigenId) (x#leftNumericId) (x#rightNumericId)
      (x#leftId) (x#rightId) (x#variableId)
      (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)
  have hBodySubstitution :
      Formula.substituteFree SetSort.set parameter replacement body =
        bodyResult := by
    dsimp [body, bodyResult, template]
    rw [logical_certificate_conjunction_substituteFree]
    simp only [List.map]
    rw [hLeftPayload, hRightPayload,
      hImplicationClosure, hLeftClosure, hRightClosure]
    simp [Formula.substituteFree, Term.substituteFree,
      hLeftQuantifierCondition, hRightQuantifierCondition,
      hFormulaCodeSubstitution, hCertificateSubstitution,
      hVariableFixed, hNumeralFixed]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId),
    (eigenId, x#eigenId),
    (leftNumericId, x#leftNumericId),
    (rightNumericId, x#rightNumericId),
    (leftId, x#leftId),
    (rightId, x#rightId),
    (variableId, x#variableId),
    (closedImplicationId, x#closedImplicationId),
    (closedLeftId, x#closedLeftId),
    (closedRightId, x#closedRightId)]
  have hAssignmentsFresh :
      parameter ∉
        assignments.map (fun assignment => assignment.1) := by
    intro hMember
    apply hParameterFresh
    have hIds :
        parameter = payloadId ∨
          parameter = eigenId ∨
            parameter = leftNumericId ∨
              parameter = rightNumericId ∨
                parameter = leftId ∨
                  parameter = rightId ∨
                    parameter = variableId ∨
                      parameter = closedImplicationId ∨
                        parameter = closedLeftId ∨
                          parameter = closedRightId := by
      simpa [assignments] using hMember
    rcases hIds with
      hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq
    all_goals simp [hEq]
  have hWrapped :=
    logical_certificate_exists_substitute_fresh
      parameter replacement assignments body bodyResult
      hAssignmentsFresh hReplacementAdmissible
      (fun id hId => by
        have hPrefix :
            id ∈
              [payloadId, eigenId, leftNumericId, rightNumericId,
                leftId, rightId, variableId, closedImplicationId,
                closedLeftId, closedRightId] := by
          simpa [assignments] using hId
        exact hReplacementFresh id (by
          simpa using
            List.mem_append_left [traceId, indexId] hPrefix))
      hBodySubstitution
  change
    Formula.substituteFree SetSort.set parameter replacement
        (Formula.existsFreeAssignments
          SetSort.set assignments body) =
      Formula.existsFreeAssignments
        SetSort.set assignments bodyResult
  exact hWrapped

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
