import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedSequenceCodeEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaBinderCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CanonicalForallOpenEncoding

/-!
# Hilbert 逻辑公理的对象层 checked 证书

逻辑证书 payload 编码一条非空自然数序列。末项是基础公理证书；此前每一项
都是一次全称闭包使用的自由变量编号。对象条件同时携带一条同长公式码轨迹：

* 第零项是当前证明行；
* 每个非末项由下一项做一次 canonical 全称闭包得到；
* 末项与基础公理证书逐字段对应。

因此 payload 的每个数值都参与检查；空序列码 `0` 不再能为任意逻辑公理作证。
本模块完全独立于对象理论公理枚举器，可供任意递归可枚举理论的证明码复用。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

namespace CertifiedProof

/-! ## 数值公式 payload -/

/--
`numericCode` 是公式 token 序列 `formulaCode` 的自然数编码。

除数值编码关系外显式保留一般公式码与有限签名/binder 词法条件。后者只保证
共享具名 decoder 可解析，不要求 payload 使用规范 quotation。
-/
def logical_formula_payload_component_condition_with_ids
    (formulaCode numericCode : SetTerm)
    (traceId indexId : FreeVarId) : SetFormula :=
  (formula_codeₘ(formulaCode) ∧ₘ
    fs_formula_replay_condition formulaCode) ∧ₘ
    nat_sequence_code_condition_with_ids
      formulaCode numericCode traceId indexId

theorem logical_formula_payload_component_condition_with_ids_admissible
    (formulaCode numericCode : SetTerm)
    (traceId indexId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hNumericCode : Term.Admissible numericCode SetSort.set) :
    Formula.Admissible
      (logical_formula_payload_component_condition_with_ids
        formulaCode numericCode traceId indexId) := by
  exact Formula.Admissible.conj
    (Formula.Admissible.conj
      (is_formula_code_formula_admissible hFormulaCode)
      (fs_formula_replay_condition_admissible
        formulaCode hFormulaCode))
    (nat_sequence_code_condition_with_ids_admissible
      formulaCode numericCode traceId indexId
      hFormulaCode hNumericCode)

/-!
单个 payload 字段的替换接口。

这个接口只暴露该字段的两个入口项；序列关系内部的对象量词由
`nat_sequence_code_condition_with_ids_substitute_closed` 统一处理。
-/
theorem logical_formula_payload_component_condition_with_ids_substitute_closed
    (formulaCode numericCode replacement formulaCodeResult numericCodeResult : SetTerm)
    (sourceId traceId indexId : FreeVarId)
    (hSourceNeTrace : sourceId ≠ traceId)
    (hSourceNeIndex : sourceId ≠ indexId)
    (hReplacementClosed : Term.BoundClosed replacement)
    (hReplacementFreshTrace :
      (SetSort.set, traceId) ∉ Term.freeSupport replacement)
    (hReplacementFreshIndex :
      (SetSort.set, indexId) ∉ Term.freeSupport replacement)
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaCode =
        formulaCodeResult)
    (hNumericCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement numericCode =
        numericCodeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_formula_payload_component_condition_with_ids
          formulaCode numericCode traceId indexId) =
      logical_formula_payload_component_condition_with_ids
        formulaCodeResult numericCodeResult traceId indexId := by
  have hSequenceSubstitution :=
    nat_sequence_code_condition_with_ids_substitute_closed
      formulaCode numericCode replacement
      formulaCodeResult numericCodeResult
      sourceId traceId indexId
      hSourceNeTrace hSourceNeIndex
      hReplacementClosed
      hReplacementFreshTrace hReplacementFreshIndex
      hFormulaCodeSubstitution hNumericCodeSubstitution
  have hReplaySubstitution :=
    fs_formula_replay_condition_substitute
      formulaCode replacement formulaCodeResult
      sourceId hFormulaCodeSubstitution
  simp only [
    logical_formula_payload_component_condition_with_ids,
    Formula.substituteFree, List.map]
  rw [hFormulaCodeSubstitution, hReplaySubstitution,
    hSequenceSubstitution]

/-! ## 有限字段合取 -/

/--
把一列证书字段右结合为一个对象公式；单字段不额外附加 `⊤`。

这一小层让 accept/reject 证明都能按字段列表递归，而不必反复手工匹配不同长度的
括号树。
-/
def logical_certificate_conjunction : List SetFormula → SetFormula
  | [] =>
      Formula.truth
  | [formula] =>
      formula
  | formula :: next :: rest =>
      formula ∧ₘ logical_certificate_conjunction (next :: rest)

/--
自由变量替换逐字段穿过有限证书合取。

证明只查看合取列表的外层结构，不展开任何字段；因此序列编码等含对象量词的字段
仍可由各自的捕获规避替换接口独立处理。
-/
theorem logical_certificate_conjunction_substituteFree
    (sourceId : FreeVarId) (replacement : SetTerm)
    (formulas : List SetFormula) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_certificate_conjunction formulas) =
      logical_certificate_conjunction
        (formulas.map
          (Formula.substituteFree SetSort.set sourceId replacement)) := by
  induction formulas with
  | nil =>
      rfl
  | cons formula formulas ih =>
      cases formulas with
      | nil =>
          rfl
      | cons next rest =>
          simp only [logical_certificate_conjunction,
            Formula.substituteFree, List.map]
          exact congrArg (Formula.conj
            (Formula.substituteFree SetSort.set sourceId replacement
              formula)) ih

theorem logical_certificate_conjunction_admissible
    (formulas : List SetFormula)
    (hFormulas :
      ∀ formula, formula ∈ formulas → Formula.Admissible formula) :
    Formula.Admissible (logical_certificate_conjunction formulas) := by
  induction formulas with
  | nil =>
      simpa [logical_certificate_conjunction] using
        (Formula.Admissible.truth :
          Formula.Admissible (Formula.truth : SetFormula))
  | cons formula formulas ih =>
      cases formulas with
      | nil =>
          simpa [logical_certificate_conjunction] using
            hFormulas formula (by simp)
      | cons next rest =>
          exact Formula.Admissible.conj
            (hFormulas formula (by simp))
            (by
              simpa [logical_certificate_conjunction] using
                ih (fun item hItem =>
                  hFormulas item (by simp [hItem])))

/-! ## 七类命题基础证书 -/

/-- 单公式 payload 的基础逻辑公理证书。 -/
def logical_unary_base_certificate_condition_with_ids
    (tag : Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId componentId traceId indexId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, payloadId],
    ∃ₘ[SetSort.set, sequenceId],
      ∃ₘ[SetSort.set, componentId],
        logical_certificate_conjunction [
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId,
          domₘ(x#sequenceId) ≐ₘ numₘ(1),
          logical_formula_payload_component_condition_with_ids
            (x#componentId) (x#sequenceId ·ₘ numₘ(0))
            traceId indexId,
          formulaCode ≐ₘ constructor (x#componentId)]

/-- 双公式 payload 的基础逻辑公理证书。 -/
def logical_binary_base_certificate_condition_with_ids
    (tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, payloadId],
    ∃ₘ[SetSort.set, sequenceId],
      ∃ₘ[SetSort.set, leftId],
        ∃ₘ[SetSort.set, rightId],
          logical_certificate_conjunction [
            certificate ≐ₘ
              godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
            nat_sequence_code_condition_with_ids
              (x#sequenceId) (x#payloadId) traceId indexId,
            domₘ(x#sequenceId) ≐ₘ numₘ(2),
            logical_formula_payload_component_condition_with_ids
              (x#leftId) (x#sequenceId ·ₘ numₘ(0))
              traceId indexId,
            logical_formula_payload_component_condition_with_ids
              (x#rightId) (x#sequenceId ·ₘ numₘ(1))
              traceId indexId,
            formulaCode ≐ₘ constructor (x#leftId) (x#rightId)]

/-- 三公式 payload 的基础逻辑公理证书。 -/
def logical_ternary_base_certificate_condition_with_ids
    (tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId firstId secondId thirdId traceId indexId :
      FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, payloadId],
    ∃ₘ[SetSort.set, sequenceId],
      ∃ₘ[SetSort.set, firstId],
        ∃ₘ[SetSort.set, secondId],
          ∃ₘ[SetSort.set, thirdId],
            logical_certificate_conjunction [
              certificate ≐ₘ
                godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
              nat_sequence_code_condition_with_ids
                (x#sequenceId) (x#payloadId) traceId indexId,
              domₘ(x#sequenceId) ≐ₘ numₘ(3),
              logical_formula_payload_component_condition_with_ids
                (x#firstId) (x#sequenceId ·ₘ numₘ(0))
                traceId indexId,
              logical_formula_payload_component_condition_with_ids
                (x#secondId) (x#sequenceId ·ₘ numₘ(1))
                traceId indexId,
              logical_formula_payload_component_condition_with_ids
                (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
                traceId indexId,
              formulaCode ≐ₘ
                constructor (x#firstId) (x#secondId) (x#thirdId)]

theorem logical_unary_base_certificate_condition_with_ids_admissible
    (tag : Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId componentId traceId indexId : FreeVarId)
    (hConstructor :
      ∀ component,
        Term.Admissible component SetSort.set →
          Term.Admissible (constructor component) SetSort.set)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (logical_unary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId componentId traceId indexId) := by
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hSequence :
      Term.Admissible (x#sequenceId) SetSort.set :=
    set_variable_admissible sequenceId
  have hComponent :
      Term.Admissible (x#componentId) SetSort.set :=
    set_variable_admissible componentId
  have hCertificateCode :
      Term.Admissible
        (godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _
      (ordered_pair_term_admissible _ _
        (finite_numeral_term_admissible tag) hPayload)
  have hCertificateEquality :=
    Formula.Admissible.equal hCertificate hCertificateCode
  have hSequenceCode :=
    nat_sequence_code_condition_with_ids_admissible
      (x#sequenceId) (x#payloadId) traceId indexId
      hSequence hPayload
  have hDomainEquality :=
    Formula.Admissible.equal
      (domain_term_admissible (x#sequenceId) hSequence)
      (finite_numeral_term_admissible 1)
  have hSequenceZero :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(0)) hSequence
      (finite_numeral_term_admissible 0)
  have hComponentPayload :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#componentId) (x#sequenceId ·ₘ numₘ(0))
      traceId indexId hComponent hSequenceZero
  have hFormulaEquality :=
    Formula.Admissible.equal hFormulaCode
      (hConstructor (x#componentId) hComponent)
  have hBody :
      Formula.Admissible
        (logical_certificate_conjunction [
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId,
          domₘ(x#sequenceId) ≐ₘ numₘ(1),
          logical_formula_payload_component_condition_with_ids
            (x#componentId) (x#sequenceId ·ₘ numₘ(0))
            traceId indexId,
          formulaCode ≐ₘ constructor (x#componentId)]) := by
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl | rfl | rfl
    · exact hCertificateEquality
    · exact hSequenceCode
    · exact hDomainEquality
    · exact hComponentPayload
    · exact hFormulaEquality
  simpa [logical_unary_base_certificate_condition_with_ids] using
    Formula.Admissible.exists_closeFreeAt SetSort.set payloadId <|
      Formula.Admissible.exists_closeFreeAt SetSort.set sequenceId <|
        Formula.Admissible.exists_closeFreeAt SetSort.set componentId <|
          hBody

theorem logical_binary_base_certificate_condition_with_ids_admissible
    (tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId)
    (hConstructor :
      ∀ left right,
        Term.Admissible left SetSort.set →
        Term.Admissible right SetSort.set →
          Term.Admissible (constructor left right) SetSort.set)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (logical_binary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId leftId rightId traceId indexId) := by
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hSequence :
      Term.Admissible (x#sequenceId) SetSort.set :=
    set_variable_admissible sequenceId
  have hLeft :
      Term.Admissible (x#leftId) SetSort.set :=
    set_variable_admissible leftId
  have hRight :
      Term.Admissible (x#rightId) SetSort.set :=
    set_variable_admissible rightId
  have hCertificateCode :
      Term.Admissible
        (godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _
      (ordered_pair_term_admissible _ _
        (finite_numeral_term_admissible tag) hPayload)
  have hCertificateEquality :=
    Formula.Admissible.equal hCertificate hCertificateCode
  have hSequenceCode :=
    nat_sequence_code_condition_with_ids_admissible
      (x#sequenceId) (x#payloadId) traceId indexId
      hSequence hPayload
  have hDomainEquality :=
    Formula.Admissible.equal
      (domain_term_admissible (x#sequenceId) hSequence)
      (finite_numeral_term_admissible 2)
  have hSequenceZero :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(0)) hSequence
      (finite_numeral_term_admissible 0)
  have hSequenceOne :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(1)) hSequence
      (finite_numeral_term_admissible 1)
  have hLeftPayload :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#leftId) (x#sequenceId ·ₘ numₘ(0))
      traceId indexId hLeft hSequenceZero
  have hRightPayload :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#rightId) (x#sequenceId ·ₘ numₘ(1))
      traceId indexId hRight hSequenceOne
  have hFormulaEquality :=
    Formula.Admissible.equal hFormulaCode
      (hConstructor (x#leftId) (x#rightId) hLeft hRight)
  have hBody :
      Formula.Admissible
        (logical_certificate_conjunction [
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId,
          domₘ(x#sequenceId) ≐ₘ numₘ(2),
          logical_formula_payload_component_condition_with_ids
            (x#leftId) (x#sequenceId ·ₘ numₘ(0))
            traceId indexId,
          logical_formula_payload_component_condition_with_ids
            (x#rightId) (x#sequenceId ·ₘ numₘ(1))
            traceId indexId,
          formulaCode ≐ₘ constructor (x#leftId) (x#rightId)]) := by
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateEquality
    · exact hSequenceCode
    · exact hDomainEquality
    · exact hLeftPayload
    · exact hRightPayload
    · exact hFormulaEquality
  simpa [logical_binary_base_certificate_condition_with_ids] using
    Formula.Admissible.exists_closeFreeAt SetSort.set payloadId <|
      Formula.Admissible.exists_closeFreeAt SetSort.set sequenceId <|
        Formula.Admissible.exists_closeFreeAt SetSort.set leftId <|
          Formula.Admissible.exists_closeFreeAt SetSort.set rightId <|
            hBody

theorem logical_ternary_base_certificate_condition_with_ids_admissible
    (tag : Nat)
    (constructor : SetTerm → SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId firstId secondId thirdId traceId indexId :
      FreeVarId)
    (hConstructor :
      ∀ first second third,
        Term.Admissible first SetSort.set →
        Term.Admissible second SetSort.set →
        Term.Admissible third SetSort.set →
          Term.Admissible (constructor first second third) SetSort.set)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (logical_ternary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId firstId secondId thirdId traceId indexId) := by
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hSequence :
      Term.Admissible (x#sequenceId) SetSort.set :=
    set_variable_admissible sequenceId
  have hFirst :
      Term.Admissible (x#firstId) SetSort.set :=
    set_variable_admissible firstId
  have hSecond :
      Term.Admissible (x#secondId) SetSort.set :=
    set_variable_admissible secondId
  have hThird :
      Term.Admissible (x#thirdId) SetSort.set :=
    set_variable_admissible thirdId
  have hCertificateCode :
      Term.Admissible
        (godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _
      (ordered_pair_term_admissible _ _
        (finite_numeral_term_admissible tag) hPayload)
  have hCertificateEquality :=
    Formula.Admissible.equal hCertificate hCertificateCode
  have hSequenceCode :=
    nat_sequence_code_condition_with_ids_admissible
      (x#sequenceId) (x#payloadId) traceId indexId
      hSequence hPayload
  have hDomainEquality :=
    Formula.Admissible.equal
      (domain_term_admissible (x#sequenceId) hSequence)
      (finite_numeral_term_admissible 3)
  have hSequenceZero :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(0)) hSequence
      (finite_numeral_term_admissible 0)
  have hSequenceOne :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(1)) hSequence
      (finite_numeral_term_admissible 1)
  have hSequenceTwo :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(2)) hSequence
      (finite_numeral_term_admissible 2)
  have hFirstPayload :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#firstId) (x#sequenceId ·ₘ numₘ(0))
      traceId indexId hFirst hSequenceZero
  have hSecondPayload :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#secondId) (x#sequenceId ·ₘ numₘ(1))
      traceId indexId hSecond hSequenceOne
  have hThirdPayload :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
      traceId indexId hThird hSequenceTwo
  have hFormulaEquality :=
    Formula.Admissible.equal hFormulaCode
      (hConstructor
        (x#firstId) (x#secondId) (x#thirdId)
        hFirst hSecond hThird)
  have hBody :
      Formula.Admissible
        (logical_certificate_conjunction [
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId,
          domₘ(x#sequenceId) ≐ₘ numₘ(3),
          logical_formula_payload_component_condition_with_ids
            (x#firstId) (x#sequenceId ·ₘ numₘ(0))
            traceId indexId,
          logical_formula_payload_component_condition_with_ids
            (x#secondId) (x#sequenceId ·ₘ numₘ(1))
            traceId indexId,
          logical_formula_payload_component_condition_with_ids
            (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
            traceId indexId,
          formulaCode ≐ₘ
            constructor (x#firstId) (x#secondId) (x#thirdId)]) := by
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateEquality
    · exact hSequenceCode
    · exact hDomainEquality
    · exact hFirstPayload
    · exact hSecondPayload
    · exact hThirdPayload
    · exact hFormulaEquality
  simpa [logical_ternary_base_certificate_condition_with_ids] using
    Formula.Admissible.exists_closeFreeAt SetSort.set payloadId <|
      Formula.Admissible.exists_closeFreeAt SetSort.set sequenceId <|
        Formula.Admissible.exists_closeFreeAt SetSort.set firstId <|
          Formula.Admissible.exists_closeFreeAt SetSort.set secondId <|
            Formula.Admissible.exists_closeFreeAt SetSort.set thirdId <|
              hBody

/-! ## 四类一阶基础证书 -/

/-- 全称特化证书：tag 7。 -/
def logical_specialization_certificate_condition_with_ids
    (formulaCode certificate : SetTerm)
    (payloadId eigenId bodyNumericId carrierNumericId sourceId carrierId
      termId variableId universalId resultId traceId indexId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, payloadId],
    ∃ₘ[SetSort.set, eigenId],
      ∃ₘ[SetSort.set, bodyNumericId],
        ∃ₘ[SetSort.set, carrierNumericId],
          ∃ₘ[SetSort.set, sourceId],
            ∃ₘ[SetSort.set, carrierId],
              ∃ₘ[SetSort.set, termId],
                ∃ₘ[SetSort.set, variableId],
                  ∃ₘ[SetSort.set, universalId],
                    ∃ₘ[SetSort.set, resultId],
                      logical_certificate_conjunction [
                        certificate ≐ₘ
                          godel_pairₘ(⟨numₘ(7), x#payloadId⟩ₘ),
                        x#payloadId ≐ₘ
                          godel_pairₘ(⟨x#eigenId,
                            godel_pairₘ(⟨x#bodyNumericId,
                              x#carrierNumericId⟩ₘ)⟩ₘ),
                        x#eigenId ∈ₘ ωₘ,
                        logical_formula_payload_component_condition_with_ids
                          (x#sourceId) (x#bodyNumericId)
                          traceId indexId,
                        logical_formula_payload_component_condition_with_ids
                          (x#carrierId) (x#carrierNumericId)
                          traceId indexId,
                        term_codeₘ(x#termId),
                        x#carrierId ≐ₘ
                          eq_codeₘ(x#termId, x#termId),
                        x#variableId ≐ₘ
                          var_codeₘ(numₘ(2) *ₘ x#eigenId),
                        ¬ₘ quantifier_occurs_condition
                          (x#variableId) (x#sourceId),
                        substitutableₘ(
                          x#variableId, x#termId, x#sourceId),
                        canonical_forall_closure_code_condition
                          (x#sourceId) (x#variableId) (x#universalId),
                        code_substitution_spec
                          (x#sourceId) (x#variableId)
                          (x#termId) (x#resultId),
                        formulaCode ≐ₘ
                          specialization_axiom_code_term
                            (x#universalId) (x#resultId)]

/-- 全称量词分配证书：tag 8。 -/
def logical_forall_distribution_certificate_condition_with_ids
    (formulaCode certificate : SetTerm)
    (payloadId eigenId leftNumericId rightNumericId leftId rightId
      variableId closedImplicationId closedLeftId closedRightId
      traceId indexId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, payloadId],
    ∃ₘ[SetSort.set, eigenId],
      ∃ₘ[SetSort.set, leftNumericId],
        ∃ₘ[SetSort.set, rightNumericId],
          ∃ₘ[SetSort.set, leftId],
            ∃ₘ[SetSort.set, rightId],
              ∃ₘ[SetSort.set, variableId],
                ∃ₘ[SetSort.set, closedImplicationId],
                  ∃ₘ[SetSort.set, closedLeftId],
                    ∃ₘ[SetSort.set, closedRightId],
                      logical_certificate_conjunction [
                        certificate ≐ₘ
                          godel_pairₘ(⟨numₘ(8), x#payloadId⟩ₘ),
                        x#payloadId ≐ₘ
                          godel_pairₘ(⟨x#eigenId,
                            godel_pairₘ(⟨x#leftNumericId,
                              x#rightNumericId⟩ₘ)⟩ₘ),
                        x#eigenId ∈ₘ ωₘ,
                        logical_formula_payload_component_condition_with_ids
                          (x#leftId) (x#leftNumericId)
                          traceId indexId,
                        logical_formula_payload_component_condition_with_ids
                          (x#rightId) (x#rightNumericId)
                          traceId indexId,
                        x#variableId ≐ₘ
                          var_codeₘ(numₘ(2) *ₘ x#eigenId),
                        ¬ₘ quantifier_occurs_condition
                          (x#variableId) (x#leftId),
                        ¬ₘ quantifier_occurs_condition
                          (x#variableId) (x#rightId),
                        canonical_forall_closure_code_condition
                          (imp_codeₘ(x#leftId, x#rightId))
                          (x#variableId) (x#closedImplicationId),
                        canonical_forall_closure_code_condition
                          (x#leftId) (x#variableId) (x#closedLeftId),
                        canonical_forall_closure_code_condition
                          (x#rightId) (x#variableId) (x#closedRightId),
                        formulaCode ≐ₘ
                          imp_codeₘ(
                            x#closedImplicationId,
                            imp_codeₘ(x#closedLeftId, x#closedRightId))]

/-- 无关全称引入证书：tag 9。 -/
def logical_vacuous_forall_certificate_condition_with_ids
    (formulaCode certificate : SetTerm)
    (payloadId eigenId bodyNumericId sourceId variableId universalId
      traceId indexId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, payloadId],
    ∃ₘ[SetSort.set, eigenId],
      ∃ₘ[SetSort.set, bodyNumericId],
        ∃ₘ[SetSort.set, sourceId],
          ∃ₘ[SetSort.set, variableId],
            ∃ₘ[SetSort.set, universalId],
              logical_certificate_conjunction [
                certificate ≐ₘ
                  godel_pairₘ(⟨numₘ(9), x#payloadId⟩ₘ),
                x#payloadId ≐ₘ
                  godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ),
                x#eigenId ∈ₘ ωₘ,
                logical_formula_payload_component_condition_with_ids
                  (x#sourceId) (x#bodyNumericId)
                  traceId indexId,
                x#variableId ≐ₘ
                  var_codeₘ(numₘ(2) *ₘ x#eigenId),
                ¬ₘ ((x#variableId) ∈ₘ varsₘ(x#sourceId)),
                canonical_forall_closure_code_condition
                  (x#sourceId) (x#variableId) (x#universalId),
                formulaCode ≐ₘ
                  imp_codeₘ(x#sourceId, x#universalId)]

/-- 等式替换证书：tag 10。 -/
def logical_equality_substitution_certificate_condition_with_ids
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId bodyId resultId traceId indexId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, payloadId],
    ∃ₘ[SetSort.set, sequenceId],
      ∃ₘ[SetSort.set, bodyId],
        ∃ₘ[SetSort.set, resultId],
          logical_certificate_conjunction [
            certificate ≐ₘ
              godel_pairₘ(⟨numₘ(10), x#payloadId⟩ₘ),
            nat_sequence_code_condition_with_ids
              (x#sequenceId) (x#payloadId) traceId indexId,
            domₘ(x#sequenceId) ≐ₘ numₘ(3),
            logical_formula_payload_component_condition_with_ids
              (x#bodyId) (x#sequenceId ·ₘ numₘ(2))
              traceId indexId,
            ¬ₘ quantifier_occurs_condition (var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0)))) (x#bodyId),
            substitutableₘ(var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0))), var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(1))), x#bodyId),
            code_substitution_spec
              (x#bodyId)
              (var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0))))
              (var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(1))))
              (x#resultId),
            formulaCode ≐ₘ
              imp_codeₘ(
                eq_codeₘ(
                  var_codeₘ(numₘ(2) *ₘ
                    (x#sequenceId ·ₘ numₘ(0))),
                  var_codeₘ(numₘ(2) *ₘ
                    (x#sequenceId ·ₘ numₘ(1)))),
                imp_codeₘ(x#bodyId, x#resultId))]

/-- 等式自反证书：tag 11。 -/
def logical_equality_reflexivity_certificate_condition_with_id
    (formulaCode certificate : SetTerm)
    (identifierId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, identifierId],
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(11), x#identifierId⟩ₘ),
      x#identifierId ∈ₘ ωₘ,
      formulaCode ≐ₘ
        eq_codeₘ(
          var_codeₘ(numₘ(2) *ₘ x#identifierId),
          var_codeₘ(numₘ(2) *ₘ x#identifierId))]

theorem logical_specialization_certificate_condition_with_ids_admissible
    (formulaCode certificate : SetTerm)
    (payloadId eigenId bodyNumericId carrierNumericId sourceId carrierId
      termId variableId universalId resultId traceId indexId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (logical_specialization_certificate_condition_with_ids
        formulaCode certificate payloadId eigenId bodyNumericId
        carrierNumericId sourceId carrierId termId variableId
        universalId resultId traceId indexId) := by
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hEigen :
      Term.Admissible (x#eigenId) SetSort.set :=
    set_variable_admissible eigenId
  have hBodyNumeric :
      Term.Admissible (x#bodyNumericId) SetSort.set :=
    set_variable_admissible bodyNumericId
  have hCarrierNumeric :
      Term.Admissible (x#carrierNumericId) SetSort.set :=
    set_variable_admissible carrierNumericId
  have hSource :
      Term.Admissible (x#sourceId) SetSort.set :=
    set_variable_admissible sourceId
  have hCarrier :
      Term.Admissible (x#carrierId) SetSort.set :=
    set_variable_admissible carrierId
  have hTerm :
      Term.Admissible (x#termId) SetSort.set :=
    set_variable_admissible termId
  have hVariable :
      Term.Admissible (x#variableId) SetSort.set :=
    set_variable_admissible variableId
  have hUniversal :
      Term.Admissible (x#universalId) SetSort.set :=
    set_variable_admissible universalId
  have hResult :
      Term.Admissible (x#resultId) SetSort.set :=
    set_variable_admissible resultId
  have hInnerPayloadPair :
      Term.Admissible
        (⟨x#bodyNumericId, x#carrierNumericId⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible _ _
      hBodyNumeric hCarrierNumeric
  have hInnerPayload :
      Term.Admissible
        (godel_pairₘ(⟨x#bodyNumericId,
          x#carrierNumericId⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _ hInnerPayloadPair
  have hPayloadPair :
      Term.Admissible
        (⟨x#eigenId,
          godel_pairₘ(⟨x#bodyNumericId,
            x#carrierNumericId⟩ₘ)⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible _ _ hEigen hInnerPayload
  have hPayloadCode :
      Term.Admissible
        (godel_pairₘ(⟨x#eigenId,
          godel_pairₘ(⟨x#bodyNumericId,
            x#carrierNumericId⟩ₘ)⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _ hPayloadPair
  have hCertificateCode :
      Term.Admissible
        (godel_pairₘ(⟨numₘ(7), x#payloadId⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _ <|
      ordered_pair_term_admissible _ _
        (finite_numeral_term_admissible 7) hPayload
  have hProduct :
      Term.Admissible (numₘ(2) *ₘ x#eigenId) SetSort.set :=
    natural_multiplication_term_admissible
      (numₘ(2)) (x#eigenId)
      (finite_numeral_term_admissible 2) hEigen
  have hVariableCode :
      Term.Admissible
        (var_codeₘ(numₘ(2) *ₘ x#eigenId)) SetSort.set :=
    variable_code_term_admissible
      (numₘ(2) *ₘ x#eigenId) hProduct
  have hCarrierCode :
      Term.Admissible
        (eq_codeₘ(x#termId, x#termId)) SetSort.set :=
    equality_formula_code_term_admissible
      (x#termId) (x#termId) hTerm hTerm
  have hSpecializationCode :
      Term.Admissible
        (specialization_axiom_code_term
          (x#universalId) (x#resultId)) SetSort.set :=
    specialization_axiom_code_term_admissible
      (x#universalId) (x#resultId) hUniversal hResult
  have hCertificateEquality :
      Formula.Admissible
        (certificate ≐ₘ
          godel_pairₘ(⟨numₘ(7), x#payloadId⟩ₘ)) :=
    Formula.Admissible.equal hCertificate hCertificateCode
  have hPayloadEquality :
      Formula.Admissible
        (x#payloadId ≐ₘ
          godel_pairₘ(⟨x#eigenId,
            godel_pairₘ(⟨x#bodyNumericId,
              x#carrierNumericId⟩ₘ)⟩ₘ)) :=
    Formula.Admissible.equal hPayload hPayloadCode
  have hEigenNatural :
      Formula.Admissible (x#eigenId ∈ₘ ωₘ) :=
    membership_formula_admissible hEigen omega_term_admissible
  have hSourcePayload :
      Formula.Admissible
        (logical_formula_payload_component_condition_with_ids
          (x#sourceId) (x#bodyNumericId)
          traceId indexId) :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#sourceId) (x#bodyNumericId)
      traceId indexId hSource hBodyNumeric
  have hCarrierPayload :
      Formula.Admissible
        (logical_formula_payload_component_condition_with_ids
          (x#carrierId) (x#carrierNumericId)
          traceId indexId) :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#carrierId) (x#carrierNumericId)
      traceId indexId hCarrier hCarrierNumeric
  have hTermCode :
      Formula.Admissible (term_codeₘ(x#termId)) :=
    is_term_code_formula_admissible hTerm
  have hCarrierEquality :
      Formula.Admissible
        (x#carrierId ≐ₘ
          eq_codeₘ(x#termId, x#termId)) :=
    Formula.Admissible.equal hCarrier hCarrierCode
  have hVariableEquality :
      Formula.Admissible
        (x#variableId ≐ₘ
          var_codeₘ(numₘ(2) *ₘ x#eigenId)) :=
    Formula.Admissible.equal hVariable hVariableCode
  have hNoQuantifier :
      Formula.Admissible
        (¬ₘ quantifier_occurs_condition
          (x#variableId) (x#sourceId)) :=
    Formula.Admissible.neg <|
      quantifier_occurs_condition_admissible
        (x#variableId) (x#sourceId) hVariable hSource
  have hSubstitutable :
      Formula.Admissible
        (substitutableₘ(x#variableId, x#termId, x#sourceId)) :=
    is_substitutable_formula_admissible
      hVariable hTerm hSource
  have hClosure :
      Formula.Admissible
        (canonical_forall_closure_code_condition
          (x#sourceId) (x#variableId) (x#universalId)) :=
    canonical_forall_closure_code_condition_admissible
      (x#sourceId) (x#variableId) (x#universalId)
      hSource hVariable hUniversal
  have hSubstitution :
      Formula.Admissible
        (code_substitution_spec
          (x#sourceId) (x#variableId)
          (x#termId) (x#resultId)) :=
    code_substitution_spec_admissible
      (x#sourceId) (x#variableId)
      (x#termId) (x#resultId)
      hSource hVariable hTerm hResult
  have hFormulaEquality :
      Formula.Admissible
        (formulaCode ≐ₘ
          specialization_axiom_code_term
            (x#universalId) (x#resultId)) :=
    Formula.Admissible.equal
      hFormulaCode hSpecializationCode
  have hCondition :
      Formula.Admissible
        (logical_certificate_conjunction [
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(7), x#payloadId⟩ₘ),
          x#payloadId ≐ₘ
            godel_pairₘ(⟨x#eigenId,
              godel_pairₘ(⟨x#bodyNumericId,
                x#carrierNumericId⟩ₘ)⟩ₘ),
          x#eigenId ∈ₘ ωₘ,
          logical_formula_payload_component_condition_with_ids
            (x#sourceId) (x#bodyNumericId)
            traceId indexId,
          logical_formula_payload_component_condition_with_ids
            (x#carrierId) (x#carrierNumericId)
            traceId indexId,
          term_codeₘ(x#termId),
          x#carrierId ≐ₘ
            eq_codeₘ(x#termId, x#termId),
          x#variableId ≐ₘ
            var_codeₘ(numₘ(2) *ₘ x#eigenId),
          ¬ₘ quantifier_occurs_condition
            (x#variableId) (x#sourceId),
          substitutableₘ(x#variableId, x#termId, x#sourceId),
          canonical_forall_closure_code_condition
            (x#sourceId) (x#variableId) (x#universalId),
          code_substitution_spec
            (x#sourceId) (x#variableId)
            (x#termId) (x#resultId),
          formulaCode ≐ₘ
            specialization_axiom_code_term
              (x#universalId) (x#resultId)]) := by
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateEquality
    · exact hPayloadEquality
    · exact hEigenNatural
    · exact hSourcePayload
    · exact hCarrierPayload
    · exact hTermCode
    · exact hCarrierEquality
    · exact hVariableEquality
    · exact hNoQuantifier
    · exact hSubstitutable
    · exact hClosure
    · exact hSubstitution
    · exact hFormulaEquality
  simpa [logical_specialization_certificate_condition_with_ids] using
    Formula.Admissible.exists_closeFreeAt SetSort.set payloadId <|
      Formula.Admissible.exists_closeFreeAt SetSort.set eigenId <|
        Formula.Admissible.exists_closeFreeAt SetSort.set bodyNumericId <|
          Formula.Admissible.exists_closeFreeAt
              SetSort.set carrierNumericId <|
            Formula.Admissible.exists_closeFreeAt SetSort.set sourceId <|
              Formula.Admissible.exists_closeFreeAt SetSort.set carrierId <|
                Formula.Admissible.exists_closeFreeAt SetSort.set termId <|
                  Formula.Admissible.exists_closeFreeAt
                      SetSort.set variableId <|
                    Formula.Admissible.exists_closeFreeAt
                        SetSort.set universalId <|
                      Formula.Admissible.exists_closeFreeAt
                        SetSort.set resultId hCondition

theorem logical_forall_distribution_certificate_condition_with_ids_admissible
    (formulaCode certificate : SetTerm)
    (payloadId eigenId leftNumericId rightNumericId leftId rightId
      variableId closedImplicationId closedLeftId closedRightId
      traceId indexId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (logical_forall_distribution_certificate_condition_with_ids
        formulaCode certificate payloadId eigenId leftNumericId
        rightNumericId leftId rightId variableId closedImplicationId
        closedLeftId closedRightId traceId indexId) := by
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hEigen :
      Term.Admissible (x#eigenId) SetSort.set :=
    set_variable_admissible eigenId
  have hLeftNumeric :
      Term.Admissible (x#leftNumericId) SetSort.set :=
    set_variable_admissible leftNumericId
  have hRightNumeric :
      Term.Admissible (x#rightNumericId) SetSort.set :=
    set_variable_admissible rightNumericId
  have hLeft :
      Term.Admissible (x#leftId) SetSort.set :=
    set_variable_admissible leftId
  have hRight :
      Term.Admissible (x#rightId) SetSort.set :=
    set_variable_admissible rightId
  have hVariable :
      Term.Admissible (x#variableId) SetSort.set :=
    set_variable_admissible variableId
  have hClosedImplication :
      Term.Admissible (x#closedImplicationId) SetSort.set :=
    set_variable_admissible closedImplicationId
  have hClosedLeft :
      Term.Admissible (x#closedLeftId) SetSort.set :=
    set_variable_admissible closedLeftId
  have hClosedRight :
      Term.Admissible (x#closedRightId) SetSort.set :=
    set_variable_admissible closedRightId
  have hInnerPayloadPair :
      Term.Admissible
        (⟨x#leftNumericId, x#rightNumericId⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible _ _
      hLeftNumeric hRightNumeric
  have hInnerPayload :
      Term.Admissible
        (godel_pairₘ(⟨x#leftNumericId,
          x#rightNumericId⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _ hInnerPayloadPair
  have hPayloadPair :
      Term.Admissible
        (⟨x#eigenId,
          godel_pairₘ(⟨x#leftNumericId,
            x#rightNumericId⟩ₘ)⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible _ _ hEigen hInnerPayload
  have hPayloadCode :
      Term.Admissible
        (godel_pairₘ(⟨x#eigenId,
          godel_pairₘ(⟨x#leftNumericId,
            x#rightNumericId⟩ₘ)⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _ hPayloadPair
  have hCertificateCode :
      Term.Admissible
        (godel_pairₘ(⟨numₘ(8), x#payloadId⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _ <|
      ordered_pair_term_admissible _ _
        (finite_numeral_term_admissible 8) hPayload
  have hProduct :
      Term.Admissible (numₘ(2) *ₘ x#eigenId) SetSort.set :=
    natural_multiplication_term_admissible
      (numₘ(2)) (x#eigenId)
      (finite_numeral_term_admissible 2) hEigen
  have hVariableCode :
      Term.Admissible
        (var_codeₘ(numₘ(2) *ₘ x#eigenId)) SetSort.set :=
    variable_code_term_admissible
      (numₘ(2) *ₘ x#eigenId) hProduct
  have hImplicationCode :
      Term.Admissible
        (imp_codeₘ(x#leftId, x#rightId)) SetSort.set :=
    implication_formula_code_term_admissible
      (x#leftId) (x#rightId) hLeft hRight
  have hClosedConclusionCode :
      Term.Admissible
        (imp_codeₘ(x#closedLeftId, x#closedRightId)) SetSort.set :=
    implication_formula_code_term_admissible
      (x#closedLeftId) (x#closedRightId)
      hClosedLeft hClosedRight
  have hDistributionCode :
      Term.Admissible
        (imp_codeₘ(
          x#closedImplicationId,
          imp_codeₘ(x#closedLeftId, x#closedRightId))) SetSort.set :=
    implication_formula_code_term_admissible _ _
      hClosedImplication hClosedConclusionCode
  have hCertificateEquality :
      Formula.Admissible
        (certificate ≐ₘ
          godel_pairₘ(⟨numₘ(8), x#payloadId⟩ₘ)) :=
    Formula.Admissible.equal hCertificate hCertificateCode
  have hPayloadEquality :
      Formula.Admissible
        (x#payloadId ≐ₘ
          godel_pairₘ(⟨x#eigenId,
            godel_pairₘ(⟨x#leftNumericId,
              x#rightNumericId⟩ₘ)⟩ₘ)) :=
    Formula.Admissible.equal hPayload hPayloadCode
  have hEigenNatural :
      Formula.Admissible (x#eigenId ∈ₘ ωₘ) :=
    membership_formula_admissible hEigen omega_term_admissible
  have hLeftPayload :
      Formula.Admissible
        (logical_formula_payload_component_condition_with_ids
          (x#leftId) (x#leftNumericId)
          traceId indexId) :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#leftId) (x#leftNumericId)
      traceId indexId hLeft hLeftNumeric
  have hRightPayload :
      Formula.Admissible
        (logical_formula_payload_component_condition_with_ids
          (x#rightId) (x#rightNumericId)
          traceId indexId) :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#rightId) (x#rightNumericId)
      traceId indexId hRight hRightNumeric
  have hVariableEquality :
      Formula.Admissible
        (x#variableId ≐ₘ
          var_codeₘ(numₘ(2) *ₘ x#eigenId)) :=
    Formula.Admissible.equal hVariable hVariableCode
  have hLeftNoQuantifier :
      Formula.Admissible
        (¬ₘ quantifier_occurs_condition
          (x#variableId) (x#leftId)) :=
    Formula.Admissible.neg <|
      quantifier_occurs_condition_admissible
        (x#variableId) (x#leftId) hVariable hLeft
  have hRightNoQuantifier :
      Formula.Admissible
        (¬ₘ quantifier_occurs_condition
          (x#variableId) (x#rightId)) :=
    Formula.Admissible.neg <|
      quantifier_occurs_condition_admissible
        (x#variableId) (x#rightId) hVariable hRight
  have hImplicationClosure :
      Formula.Admissible
        (canonical_forall_closure_code_condition
          (imp_codeₘ(x#leftId, x#rightId))
          (x#variableId) (x#closedImplicationId)) :=
    canonical_forall_closure_code_condition_admissible
      (imp_codeₘ(x#leftId, x#rightId))
      (x#variableId) (x#closedImplicationId)
      hImplicationCode hVariable hClosedImplication
  have hLeftClosure :
      Formula.Admissible
        (canonical_forall_closure_code_condition
          (x#leftId) (x#variableId) (x#closedLeftId)) :=
    canonical_forall_closure_code_condition_admissible
      (x#leftId) (x#variableId) (x#closedLeftId)
      hLeft hVariable hClosedLeft
  have hRightClosure :
      Formula.Admissible
        (canonical_forall_closure_code_condition
          (x#rightId) (x#variableId) (x#closedRightId)) :=
    canonical_forall_closure_code_condition_admissible
      (x#rightId) (x#variableId) (x#closedRightId)
      hRight hVariable hClosedRight
  have hFormulaEquality :
      Formula.Admissible
        (formulaCode ≐ₘ
          imp_codeₘ(
            x#closedImplicationId,
            imp_codeₘ(x#closedLeftId, x#closedRightId))) :=
    Formula.Admissible.equal
      hFormulaCode hDistributionCode
  have hCondition :
      Formula.Admissible
        (logical_certificate_conjunction [
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(8), x#payloadId⟩ₘ),
          x#payloadId ≐ₘ
            godel_pairₘ(⟨x#eigenId,
              godel_pairₘ(⟨x#leftNumericId,
                x#rightNumericId⟩ₘ)⟩ₘ),
          x#eigenId ∈ₘ ωₘ,
          logical_formula_payload_component_condition_with_ids
            (x#leftId) (x#leftNumericId)
            traceId indexId,
          logical_formula_payload_component_condition_with_ids
            (x#rightId) (x#rightNumericId)
            traceId indexId,
          x#variableId ≐ₘ
            var_codeₘ(numₘ(2) *ₘ x#eigenId),
          ¬ₘ quantifier_occurs_condition
            (x#variableId) (x#leftId),
          ¬ₘ quantifier_occurs_condition
            (x#variableId) (x#rightId),
          canonical_forall_closure_code_condition
            (imp_codeₘ(x#leftId, x#rightId))
            (x#variableId) (x#closedImplicationId),
          canonical_forall_closure_code_condition
            (x#leftId) (x#variableId) (x#closedLeftId),
          canonical_forall_closure_code_condition
            (x#rightId) (x#variableId) (x#closedRightId),
          formulaCode ≐ₘ
            imp_codeₘ(
              x#closedImplicationId,
              imp_codeₘ(x#closedLeftId, x#closedRightId))]) := by
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateEquality
    · exact hPayloadEquality
    · exact hEigenNatural
    · exact hLeftPayload
    · exact hRightPayload
    · exact hVariableEquality
    · exact hLeftNoQuantifier
    · exact hRightNoQuantifier
    · exact hImplicationClosure
    · exact hLeftClosure
    · exact hRightClosure
    · exact hFormulaEquality
  simpa [logical_forall_distribution_certificate_condition_with_ids] using
    Formula.Admissible.exists_closeFreeAt SetSort.set payloadId <|
      Formula.Admissible.exists_closeFreeAt SetSort.set eigenId <|
        Formula.Admissible.exists_closeFreeAt SetSort.set leftNumericId <|
          Formula.Admissible.exists_closeFreeAt SetSort.set rightNumericId <|
            Formula.Admissible.exists_closeFreeAt SetSort.set leftId <|
              Formula.Admissible.exists_closeFreeAt SetSort.set rightId <|
                Formula.Admissible.exists_closeFreeAt
                    SetSort.set variableId <|
                  Formula.Admissible.exists_closeFreeAt
                      SetSort.set closedImplicationId <|
                    Formula.Admissible.exists_closeFreeAt
                        SetSort.set closedLeftId <|
                      Formula.Admissible.exists_closeFreeAt
                        SetSort.set closedRightId hCondition

theorem logical_vacuous_forall_certificate_condition_with_ids_admissible
    (formulaCode certificate : SetTerm)
    (payloadId eigenId bodyNumericId sourceId variableId universalId
      traceId indexId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (logical_vacuous_forall_certificate_condition_with_ids
        formulaCode certificate payloadId eigenId bodyNumericId sourceId
        variableId universalId traceId indexId) := by
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hEigen :
      Term.Admissible (x#eigenId) SetSort.set :=
    set_variable_admissible eigenId
  have hBodyNumeric :
      Term.Admissible (x#bodyNumericId) SetSort.set :=
    set_variable_admissible bodyNumericId
  have hSource :
      Term.Admissible (x#sourceId) SetSort.set :=
    set_variable_admissible sourceId
  have hVariable :
      Term.Admissible (x#variableId) SetSort.set :=
    set_variable_admissible variableId
  have hUniversal :
      Term.Admissible (x#universalId) SetSort.set :=
    set_variable_admissible universalId
  have hCertificateCode :
      Term.Admissible
        (godel_pairₘ(⟨numₘ(9), x#payloadId⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _ <|
      ordered_pair_term_admissible _ _
        (finite_numeral_term_admissible 9) hPayload
  have hPayloadCode :
      Term.Admissible
        (godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _ <|
      ordered_pair_term_admissible _ _ hEigen hBodyNumeric
  have hProduct :
      Term.Admissible (numₘ(2) *ₘ x#eigenId) SetSort.set :=
    natural_multiplication_term_admissible
      (numₘ(2)) (x#eigenId)
      (finite_numeral_term_admissible 2) hEigen
  have hVariableCode :
      Term.Admissible
        (var_codeₘ(numₘ(2) *ₘ x#eigenId)) SetSort.set :=
    variable_code_term_admissible
      (numₘ(2) *ₘ x#eigenId) hProduct
  have hCertificateEquality :
      Formula.Admissible
        (certificate ≐ₘ
          godel_pairₘ(⟨numₘ(9), x#payloadId⟩ₘ)) :=
    Formula.Admissible.equal hCertificate hCertificateCode
  have hPayloadEquality :
      Formula.Admissible
        (x#payloadId ≐ₘ
          godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ)) :=
    Formula.Admissible.equal hPayload hPayloadCode
  have hEigenNatural :
      Formula.Admissible (x#eigenId ∈ₘ ωₘ) :=
    membership_formula_admissible hEigen omega_term_admissible
  have hSourcePayload :
      Formula.Admissible
        (logical_formula_payload_component_condition_with_ids
          (x#sourceId) (x#bodyNumericId) traceId indexId) :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#sourceId) (x#bodyNumericId) traceId indexId
      hSource hBodyNumeric
  have hVariableEquality :
      Formula.Admissible
        (x#variableId ≐ₘ
          var_codeₘ(numₘ(2) *ₘ x#eigenId)) :=
    Formula.Admissible.equal hVariable hVariableCode
  have hVariableCollection :
      Term.Admissible (varsₘ(x#sourceId)) SetSort.set :=
    variable_collection_term_admissible (x#sourceId) hSource
  have hNonoccurrence :
      Formula.Admissible
        (¬ₘ ((x#variableId) ∈ₘ varsₘ(x#sourceId))) :=
    Formula.Admissible.neg <|
      membership_formula_admissible hVariable hVariableCollection
  have hClosure :
      Formula.Admissible
        (canonical_forall_closure_code_condition
          (x#sourceId) (x#variableId) (x#universalId)) :=
    canonical_forall_closure_code_condition_admissible
      (x#sourceId) (x#variableId) (x#universalId)
      hSource hVariable hUniversal
  have hFormulaEquality :
      Formula.Admissible
        (formulaCode ≐ₘ
          imp_codeₘ(x#sourceId, x#universalId)) :=
    Formula.Admissible.equal hFormulaCode <|
      implication_formula_code_term_admissible
        (x#sourceId) (x#universalId) hSource hUniversal
  have hBody :
      Formula.Admissible
        (logical_certificate_conjunction [
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(9), x#payloadId⟩ₘ),
          x#payloadId ≐ₘ
            godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ),
          x#eigenId ∈ₘ ωₘ,
          logical_formula_payload_component_condition_with_ids
            (x#sourceId) (x#bodyNumericId)
            traceId indexId,
          x#variableId ≐ₘ
            var_codeₘ(numₘ(2) *ₘ x#eigenId),
          ¬ₘ ((x#variableId) ∈ₘ varsₘ(x#sourceId)),
          canonical_forall_closure_code_condition
            (x#sourceId) (x#variableId) (x#universalId),
          formulaCode ≐ₘ
            imp_codeₘ(x#sourceId, x#universalId)]) := by
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateEquality
    · exact hPayloadEquality
    · exact hEigenNatural
    · exact hSourcePayload
    · exact hVariableEquality
    · exact hNonoccurrence
    · exact hClosure
    · exact hFormulaEquality
  simpa [logical_vacuous_forall_certificate_condition_with_ids] using
    Formula.Admissible.exists_closeFreeAt SetSort.set payloadId <|
      Formula.Admissible.exists_closeFreeAt SetSort.set eigenId <|
        Formula.Admissible.exists_closeFreeAt SetSort.set bodyNumericId <|
          Formula.Admissible.exists_closeFreeAt SetSort.set sourceId <|
            Formula.Admissible.exists_closeFreeAt SetSort.set variableId <|
              Formula.Admissible.exists_closeFreeAt
                SetSort.set universalId hBody

theorem logical_equality_substitution_certificate_condition_with_ids_admissible
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId bodyId resultId traceId indexId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (logical_equality_substitution_certificate_condition_with_ids
        formulaCode certificate payloadId sequenceId bodyId resultId
        traceId indexId) := by
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hSequence :
      Term.Admissible (x#sequenceId) SetSort.set :=
    set_variable_admissible sequenceId
  have hBodyCode :
      Term.Admissible (x#bodyId) SetSort.set :=
    set_variable_admissible bodyId
  have hResult :
      Term.Admissible (x#resultId) SetSort.set :=
    set_variable_admissible resultId
  have hSequenceZero :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(0)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(0)) hSequence
      (finite_numeral_term_admissible 0)
  have hSequenceOne :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(1)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(1)) hSequence
      (finite_numeral_term_admissible 1)
  have hSequenceTwo :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(2)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(2)) hSequence
      (finite_numeral_term_admissible 2)
  have hLeftProduct :
      Term.Admissible
        (numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0))) SetSort.set :=
    natural_multiplication_term_admissible
      (numₘ(2)) (x#sequenceId ·ₘ numₘ(0))
      (finite_numeral_term_admissible 2) hSequenceZero
  have hRightProduct :
      Term.Admissible
        (numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(1))) SetSort.set :=
    natural_multiplication_term_admissible
      (numₘ(2)) (x#sequenceId ·ₘ numₘ(1))
      (finite_numeral_term_admissible 2) hSequenceOne
  have hLeftVariable :
      Term.Admissible
        (var_codeₘ(numₘ(2) *ₘ
          (x#sequenceId ·ₘ numₘ(0)))) SetSort.set :=
    variable_code_term_admissible
      (numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0))) hLeftProduct
  have hRightVariable :
      Term.Admissible
        (var_codeₘ(numₘ(2) *ₘ
          (x#sequenceId ·ₘ numₘ(1)))) SetSort.set :=
    variable_code_term_admissible
      (numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(1))) hRightProduct
  have hCertificateEquality :
      Formula.Admissible
        (certificate ≐ₘ
          godel_pairₘ(⟨numₘ(10), x#payloadId⟩ₘ)) :=
    Formula.Admissible.equal hCertificate <|
      godel_pairing_term_admissible _ <|
        ordered_pair_term_admissible _ _
          (finite_numeral_term_admissible 10) hPayload
  have hSequenceCode :
      Formula.Admissible
        (nat_sequence_code_condition_with_ids
          (x#sequenceId) (x#payloadId) traceId indexId) :=
    nat_sequence_code_condition_with_ids_admissible
      (x#sequenceId) (x#payloadId) traceId indexId
      hSequence hPayload
  have hDomainEquality :
      Formula.Admissible
        (domₘ(x#sequenceId) ≐ₘ numₘ(3)) :=
    Formula.Admissible.equal
      (domain_term_admissible (x#sequenceId) hSequence)
      (finite_numeral_term_admissible 3)
  have hBodyPayload :
      Formula.Admissible
        (logical_formula_payload_component_condition_with_ids
          (x#bodyId) (x#sequenceId ·ₘ numₘ(2))
          traceId indexId) :=
    logical_formula_payload_component_condition_with_ids_admissible
      (x#bodyId) (x#sequenceId ·ₘ numₘ(2))
      traceId indexId hBodyCode hSequenceTwo
  have hSubstitution :
      Formula.Admissible
        (code_substitution_spec
          (x#bodyId)
          (var_codeₘ(numₘ(2) *ₘ
            (x#sequenceId ·ₘ numₘ(0))))
          (var_codeₘ(numₘ(2) *ₘ
            (x#sequenceId ·ₘ numₘ(1))))
          (x#resultId)) :=
    code_substitution_spec_admissible
      (x#bodyId)
      (var_codeₘ(numₘ(2) *ₘ
        (x#sequenceId ·ₘ numₘ(0))))
      (var_codeₘ(numₘ(2) *ₘ
        (x#sequenceId ·ₘ numₘ(1))))
      (x#resultId)
      hBodyCode hLeftVariable hRightVariable hResult
  have hVariableEqualityCode :
      Term.Admissible
        (eq_codeₘ(
          var_codeₘ(numₘ(2) *ₘ
            (x#sequenceId ·ₘ numₘ(0))),
          var_codeₘ(numₘ(2) *ₘ
            (x#sequenceId ·ₘ numₘ(1))))) SetSort.set :=
    equality_formula_code_term_admissible _ _
      hLeftVariable hRightVariable
  have hBodyImplicationCode :
      Term.Admissible
        (imp_codeₘ(x#bodyId, x#resultId)) SetSort.set :=
    implication_formula_code_term_admissible
      (x#bodyId) (x#resultId) hBodyCode hResult
  have hFormulaEquality :
      Formula.Admissible
        (formulaCode ≐ₘ
          imp_codeₘ(
            eq_codeₘ(
              var_codeₘ(numₘ(2) *ₘ
                (x#sequenceId ·ₘ numₘ(0))),
              var_codeₘ(numₘ(2) *ₘ
                (x#sequenceId ·ₘ numₘ(1)))),
            imp_codeₘ(x#bodyId, x#resultId))) :=
    Formula.Admissible.equal hFormulaCode <|
      implication_formula_code_term_admissible _ _
        hVariableEqualityCode hBodyImplicationCode
  have hCondition :
      Formula.Admissible
        (logical_certificate_conjunction [
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(10), x#payloadId⟩ₘ),
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId,
          domₘ(x#sequenceId) ≐ₘ numₘ(3),
          logical_formula_payload_component_condition_with_ids
            (x#bodyId) (x#sequenceId ·ₘ numₘ(2))
            traceId indexId,
          ¬ₘ quantifier_occurs_condition (var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0)))) (x#bodyId),
          substitutableₘ(var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(0))), var_codeₘ(numₘ(2) *ₘ (x#sequenceId ·ₘ numₘ(1))), x#bodyId),
          code_substitution_spec
            (x#bodyId)
            (var_codeₘ(numₘ(2) *ₘ
              (x#sequenceId ·ₘ numₘ(0))))
            (var_codeₘ(numₘ(2) *ₘ
              (x#sequenceId ·ₘ numₘ(1))))
            (x#resultId),
          formulaCode ≐ₘ
            imp_codeₘ(
              eq_codeₘ(
                var_codeₘ(numₘ(2) *ₘ
                  (x#sequenceId ·ₘ numₘ(0))),
                var_codeₘ(numₘ(2) *ₘ
                  (x#sequenceId ·ₘ numₘ(1)))),
              imp_codeₘ(x#bodyId, x#resultId))]) := by
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateEquality
    · exact hSequenceCode
    · exact hDomainEquality
    · exact hBodyPayload
    · exact Formula.Admissible.neg <|
        quantifier_occurs_condition_admissible _ _
          hLeftVariable hBodyCode
    · exact is_substitutable_formula_admissible
        hLeftVariable hRightVariable hBodyCode
    · exact hSubstitution
    · exact hFormulaEquality
  simpa [logical_equality_substitution_certificate_condition_with_ids] using
    Formula.Admissible.exists_closeFreeAt SetSort.set payloadId <|
      Formula.Admissible.exists_closeFreeAt SetSort.set sequenceId <|
        Formula.Admissible.exists_closeFreeAt SetSort.set bodyId <|
          Formula.Admissible.exists_closeFreeAt
            SetSort.set resultId hCondition

theorem logical_equality_reflexivity_certificate_condition_with_id_admissible
    (formulaCode certificate : SetTerm)
    (identifierId : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (logical_equality_reflexivity_certificate_condition_with_id
        formulaCode certificate identifierId) := by
  have hIdentifier :
      Term.Admissible (x#identifierId) SetSort.set :=
    set_variable_admissible identifierId
  have hProduct :
      Term.Admissible (numₘ(2) *ₘ x#identifierId) SetSort.set :=
    natural_multiplication_term_admissible
      (numₘ(2)) (x#identifierId)
      (finite_numeral_term_admissible 2) hIdentifier
  have hVariable :
      Term.Admissible
        (var_codeₘ(numₘ(2) *ₘ x#identifierId)) SetSort.set :=
    variable_code_term_admissible
      (numₘ(2) *ₘ x#identifierId) hProduct
  have hCertificateEquality :
      Formula.Admissible
        (certificate ≐ₘ
          godel_pairₘ(⟨numₘ(11), x#identifierId⟩ₘ)) :=
    Formula.Admissible.equal hCertificate <|
      godel_pairing_term_admissible _ <|
        ordered_pair_term_admissible _ _
          (finite_numeral_term_admissible 11) hIdentifier
  have hNatural :
      Formula.Admissible (x#identifierId ∈ₘ ωₘ) :=
    membership_formula_admissible hIdentifier omega_term_admissible
  have hFormulaEquality :
      Formula.Admissible
        (formulaCode ≐ₘ
          eq_codeₘ(
            var_codeₘ(numₘ(2) *ₘ x#identifierId),
            var_codeₘ(numₘ(2) *ₘ x#identifierId))) :=
    Formula.Admissible.equal hFormulaCode <|
      equality_formula_code_term_admissible _ _
        hVariable hVariable
  have hBody :
      Formula.Admissible
        (logical_certificate_conjunction [
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(11), x#identifierId⟩ₘ),
          x#identifierId ∈ₘ ωₘ,
          formulaCode ≐ₘ
            eq_codeₘ(
              var_codeₘ(numₘ(2) *ₘ x#identifierId),
              var_codeₘ(numₘ(2) *ₘ x#identifierId))]) := by
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl
    · exact hCertificateEquality
    · exact hNatural
    · exact hFormulaEquality
  simpa [logical_equality_reflexivity_certificate_condition_with_id] using
    Formula.Admissible.exists_closeFreeAt
      SetSort.set identifierId hBody

/-! ## 基础证书总条件 -/

def logical_certificate_fresh_base (terms : List SetTerm) :
    FreeVarId :=
  700 + FreshVariable.fresh_id SetSort.set
    (terms.map fun term => term ≐ₘ term)

/-- 显式 binder 基址下十二类基础 Hilbert 公理与 checked payload 的精确关系。 -/
def logical_base_certificate_condition_with_base
    (formulaCode certificate : SetTerm)
    (base : FreeVarId) : SetFormula :=
  let traceId := base + 40
  let indexId := base + 41
  (logical_ternary_base_certificate_condition_with_ids
      0 implication_distribution_axiom_code_term
      formulaCode certificate
      base (base + 1) (base + 2) (base + 3) (base + 4)
      traceId indexId) ∨ₘ
    ((logical_unary_base_certificate_condition_with_ids
        1 self_implication_axiom_code_term
        formulaCode certificate
        (base + 5) (base + 6) (base + 7) traceId indexId) ∨ₘ
      ((logical_binary_base_certificate_condition_with_ids
          2 weakening_axiom_code_term
          formulaCode certificate
          (base + 8) (base + 9) (base + 10) (base + 11)
          traceId indexId) ∨ₘ
        ((logical_binary_base_certificate_condition_with_ids
            3 contradiction_axiom_code_term
            formulaCode certificate
            (base + 12) (base + 13) (base + 14) (base + 15)
            traceId indexId) ∨ₘ
          ((logical_unary_base_certificate_condition_with_ids
              4 classical_axiom_code_term
              formulaCode certificate
              (base + 16) (base + 17) (base + 18)
              traceId indexId) ∨ₘ
            ((logical_binary_base_certificate_condition_with_ids
                5 explosion_axiom_code_term
                formulaCode certificate
                (base + 19) (base + 20) (base + 21) (base + 22)
                traceId indexId) ∨ₘ
              ((logical_binary_base_certificate_condition_with_ids
                  6 case_analysis_axiom_code_term
                  formulaCode certificate
                  (base + 23) (base + 24) (base + 25) (base + 26)
                  traceId indexId) ∨ₘ
                ((logical_specialization_certificate_condition_with_ids
                    formulaCode certificate
                    (base + 27) (base + 28) (base + 29) (base + 30)
                    (base + 31) (base + 32) (base + 33) (base + 34)
                    (base + 35) (base + 36) traceId indexId) ∨ₘ
                  ((logical_forall_distribution_certificate_condition_with_ids
                      formulaCode certificate
                      (base + 42) (base + 43) (base + 44) (base + 45)
                      (base + 46) (base + 47) (base + 48) (base + 49)
                      (base + 50) (base + 51) traceId indexId) ∨ₘ
                    ((logical_vacuous_forall_certificate_condition_with_ids
                        formulaCode certificate
                        (base + 52) (base + 53) (base + 54) (base + 55)
                        (base + 56) (base + 57) traceId indexId) ∨ₘ
                      ((logical_equality_substitution_certificate_condition_with_ids
                          formulaCode certificate
                          (base + 58) (base + 59) (base + 60) (base + 61)
                          traceId indexId) ∨ₘ
                        logical_equality_reflexivity_certificate_condition_with_id
                          formulaCode certificate (base + 62)))))))))))

/-- 自动选择内部 binder 的基础逻辑证书条件。 -/
def logical_base_certificate_condition
    (formulaCode certificate : SetTerm) : SetFormula :=
  logical_base_certificate_condition_with_base
    formulaCode certificate
    (logical_certificate_fresh_base [formulaCode, certificate])

theorem logical_base_certificate_condition_with_base_admissible
    (formulaCode certificate : SetTerm)
    (base : FreeVarId)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (logical_base_certificate_condition_with_base
        formulaCode certificate base) := by
  unfold logical_base_certificate_condition_with_base
  repeat' apply Formula.Admissible.disj
  · exact logical_ternary_base_certificate_condition_with_ids_admissible
      0 implication_distribution_axiom_code_term
      formulaCode certificate _ _ _ _ _ _ _
      (fun first second third hFirst hSecond hThird =>
        implication_distribution_axiom_code_term_admissible
          first second third hFirst hSecond hThird)
      hFormulaCode hCertificate
  · exact logical_unary_base_certificate_condition_with_ids_admissible
      1 self_implication_axiom_code_term
      formulaCode certificate _ _ _ _ _
      (fun component hComponent =>
        self_implication_axiom_code_term_admissible
          component hComponent)
      hFormulaCode hCertificate
  · exact logical_binary_base_certificate_condition_with_ids_admissible
      2 weakening_axiom_code_term
      formulaCode certificate _ _ _ _ _ _
      (fun left right hLeft hRight =>
        weakening_axiom_code_term_admissible
          left right hLeft hRight)
      hFormulaCode hCertificate
  · exact logical_binary_base_certificate_condition_with_ids_admissible
      3 contradiction_axiom_code_term
      formulaCode certificate _ _ _ _ _ _
      (fun left right hLeft hRight =>
        contradiction_axiom_code_term_admissible
          left right hLeft hRight)
      hFormulaCode hCertificate
  · exact logical_unary_base_certificate_condition_with_ids_admissible
      4 classical_axiom_code_term
      formulaCode certificate _ _ _ _ _
      (fun component hComponent =>
        classical_axiom_code_term_admissible
          component hComponent)
      hFormulaCode hCertificate
  · exact logical_binary_base_certificate_condition_with_ids_admissible
      5 explosion_axiom_code_term
      formulaCode certificate _ _ _ _ _ _
      (fun left right hLeft hRight =>
        explosion_axiom_code_term_admissible
          left right hLeft hRight)
      hFormulaCode hCertificate
  · exact logical_binary_base_certificate_condition_with_ids_admissible
      6 case_analysis_axiom_code_term
      formulaCode certificate _ _ _ _ _ _
      (fun left right hLeft hRight =>
        case_analysis_axiom_code_term_admissible
          left right hLeft hRight)
      hFormulaCode hCertificate
  · exact logical_specialization_certificate_condition_with_ids_admissible
      formulaCode certificate _ _ _ _ _ _ _ _ _ _ _ _
      hFormulaCode hCertificate
  · exact
      logical_forall_distribution_certificate_condition_with_ids_admissible
        formulaCode certificate _ _ _ _ _ _ _ _ _ _ _ _
        hFormulaCode hCertificate
  · exact logical_vacuous_forall_certificate_condition_with_ids_admissible
      formulaCode certificate _ _ _ _ _ _ _ _
      hFormulaCode hCertificate
  · exact
      logical_equality_substitution_certificate_condition_with_ids_admissible
        formulaCode certificate _ _ _ _ _ _
        hFormulaCode hCertificate
  · exact
      logical_equality_reflexivity_certificate_condition_with_id_admissible
        formulaCode certificate _
        hFormulaCode hCertificate

theorem logical_base_certificate_condition_admissible
    (formulaCode certificate : SetTerm)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (logical_base_certificate_condition formulaCode certificate) := by
  exact logical_base_certificate_condition_with_base_admissible
    formulaCode certificate _ hFormulaCode hCertificate

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
