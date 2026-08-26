import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedProofCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedSequenceCodeEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding

/-!
# 证书化 Hilbert 证明码的对象层条件

本模块只编码“有限证明轨迹 + 每行有限证书”。理论公理行不再读取
`formula ∈ theory`，而是要求证书码通过调用方提供的对象层 verifier。
外部 `FSCheckedHilbertTrace` 使用相同的三类标签并保留实际布尔检查，
因此对象层与元层的行结构可以逐行对齐。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 证书 verifier 合同 -/

/-- 对象层证书 verifier 的最小语法合同。 -/
structure ObjectCertificateVerifier where
  formula_condition : SetTerm → SetFormula
  formula_condition_admissible :
    ∀ formula,
      Term.Admissible formula SetSort.set →
      Formula.Admissible (formula_condition formula)
  condition : SetTerm → SetTerm → SetFormula
  condition_admissible :
    ∀ formula certificate,
      Term.Admissible formula SetSort.set →
      Term.Admissible certificate SetSort.set →
      Formula.Admissible (condition formula certificate)

namespace CertifiedProof

/-! ## 行证书标签 -/

/-- 逻辑公理行的证书码，第二坐标保存语法证书 payload。 -/
def logical_certificate_code (certificate : SetTerm) : SetTerm :=
  godel_pairₘ(⟨numₘ(0), certificate⟩ₘ)

/-- 理论公理行的证书码，第二坐标保存枚举证书 payload。 -/
def theory_certificate_code (certificate : SetTerm) : SetTerm :=
  godel_pairₘ(⟨numₘ(1), certificate⟩ₘ)

/-- MP 行的证书码，第二坐标保存蕴含行与前件行索引。 -/
def modus_ponens_certificate_code
    (implicationIndex premiseIndex : SetTerm) : SetTerm :=
  godel_pairₘ(⟨numₘ(2), godel_pairₘ(
    ⟨implicationIndex, premiseIndex⟩ₘ)⟩ₘ)

/-! ## 证书载荷边界 -/

/--
逻辑与理论证书的载荷严格受当前整行证书码控制。

这个边界对规范 Gödel 对码是冗余真命题，但把负向 checked replay 所需的
有限搜索空间显式保留在对象证明谓词中，避免反演任意对象自然数上的配对函数。
-/
def certificate_payload_bound
    (certificates index payload : SetTerm) : SetFormula :=
  payload ∈ₘ Sₘ(certificates ·ₘ index)

/-! ## 逐行条件 -/

/-- 证书码为 MP 时所需的两个严格早先行索引。 -/
def modus_ponens_line_condition_with_ids
    (sequence certificates index : SetTerm)
    (implicationIndex premiseIndex : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, implicationIndex],
    (x#implicationIndex ∈ₘ index) ∧ₘ
      (∃ₘ[SetSort.set, premiseIndex],
        (x#premiseIndex ∈ₘ x#implicationIndex) ∧ₘ
          (((certificates ·ₘ index) ≐ₘ
              modus_ponens_certificate_code
                (x#implicationIndex) (x#premiseIndex)) ∧ₘ
            modus_ponensₘ(
              sequence ·ₘ x#premiseIndex,
              sequence ·ₘ x#implicationIndex,
              sequence ·ₘ index)))

/-- 理论证书行的显式 payload 见证。 -/
def theory_certificate_line_condition_with_id
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (certificateCodeId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, certificateCodeId],
    certificate_payload_bound
        certificates index (x#certificateCodeId) ∧ₘ
      ((certificates ·ₘ index ≐ₘ
          theory_certificate_code (x#certificateCodeId)) ∧ₘ
        verifier.condition
          (sequence ·ₘ index) (x#certificateCodeId))

/--
证书化 Hilbert 逐行合法性。

第一分支要求逻辑公理证书；第二分支要求 verifier 通过枚举证书；
第三分支要求 MP 证书中的两个索引严格早于当前行。
-/
def line_condition_with_ids
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId) :
    SetFormula :=
  (∃ₘ[SetSort.set, certificateCodeId],
    certificate_payload_bound
        certificates index (x#certificateCodeId) ∧ₘ
      ((certificates ·ₘ index ≐ₘ
          logical_certificate_code (x#certificateCodeId)) ∧ₘ
        logical_certificate_condition_with_ids
          (sequence ·ₘ index) (x#certificateCodeId)
          logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
          logicalLineIndexId logicalCodeTraceId logicalCodeIndexId)) ∨ₘ
    (theory_certificate_line_condition_with_id
      verifier sequence certificates index certificateCodeId) ∨ₘ
    (modus_ponens_line_condition_with_ids
      sequence certificates index
      implicationIndex premiseIndex)

/-! ## 证书化证明序列条件 -/

/-- 显式 binder 编号下的证书化证明序列合法性。 -/
def sequence_condition_with_ids
    (verifier : ObjectCertificateVerifier)
    (sequence certificates : SetTerm)
    (legalityIndexId certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId) :
    SetFormula :=
  ((((sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
      (certificates ∈ₘ seq₊_spaceₘ(ωₘ))) ∧ₘ
      (domₘ(sequence) ≐ₘ domₘ(certificates))) ∧ₘ
      (numₘ(0) ∈ₘ domₘ(sequence))) ∧ₘ
    (∀ₘ[SetSort.set, legalityIndexId],
      ((x#legalityIndexId ∈ₘ domₘ(sequence)) ⟶ₘ
        (verifier.formula_condition
            (sequence ·ₘ x#legalityIndexId) ∧ₘ
          line_condition_with_ids
            verifier sequence certificates (x#legalityIndexId)
            certificateCodeId
            logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
            logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
            implicationIndex premiseIndex)))

/-! ## 证明码条件 -/

/-!
总证明码由公式序列码与证书序列码配对得到。把两个坐标的有限上界
显式写入 checked payload，后续负向 replay 就能只在 `S(proofCode)`
内消去这两个见证，而无需对象层全局配对唯一性。
-/

/-- 总证明码的一个自然数坐标不超过该证明码。 -/
def proof_code_component_bound
    (proofCode component : SetTerm) : SetFormula :=
  component ∈ₘ Sₘ(proofCode)

/-!
`proof_code_condition_with_ids` 的 binder 分组如下：
* `sequenceId` 与 `certificatesId`：两条有限序列；
* `formulaCodeId` 与 `certificateCodeId`：两条序列的数值编码；
* `legalityIndexId`、`certificatePayloadId`、`implicationIndex`、`premiseIndex`：
  逐行证书；
* `logicalCertificateSequenceId`、`logicalFormulaTraceId`、
  `logicalLastIndexId`、`logicalLineIndexId`、`logicalCodeTraceId`、
  `logicalCodeIndexId`：逻辑公理证书的闭包回放；
* `proofTraceId`、`proofIndexId`、`proofRowCodeId`、`proofRowTraceId`、
  `proofRowIndexId`：公式序列的数值编码轨迹；
* `certificateTraceId`、`certificateIndexId`：证书序列的数值编码轨迹。

前四个编号都是证明码关系的存在见证；其余编号由各自子条件内部闭合。
-/

/-- 显式编号下的完整证书化证明码条件。 -/
def code_condition_with_ids
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (sequenceId certificatesId formulaCodeId certificateCodeId
      legalityIndexId certificatePayloadId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex
      proofTraceId proofIndexId proofRowCodeId proofRowTraceId proofRowIndexId
      certificateTraceId certificateIndexId : FreeVarId) :
    SetFormula :=
  (formula_codeₘ(conclusion) ∧ₘ proofCode ∈ₘ ωₘ) ∧ₘ
    (∃ₘ[SetSort.set, sequenceId],
      (x#sequenceId ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
        (∃ₘ[SetSort.set, certificatesId],
          (x#certificatesId ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
            (∃ₘ[SetSort.set, formulaCodeId],
              proof_code_component_bound
                  proofCode (x#formulaCodeId) ∧ₘ
                (∃ₘ[SetSort.set, certificateCodeId],
                  proof_code_component_bound
                      proofCode (x#certificateCodeId) ∧ₘ
                    (((sequence_condition_with_ids
                        verifier (x#sequenceId) (x#certificatesId)
                        legalityIndexId certificatePayloadId
                        logicalCertificateSequenceId logicalFormulaTraceId
                        logicalLastIndexId logicalLineIndexId
                        logicalCodeTraceId logicalCodeIndexId
                        implicationIndex premiseIndex) ∧ₘ
                      proof_sequence_code_condition_with_ids
                        (x#sequenceId) (x#formulaCodeId)
                        proofTraceId proofIndexId proofRowCodeId
                        proofRowTraceId proofRowIndexId) ∧ₘ
                      nat_sequence_code_condition_with_ids
                        (x#certificatesId) (x#certificateCodeId)
                        certificateTraceId certificateIndexId) ∧ₘ
                    ((proof_code_component_bound
                        proofCode (x#formulaCodeId) ∧ₘ
                      proof_code_component_bound
                        proofCode (x#certificateCodeId)) ∧ₘ
                      ((proofCode ≐ₘ
                          godel_pairₘ(
                            ⟨x#formulaCodeId, x#certificateCodeId⟩ₘ)) ∧ₘ
                        proof_sequence_terminal_condition
                          (x#sequenceId) conclusion))))))

/-! ## admissibility -/

private theorem modus_ponens_line_condition_with_ids_admissible
    (sequence certificates index : SetTerm)
    (implicationIndex premiseIndex : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (modus_ponens_line_condition_with_ids
        sequence certificates index
        implicationIndex premiseIndex) := by
  have hCertificateValue :
      Term.Admissible
        (certificates ·ₘ index) SetSort.set :=
    function_application_term_admissible
      certificates index hCertificates hIndex
  have hImplicationIndex :
      Term.Admissible (x#implicationIndex) SetSort.set :=
    set_variable_admissible implicationIndex
  have hPremiseIndex :
      Term.Admissible (x#premiseIndex) SetSort.set :=
    set_variable_admissible premiseIndex
  have hImplicationEarlier :=
    membership_formula_admissible
      hImplicationIndex hIndex
  have hPremiseEarlier :=
    membership_formula_admissible
      hPremiseIndex hImplicationIndex
  have hIndexPair :
      Term.Admissible
        (⟨x#implicationIndex, x#premiseIndex⟩ₘ)
        SetSort.set :=
    ordered_pair_term_admissible
      (x#implicationIndex) (x#premiseIndex)
      hImplicationIndex hPremiseIndex
  have hIndexPairCode :=
    godel_pairing_term_admissible
      (⟨x#implicationIndex, x#premiseIndex⟩ₘ)
      hIndexPair
  have hCertificateCode :=
    godel_pairing_term_admissible
      (⟨numₘ(2),
        godel_pairₘ(⟨x#implicationIndex, x#premiseIndex⟩ₘ)⟩ₘ)
      (ordered_pair_term_admissible
        (numₘ(2))
        (godel_pairₘ(⟨x#implicationIndex, x#premiseIndex⟩ₘ))
        (finite_numeral_term_admissible 2)
        hIndexPairCode)
  have hCodeEquality :
      Formula.Admissible
        ((certificates ·ₘ index) ≐ₘ
          modus_ponens_certificate_code
            (x#implicationIndex) (x#premiseIndex)) :=
    Formula.Admissible.equal
      hCertificateValue hCertificateCode
  have hRule :=
    modus_ponens_formula_admissible
      (sequence ·ₘ x#premiseIndex)
      (sequence ·ₘ x#implicationIndex)
      (sequence ·ₘ index)
      (function_application_term_admissible
        sequence (x#premiseIndex) hSequence hPremiseIndex)
      (function_application_term_admissible
        sequence (x#implicationIndex) hSequence hImplicationIndex)
      (function_application_term_admissible
        sequence index hSequence hIndex)
  have hPremiseBody :
      Formula.Admissible
        ((x#premiseIndex ∈ₘ x#implicationIndex) ∧ₘ
          (((certificates ·ₘ index) ≐ₘ
              modus_ponens_certificate_code
                (x#implicationIndex) (x#premiseIndex)) ∧ₘ
            modus_ponensₘ(
              sequence ·ₘ x#premiseIndex,
              sequence ·ₘ x#implicationIndex,
              sequence ·ₘ index))) := by
    exact Formula.Admissible.conj
      hPremiseEarlier
      (Formula.Admissible.conj hCodeEquality hRule)
  have hPremiseExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set premiseIndex hPremiseBody
  simpa [modus_ponens_line_condition_with_ids] using
    Formula.Admissible.exists_closeFreeAt
      SetSort.set implicationIndex
      (Formula.Admissible.conj
        hImplicationEarlier hPremiseExists)

private theorem theory_certificate_line_condition_with_id_admissible
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (certificateCodeId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (theory_certificate_line_condition_with_id
        verifier sequence certificates index certificateCodeId) := by
  have hCertificateValue :
      Term.Admissible
        (certificates ·ₘ index) SetSort.set :=
    function_application_term_admissible
      certificates index hCertificates hIndex
  have hPayload :
      Term.Admissible (x#certificateCodeId) SetSort.set :=
    set_variable_admissible certificateCodeId
  have hTag :
      Term.Admissible
        (theory_certificate_code (x#certificateCodeId))
        SetSort.set := by
    exact godel_pairing_term_admissible
      (⟨numₘ(1), x#certificateCodeId⟩ₘ)
      (ordered_pair_term_admissible
        (numₘ(1)) (x#certificateCodeId)
        (finite_numeral_term_admissible 1) hPayload)
  have hCondition :=
    verifier.condition_admissible
      (sequence ·ₘ index) (x#certificateCodeId)
      (function_application_term_admissible
        sequence index hSequence hIndex)
      hPayload
  have hEquality :=
    Formula.Admissible.equal hCertificateValue hTag
  have hBound :
      Formula.Admissible
        (certificate_payload_bound
          certificates index (x#certificateCodeId)) := by
    exact membership_formula_admissible hPayload
      (successor_term_admissible
        (certificates ·ₘ index) hCertificateValue)
  simpa [theory_certificate_line_condition_with_id] using
    Formula.Admissible.exists_closeFreeAt
      SetSort.set certificateCodeId
      (Formula.Admissible.conj
        hBound
        (Formula.Admissible.conj hEquality hCondition))

theorem line_condition_with_ids_admissible
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (line_condition_with_ids
        verifier sequence certificates index
        certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
        logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex) := by
  have hCertificateValue :
      Term.Admissible
        (certificates ·ₘ index) SetSort.set :=
    function_application_term_admissible
      certificates index hCertificates hIndex
  have hLogicalPayload :
      Term.Admissible (x#certificateCodeId) SetSort.set :=
    set_variable_admissible certificateCodeId
  have hLogicalTag :
      Term.Admissible
        (logical_certificate_code (x#certificateCodeId))
        SetSort.set := by
    exact godel_pairing_term_admissible
      (⟨numₘ(0), x#certificateCodeId⟩ₘ)
      (ordered_pair_term_admissible
        (numₘ(0)) (x#certificateCodeId)
        (finite_numeral_term_admissible 0)
        hLogicalPayload)
  have hLogical :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set certificateCodeId
      (Formula.Admissible.conj
        (membership_formula_admissible hLogicalPayload
          (successor_term_admissible
            (certificates ·ₘ index) hCertificateValue))
        (Formula.Admissible.conj
          (Formula.Admissible.equal hCertificateValue hLogicalTag)
          (logical_certificate_condition_with_ids_admissible
            (sequence ·ₘ index)
            (x#certificateCodeId)
            logicalCertificateSequenceId logicalFormulaTraceId
            logicalLastIndexId logicalLineIndexId
            logicalCodeTraceId logicalCodeIndexId
            (function_application_term_admissible
              sequence index hSequence hIndex)
            hLogicalPayload)))
  have hTheory :=
    theory_certificate_line_condition_with_id_admissible
      verifier sequence certificates index certificateCodeId
      hSequence hCertificates hIndex
  have hModus :=
    modus_ponens_line_condition_with_ids_admissible
      sequence certificates index
      implicationIndex premiseIndex
      hSequence hCertificates hIndex
  exact Formula.Admissible.disj hLogical
    (Formula.Admissible.disj hTheory hModus)

theorem sequence_condition_with_ids_admissible
    (verifier : ObjectCertificateVerifier)
    (sequence certificates : SetTerm)
    (legalityIndexId certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set) :
    Formula.Admissible
      (sequence_condition_with_ids
        verifier sequence certificates
        legalityIndexId certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
        logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex) := by
  have hSequenceSpace :=
    nonempty_finite_sequence_space_term_admissible
      FormulaCodeₘ formula_code_set_term_admissible
  have hCertificateSpace :=
    nonempty_finite_sequence_space_term_admissible
      ωₘ omega_term_admissible
  have hDomainSequence :=
    domain_term_admissible sequence hSequence
  have hDomainCertificates :=
    domain_term_admissible certificates hCertificates
  have hZero :=
    membership_formula_admissible
      (finite_numeral_term_admissible 0)
      hDomainSequence
  have hDomainEquality :=
    Formula.Admissible.equal
      hDomainSequence hDomainCertificates
  have hIndex :
      Term.Admissible (x#legalityIndexId) SetSort.set :=
    set_variable_admissible legalityIndexId
  have hIndexDomain :=
    membership_formula_admissible hIndex hDomainSequence
  have hFormulaCondition :=
    verifier.formula_condition_admissible
      (sequence ·ₘ x#legalityIndexId)
      (function_application_term_admissible
        sequence (x#legalityIndexId)
        hSequence hIndex)
  have hLine :=
    line_condition_with_ids_admissible
      verifier sequence certificates
      (x#legalityIndexId)
      certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex
      hSequence hCertificates hIndex
  have hAllLines :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set legalityIndexId
      (Formula.Admissible.imp hIndexDomain
        (Formula.Admissible.conj
          hFormulaCondition hLine))
  have hSpaces :
      Formula.Admissible
        ((sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
          (certificates ∈ₘ seq₊_spaceₘ(ωₘ))) :=
    Formula.Admissible.conj
      (membership_formula_admissible hSequence hSequenceSpace)
      (membership_formula_admissible hCertificates hCertificateSpace)
  have hSpacesDomain :=
    Formula.Admissible.conj hSpaces hDomainEquality
  have hSpacesDomainZero :=
    Formula.Admissible.conj hSpacesDomain hZero
  exact Formula.Admissible.conj hSpacesDomainZero hAllLines

theorem code_condition_with_ids_admissible
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (sequenceId certificatesId formulaCodeId certificateCodeId
      legalityIndexId certificatePayloadId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex
      proofTraceId proofIndexId proofRowCodeId proofRowTraceId proofRowIndexId
      certificateTraceId certificateIndexId : FreeVarId)
    (hProofCode : Term.Admissible proofCode SetSort.set)
    (hConclusion : Term.Admissible conclusion SetSort.set) :
    Formula.Admissible
      (code_condition_with_ids
        verifier proofCode conclusion
        sequenceId certificatesId formulaCodeId certificateCodeId
        legalityIndexId certificatePayloadId
        logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
        logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex
        proofTraceId proofIndexId proofRowCodeId
        proofRowTraceId proofRowIndexId
        certificateTraceId certificateIndexId) := by
  have hConclusionCode :=
    is_formula_code_formula_admissible hConclusion
  have hProofCodeNatural :=
    membership_formula_admissible hProofCode omega_term_admissible
  have hSequence :
      Term.Admissible (x#sequenceId) SetSort.set :=
    set_variable_admissible sequenceId
  have hCertificates :
      Term.Admissible (x#certificatesId) SetSort.set :=
    set_variable_admissible certificatesId
  have hFormulaCode :
      Term.Admissible (x#formulaCodeId) SetSort.set :=
    set_variable_admissible formulaCodeId
  have hCertificateCode :
      Term.Admissible (x#certificateCodeId) SetSort.set :=
    set_variable_admissible certificateCodeId
  have hProofCodeSuccessor :
      Term.Admissible (Sₘ(proofCode)) SetSort.set :=
    successor_term_admissible proofCode hProofCode
  have hFormulaCodeBound :
      Formula.Admissible
        (proof_code_component_bound
          proofCode (x#formulaCodeId)) := by
    simpa [proof_code_component_bound] using
      membership_formula_admissible
        hFormulaCode hProofCodeSuccessor
  have hCertificateCodeBound :
      Formula.Admissible
        (proof_code_component_bound
          proofCode (x#certificateCodeId)) := by
    simpa [proof_code_component_bound] using
      membership_formula_admissible
        hCertificateCode hProofCodeSuccessor
  have hPair :
      Term.Admissible
        (godel_pairₘ(⟨x#formulaCodeId, x#certificateCodeId⟩ₘ))
        SetSort.set :=
    godel_pairing_term_admissible
      (⟨x#formulaCodeId, x#certificateCodeId⟩ₘ)
      (ordered_pair_term_admissible
        (x#formulaCodeId) (x#certificateCodeId)
        hFormulaCode hCertificateCode)
  have hCodeEquality :=
    Formula.Admissible.equal hProofCode hPair
  have hTerminal :=
    proof_sequence_terminal_condition_admissible
      (x#sequenceId) conclusion hSequence hConclusion
  have hSequenceCondition :=
    sequence_condition_with_ids_admissible
      verifier (x#sequenceId) (x#certificatesId)
      legalityIndexId certificatePayloadId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex
      hSequence hCertificates
  have hProofCodeCondition :=
    proof_sequence_code_condition_with_ids_admissible
      (x#sequenceId) (x#formulaCodeId)
      proofTraceId proofIndexId proofRowCodeId
      proofRowTraceId proofRowIndexId
      hSequence hFormulaCode
  have hCertificateCodeCondition :=
    nat_sequence_code_condition_with_ids_admissible
      (x#certificatesId) (x#certificateCodeId)
      certificateTraceId certificateIndexId
      hCertificates hCertificateCode
  have hSequenceSpace :
      Formula.Admissible
        (x#sequenceId ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) :=
    membership_formula_admissible hSequence
      (nonempty_finite_sequence_space_term_admissible
        FormulaCodeₘ formula_code_set_term_admissible)
  have hCertificateSpace :
      Formula.Admissible
        (x#certificatesId ∈ₘ seq₊_spaceₘ(ωₘ)) :=
    membership_formula_admissible hCertificates
      (nonempty_finite_sequence_space_term_admissible
        ωₘ omega_term_admissible)
  have hBody :=
    Formula.Admissible.conj
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          hSequenceCondition hProofCodeCondition)
        hCertificateCodeCondition)
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          hFormulaCodeBound hCertificateCodeBound)
        (Formula.Admissible.conj hCodeEquality hTerminal))
  have hCertificateCodeExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set certificateCodeId
      (Formula.Admissible.conj
        hCertificateCodeBound hBody)
  have hFormulaCodeExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set formulaCodeId
      (Formula.Admissible.conj
        hFormulaCodeBound hCertificateCodeExists)
  have hCertificateExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set certificatesId
      (Formula.Admissible.conj
        hCertificateSpace hFormulaCodeExists)
  have hSequenceExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set sequenceId
      (Formula.Admissible.conj
        hSequenceSpace hCertificateExists)
  simpa [code_condition_with_ids] using
    Formula.Admissible.conj
      (Formula.Admissible.conj hConclusionCode hProofCodeNatural)
      hSequenceExists

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
