import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CertifiedProofRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SequenceInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedModusPonensRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementObjectCertificateRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedVerifierRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementVerifierSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaDecodeFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateLineRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateLineRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalTailFailureAssembly
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCFormulaBinderRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCFormulaSignatureRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.RawAlignment
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeDecodeRejection

/-!
# ZFC 证书化证明码的对象层拒绝

本模块把规范 terminal 的否定提升为完整
`proof_condition` 的否定。第一批公开实例覆盖空证明序列与
末行 quotation 不匹配；行级 checker 失败将在同一提升接口上继续接入。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation
open Rosser

set_option autoImplicit false

def ProofT.ZFCRep.proof_sequence
    (number : Nat) : SetTerm :=
  standard_sequence
    ((proof_sequence_decode
        (godel_unpair_value number).1).map
      standard_token_sequence)

def ProofT.ZFCRep.certificate_sequence
    (number : Nat) : SetTerm :=
  standard_token_sequence
    (nat_sequence_decode
      (godel_unpair_value number).2)

def ProofT.ZFCRep.witness
    (number : Nat)
    (conclusion : SetTerm) : SetFormula :=
  proof_witness
    fs_zfc_replacement_object_certificate_verifier
    (numₘ(number)) conclusion
    (x#ProofT.condition_base)
    (x#(ProofT.condition_base + 1))
    (x#(ProofT.condition_base + 2))
    (x#(ProofT.condition_base + 3))
    ProofT.condition_base

theorem ProofT.ZFCRep.proof_sequence_boundary
    (number : Nat) :
    GodelQuotation.Numbered.CodeBoundary
      (ProofT.ZFCRep.proof_sequence number) := by
  let rows : List (List Nat) :=
    proof_sequence_decode
      (godel_unpair_value number).1
  have hElements :
      ∀ element,
        element ∈ rows.map standard_token_sequence →
          Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_admissible tokens
  have hElementsClosed :
      ∀ element,
        element ∈ rows.map standard_token_sequence →
          Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_freeSupport_nil tokens
  constructor
  · simpa [ProofT.ZFCRep.proof_sequence, rows] using
      seq_admissible_m 0 hElements
  · simpa [ProofT.ZFCRep.proof_sequence, rows] using
      seq_support_nil_m 0 hElementsClosed

theorem ProofT.ZFCRep.certificate_sequence_boundary
    (number : Nat) :
    GodelQuotation.Numbered.CodeBoundary
      (ProofT.ZFCRep.certificate_sequence number) :=
  ⟨standard_token_sequence_admissible
      (nat_sequence_decode
        (godel_unpair_value number).2),
    standard_token_sequence_freeSupport_nil
      (nat_sequence_decode
        (godel_unpair_value number).2)⟩

theorem ProofT.ZFCRep.witness_admissible
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      Term.Admissible conclusion SetSort.set) :
    Formula.Admissible
      (ProofT.ZFCRep.witness
        number conclusion) := by
  simpa [ProofT.ZFCRep.witness] using
    proof_witness_admissible
      fs_zfc_replacement_object_certificate_verifier
      (numₘ(number)) conclusion
      (x#ProofT.condition_base)
      (x#(ProofT.condition_base + 1))
      (x#(ProofT.condition_base + 2))
      (x#(ProofT.condition_base + 3))
      ProofT.condition_base
      (finite_numeral_term_admissible number)
      hConclusion
      (set_variable_admissible ProofT.condition_base)
      (set_variable_admissible
        (ProofT.condition_base + 1))
      (set_variable_admissible
        (ProofT.condition_base + 2))
      (set_variable_admissible
        (ProofT.condition_base + 3))

theorem ProofT.ZFCRep.content_of_witness
    {Γ : Context signature}
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hWitness :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ProofT.ZFCRep.witness
          number conclusion) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (ProofT.sequence_condition fs_zfc_replacement_object_certificate_verifier
          (ProofT.ZFCRep.proof_sequence number)
          (ProofT.ZFCRep.certificate_sequence number)) ∧ₘ
        proof_sequence_terminal_condition
          (ProofT.ZFCRep.proof_sequence number)
          conclusion := by
  simpa [ProofT.ZFCRep.witness,
    ProofT.ZFCRep.proof_sequence,
    ProofT.ZFCRep.certificate_sequence] using
    ProofT.witness_content
      ProofT.ZFC.certificate_core
      ProofT.ZFC.sequence_inversion
      fs_zfc_replacement_object_certificate_verifier
      ProofT.ZFCRep.verifier_transport
      ProofT.ZFCRep.verifier_support
      number conclusion hConclusion hWitness

/--
公式行序列与证书序列的规范长度不同时，完整证明码条件被对象层拒绝。
-/
theorem ProofT.ZFCRep.code_neg_of_length
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hLength :
      (proof_sequence_decode
          (godel_unpair_value number).1).length ≠
        (nat_sequence_decode
          (godel_unpair_value number).2).length) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ proof_condition
        fs_zfc_replacement_object_certificate_verifier
        (numₘ(number)) conclusion
        ProofT.condition_base) := by
  exact
    ProofT.code_neg_of_decoded_length
      ProofT.ZFC.certificate_core
      ProofT.ZFC.sequence_inversion
      ProofT.ZFC.object_replay
      fs_zfc_replacement_object_certificate_verifier
      ProofT.ZFCRep.verifier_transport
      ProofT.ZFCRep.verifier_support
      number conclusion hConclusion hLength

/--
某个规范 proof row 已有闭的有限签名公式条件否定时，完整 numeral 证明码条件
被对象层拒绝。该条件同时覆盖公式语法损坏与当前 FormalSystem 签名越界。
-/
theorem ProofT.ZFCRep.code_neg_of_formula_condition
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (index : Nat)
    (hIndex :
      index <
        (proof_sequence_decode
          (godel_unpair_value number).1).length)
    (hRowNeg :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ fs_formula_code_condition
          (standard_token_sequence
            (proof_sequence_decode
              (godel_unpair_value number).1)[index]))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ proof_condition
        fs_zfc_replacement_object_certificate_verifier
        (numₘ(number)) conclusion
        ProofT.condition_base) := by
  apply
    ProofT.code_neg_of_witness
      ProofT.ZFC.certificate_core.toFiniteCore
      fs_zfc_replacement_object_certificate_verifier
      number conclusion ProofT.condition_base hConclusion
  have hWitnessBodyAdmissible :
      Formula.Admissible
        (ProofT.ZFCRep.witness
          number conclusion) :=
    ProofT.ZFCRep.witness_admissible
      number conclusion hConclusion.1
  nd_apply FirstOrder.Derives.impIntro
  let witnessBody : SetFormula :=
    ProofT.ZFCRep.witness number conclusion
  let Δ : Context signature := [witnessBody]
  let rows : List (List Nat) :=
    proof_sequence_decode
      (godel_unpair_value number).1
  have hWitness :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        witnessBody :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hCanonical :=
    ProofT.ZFCRep.content_of_witness
      number conclusion hConclusion
      (by simpa [witnessBody] using hWitness)
  have hSequenceCondition :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        ProofT.sequence_condition fs_zfc_replacement_object_certificate_verifier
          (ProofT.ZFCRep.proof_sequence number)
          (ProofT.ZFCRep.certificate_sequence number) :=
    FirstOrder.Derives.conjElimLeft hCanonical
  have hBeforeForall :=
    FirstOrder.Derives.conjElimLeft hSequenceCondition
  have hBeforeZero :=
    FirstOrder.Derives.conjElimLeft hBeforeForall
  have hBeforeDomain :=
    FirstOrder.Derives.conjElimLeft hBeforeZero
  have hSpaces :=
    FirstOrder.Derives.conjElimLeft hBeforeDomain
  have hFormulaSpace :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_sequence
            (rows.map standard_token_sequence) ∈ₘ
          seq₊_spaceₘ(FormulaCodeₘ) := by
    simpa [ProofT.sequence_condition,
      CertifiedProof.sequence_condition_with_ids,
      ProofT.ZFCRep.proof_sequence, rows] using
      hSpaces
  have hRowIndex :
      index < rows.length := by
    simpa [rows] using hIndex
  have hFormulaMember :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence rows[index] ∈ₘ
          FormulaCodeₘ :=
    ProofT.row_formula_mem
      ProofT.ZFC.object_replay
      rows index hRowIndex hFormulaSpace
  have hRowReplay :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_formula_replay_condition
          (standard_token_sequence rows[index]) :=
    ProofT.row_replay
      ProofT.ZFC.object_replay
      fs_zfc_replacement_object_certificate_verifier
      ProofT.ZFCRep.verifier_transport
      rows
      (ProofT.ZFCRep.certificate_sequence number)
      index hRowIndex
      (by
        simpa [ProofT.ZFCRep.proof_sequence,
          rows] using hSequenceCondition)
  have hRowAdmissible :
      Term.Admissible
        (standard_token_sequence rows[index])
        SetSort.set :=
    standard_token_sequence_admissible rows[index]
  have hRowSignature :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_formula_signature_condition
          (standard_token_sequence rows[index]) := by
    simpa [fs_formula_replay_condition] using
      FirstOrder.Derives.conjElimLeft hRowReplay
  have hFormulaPredicate :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        formula_codeₘ(
          standard_token_sequence rows[index]) := by
    have hDefinition :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          is_formula_code_definition_instance
            (standard_token_sequence rows[index]) := by
      apply FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp)
      exact fs_zfc_support_raw_derives_of_godel_quotation
        (gq_formula_code_definition_instance
          (standard_token_sequence rows[index])
          hRowAdmissible)
    exact FirstOrder.Derives.iffElimLeft
      hDefinition hFormulaMember
  have hRowCondition :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_formula_code_condition
          (standard_token_sequence rows[index]) := by
    simpa [fs_formula_code_condition] using
      FirstOrder.Derives.conjIntro
        hFormulaPredicate hRowSignature
  exact FirstOrder.Derives.negElim
    hRowCondition
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp)
      (by simpa [rows] using hRowNeg))

/--
某个规范 proof row 的完整 verifier replay 条件已有闭否定时，完整 numeral
证明码条件被对象层拒绝。
-/
theorem
    ProofT.ZFCRep.code_neg_of_formula_replay
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (index : Nat)
    (hIndex :
      index <
        (proof_sequence_decode
          (godel_unpair_value number).1).length)
    (hRowNeg :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ fs_formula_replay_condition
          (standard_token_sequence
            (proof_sequence_decode
              (godel_unpair_value number).1)[index]))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ proof_condition
        fs_zfc_replacement_object_certificate_verifier
        (numₘ(number)) conclusion
        ProofT.condition_base) := by
  apply
    ProofT.code_neg_of_witness
      ProofT.ZFC.certificate_core.toFiniteCore
      fs_zfc_replacement_object_certificate_verifier
      number conclusion ProofT.condition_base hConclusion
  have hWitnessBodyAdmissible :
      Formula.Admissible
        (ProofT.ZFCRep.witness
          number conclusion) :=
    ProofT.ZFCRep.witness_admissible
      number conclusion hConclusion.1
  nd_apply FirstOrder.Derives.impIntro
  let witnessBody : SetFormula :=
    ProofT.ZFCRep.witness number conclusion
  let Δ : Context signature := [witnessBody]
  have hWitness :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        witnessBody :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hCanonical :=
    ProofT.ZFCRep.content_of_witness
      number conclusion hConclusion
      (by simpa [witnessBody] using hWitness)
  have hSequenceCondition :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        ProofT.sequence_condition fs_zfc_replacement_object_certificate_verifier
          (ProofT.ZFCRep.proof_sequence number)
          (ProofT.ZFCRep.certificate_sequence number) :=
    FirstOrder.Derives.conjElimLeft hCanonical
  have hRowReplay :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_formula_replay_condition
          (standard_token_sequence
            (proof_sequence_decode
              (godel_unpair_value number).1)[index]) :=
    ProofT.row_replay
      ProofT.ZFC.object_replay
      fs_zfc_replacement_object_certificate_verifier
      ProofT.ZFCRep.verifier_transport
      (proof_sequence_decode
        (godel_unpair_value number).1)
      (ProofT.ZFCRep.certificate_sequence number)
      index hIndex
      (by
        simpa [ProofT.ZFCRep.proof_sequence] using
          hSequenceCondition)
  exact FirstOrder.Derives.negElim
    hRowReplay
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp) hRowNeg)

/--
某个规范公式行含有当前 `FormalSystem` 签名之外的具体 token 时，完整 numeral
证明码条件被对象层拒绝。
-/
theorem ProofT.ZFCRep.code_neg_of_bad_token
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (rowIndex tokenIndex : Nat)
    (hRowIndex :
      rowIndex <
        (proof_sequence_decode
          (godel_unpair_value number).1).length)
    (hTokenIndex :
      tokenIndex <
        (proof_sequence_decode
          (godel_unpair_value number).1)[rowIndex].length)
    (hToken :
      ¬ FSFormulaToken
        (proof_sequence_decode
          (godel_unpair_value number).1)[rowIndex][tokenIndex]) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ proof_condition
        fs_zfc_replacement_object_certificate_verifier
        (numₘ(number)) conclusion
        ProofT.condition_base) := by
  apply
    ProofT.ZFCRep.code_neg_of_formula_condition
      number conclusion hConclusion rowIndex hRowIndex
  exact
    fs_zfc_support_raw_standard_token_sequence_formula_condition_neg_of_token
      (proof_sequence_decode
        (godel_unpair_value number).1)[rowIndex]
      tokenIndex hTokenIndex hToken

/--
某个规范公式行的第零、第一位均不以左括号开头时，完整 numeral 证明码条件
被对象层拒绝。
-/
theorem
    ProofT.ZFCRep.code_neg_of_no_left_opening
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (rowIndex : Nat)
    (hRowIndex :
      rowIndex <
        (proof_sequence_decode
          (godel_unpair_value number).1).length)
    (hZero :
      (proof_sequence_decode
        (godel_unpair_value number).1)[rowIndex][0]? ≠
          some (GodelQuotation.Numbered.logical_token
            .leftParenthesis))
    (hOne :
      (proof_sequence_decode
        (godel_unpair_value number).1)[rowIndex][1]? ≠
          some (GodelQuotation.Numbered.logical_token
            .leftParenthesis)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ proof_condition
        fs_zfc_replacement_object_certificate_verifier
        (numₘ(number)) conclusion
        ProofT.condition_base) := by
  apply
    ProofT.ZFCRep.code_neg_of_formula_condition
      number conclusion hConclusion rowIndex hRowIndex
  exact
    fs_zfc_support_raw_standard_token_sequence_formula_condition_neg_of_no_left_opening
      (proof_sequence_decode
        (godel_unpair_value number).1)[rowIndex]
      hZero hOne

/--
某个规范公式行缺少第一号位置时，完整 numeral 证明码条件被对象层拒绝。
-/
theorem
    ProofT.ZFCRep.code_neg_of_one_absent
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (rowIndex : Nat)
    (hRowIndex :
      rowIndex <
        (proof_sequence_decode
          (godel_unpair_value number).1).length)
    (hOne :
      (proof_sequence_decode
        (godel_unpair_value number).1)[rowIndex][1]? =
          none) :
    ⊢ₘ[fs_zfc_support_raw_theory]
      ¬ₘ proof_condition
        fs_zfc_replacement_object_certificate_verifier
        (numₘ(number)) conclusion
        ProofT.condition_base := by
  apply
    ProofT.ZFCRep.code_neg_of_formula_condition
      number conclusion hConclusion rowIndex hRowIndex
  exact
    fs_zfc_support_raw_standard_token_sequence_formula_condition_neg_of_one_absent
      (proof_sequence_decode
        (godel_unpair_value number).1)[rowIndex]
      hOne

/--
公式 payload 解码失败时，最小长度与开头反演自动关闭两类结构失败：

* 失败行缺少第一号位置；
* 失败行的第零、第一位均不是左括号。

剩余分支精确记录为 `FSFormulaRowsDecodeStructuralResidual`，后续只需反演整行
签名与 binder 后继均合法且已经具有左括号开头的 parser 失败。
-/
theorem
    ProofT.ZFCRep.code_neg_or_decode_residual
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hDecode :
      fs_formula_rows_decode_payload number
          (fs_certified_proof_code_decode number).1 =
        none) :
    Derives fs_zfc_support_raw_theory [] (
        ¬ₘ proof_condition
          fs_zfc_replacement_object_certificate_verifier
          (numₘ(number)) conclusion
          ProofT.condition_base) ∨
      FSFormulaRowsDecodeStructuralResidual number
        (fs_certified_proof_code_decode number).1 := by
  rcases
      fs_formula_rows_decode_payload_failure_view_of_none
        number hDecode with
    ⟨rowIndex, hRowIndex, hFailure⟩
  cases hFailure with
  | one_absent hRowDecode hOne =>
      left
      exact
        ProofT.ZFCRep.code_neg_of_one_absent
          number conclusion hConclusion rowIndex
          (by
            simpa [fs_certified_proof_code_decode] using
              hRowIndex)
          (by
            simpa [fs_certified_proof_code_decode] using
              hOne)
  | no_left_opening hRowDecode hOnePresent hZero hOne =>
      left
      exact
        ProofT.ZFCRep.code_neg_of_no_left_opening
          number conclusion hConclusion rowIndex
          (by
            simpa [fs_certified_proof_code_decode] using
              hRowIndex)
          (by
            simpa [fs_certified_proof_code_decode] using
              hZero)
          (by
            simpa [fs_certified_proof_code_decode] using
              hOne)
  | opening_present hRowDecode hOnePresent hOpening =>
      rcases
          fs_formula_tokens_or_bad_index
            (fs_certified_proof_code_decode number).1[rowIndex] with
        hTokens | hBad
      · cases hBinderCheck :
            fs_formula_binder_tokens_check
              (fs_certified_proof_code_decode number).1[rowIndex] with
        | false =>
            left
            apply
              ProofT.ZFCRep.code_neg_of_formula_replay
                number conclusion hConclusion rowIndex
                (by
                  simpa [fs_certified_proof_code_decode] using
                    hRowIndex)
            simpa [fs_certified_proof_code_decode] using
              fs_zfc_support_raw_standard_token_sequence_replay_neg_of_binder_check
                (fs_certified_proof_code_decode number).1[rowIndex]
                hBinderCheck
        | true =>
            right
            exact
              ⟨rowIndex, hRowIndex, hRowDecode,
                hTokens,
                (by
                  simpa [FSFormulaBinderTokens] using
                    hBinderCheck),
                hOnePresent, hOpening⟩
      · rcases hBad with
          ⟨tokenIndex, hTokenIndex, hToken⟩
        left
        exact
          ProofT.ZFCRep.code_neg_of_bad_token
            number conclusion hConclusion rowIndex tokenIndex
            (by
              simpa [fs_certified_proof_code_decode] using
                hRowIndex)
            (by
              simpa [fs_certified_proof_code_decode] using
                hTokenIndex)
            (by
              simpa [fs_certified_proof_code_decode] using
                hToken)

/--
公式 payload 解码的最终结构残余由通用公式码强归纳直接关闭。

此处只负责把失败行的 `FormulaCodeₘ` 否定提升到整条证书化证明码；具体公式
构造反演全部留在公共 quotation 层。
-/
theorem
    ProofT.ZFCRep.code_neg_of_decode_residual
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hResidual :
      FSFormulaRowsDecodeStructuralResidual number
        (fs_certified_proof_code_decode number).1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ proof_condition
        fs_zfc_replacement_object_certificate_verifier
        (numₘ(number)) conclusion
        ProofT.condition_base) := by
  rcases hResidual with
    ⟨rowIndex, hRowIndex, hDecode,
      hTokens, hBinders, _hOne, _hOpening⟩
  have hNamedDecode :
      fs_named_hilbert_tokens_decode_with_env
          number []
          (fs_certified_proof_code_decode number).1[rowIndex] =
        none := by
    unfold fs_formula_row_decode at hDecode
    split at hDecode
    · assumption
    · simp at hDecode
  have hFormulaCodeNot :
      ⊢ₘ[godel_quotation_theory]
        ¬ₘ (standard_token_sequence
            (fs_certified_proof_code_decode number).1[rowIndex] ∈ₘ
          FormulaCodeₘ) :=
    gq_standard_formula_code_not_of_decode_none
      number []
      (fs_certified_proof_code_decode number).1[rowIndex]
      hTokens hBinders hNamedDecode
  have hConditionNot :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ fs_formula_code_condition
          (standard_token_sequence
            (fs_certified_proof_code_decode number).1[rowIndex])) :=
    fs_zfc_support_raw_derives_of_godel_quotation <|
      gq_fs_formula_code_condition_not_of_formula_code_not
        (fs_certified_proof_code_decode number).1[rowIndex]
        hFormulaCodeNot
  exact
    ProofT.ZFCRep.code_neg_of_formula_condition
      number conclusion hConclusion rowIndex
      (by
        simpa [fs_certified_proof_code_decode] using
          hRowIndex)
      (by
        simpa [fs_certified_proof_code_decode] using
          hConditionNot)

/--
某个规范位置的 checked 行实例已有对象层否定时，完整 numeral 证明码条件
被对象层拒绝。
-/
theorem ProofT.ZFCRep.code_neg_of_line
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (index : Nat)
    (hIndex :
      index <
        (proof_sequence_decode
          (godel_unpair_value number).1).length)
    (hLineNeg :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ ProofT.line_instance fs_zfc_replacement_object_certificate_verifier
          (ProofT.ZFCRep.proof_sequence number)
          (ProofT.ZFCRep.certificate_sequence number)
          index)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ proof_condition
        fs_zfc_replacement_object_certificate_verifier
        (numₘ(number)) conclusion
        ProofT.condition_base) := by
  let rows : List (List Nat) :=
    proof_sequence_decode
      (godel_unpair_value number).1
  apply
    ProofT.code_neg_of_line
      ProofT.ZFC.certificate_core.toFiniteCore
      fs_zfc_replacement_object_certificate_verifier
      ProofT.ZFCRep.verifier_transport
      number conclusion ProofT.condition_base
      (ProofT.ZFCRep.proof_sequence number)
      (ProofT.ZFCRep.certificate_sequence number)
      index hConclusion
      (ProofT.ZFCRep.proof_sequence_boundary number).2
  · intro Γ hWitness
    have hCanonical :=
      ProofT.ZFCRep.content_of_witness
        number conclusion hConclusion
        (by
          simpa [ProofT.ZFCRep.witness] using
            hWitness)
    exact FirstOrder.Derives.conjElimLeft hCanonical
  · simpa [ProofT.ZFCRep.proof_sequence, rows] using
      ProofT.row_index_mem
        ProofT.ZFC.object_replay
        (Γ := ([] : Context signature)) rows index
        (by simpa [rows] using hIndex)
  · exact hLineNeg

/--
规范证书自然数序列无法逐项解码时，完整 numeral 证明码条件被对象层拒绝。

若两侧外部长度不同则使用定义域矛盾；长度相同时，失败位置自动落入证明行
定义域，并由标准 token 序列逐点语义生成该位置的坏证书等式。
-/
theorem ProofT.ZFCRep.code_neg_of_bad_certificate
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hDecode :
      fs_certificate_sequence_decode
          (godel_unpair_value number).2 =
        none) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ proof_condition
        fs_zfc_replacement_object_certificate_verifier
        (numₘ(number)) conclusion
        ProofT.condition_base) := by
  let rows : List (List Nat) :=
    proof_sequence_decode
      (godel_unpair_value number).1
  let rawCertificates : List Nat :=
    nat_sequence_decode
      (godel_unpair_value number).2
  by_cases hLength :
      rows.length = rawCertificates.length
  · rcases
        fs_certificate_sequence_decode_failure_of_none hDecode with
      ⟨index, hCertificateIndex, hBadDecode⟩
    have hRowIndex : index < rows.length := by
      rw [hLength]
      simpa [rawCertificates] using hCertificateIndex
    have hCertificateGet :
        rawCertificates[index]? =
          some rawCertificates[index] :=
      List.getElem?_eq_getElem <| by
        simpa [rawCertificates] using hCertificateIndex
    have hCertificateAt :
        Derives fs_zfc_support_raw_theory [] (
          ProofT.ZFCRep.certificate_sequence number ·ₘ
              numₘ(index) ≐ₘ
            numₘ(rawCertificates[index])) := by
      simpa [ProofT.ZFCRep.certificate_sequence,
        rawCertificates] using
        fs_zfc_support_raw_derives_of_standard_sequence
          (standard_token_sequence_apply_getElem?
            rawCertificates hCertificateGet)
    have hLineNeg :
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ ProofT.line_instance fs_zfc_replacement_object_certificate_verifier
            (ProofT.ZFCRep.proof_sequence number)
            (ProofT.ZFCRep.certificate_sequence number)
            index) :=
      ProofT.line_instance_neg_of_certificate_decode_none
        ProofT.ZFC.certificate_core
        fs_zfc_replacement_object_certificate_verifier
        ProofT.ZFCRep.verifier_transport
        (ProofT.ZFCRep.proof_sequence number)
        (ProofT.ZFCRep.certificate_sequence number)
        index rawCertificates[index]
        (ProofT.ZFCRep.proof_sequence_boundary number).1
        (ProofT.ZFCRep.certificate_sequence_boundary number).1
        (ProofT.ZFCRep.proof_sequence_boundary number).2
        (ProofT.ZFCRep.certificate_sequence_boundary number).2
        hCertificateAt
        (by simpa [rawCertificates] using hBadDecode)
    exact
      ProofT.ZFCRep.code_neg_of_line
        number conclusion hConclusion index
        (by simpa [rows] using hRowIndex)
        hLineNeg
  · exact
      ProofT.ZFCRep.code_neg_of_length
        number conclusion hConclusion
        (by simpa [rows, rawCertificates] using hLength)

/--
完整 replay 失败到对象层证明码条件否定的直接适配器。

该接口直接消费宿主递归失败树；成功反演、行内容与证书字段均由既有层提供。
-/
theorem
    ProofT.ZFCRep.code_neg_of_replay_failure
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hFailure :
      FSReplayCodeFailure
        ProofCode.fs_zfc_replacement_support_enumeration number) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ proof_condition
        fs_zfc_replacement_object_certificate_verifier
        (numₘ(number)) conclusion
        ProofT.condition_base) := by
  cases hFailure with
  | certificate_decode hDecode =>
      exact
        ProofT.ZFCRep.code_neg_of_bad_certificate
          number conclusion hConclusion <| by
          simpa [fs_certified_proof_code_decode] using hDecode
  | @rows certificates hCertificates hRowsFailure =>
      have consume :
          ∀ (P : Prop) {state rows certificates},
            FSReplayRawRowsFailure
                ProofCode.fs_zfc_replacement_support_enumeration number
                state rows certificates →
            (rows.length ≠ certificates.length → P) →
            (∀ index row certificate prefixState,
              rows[index]? = some row →
              certificates[index]? = some certificate →
              fs_replay_raw_rows
                  ProofCode.fs_zfc_replacement_support_enumeration number state
                  (rows.take index) (certificates.take index) =
                some prefixState →
              fs_formula_row_decode number row = none → P) →
            (∀ index row decoded certificate prefixState,
              rows[index]? = some row →
              certificates[index]? = some certificate →
              fs_replay_raw_rows
                  ProofCode.fs_zfc_replacement_support_enumeration number state
                  (rows.take index) (certificates.take index) =
                some prefixState →
              fs_formula_row_decode number row = some decoded →
              FSReplayRowFailure
                ProofCode.fs_zfc_replacement_support_enumeration number prefixState
                decoded.formula certificate →
              P) →
            P := by
        intro P state rows certificates hFailure
        induction hFailure with
        | extra_certificates =>
            intro hLength _ _
            exact hLength (by simp)
        | missing_certificate =>
            intro hLength _ _
            exact hLength (by simp)
        | @formula_decode state row rows certificate certificates hDecode =>
            intro _ hReject _
            exact hReject 0 row certificate state
              (by simp) (by simp) rfl hDecode
        | @rejected_row state row rows certificate certificates
            decoded hDecode hFailure =>
            intro _ _ hReject
            exact hReject 0 row decoded certificate state
              (by simp) (by simp) rfl
              hDecode hFailure
        | tail hDecode hReplay hFailure ih =>
            intro hLength hFormula hReject
            apply ih
            · intro h
              exact hLength (by simpa using h)
            · intro index row certificate prefixState
                hRow hCertificate hPrefix hFailedDecode
              exact hFormula (index + 1) row certificate prefixState
                (by
                  simpa only [List.getElem?_cons_succ] using hRow)
                (by
                  simpa only [List.getElem?_cons_succ] using hCertificate)
                (by
                  simpa [List.take, fs_replay_raw_rows,
                    hDecode, hReplay] using hPrefix)
                hFailedDecode
            · intro index row decoded certificate prefixState
                hRow hCertificate hPrefix hFailedDecode hRejected
              exact hReject (index + 1) row decoded certificate prefixState
                (by
                  simpa only [List.getElem?_cons_succ] using hRow)
                (by
                  simpa only [List.getElem?_cons_succ] using hCertificate)
                (by
                  simpa [List.take, fs_replay_raw_rows,
                    hDecode, hReplay] using hPrefix)
                hFailedDecode hRejected
      apply consume _ hRowsFailure
      · intro hLength
        have hCertificateDecode :
            fs_certificate_sequence_decode
                (godel_unpair_value number).2 =
              some certificates := by
          simpa [fs_certified_proof_code_decode] using
            hCertificates
        have hCertificatesLength :
            certificates.length =
              (nat_sequence_decode
                (godel_unpair_value number).2).length :=
          fs_certificate_sequence_decode_length
            hCertificateDecode
        have hRawLength :
            (proof_sequence_decode
                (godel_unpair_value number).1).length ≠
              (nat_sequence_decode
                (godel_unpair_value number).2).length := by
          intro hLengthEquality
          apply hLength
          calc
            (fs_certified_proof_code_decode number).1.length =
                (nat_sequence_decode
                  (godel_unpair_value number).2).length :=
              (by
                simpa [fs_certified_proof_code_decode] using
                  hLengthEquality)
            _ = certificates.length :=
              hCertificatesLength.symm
        exact
          ProofT.ZFCRep.code_neg_of_length
            number conclusion hConclusion hRawLength
      · exact fun index row certificate prefixState
          hRow hCertificate hPrefix hDecode => by
          have hRowsDecode :
              fs_formula_rows_decode_payload number
                  (fs_certified_proof_code_decode number).1 =
                none :=
            fs_mapM_eq_none_of_getElem?_decode_none
              hRow hDecode
          rcases
              ProofT.ZFCRep.code_neg_or_decode_residual
                number conclusion hConclusion hRowsDecode with
            hNeg | hStructural
          · exact hNeg
          · exact
              ProofT.ZFCRep.code_neg_of_decode_residual
                number conclusion hConclusion hStructural
      · exact fun index row decoded certificate prefixState
          hRow hCertificate hPrefix hDecode hRejected => by
          have hCertificateValue :
              (certificates.map
                  HilbertLineCertificateCode.value)[index]? =
                some certificate.value := by
            simpa using
              congrArg
                (Option.map HilbertLineCertificateCode.value)
                hCertificate
          cases hRejected with
          | @logical certificateCode hFailure =>
              have hCheck :
                  fs_logical_axiom_check
                      number certificateCode decoded.formula =
                    false := by
                simpa [fs_logical_axiom_check] using
                  hFailure.check_eq_false
              have hCertificateDecode :
                  fs_certificate_sequence_decode
                      (godel_unpair_value number).2 =
                    some certificates := by
                simpa [fs_certified_proof_code_decode] using
                  hCertificates
              have hRawValues :
                  nat_sequence_decode
                      (godel_unpair_value number).2 =
                    certificates.map
                      HilbertLineCertificateCode.value :=
                fs_certificate_sequence_decode_some_values
                  hCertificateDecode
              have hCertificateCodeValue :
                  (certificates.map
                      HilbertLineCertificateCode.value)[index]? =
                    some
                      (godel_pair_value 0 certificateCode) := by
                simpa [HilbertLineCertificateCode.value] using
                  hCertificateValue
              have hRawCertificate :
                  (nat_sequence_decode
                      (godel_unpair_value number).2)[index]? =
                    some
                      (godel_pair_value 0 certificateCode) := by
                simpa [hRawValues] using hCertificateCodeValue
              have hCertificateAt :
                  Derives fs_zfc_support_raw_theory [] (
                    ProofT.ZFCRep.certificate_sequence number ·ₘ
                        numₘ(index) ≐ₘ
                      numₘ(godel_pair_value 0 certificateCode)) := by
                simpa [ProofT.ZFCRep.certificate_sequence] using
                  fs_zfc_support_raw_derives_of_standard_sequence
                    (standard_token_sequence_apply_getElem?
                      (nat_sequence_decode
                        (godel_unpair_value number).2)
                      hRawCertificate)
              let rawRows : List (List Nat) :=
                proof_sequence_decode
                  (godel_unpair_value number).1
              have hRowRaw :
                  rawRows[index]? = some row := by
                simpa [rawRows, fs_certified_proof_code_decode] using
                  hRow
              have hRowIndex : index < rawRows.length :=
                (List.getElem?_eq_some_iff.mp hRowRaw).1
              have hFormulaBoundary :
                  GodelQuotation.Numbered.CodeBoundary
                    (ProofT.ZFCRep.proof_sequence number ·ₘ
                      numₘ(index)) := by
                constructor
                · exact function_application_term_admissible
                    (ProofT.ZFCRep.proof_sequence number)
                    (numₘ(index))
                    (ProofT.ZFCRep.proof_sequence_boundary number).1
                    (finite_numeral_term_admissible index)
                · simp [Term.freeSupport, Term.freeSupportList,
                    (ProofT.ZFCRep.proof_sequence_boundary number).2,
                    finite_numeral_term_freeSupport]
              have hRowValue :
                  rawRows[index] = row :=
                Option.some.inj <|
                  (List.getElem?_eq_getElem hRowIndex).symm.trans
                    hRowRaw
              have hFormulaToRow :
                  Derives fs_zfc_support_raw_theory [] (
                    (ProofT.ZFCRep.proof_sequence number ·ₘ
                        numₘ(index)) ≐ₘ
                      standard_token_sequence row) := by
                simpa [ProofT.ZFCRep.proof_sequence,
                  rawRows, hRowValue] using
                  ProofT.row_apply
                    ProofT.ZFC.object_replay
                    rawRows index hRowIndex
              have hCertificateBound :
                  certificateCode < number := by
                have hTaggedBound :
                    godel_pair_value 0 certificateCode <
                      (godel_unpair_value number).2 := by
                  simpa [nat_sequence_code_value_decode] using
                    mem_lt_nat_sequence_code_value
                      (List.mem_of_getElem? hRawCertificate)
                exact Nat.lt_of_le_of_lt
                  (right_le_godel_pair_value 0 certificateCode)
                  (Nat.lt_of_lt_of_le hTaggedBound
                    (godel_unpair_value_right_le number))
              have hConditionNeg :
                  Derives fs_zfc_support_raw_theory [] (
                    ¬ₘ CertifiedProof.logical_certificate_condition_with_ids
                      (ProofT.ZFCRep.proof_sequence number ·ₘ
                        numₘ(index))
                      (numₘ(certificateCode))
                      ProofT.lc_sequence_id
                      ProofT.lc_formula_trace_id
                      ProofT.lc_last_index_id
                      ProofT.lc_line_index_id
                      ProofT.lc_code_trace_id
                      ProofT.lc_code_index_id) :=
                CertifiedProof.fs_zfc_support_raw_logical_certificate_condition_neg_of_failure
                  (ProofT.ZFCRep.proof_sequence number ·ₘ
                    numₘ(index))
                  certificateCode number row
                  (nat_sequence_decode certificateCode) decoded
                  hFormulaBoundary hFormulaToRow rfl
                  hCertificateBound hDecode hFailure
              have hLineNeg :
                  Derives fs_zfc_support_raw_theory [] (
                    ¬ₘ ProofT.line_instance fs_zfc_replacement_object_certificate_verifier
                      (ProofT.ZFCRep.proof_sequence number)
                      (ProofT.ZFCRep.certificate_sequence number)
                      index) :=
                ProofT.line_instance_neg_of_logical_ground
                  ProofT.ZFC.certificate_core
                  fs_zfc_replacement_object_certificate_verifier
                  ProofT.ZFCRep.verifier_transport
                  (ProofT.ZFCRep.proof_sequence number)
                  (ProofT.ZFCRep.certificate_sequence number)
                  index certificateCode
                  (ProofT.ZFCRep.proof_sequence_boundary number).1
                  (ProofT.ZFCRep.certificate_sequence_boundary number).1
                  (ProofT.ZFCRep.proof_sequence_boundary number).2
                  (ProofT.ZFCRep.certificate_sequence_boundary number).2
                  hCertificateAt hConditionNeg
              exact
                ProofT.ZFCRep.code_neg_of_line
                  number conclusion hConclusion index
                  (by simpa [rawRows] using hRowIndex)
                  hLineNeg
          | @theory certificateCode hCheck =>
              have hCertificateDecode :
                  fs_certificate_sequence_decode
                      (godel_unpair_value number).2 =
                    some certificates := by
                simpa [fs_certified_proof_code_decode] using
                  hCertificates
              have hRawValues :
                  nat_sequence_decode
                      (godel_unpair_value number).2 =
                    certificates.map
                      HilbertLineCertificateCode.value :=
                fs_certificate_sequence_decode_some_values
                  hCertificateDecode
              have hCertificateCodeValue :
                  (certificates.map
                      HilbertLineCertificateCode.value)[index]? =
                    some
                      (godel_pair_value 1 certificateCode) := by
                simpa [HilbertLineCertificateCode.value] using
                  hCertificateValue
              have hRawCertificate :
                  (nat_sequence_decode
                      (godel_unpair_value number).2)[index]? =
                    some
                      (godel_pair_value 1 certificateCode) := by
                simpa [hRawValues] using hCertificateCodeValue
              have hCertificateAt :
                  Derives fs_zfc_support_raw_theory [] (
                    ProofT.ZFCRep.certificate_sequence number ·ₘ
                        numₘ(index) ≐ₘ
                      numₘ(godel_pair_value 1 certificateCode)) := by
                simpa [ProofT.ZFCRep.certificate_sequence] using
                  fs_zfc_support_raw_derives_of_standard_sequence
                    (standard_token_sequence_apply_getElem?
                      (nat_sequence_decode
                        (godel_unpair_value number).2)
                      hRawCertificate)
              let rawRows : List (List Nat) :=
                proof_sequence_decode
                  (godel_unpair_value number).1
              have hRowRaw :
                  rawRows[index]? = some row := by
                simpa [rawRows, fs_certified_proof_code_decode] using
                  hRow
              have hRowIndex : index < rawRows.length :=
                (List.getElem?_eq_some_iff.mp hRowRaw).1
              have hFormulaAdmissible :
                  Term.Admissible
                    (ProofT.ZFCRep.proof_sequence number ·ₘ
                      numₘ(index)) SetSort.set :=
                function_application_term_admissible
                  (ProofT.ZFCRep.proof_sequence number)
                  (numₘ(index))
                  (ProofT.ZFCRep.proof_sequence_boundary number).1
                  (finite_numeral_term_admissible index)
              have hFormulaClosed :
                  Term.freeSupport
                      (ProofT.ZFCRep.proof_sequence number ·ₘ
                        numₘ(index)) =
                    [] := by
                simp [Term.freeSupport, Term.freeSupportList,
                  (ProofT.ZFCRep.proof_sequence_boundary number).2,
                  finite_numeral_term_freeSupport]
              have hRowValue :
                  rawRows[index] = row :=
                Option.some.inj <|
                  (List.getElem?_eq_getElem hRowIndex).symm.trans
                    hRowRaw
              have hFormulaToRow :
                  Derives fs_zfc_support_raw_theory [] (
                    (ProofT.ZFCRep.proof_sequence number ·ₘ
                        numₘ(index)) ≐ₘ
                      standard_token_sequence row) := by
                simpa [ProofT.ZFCRep.proof_sequence, rawRows,
                  hRowValue] using
                  ProofT.row_apply
                    ProofT.ZFC.object_replay
                    rawRows index hRowIndex
              have hRejectOfConditionNeg
                  (hConditionNeg :
                    Derives fs_zfc_support_raw_theory [] (
                      ¬ₘ fs_zfc_replacement_object_certificate_verifier.condition
                        (ProofT.ZFCRep.proof_sequence number ·ₘ
                          numₘ(index))
                        (numₘ(certificateCode)))) :
                  Derives fs_zfc_support_raw_theory [] (
                    ¬ₘ proof_condition
                      fs_zfc_replacement_object_certificate_verifier
                      (numₘ(number)) conclusion
                      ProofT.condition_base) := by
                have hLineNeg :
                    Derives fs_zfc_support_raw_theory [] (
                      ¬ₘ ProofT.line_instance fs_zfc_replacement_object_certificate_verifier
                        (ProofT.ZFCRep.proof_sequence number)
                        (ProofT.ZFCRep.certificate_sequence number)
                        index) :=
                  ProofT.line_instance_neg_of_theory_ground
                    ProofT.ZFC.certificate_core
                    fs_zfc_replacement_object_certificate_verifier
                    ProofT.ZFCRep.verifier_transport
                    (ProofT.ZFCRep.proof_sequence number)
                    (ProofT.ZFCRep.certificate_sequence number)
                    index certificateCode
                    (ProofT.ZFCRep.proof_sequence_boundary number).1
                    (ProofT.ZFCRep.certificate_sequence_boundary number).1
                    (ProofT.ZFCRep.proof_sequence_boundary number).2
                    (ProofT.ZFCRep.certificate_sequence_boundary number).2
                    hCertificateAt hConditionNeg
                exact
                  ProofT.ZFCRep.code_neg_of_line
                    number conclusion hConclusion index
                    (by simpa [rawRows] using hRowIndex)
                    hLineNeg
              have hRejectFixed
                  (hFixedTag :
                    (godel_unpair_value certificateCode).1 = 0 ∨
                    (godel_unpair_value certificateCode).1 = 2 ∨
                    (godel_unpair_value certificateCode).1 = 3) :
                  Derives fs_zfc_support_raw_theory [] (
                    ¬ₘ proof_condition
                      fs_zfc_replacement_object_certificate_verifier
                      (numₘ(number)) conclusion
                      ProofT.condition_base) := by
                rcases
                    fs_zfc_replacement_support_generate_none_or_formula_ne_of_verifier_false
                      hCheck with
                  hGenerate | ⟨candidate, hGenerate, hDifferent⟩
                · have hOuterNeOne :
                      (godel_unpair_value certificateCode).1 ≠ 1 := by
                    rcases hFixedTag with hZero | hTwo | hThree <;>
                      omega
                  exact hRejectOfConditionNeg <| by
                    simpa [fs_zfc_replacement_object_certificate_verifier] using
                      fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_generate_none
                        (ProofT.ZFCRep.proof_sequence number ·ₘ
                          numₘ(index))
                        certificateCode hFormulaAdmissible hFormulaClosed
                        hGenerate hOuterNeOne
                · have hRowNe :
                      Derives fs_zfc_support_raw_theory [] (
                        ¬ₘ (standard_token_sequence row ≐ₘ
                          fs_zfc_formula_code_term candidate)) :=
                    fs_zfc_support_raw_standard_row_ne_formula_code
                      hDecode
                      (fs_zfc_replacement_support_generate_admissible hGenerate)
                      (fs_zfc_replacement_support_generate_hilbertize_eq_self
                        hGenerate)
                      hDifferent
                  have hFormulaNe :
                      Derives fs_zfc_support_raw_theory [] (
                        ¬ₘ
                          ((ProofT.ZFCRep.proof_sequence number ·ₘ
                              numₘ(index)) ≐ₘ
                            fs_zfc_formula_code_term candidate)) :=
                    fs_zfc_support_raw_formula_ne_formula_code_of_row_equality
                      (ProofT.ZFCRep.proof_sequence number ·ₘ
                        numₘ(index))
                      row candidate hFormulaAdmissible hFormulaToRow hRowNe
                  exact hRejectOfConditionNeg <| by
                    simpa [fs_zfc_replacement_object_certificate_verifier] using
                      fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_fixed_generate
                        (ProofT.ZFCRep.proof_sequence number ·ₘ
                          numₘ(index))
                        certificateCode candidate
                        hFormulaAdmissible hFormulaClosed hGenerate
                        hFixedTag hFormulaNe
              by_cases hOuterZero :
                  (godel_unpair_value certificateCode).1 = 0
              · exact hRejectFixed <| Or.inl hOuterZero
              by_cases hOuterOne :
                  (godel_unpair_value certificateCode).1 = 1
              · by_cases hSeparation :
                    (godel_unpair_value
                      (godel_unpair_value certificateCode).2).1 = 0
                · rcases
                      fs_zfc_replacement_support_generate_none_or_formula_ne_of_verifier_false
                        hCheck with
                    hGenerate | ⟨candidate, hGenerate, hDifferent⟩
                  · exact hRejectOfConditionNeg <| by
                      simpa [fs_zfc_replacement_object_certificate_verifier] using
                        fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_separation_generate_none
                          (ProofT.ZFCRep.proof_sequence number ·ₘ
                            numₘ(index))
                          certificateCode
                          hFormulaAdmissible hFormulaClosed
                          hGenerate hOuterOne hSeparation
                  · have hRowNe :
                        Derives fs_zfc_support_raw_theory [] (
                          ¬ₘ (standard_token_sequence row ≐ₘ
                            fs_zfc_formula_code_term candidate)) :=
                      fs_zfc_support_raw_standard_row_ne_formula_code
                        hDecode
                        (fs_zfc_replacement_support_generate_admissible hGenerate)
                        (fs_zfc_replacement_support_generate_hilbertize_eq_self
                          hGenerate)
                        hDifferent
                    have hFormulaNe :
                        Derives fs_zfc_support_raw_theory [] (
                          ¬ₘ
                            ((ProofT.ZFCRep.proof_sequence number ·ₘ
                                numₘ(index)) ≐ₘ
                              fs_zfc_formula_code_term candidate)) :=
                      fs_zfc_support_raw_formula_ne_formula_code_of_row_equality
                        (ProofT.ZFCRep.proof_sequence number ·ₘ
                          numₘ(index))
                        row candidate hFormulaAdmissible hFormulaToRow hRowNe
                    exact hRejectOfConditionNeg <| by
                      simpa [fs_zfc_replacement_object_certificate_verifier] using
                        fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_separation_generate
                          (ProofT.ZFCRep.proof_sequence number ·ₘ
                            numₘ(index))
                          certificateCode candidate
                          hFormulaAdmissible hFormulaClosed
                          hGenerate hFormulaNe
                          hOuterOne hSeparation
                by_cases hReplacement :
                    (godel_unpair_value
                      (godel_unpair_value certificateCode).2).1 = 2
                · rcases
                      fs_zfc_replacement_support_generate_none_or_formula_ne_of_verifier_false
                        hCheck with
                    hGenerate | ⟨candidate, hGenerate, hDifferent⟩
                  · exact hRejectOfConditionNeg <| by
                      simpa [fs_zfc_replacement_object_certificate_verifier] using
                        fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_replacement_generate_none
                          (ProofT.ZFCRep.proof_sequence number ·ₘ
                            numₘ(index))
                          certificateCode
                          hFormulaAdmissible hFormulaClosed
                          hGenerate hOuterOne hReplacement
                  · have hRowNe :
                        Derives fs_zfc_support_raw_theory [] (
                          ¬ₘ (standard_token_sequence row ≐ₘ
                            fs_zfc_formula_code_term candidate)) :=
                      fs_zfc_support_raw_standard_row_ne_formula_code
                        hDecode
                        (fs_zfc_replacement_support_generate_admissible hGenerate)
                        (fs_zfc_replacement_support_generate_hilbertize_eq_self
                          hGenerate)
                        hDifferent
                    have hFormulaNe :
                        Derives fs_zfc_support_raw_theory [] (
                          ¬ₘ
                            ((ProofT.ZFCRep.proof_sequence number ·ₘ
                                numₘ(index)) ≐ₘ
                              fs_zfc_formula_code_term candidate)) :=
                      fs_zfc_support_raw_formula_ne_formula_code_of_row_equality
                        (ProofT.ZFCRep.proof_sequence number ·ₘ
                          numₘ(index))
                        row candidate hFormulaAdmissible hFormulaToRow hRowNe
                    exact hRejectOfConditionNeg <| by
                      simpa [fs_zfc_replacement_object_certificate_verifier] using
                        fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_replacement_generate
                          (ProofT.ZFCRep.proof_sequence number ·ₘ
                            numₘ(index))
                          certificateCode candidate
                          hFormulaAdmissible hFormulaClosed
                          hGenerate hFormulaNe
                          hOuterOne hReplacement
                · exact hRejectOfConditionNeg <| by
                    simpa [fs_zfc_replacement_object_certificate_verifier] using
                      fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_unknown_schema_tag
                        (ProofT.ZFCRep.proof_sequence number ·ₘ
                          numₘ(index))
                        certificateCode hFormulaAdmissible hFormulaClosed
                        hOuterOne hSeparation hReplacement
              by_cases hOuterTwo :
                  (godel_unpair_value certificateCode).1 = 2
              · exact hRejectFixed <|
                  Or.inr <| Or.inl hOuterTwo
              by_cases hOuterThree :
                  (godel_unpair_value certificateCode).1 = 3
              · exact hRejectFixed <|
                  Or.inr <| Or.inr hOuterThree
              · exact hRejectOfConditionNeg <| by
                  simpa [fs_zfc_replacement_object_certificate_verifier] using
                    fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_unknown_outer_tag
                      (ProofT.ZFCRep.proof_sequence number ·ₘ
                        numₘ(index))
                      certificateCode hFormulaAdmissible hFormulaClosed
                      hOuterZero hOuterOne hOuterTwo hOuterThree
          | @modus_ponens implicationIndex premiseIndex hCheck =>
              have hCertificateDecode :
                  fs_certificate_sequence_decode
                      (godel_unpair_value number).2 =
                    some certificates := by
                simpa [fs_certified_proof_code_decode] using
                  hCertificates
              have hRawValues :
                  nat_sequence_decode
                      (godel_unpair_value number).2 =
                    certificates.map
                      HilbertLineCertificateCode.value :=
                fs_certificate_sequence_decode_some_values
                  hCertificateDecode
              have hCertificateCodeValue :
                  (certificates.map
                      HilbertLineCertificateCode.value)[index]? =
                    some
                      (godel_pair_value 2
                        (godel_pair_value implicationIndex premiseIndex)) := by
                simpa [HilbertLineCertificateCode.value] using
                  hCertificateValue
              have hRawCertificate :
                  (nat_sequence_decode
                      (godel_unpair_value number).2)[index]? =
                    some
                      (godel_pair_value 2
                        (godel_pair_value implicationIndex premiseIndex)) := by
                simpa [hRawValues] using hCertificateCodeValue
              have hCertificateAt :
                  Derives fs_zfc_support_raw_theory [] (
                    ProofT.ZFCRep.certificate_sequence number ·ₘ
                        numₘ(index) ≐ₘ
                      numₘ(godel_pair_value 2
                        (godel_pair_value implicationIndex
                          premiseIndex))) := by
                simpa [ProofT.ZFCRep.certificate_sequence] using
                  fs_zfc_support_raw_derives_of_standard_sequence
                    (standard_token_sequence_apply_getElem?
                      (nat_sequence_decode
                        (godel_unpair_value number).2)
                      hRawCertificate)
              let rawRows : List (List Nat) :=
                proof_sequence_decode
                  (godel_unpair_value number).1
              have hRowRaw :
                  rawRows[index]? = some row := by
                simpa [rawRows, fs_certified_proof_code_decode] using
                  hRow
              have hRowIndex : index < rawRows.length :=
                (List.getElem?_eq_some_iff.mp hRowRaw).1
              by_cases hOrder :
                  premiseIndex < implicationIndex ∧
                    implicationIndex < index
              · have hImplicationIndex :
                    implicationIndex < rawRows.length := by
                  omega
                have hPremiseIndex :
                    premiseIndex < rawRows.length := by
                  omega
                have hImplicationRow :
                    rawRows[implicationIndex]? =
                      some rawRows[implicationIndex] :=
                  List.getElem?_eq_getElem hImplicationIndex
                have hPremiseRow :
                    rawRows[premiseIndex]? =
                      some rawRows[premiseIndex] :=
                  List.getElem?_eq_getElem hPremiseIndex
                have hShape :
                    rawRows[implicationIndex] ≠
                      Numbered.implication_tokens
                        rawRows[premiseIndex] row :=
                  fs_modus_ponens_raw_shape_ne_of_check_false
                    ProofCode.fs_zfc_replacement_support_enumeration
                    number rawRows certificates
                    index implicationIndex premiseIndex
                    row rawRows[implicationIndex]
                    rawRows[premiseIndex]
                    decoded prefixState
                    hImplicationRow hPremiseRow
                    (by
                      simpa [rawRows, fs_certified_proof_code_decode] using
                        hPrefix)
                    hDecode hOrder hCheck
                have hRowValue :
                    rawRows[index] = row :=
                  Option.some.inj <|
                    (List.getElem?_eq_getElem hRowIndex).symm.trans
                      hRowRaw
                have hGroundNeg :
                    Derives fs_zfc_support_raw_theory [] (
                      ¬ₘ modus_ponensₘ(
                        ProofT.ZFCRep.proof_sequence number ·ₘ
                          numₘ(premiseIndex),
                        ProofT.ZFCRep.proof_sequence number ·ₘ
                          numₘ(implicationIndex),
                        ProofT.ZFCRep.proof_sequence number ·ₘ
                          numₘ(index))) := by
                  simpa [ProofT.ZFCRep.proof_sequence, rawRows] using
                    ProofT.row_modus_ponens_neg
                      ProofT.ZFC.object_replay
                      rawRows index implicationIndex premiseIndex
                      hRowIndex hImplicationIndex hPremiseIndex
                      (by
                        simpa [hRowValue] using hShape)
                have hLineNeg :
                    Derives fs_zfc_support_raw_theory [] (
                      ¬ₘ ProofT.line_instance fs_zfc_replacement_object_certificate_verifier
                        (ProofT.ZFCRep.proof_sequence number)
                        (ProofT.ZFCRep.certificate_sequence number)
                        index) :=
                  ProofT.line_instance_neg_of_modus_ponens_ground
                    ProofT.ZFC.certificate_core
                    fs_zfc_replacement_object_certificate_verifier
                    ProofT.ZFCRep.verifier_transport
                    (ProofT.ZFCRep.proof_sequence number)
                    (ProofT.ZFCRep.certificate_sequence number)
                    index implicationIndex premiseIndex
                    (ProofT.ZFCRep.proof_sequence_boundary number).1
                    (ProofT.ZFCRep.certificate_sequence_boundary number).1
                    (ProofT.ZFCRep.proof_sequence_boundary number).2
                    (ProofT.ZFCRep.certificate_sequence_boundary number).2
                    hCertificateAt hGroundNeg
                exact
                  ProofT.ZFCRep.code_neg_of_line
                    number conclusion hConclusion index
                    (by simpa [rawRows] using hRowIndex)
                    hLineNeg
              · have hBadOrder :
                    ¬ premiseIndex < implicationIndex ∨
                      ¬ implicationIndex < index := by
                  omega
                have hLineNeg :
                    Derives fs_zfc_support_raw_theory [] (
                      ¬ₘ ProofT.line_instance fs_zfc_replacement_object_certificate_verifier
                        (ProofT.ZFCRep.proof_sequence number)
                        (ProofT.ZFCRep.certificate_sequence number)
                        index) :=
                  ProofT.line_instance_neg_of_modus_ponens_order
                    ProofT.ZFC.certificate_core
                    fs_zfc_replacement_object_certificate_verifier
                    ProofT.ZFCRep.verifier_transport
                    (ProofT.ZFCRep.proof_sequence number)
                    (ProofT.ZFCRep.certificate_sequence number)
                    index implicationIndex premiseIndex
                    (godel_pair_value 2
                      (godel_pair_value implicationIndex premiseIndex))
                    (ProofT.ZFCRep.proof_sequence_boundary number).1
                    (ProofT.ZFCRep.certificate_sequence_boundary number).1
                    (ProofT.ZFCRep.proof_sequence_boundary number).2
                    (ProofT.ZFCRep.certificate_sequence_boundary number).2
                    hCertificateAt rfl hBadOrder
                exact
                  ProofT.ZFCRep.code_neg_of_line
                    number conclusion hConclusion index
                    (by simpa [rawRows] using hRowIndex)
                    hLineNeg

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
