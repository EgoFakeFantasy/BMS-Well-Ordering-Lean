import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedCompleteness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedTraceReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSubstitution

/-!
# ZFC checked 证明的对象层内部化

本模块把一条完整的外部 checked trace 封装为对象理论中的闭合
`CertifiedProof.code_condition_with_ids`。四个存在见证依次是公式序列、
证书序列、公式序列数值码和证书序列数值码；逐行检查与逻辑 transcript
统一使用 `ProofT.CheckedSyntax` 的固定编号表。
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

/--
一条以 `formula` 为末行的 checked trace 自动给出其规范证明码的对象层证明。

该接口同时闭合四类见证，不向调用方暴露任何序列、编码轨迹或逐行证明参数。
-/
theorem fs_zfc_support_raw_certified_code_condition_of_checked_trace
    {Thilbert : SetTheory}
    (enumeration : HilbertTheoryEnumeration Thilbert)
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (hTheoryCertificate :
      ∀ {certificate : Nat} {row : SetFormula},
        enumeration.certificate_verifier certificate row = true →
          Derives fs_zfc_support_raw_theory [] (
            verifier.condition
              (fs_zfc_formula_code_term row)
              (numₘ(certificate))))
    {proof initial : List SetFormula}
    {certificates : List HilbertLineCertificateCode}
    {formula : SetFormula}
    (hTrace :
      FSCheckedHilbertTrace
        enumeration
        fs_logical_axiom_canonical_check
        proof certificates)
    (hProof : proof = initial ++ [formula]) :
    Derives fs_zfc_support_raw_theory [] (
      proof_condition
        verifier
        (numₘ(certified_hilbert_proof_code_value
          certified_row_tokens proof certificates))
        (fs_zfc_formula_code_term formula)
        ProofT.condition_base) := by
  let sequence : SetTerm :=
    standard_sequence
      (proof.map (fun row =>
        standard_token_sequence (certified_row_tokens row)))
  let certificateSequence : SetTerm :=
    standard_token_sequence
      (certificates.map HilbertLineCertificateCode.value)
  let formulaCode : SetTerm :=
    numₘ(proof_sequence_code_value
      (proof.map certified_row_tokens))
  let certificateCode : SetTerm :=
    numₘ(nat_sequence_code_value
      (certificates.map HilbertLineCertificateCode.value))
  let proofCode : SetTerm :=
    numₘ(certified_hilbert_proof_code_value
      certified_row_tokens proof certificates)
  let conclusion : SetTerm :=
    fs_zfc_formula_code_term formula
  have hRows :
      ∀ row, row ∈ proof →
        Formula.Admissible row := by
    intro row hRow
    exact fs_checked_trace_admissible_of_mem hTrace hRow
  have hNonempty : proof ≠ [] := by
    rw [hProof]
    simp
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    dsimp [sequence]
    apply seq_admissible_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, hRow, rfl⟩
    exact standard_token_sequence_admissible
      (certified_row_tokens row)
  have hCertificateSequence :
      Term.Admissible certificateSequence SetSort.set := by
    simpa [certificateSequence] using
      standard_token_sequence_admissible
        (certificates.map HilbertLineCertificateCode.value)
  have hFormulaCode :
      Term.Admissible formulaCode SetSort.set := by
    simpa [formulaCode] using
      finite_numeral_term_admissible
        (proof_sequence_code_value
          (proof.map certified_row_tokens))
  have hCertificateCode :
      Term.Admissible certificateCode SetSort.set := by
    simpa [certificateCode] using
      finite_numeral_term_admissible
        (nat_sequence_code_value
          (certificates.map HilbertLineCertificateCode.value))
  have hProofCode :
      Term.Admissible proofCode SetSort.set := by
    simpa [proofCode] using
      finite_numeral_term_admissible
        (certified_hilbert_proof_code_value
          certified_row_tokens proof certificates)
  have hConclusion :
      Term.Admissible conclusion SetSort.set := by
    simpa [conclusion] using
      fs_zfc_formula_code_term_admissible formula
  have hSequenceClosed :
      Term.freeSupport sequence = [] := by
    dsimp [sequence]
    apply seq_support_nil_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, hRow, rfl⟩
    exact standard_token_sequence_freeSupport_nil
      (certified_row_tokens row)
  have hCertificateSequenceClosed :
      Term.freeSupport certificateSequence = [] := by
    simp [certificateSequence]
  have hFormulaCodeClosed :
      Term.freeSupport formulaCode = [] := by
    simpa [formulaCode] using
      finite_numeral_term_freeSupport
        (proof_sequence_code_value
          (proof.map certified_row_tokens))
  have hCertificateCodeClosed :
      Term.freeSupport certificateCode = [] := by
    simpa [certificateCode] using
      finite_numeral_term_freeSupport
        (nat_sequence_code_value
          (certificates.map HilbertLineCertificateCode.value))
  have hProofCodeClosed :
      Term.freeSupport proofCode = [] := by
    simpa [proofCode] using
      finite_numeral_term_freeSupport
        (certified_hilbert_proof_code_value
          certified_row_tokens proof certificates)
  have hConclusionClosed :
      Term.freeSupport conclusion = [] := by
    simpa [conclusion] using
      fs_zfc_formula_code_term_freeSupport_nil formula
  have hSequenceBoundary :
      GodelQuotation.Numbered.CodeBoundary sequence :=
    ⟨hSequence, hSequenceClosed⟩
  have hCertificateSequenceBoundary :
      GodelQuotation.Numbered.CodeBoundary certificateSequence :=
    ⟨hCertificateSequence, hCertificateSequenceClosed⟩
  have hFormulaCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary formulaCode :=
    ⟨hFormulaCode, hFormulaCodeClosed⟩
  have hCertificateCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary certificateCode :=
    ⟨hCertificateCode, hCertificateCodeClosed⟩
  have hProofCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary proofCode :=
    ⟨hProofCode, hProofCodeClosed⟩
  have hConclusionBoundary :
      GodelQuotation.Numbered.CodeBoundary conclusion :=
    ⟨hConclusion, hConclusionClosed⟩
  have hConclusionFormulaCode :
      Derives fs_zfc_support_raw_theory [] (
        formula_codeₘ(conclusion)) := by
    simpa [conclusion] using
      fs_zfc_support_raw_formula_code_term_is_formula_code
        (hRows formula (by rw [hProof]; simp))
  have hProofCodeOmega :
      Derives fs_zfc_support_raw_theory [] (
        proofCode ∈ₘ ωₘ) := by
    simpa [proofCode] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_mem_omega
          (certified_hilbert_proof_code_value
            certified_row_tokens proof certificates))
  have hSequenceCondition :
      Derives fs_zfc_support_raw_theory [] (
        ProofT.sequence_condition verifier
          sequence certificateSequence) := by
    simpa [sequence, certificateSequence] using
      ProofT.ZFC.trace_sequence_condition
        enumeration verifier hContract hTheoryCertificate
        hTrace hNonempty
  have hProofSequenceCode :
      Derives fs_zfc_support_raw_theory [] (
        proof_sequence_code_condition_with_ids
          sequence formulaCode
          884 885 886 887 888) := by
    simpa [sequence, formulaCode] using
      fs_zfc_support_raw_proof_sequence_code_condition_with_ids
        hRows hNonempty
        884 885 886 887 888
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
  have hCertificateSequenceCode :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          certificateSequence certificateCode
          889 890) := by
    simpa [certificateSequence, certificateCode] using
      fs_zfc_support_raw_certificate_code_condition_with_ids
        certificates 889 890 (by native_decide)
  have hCodeEquality :
      Derives fs_zfc_support_raw_theory [] (
        proofCode ≐ₘ
          godel_pairₘ(⟨formulaCode, certificateCode⟩ₘ)) := by
    have hPair :=
      fs_zfc_support_raw_certified_hilbert_proof_code_pair_eq
        (proof := proof) certificates
    have hSymmetric :=
      Metatheory.Derives.equality_symm
        hPair
    simpa [proofCode, formulaCode, certificateCode,
      certified_hilbert_proof_code_value] using hSymmetric
  have hFormulaCodeBound :
      Derives fs_zfc_support_raw_theory [] (
        CertifiedProof.proof_code_component_bound
          proofCode formulaCode) := by
    simpa [CertifiedProof.proof_code_component_bound,
      proofCode, formulaCode,
      certified_hilbert_proof_code_value,
      finite_numeral_term, successor_term] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          (proof_sequence_code_value
            (proof.map certified_row_tokens))
          (certified_hilbert_proof_code_value
            certified_row_tokens proof certificates + 1)
          (Nat.lt_succ_of_le
            (left_le_godel_pair_value
              (proof_sequence_code_value
                (proof.map certified_row_tokens))
              (nat_sequence_code_value
                (certificates.map
                  HilbertLineCertificateCode.value)))))
  have hCertificateCodeBound :
      Derives fs_zfc_support_raw_theory [] (
        CertifiedProof.proof_code_component_bound
          proofCode certificateCode) := by
    simpa [CertifiedProof.proof_code_component_bound,
      proofCode, certificateCode,
      certified_hilbert_proof_code_value,
      finite_numeral_term, successor_term] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          (nat_sequence_code_value
            (certificates.map
              HilbertLineCertificateCode.value))
          (certified_hilbert_proof_code_value
            certified_row_tokens proof certificates + 1)
          (Nat.lt_succ_of_le
            (right_le_godel_pair_value
              (proof_sequence_code_value
                (proof.map certified_row_tokens))
              (nat_sequence_code_value
                (certificates.map
                  HilbertLineCertificateCode.value)))))
  have hTerminal :
      Derives fs_zfc_support_raw_theory [] (
        proof_sequence_terminal_condition
          sequence conclusion) := by
    simpa [sequence, conclusion] using
      ProofT.terminal_of_last
        fs_zfc_support_raw_contains_standard_sequence_semantics
        fs_zfc_support_raw_contains_godel_quotation
        hProof hRows
  have hSequenceSpace :
      Derives fs_zfc_support_raw_theory [] (
        sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) := by
    exact FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimLeft hSequenceCondition
  have hCertificateSequenceSpace :
      Derives fs_zfc_support_raw_theory [] (
        certificateSequence ∈ₘ seq₊_spaceₘ(ωₘ)) := by
    exact FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimLeft hSequenceCondition
  have hBody :
      Derives fs_zfc_support_raw_theory [] (
        ((ProofT.sequence_condition verifier
            sequence certificateSequence ∧ₘ
          proof_sequence_code_condition_with_ids
            sequence formulaCode
            884 885 886 887 888) ∧ₘ
          nat_sequence_code_condition_with_ids
            certificateSequence certificateCode
            889 890) ∧ₘ
        ((CertifiedProof.proof_code_component_bound
            proofCode formulaCode ∧ₘ
          CertifiedProof.proof_code_component_bound
            proofCode certificateCode) ∧ₘ
          ((proofCode ≐ₘ
              godel_pairₘ(⟨formulaCode, certificateCode⟩ₘ)) ∧ₘ
            proof_sequence_terminal_condition
              sequence conclusion))) :=
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro
          hSequenceCondition hProofSequenceCode)
        hCertificateSequenceCode)
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro
          hFormulaCodeBound hCertificateCodeBound)
        (FirstOrder.Derives.conjIntro hCodeEquality hTerminal))
  let codeBody
      (sequenceTerm certificatesTerm
        formulaCodeTerm certificateCodeTerm : SetTerm) :
      SetFormula :=
    ((ProofT.sequence_condition verifier
        sequenceTerm certificatesTerm ∧ₘ
      proof_sequence_code_condition_with_ids
        sequenceTerm formulaCodeTerm
        884 885 886 887 888) ∧ₘ
      nat_sequence_code_condition_with_ids
        certificatesTerm certificateCodeTerm
        889 890) ∧ₘ
    ((CertifiedProof.proof_code_component_bound
        proofCode formulaCodeTerm ∧ₘ
      CertifiedProof.proof_code_component_bound
        proofCode certificateCodeTerm) ∧ₘ
      ((proofCode ≐ₘ
          godel_pairₘ(
            ⟨formulaCodeTerm, certificateCodeTerm⟩ₘ)) ∧ₘ
        proof_sequence_terminal_condition
          sequenceTerm conclusion))
  let certificateBody
      (sequenceTerm certificatesTerm
        formulaCodeTerm certificateCodeTerm : SetTerm) :
      SetFormula :=
    CertifiedProof.proof_code_component_bound
        proofCode certificateCodeTerm ∧ₘ
      codeBody sequenceTerm certificatesTerm
        formulaCodeTerm certificateCodeTerm
  let formulaBody
      (sequenceTerm certificatesTerm formulaCodeTerm : SetTerm) :
      SetFormula :=
    CertifiedProof.proof_code_component_bound
        proofCode formulaCodeTerm ∧ₘ
      (∃ₘ[SetSort.set, 883],
        certificateBody sequenceTerm certificatesTerm
          formulaCodeTerm (x#883))
  let certificatesBody
      (sequenceTerm certificatesTerm : SetTerm) :
      SetFormula :=
    certificatesTerm ∈ₘ seq₊_spaceₘ(ωₘ) ∧ₘ
      (∃ₘ[SetSort.set, 882],
        formulaBody sequenceTerm certificatesTerm (x#882))
  let sequenceBody (sequenceTerm : SetTerm) : SetFormula :=
    sequenceTerm ∈ₘ seq₊_spaceₘ(FormulaCodeₘ) ∧ₘ
      (∃ₘ[SetSort.set, 881],
        certificatesBody sequenceTerm (x#881))
  have hVariableVerifierBase :
      ProofT.schema_base
          [(x#880) ·ₘ (x#900), (x#903)] =
        904 := by
    simp [ProofT.schema_base, FreshVariable.fresh_id,
      FreshVariable.formulas_bound, FreshVariable.formula_bound,
      FreshVariable.support_bound, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList]
  have hSequenceVerifierBase :
      ProofT.schema_base
          [sequence ·ₘ (x#900), (x#903)] =
        904 := by
    simp [ProofT.schema_base, FreshVariable.fresh_id,
      FreshVariable.formulas_bound, FreshVariable.formula_bound,
      FreshVariable.support_bound, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList,
      hSequenceClosed]
  have hCodeBodySubstitute
      (sequenceTerm certificatesTerm
        formulaCodeTerm certificateCodeTerm
        sequenceResult certificatesResult
        formulaCodeResult certificateCodeResult
        replacement : SetTerm)
      (sourceId : FreeVarId)
      (hSource : sourceId < 884)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement)
      (hSequenceSubstitution :
        Term.substituteFree SetSort.set sourceId replacement
            sequenceTerm =
          sequenceResult)
      (hCertificatesSubstitution :
        Term.substituteFree SetSort.set sourceId replacement
            certificatesTerm =
          certificatesResult)
      (hFormulaCodeSubstitution :
        Term.substituteFree SetSort.set sourceId replacement
            formulaCodeTerm =
          formulaCodeResult)
      (hCertificateCodeSubstitution :
        Term.substituteFree SetSort.set sourceId replacement
            certificateCodeTerm =
          certificateCodeResult)
      (hVerifierSourceBase :
        ProofT.schema_base
            [sequenceTerm ·ₘ (x#900), (x#903)] =
          904)
      (hVerifierTargetBase :
        ProofT.schema_base
            [sequenceResult ·ₘ (x#900), (x#903)] =
          904) :
      Formula.substituteFree SetSort.set sourceId replacement
          (codeBody sequenceTerm certificatesTerm
            formulaCodeTerm certificateCodeTerm) =
        codeBody sequenceResult certificatesResult
          formulaCodeResult certificateCodeResult := by
    have hSourceNe
        (id : FreeVarId) (hId : 884 ≤ id) :
        sourceId ≠ id :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le hSource hId)
    have hFresh (id : FreeVarId) :
        (SetSort.set, id) ∉ Term.freeSupport replacement := by
      rw [hReplacement.2]
      exact List.not_mem_nil
    have hSequenceConditionSubstitution :=
      ProofT.sequence_condition_substitute
        verifier hContract
        sequenceTerm certificatesTerm replacement
        sequenceResult certificatesResult sourceId
        (Nat.lt_trans hSource (by decide))
        hReplacement hSequenceSubstitution
        hCertificatesSubstitution
        hVerifierSourceBase hVerifierTargetBase
    have hProofSequenceSubstitution :=
      proof_sequence_code_condition_with_ids_substitute_closed
        sequenceTerm formulaCodeTerm replacement
        sequenceResult formulaCodeResult
        sourceId 884 885 886 887 888
        (hSourceNe 884 (by decide))
        (hSourceNe 885 (by decide))
        (hSourceNe 886 (by decide))
        (hSourceNe 887 (by decide))
        (hSourceNe 888 (by decide))
        hReplacement.1.2
        (hFresh 884) (hFresh 885) (hFresh 886)
        (hFresh 887) (hFresh 888)
        hSequenceSubstitution hFormulaCodeSubstitution
    have hCertificateSequenceSubstitution :=
      nat_sequence_code_condition_with_ids_substitute_closed
        certificatesTerm certificateCodeTerm replacement
        certificatesResult certificateCodeResult
        sourceId 889 890
        (hSourceNe 889 (by decide))
        (hSourceNe 890 (by decide))
        hReplacement.1.2
        (hFresh 889) (hFresh 890)
        hCertificatesSubstitution hCertificateCodeSubstitution
    have hTerminalSubstitution :=
      proof_sequence_terminal_condition_substitute
        sequenceTerm conclusion replacement
        sequenceResult conclusion sourceId
        hSequenceSubstitution
        (GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
          hConclusionBoundary sourceId replacement)
    have hProofCodeFixed :=
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hProofCodeBoundary sourceId replacement
    simp [codeBody, Formula.substituteFree,
      Term.substituteFree,
      CertifiedProof.proof_code_component_bound,
      hSequenceConditionSubstitution,
      hProofSequenceSubstitution,
      hCertificateSequenceSubstitution,
      hTerminalSubstitution,
      hProofCodeFixed,
      hFormulaCodeSubstitution,
      hCertificateCodeSubstitution]
  have hSequenceFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport sequence := by
    rw [hSequenceClosed]
    exact List.not_mem_nil
  have hCertificateSequenceFresh (id : FreeVarId) :
      (SetSort.set, id) ∉
        Term.freeSupport certificateSequence := by
    rw [hCertificateSequenceClosed]
    exact List.not_mem_nil
  have hFormulaCodeFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport formulaCode := by
    rw [hFormulaCodeClosed]
    exact List.not_mem_nil
  have hCertificateCodeFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport certificateCode := by
    rw [hCertificateCodeClosed]
    exact List.not_mem_nil
  have hBody0 :
      Formula.substituteFree SetSort.set 880 sequence
          (codeBody (x#880) (x#881) (x#882) (x#883)) =
        codeBody sequence (x#881) (x#882) (x#883) := by
    exact hCodeBodySubstitute
      (x#880) (x#881) (x#882) (x#883)
      sequence (x#881) (x#882) (x#883)
      sequence 880 (by native_decide) hSequenceBoundary
      (by simp [Term.substituteFree, set_variable])
      (by simp [Term.substituteFree, set_variable])
      (by simp [Term.substituteFree, set_variable])
      (by simp [Term.substituteFree, set_variable])
      hVariableVerifierBase hSequenceVerifierBase
  have hBody1 :
      Formula.substituteFree SetSort.set 881
          certificateSequence
          (codeBody sequence (x#881) (x#882) (x#883)) =
        codeBody sequence certificateSequence
          (x#882) (x#883) := by
    exact hCodeBodySubstitute
      sequence (x#881) (x#882) (x#883)
      sequence certificateSequence (x#882) (x#883)
      certificateSequence 881 (by native_decide)
      hCertificateSequenceBoundary
      (GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hSequenceBoundary 881 certificateSequence)
      (by simp [Term.substituteFree, set_variable])
      (by simp [Term.substituteFree, set_variable])
      (by simp [Term.substituteFree, set_variable])
      hSequenceVerifierBase hSequenceVerifierBase
  have hBody2 :
      Formula.substituteFree SetSort.set 882 formulaCode
          (codeBody sequence certificateSequence
            (x#882) (x#883)) =
        codeBody sequence certificateSequence
          formulaCode (x#883) := by
    exact hCodeBodySubstitute
      sequence certificateSequence (x#882) (x#883)
      sequence certificateSequence formulaCode (x#883)
      formulaCode 882 (by native_decide)
      hFormulaCodeBoundary
      (GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hSequenceBoundary 882 formulaCode)
      (GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hCertificateSequenceBoundary 882 formulaCode)
      (by simp [Term.substituteFree, set_variable])
      (by simp [Term.substituteFree, set_variable])
      hSequenceVerifierBase hSequenceVerifierBase
  have hBody3 :
      Formula.substituteFree SetSort.set 883 certificateCode
          (codeBody sequence certificateSequence
            formulaCode (x#883)) =
        codeBody sequence certificateSequence
          formulaCode certificateCode := by
    exact hCodeBodySubstitute
      sequence certificateSequence formulaCode (x#883)
      sequence certificateSequence formulaCode certificateCode
      certificateCode 883 (by native_decide)
      hCertificateCodeBoundary
      (GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hSequenceBoundary 883 certificateCode)
      (GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hCertificateSequenceBoundary 883 certificateCode)
      (GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hFormulaCodeBoundary 883 certificateCode)
      (by simp [Term.substituteFree, set_variable])
      hSequenceVerifierBase hSequenceVerifierBase
  have hExists0At883 :
      Formula.substituteFree SetSort.set 880 sequence
          (∃ₘ[SetSort.set, 883],
            codeBody (x#880) (x#881) (x#882) (x#883)) =
        (∃ₘ[SetSort.set, 883],
          codeBody sequence (x#881) (x#882) (x#883)) :=
    fs_zfc_substitute_free_exists_closed
      880 883 sequence
      (codeBody (x#880) (x#881) (x#882) (x#883))
      (codeBody sequence (x#881) (x#882) (x#883))
      (by native_decide) hSequence.2
      (hSequenceFresh 883) hBody0
  have hExists0At882 :
      Formula.substituteFree SetSort.set 880 sequence
          (∃ₘ[SetSort.set, 882],
            ∃ₘ[SetSort.set, 883],
              codeBody (x#880) (x#881) (x#882) (x#883)) =
        (∃ₘ[SetSort.set, 882],
          ∃ₘ[SetSort.set, 883],
            codeBody sequence (x#881) (x#882) (x#883)) :=
    fs_zfc_substitute_free_exists_closed
      880 882 sequence
      (∃ₘ[SetSort.set, 883],
        codeBody (x#880) (x#881) (x#882) (x#883))
      (∃ₘ[SetSort.set, 883],
        codeBody sequence (x#881) (x#882) (x#883))
      (by native_decide) hSequence.2
      (hSequenceFresh 882) hExists0At883
  have hExists0 :
      Formula.substituteFree SetSort.set 880 sequence
          (∃ₘ[SetSort.set, 881],
            ∃ₘ[SetSort.set, 882],
              ∃ₘ[SetSort.set, 883],
                codeBody (x#880) (x#881) (x#882) (x#883)) =
        (∃ₘ[SetSort.set, 881],
          ∃ₘ[SetSort.set, 882],
            ∃ₘ[SetSort.set, 883],
              codeBody sequence (x#881) (x#882) (x#883)) :=
    fs_zfc_substitute_free_exists_closed
      880 881 sequence
      (∃ₘ[SetSort.set, 882],
        ∃ₘ[SetSort.set, 883],
          codeBody (x#880) (x#881) (x#882) (x#883))
      (∃ₘ[SetSort.set, 882],
        ∃ₘ[SetSort.set, 883],
          codeBody sequence (x#881) (x#882) (x#883))
      (by native_decide) hSequence.2
      (hSequenceFresh 881) hExists0At882
  have hExists1At883 :
      Formula.substituteFree SetSort.set 881
          certificateSequence
          (∃ₘ[SetSort.set, 883],
            codeBody sequence (x#881) (x#882) (x#883)) =
        (∃ₘ[SetSort.set, 883],
          codeBody sequence certificateSequence
            (x#882) (x#883)) :=
    fs_zfc_substitute_free_exists_closed
      881 883 certificateSequence
      (codeBody sequence (x#881) (x#882) (x#883))
      (codeBody sequence certificateSequence
        (x#882) (x#883))
      (by native_decide) hCertificateSequence.2
      (hCertificateSequenceFresh 883) hBody1
  have hExists1 :
      Formula.substituteFree SetSort.set 881
          certificateSequence
          (∃ₘ[SetSort.set, 882],
            ∃ₘ[SetSort.set, 883],
              codeBody sequence (x#881) (x#882) (x#883)) =
        (∃ₘ[SetSort.set, 882],
          ∃ₘ[SetSort.set, 883],
            codeBody sequence certificateSequence
              (x#882) (x#883)) :=
    fs_zfc_substitute_free_exists_closed
      881 882 certificateSequence
      (∃ₘ[SetSort.set, 883],
        codeBody sequence (x#881) (x#882) (x#883))
      (∃ₘ[SetSort.set, 883],
        codeBody sequence certificateSequence
          (x#882) (x#883))
      (by native_decide) hCertificateSequence.2
      (hCertificateSequenceFresh 882) hExists1At883
  have hExists2 :
      Formula.substituteFree SetSort.set 882 formulaCode
          (∃ₘ[SetSort.set, 883],
            codeBody sequence certificateSequence
              (x#882) (x#883)) =
        (∃ₘ[SetSort.set, 883],
          codeBody sequence certificateSequence
            formulaCode (x#883)) :=
    fs_zfc_substitute_free_exists_closed
      882 883 formulaCode
      (codeBody sequence certificateSequence
        (x#882) (x#883))
      (codeBody sequence certificateSequence
        formulaCode (x#883))
      (by native_decide) hFormulaCode.2
      (hFormulaCodeFresh 883) hBody2
  have hProofCodeSubstitute
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement proofCode =
        proofCode :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hProofCodeBoundary id replacement
  have hCodeBodyAt :
      Derives fs_zfc_support_raw_theory [] (
        codeBody sequence certificateSequence
          formulaCode certificateCode) := by
    simpa [codeBody, ProofT.sequence_condition] using hBody
  have hCertificateBody3 :
      Formula.substituteFree SetSort.set 883 certificateCode
          (certificateBody sequence certificateSequence
            formulaCode (x#883)) =
        certificateBody sequence certificateSequence
          formulaCode certificateCode := by
    simp [certificateBody, Formula.substituteFree,
      Term.substituteFree, set_variable,
      CertifiedProof.proof_code_component_bound,
      hProofCodeSubstitute, hBody3]
  have hCertificateInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 883 certificateCode
          (certificateBody sequence certificateSequence
            formulaCode (x#883))) := by
    rw [hCertificateBody3]
    exact FirstOrder.Derives.conjIntro
      hCertificateCodeBound hCodeBodyAt
  have hCertificateExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 883],
          certificateBody sequence certificateSequence
            formulaCode (x#883)) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := certificateCode) 883 hCertificateInstance
  have hCertificateBody2 :
      Formula.substituteFree SetSort.set 882 formulaCode
          (certificateBody sequence certificateSequence
            (x#882) (x#883)) =
        certificateBody sequence certificateSequence
          formulaCode (x#883) := by
    simp [certificateBody, Formula.substituteFree,
      Term.substituteFree, set_variable,
      CertifiedProof.proof_code_component_bound,
      hProofCodeSubstitute, hBody2]
  have hCertificateExists2 :
      Formula.substituteFree SetSort.set 882 formulaCode
          (∃ₘ[SetSort.set, 883],
            certificateBody sequence certificateSequence
              (x#882) (x#883)) =
        (∃ₘ[SetSort.set, 883],
          certificateBody sequence certificateSequence
            formulaCode (x#883)) :=
    fs_zfc_substitute_free_exists_closed
      882 883 formulaCode
      (certificateBody sequence certificateSequence
        (x#882) (x#883))
      (certificateBody sequence certificateSequence
        formulaCode (x#883))
      (by native_decide) hFormulaCode.2
      (hFormulaCodeFresh 883) hCertificateBody2
  have hFormulaBody2 :
      Formula.substituteFree SetSort.set 882 formulaCode
          (formulaBody sequence certificateSequence (x#882)) =
        formulaBody sequence certificateSequence formulaCode := by
    have hGuard :
        Formula.substituteFree SetSort.set 882 formulaCode
            (CertifiedProof.proof_code_component_bound
              proofCode (x#882)) =
          CertifiedProof.proof_code_component_bound
            proofCode formulaCode := by
      simp [Formula.substituteFree, Term.substituteFree,
        set_variable,
        CertifiedProof.proof_code_component_bound,
        hProofCodeSubstitute]
    simp only [formulaBody, Formula.substituteFree] at hGuard ⊢
    have hRight := hCertificateExists2
    simp only [Formula.substituteFree] at hRight
    rw [hGuard, hRight]
  have hFormulaInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 882 formulaCode
          (formulaBody sequence certificateSequence (x#882))) := by
    rw [hFormulaBody2]
    exact FirstOrder.Derives.conjIntro
      hFormulaCodeBound hCertificateExists
  have hFormulaExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 882],
          formulaBody sequence certificateSequence (x#882)) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := formulaCode) 882 hFormulaInstance
  have hCertificateBody1 :
      Formula.substituteFree SetSort.set 881 certificateSequence
          (certificateBody sequence (x#881)
            (x#882) (x#883)) =
        certificateBody sequence certificateSequence
          (x#882) (x#883) := by
    simp [certificateBody, Formula.substituteFree,
      Term.substituteFree, set_variable,
      CertifiedProof.proof_code_component_bound,
      hProofCodeSubstitute, hBody1]
  have hCertificateExists1 :
      Formula.substituteFree SetSort.set 881 certificateSequence
          (∃ₘ[SetSort.set, 883],
            certificateBody sequence (x#881)
              (x#882) (x#883)) =
        (∃ₘ[SetSort.set, 883],
          certificateBody sequence certificateSequence
            (x#882) (x#883)) :=
    fs_zfc_substitute_free_exists_closed
      881 883 certificateSequence
      (certificateBody sequence (x#881)
        (x#882) (x#883))
      (certificateBody sequence certificateSequence
        (x#882) (x#883))
      (by native_decide) hCertificateSequence.2
      (hCertificateSequenceFresh 883) hCertificateBody1
  have hFormulaBody1 :
      Formula.substituteFree SetSort.set 881 certificateSequence
          (formulaBody sequence (x#881) (x#882)) =
        formulaBody sequence certificateSequence (x#882) := by
    have hGuard :
        Formula.substituteFree SetSort.set 881 certificateSequence
            (CertifiedProof.proof_code_component_bound
              proofCode (x#882)) =
          CertifiedProof.proof_code_component_bound
            proofCode (x#882) := by
      simp [Formula.substituteFree, Term.substituteFree,
        set_variable,
        CertifiedProof.proof_code_component_bound,
        hProofCodeSubstitute]
    simp only [formulaBody, Formula.substituteFree] at hGuard ⊢
    have hRight := hCertificateExists1
    simp only [Formula.substituteFree] at hRight
    rw [hGuard, hRight]
  have hFormulaExists1 :
      Formula.substituteFree SetSort.set 881 certificateSequence
          (∃ₘ[SetSort.set, 882],
            formulaBody sequence (x#881) (x#882)) =
        (∃ₘ[SetSort.set, 882],
          formulaBody sequence certificateSequence (x#882)) :=
    fs_zfc_substitute_free_exists_closed
      881 882 certificateSequence
      (formulaBody sequence (x#881) (x#882))
      (formulaBody sequence certificateSequence (x#882))
      (by native_decide) hCertificateSequence.2
      (hCertificateSequenceFresh 882) hFormulaBody1
  have hCertificatesBody1 :
      Formula.substituteFree SetSort.set 881 certificateSequence
          (certificatesBody sequence (x#881)) =
        certificatesBody sequence certificateSequence := by
    have hGuard :
        Formula.substituteFree SetSort.set 881 certificateSequence
            (x#881 ∈ₘ seq₊_spaceₘ(ωₘ)) =
          (certificateSequence ∈ₘ seq₊_spaceₘ(ωₘ)) := by
      simp [Formula.substituteFree, Term.substituteFree,
        set_variable]
    simp only [certificatesBody, Formula.substituteFree] at hGuard ⊢
    have hRight := hFormulaExists1
    simp only [Formula.substituteFree] at hRight
    rw [hGuard, hRight]
  have hCertificatesInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 881 certificateSequence
          (certificatesBody sequence (x#881))) := by
    rw [hCertificatesBody1]
    exact FirstOrder.Derives.conjIntro
      hCertificateSequenceSpace hFormulaExists
  have hCertificatesExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 881],
          certificatesBody sequence (x#881)) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := certificateSequence) 881 hCertificatesInstance
  have hCertificateBody0 :
      Formula.substituteFree SetSort.set 880 sequence
          (certificateBody (x#880) (x#881)
            (x#882) (x#883)) =
        certificateBody sequence (x#881)
          (x#882) (x#883) := by
    simp [certificateBody, Formula.substituteFree,
      Term.substituteFree, set_variable,
      CertifiedProof.proof_code_component_bound,
      hProofCodeSubstitute, hBody0]
  have hCertificateExists0 :
      Formula.substituteFree SetSort.set 880 sequence
          (∃ₘ[SetSort.set, 883],
            certificateBody (x#880) (x#881)
              (x#882) (x#883)) =
        (∃ₘ[SetSort.set, 883],
          certificateBody sequence (x#881)
            (x#882) (x#883)) :=
    fs_zfc_substitute_free_exists_closed
      880 883 sequence
      (certificateBody (x#880) (x#881)
        (x#882) (x#883))
      (certificateBody sequence (x#881)
        (x#882) (x#883))
      (by native_decide) hSequence.2
      (hSequenceFresh 883) hCertificateBody0
  have hFormulaBody0 :
      Formula.substituteFree SetSort.set 880 sequence
          (formulaBody (x#880) (x#881) (x#882)) =
        formulaBody sequence (x#881) (x#882) := by
    have hGuard :
        Formula.substituteFree SetSort.set 880 sequence
            (CertifiedProof.proof_code_component_bound
              proofCode (x#882)) =
          CertifiedProof.proof_code_component_bound
            proofCode (x#882) := by
      simp [Formula.substituteFree, Term.substituteFree,
        set_variable,
        CertifiedProof.proof_code_component_bound,
        hProofCodeSubstitute]
    simp only [formulaBody, Formula.substituteFree] at hGuard ⊢
    have hRight := hCertificateExists0
    simp only [Formula.substituteFree] at hRight
    rw [hGuard, hRight]
  have hFormulaExists0 :
      Formula.substituteFree SetSort.set 880 sequence
          (∃ₘ[SetSort.set, 882],
            formulaBody (x#880) (x#881) (x#882)) =
        (∃ₘ[SetSort.set, 882],
          formulaBody sequence (x#881) (x#882)) :=
    fs_zfc_substitute_free_exists_closed
      880 882 sequence
      (formulaBody (x#880) (x#881) (x#882))
      (formulaBody sequence (x#881) (x#882))
      (by native_decide) hSequence.2
      (hSequenceFresh 882) hFormulaBody0
  have hCertificatesBody0 :
      Formula.substituteFree SetSort.set 880 sequence
          (certificatesBody (x#880) (x#881)) =
        certificatesBody sequence (x#881) := by
    have hGuard :
        Formula.substituteFree SetSort.set 880 sequence
            (x#881 ∈ₘ seq₊_spaceₘ(ωₘ)) =
          (x#881 ∈ₘ seq₊_spaceₘ(ωₘ)) := by
      simp [Formula.substituteFree, Term.substituteFree,
        set_variable]
    simp only [certificatesBody, Formula.substituteFree] at hGuard ⊢
    have hRight := hFormulaExists0
    simp only [Formula.substituteFree] at hRight
    rw [hGuard, hRight]
  have hCertificatesExists0 :
      Formula.substituteFree SetSort.set 880 sequence
          (∃ₘ[SetSort.set, 881],
            certificatesBody (x#880) (x#881)) =
        (∃ₘ[SetSort.set, 881],
          certificatesBody sequence (x#881)) :=
    fs_zfc_substitute_free_exists_closed
      880 881 sequence
      (certificatesBody (x#880) (x#881))
      (certificatesBody sequence (x#881))
      (by native_decide) hSequence.2
      (hSequenceFresh 881) hCertificatesBody0
  have hSequenceBody0 :
      Formula.substituteFree SetSort.set 880 sequence
          (sequenceBody (x#880)) =
        sequenceBody sequence := by
    have hGuard :
        Formula.substituteFree SetSort.set 880 sequence
            (x#880 ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) =
          (sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) := by
      simp [Formula.substituteFree, Term.substituteFree,
        set_variable]
    simp only [sequenceBody, Formula.substituteFree] at hGuard ⊢
    have hRight := hCertificatesExists0
    simp only [Formula.substituteFree] at hRight
    rw [hGuard, hRight]
  have hSequenceInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 880 sequence
          (sequenceBody (x#880))) := by
    rw [hSequenceBody0]
    exact FirstOrder.Derives.conjIntro
      hSequenceSpace hCertificatesExists
  have hSequenceExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 880],
          sequenceBody (x#880)) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := sequence) 880 hSequenceInstance
  rw [proof_condition_eq_witness]
  simpa [sequenceBody, certificatesBody, formulaBody,
    certificateBody, codeBody,
    ProofT.condition_base,
    ProofT.sequence_condition] using
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        hConclusionFormulaCode hProofCodeOmega)
      hSequenceExists

/-! ## 从任意有限 Hilbert 证明接入 checked internalization -/

/-- 一条以指定公式收尾的 Hilbert 证明给出其 Hilbert 化证明码的对象条件。 -/
theorem fs_zfc_support_raw_certified_code_condition_of_hilbert_proof
    {Thilbert : SetTheory}
    (enumeration : HilbertTheoryEnumeration Thilbert)
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (hTheoryCertificate :
      ∀ {certificate : Nat} {row : SetFormula},
        enumeration.certificate_verifier certificate row = true →
          Derives fs_zfc_support_raw_theory [] (
            verifier.condition
              (fs_zfc_formula_code_term row)
              (numₘ(certificate))))
    (hHilbertizeClosed :
      ∀ row, Thilbert row →
        Thilbert (Formula.hilbertize SetSort.set row))
    {initial : List SetFormula}
    {formula : SetFormula}
    (hProof :
      HilbertProof Thilbert
        (initial ++ [formula])) :
    ∃ certificates,
      Derives fs_zfc_support_raw_theory [] (
        proof_condition
          verifier
          (numₘ(certified_hilbert_proof_code_value
            certified_row_tokens
            ((initial ++ [formula]).map
              (Formula.hilbertize SetSort.set))
            certificates))
          (fs_zfc_formula_code_term
            (Formula.hilbertize SetSort.set formula))
          ProofT.condition_base) := by
  rcases fs_checked_trace_exists_of_hilbert_proof
      enumeration hHilbertizeClosed
      hProof with
    ⟨certificates, _, hTrace⟩
  refine ⟨certificates, ?_⟩
  exact fs_zfc_support_raw_certified_code_condition_of_checked_trace
    enumeration verifier hContract hTheoryCertificate
    (proof := (initial ++ [formula]).map
      (Formula.hilbertize SetSort.set))
    (initial := initial.map (Formula.hilbertize SetSort.set))
    (formula := Formula.hilbertize SetSort.set formula)
    hTrace (by simp [List.map_append])

/-- 每个 ZFC 支持理论可推导公式都有一个内部化的 checked 证明码。 -/
theorem fs_zfc_support_raw_certified_code_condition_of_derives
    {Thilbert : SetTheory}
    (enumeration : HilbertTheoryEnumeration Thilbert)
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (hTheoryCertificate :
      ∀ {certificate : Nat} {row : SetFormula},
        enumeration.certificate_verifier certificate row = true →
          Derives fs_zfc_support_raw_theory [] (
            verifier.condition
              (fs_zfc_formula_code_term row)
              (numₘ(certificate))))
    (hHilbertizeClosed :
      ∀ row, Thilbert row →
        Thilbert (Formula.hilbertize SetSort.set row))
    {formula : SetFormula}
    (hDerives :
      HilbertDerives Thilbert formula) :
    ∃ proofCode,
      Derives fs_zfc_support_raw_theory [] (
        proof_condition
          verifier
          (numₘ(proofCode))
          (fs_zfc_formula_code_term
            (Formula.hilbertize SetSort.set formula))
          ProofT.condition_base) := by
  rcases HilbertProof.exists_finite hDerives with
    ⟨initial, hProof⟩
  rcases fs_zfc_support_raw_certified_code_condition_of_hilbert_proof
      enumeration verifier hContract hTheoryCertificate
      hHilbertizeClosed
      hProof with
    ⟨certificates, hCode⟩
  refine ⟨certified_hilbert_proof_code_value
      certified_row_tokens
      ((initial ++ [formula]).map
        (Formula.hilbertize SetSort.set))
      certificates, ?_⟩
  simpa using hCode

/--
真实 quotation 与正向 checked internalization 使用的总化公式码完全对齐。

`quote?` 本身先做一次 Hilbert 化，因此这里只使用 Hilbert 化幂等性，不附加
公式已经处于核心片段之类的额外前提。
-/
theorem fs_zfc_formula_code_term_hilbertize_eq_of_quote
    {formula : SetFormula} {code : SetTerm}
    (hQuote :
      GodelQuotation.Numbered.quote? formula = some code) :
    fs_zfc_formula_code_term
        (Formula.hilbertize SetSort.set formula) =
      code := by
  have hHilbertQuote :
      GodelQuotation.Numbered.quote?
          (Formula.hilbertize SetSort.set formula) =
        some code := by
    change
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          [] 0
          (Formula.hilbertize SetSort.set
            (Formula.hilbertize SetSort.set formula)) =
        some code
    change
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          [] 0
          (Formula.hilbertize SetSort.set formula) =
        some code at hQuote
    rw [Formula.hilbertize_idempotent]
    exact hQuote
  simp [fs_zfc_formula_code_term, hHilbertQuote]

/--
每个可推导公式都在其真实 quotation 项上拥有一个对象层 checked 证明码。

该接口消除了调用方反复处理
`fs_zfc_formula_code_term (hilbertize formula)` 的实现细节。
-/
theorem fs_zfc_support_raw_certified_code_condition_of_derives_at_quote
    {Thilbert : SetTheory}
    (enumeration : HilbertTheoryEnumeration Thilbert)
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (hTheoryCertificate :
      ∀ {certificate : Nat} {row : SetFormula},
        enumeration.certificate_verifier certificate row = true →
          Derives fs_zfc_support_raw_theory [] (
            verifier.condition
              (fs_zfc_formula_code_term row)
              (numₘ(certificate))))
    (hHilbertizeClosed :
      ∀ row, Thilbert row →
        Thilbert (Formula.hilbertize SetSort.set row))
    {formula : SetFormula} {code : SetTerm}
    (hQuote :
      GodelQuotation.Numbered.quote? formula = some code)
    (hDerives :
      HilbertDerives Thilbert formula) :
    ∃ proofCode,
      Derives fs_zfc_support_raw_theory [] (
        proof_condition
          verifier
          (numₘ(proofCode))
          code
          ProofT.condition_base) := by
  rcases fs_zfc_support_raw_certified_code_condition_of_derives
      enumeration verifier hContract hTheoryCertificate
      hHilbertizeClosed
      hDerives with
    ⟨proofCode, hCode⟩
  refine ⟨proofCode, ?_⟩
  simpa [fs_zfc_formula_code_term_hilbertize_eq_of_quote hQuote] using
    hCode

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
