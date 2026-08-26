import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta0Encoding

/-!
# `ProofT` 编码条件的 `Sigma1` 支撑

本模块只把对象 verifier 的 `Sigma1` 条件沿 checked replay 的有界骨架向上传播。
证明序列、有限数值轨迹、配对边界和末行条件仍复用 `Delta0Encoding` 的结果；
因此这里不会把有界回放误报为无界 `Delta0`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace Sigma1Encoding

open Nonlogical.BasicSetTheory
open GodelQuotation
open Rosser
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 逐行证书与序列合法性 -/

theorem theory_certificate_line_condition_with_id_sigma1
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (certificateCodeId : FreeVarId)
    (_hCertificateFresh :
      (SetSort.set, certificateCodeId) ∉
        Term.freeSupport (Sₘ(certificates ·ₘ index)))
    (hCondition :
      Formula.IsSigma1 set_levy_bound
        (verifier.condition
          (sequence ·ₘ index) (x#certificateCodeId))) :
    Formula.IsSigma1 set_levy_bound
      (CertifiedProof.theory_certificate_line_condition_with_id
        verifier sequence certificates index certificateCodeId) := by
  have hBody :
      Formula.IsSigma1 set_levy_bound
        ((x#certificateCodeId ∈ₘ
            Sₘ(certificates ·ₘ index)) ∧ₘ
          (((certificates ·ₘ index) ≐ₘ
              CertifiedProof.theory_certificate_code
                (x#certificateCodeId)) ∧ₘ
            verifier.condition
              (sequence ·ₘ index) (x#certificateCodeId))) := by
    exact Formula.IsSigma1.conj
      (Formula.IsSigma1.delta0
        (Formula.IsDelta0.rel
          RelationSymbol.membership
          [x#certificateCodeId,
            Sₘ(certificates ·ₘ index)]))
      (Formula.IsSigma1.conj
        (Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            (certificates ·ₘ index)
            (CertifiedProof.theory_certificate_code
              (x#certificateCodeId))))
        hCondition)
  simpa [CertifiedProof.theory_certificate_line_condition_with_id,
    CertifiedProof.certificate_payload_bound] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set certificateCodeId hBody

theorem line_condition_with_ids_sigma1_of_parts
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId)
    (hCertificateFresh :
      (SetSort.set, certificateCodeId) ∉
        Term.freeSupport (Sₘ(certificates ·ₘ index)))
    (hLogical :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ index) (x#certificateCodeId)
          logicalCertificateSequenceId logicalFormulaTraceId
          logicalLastIndexId logicalLineIndexId
          logicalCodeTraceId logicalCodeIndexId))
    (hTheory :
      Formula.IsSigma1 set_levy_bound
        (verifier.condition
          (sequence ·ₘ index) (x#certificateCodeId)))
    (hImplicationFresh :
      (SetSort.set, implicationIndex) ∉
        Term.freeSupport index)
    (hPremiseFresh :
      (SetSort.set, premiseIndex) ∉
        Term.freeSupport (x#implicationIndex)) :
    Formula.IsSigma1 set_levy_bound
      (CertifiedProof.line_condition_with_ids
        verifier sequence certificates index
        certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId
        logicalLastIndexId logicalLineIndexId
        logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex) := by
  have hLogicalBody :
      Formula.IsSigma1 set_levy_bound
        ((x#certificateCodeId ∈ₘ
            Sₘ(certificates ·ₘ index)) ∧ₘ
          (((certificates ·ₘ index) ≐ₘ
              CertifiedProof.logical_certificate_code
                (x#certificateCodeId)) ∧ₘ
            CertifiedProof.logical_certificate_condition_with_ids
              (sequence ·ₘ index) (x#certificateCodeId)
              logicalCertificateSequenceId logicalFormulaTraceId
              logicalLastIndexId logicalLineIndexId
              logicalCodeTraceId logicalCodeIndexId)) := by
    exact Formula.IsSigma1.conj
      (Formula.IsSigma1.delta0
        (Formula.IsDelta0.rel
          RelationSymbol.membership
          [x#certificateCodeId,
            Sₘ(certificates ·ₘ index)]))
      (Formula.IsSigma1.conj
        (Formula.IsSigma1.delta0
          (Formula.IsDelta0.equal
            (certificates ·ₘ index)
            (CertifiedProof.logical_certificate_code
              (x#certificateCodeId))))
        hLogical)
  have hLogicalLine :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, certificateCodeId],
          (x#certificateCodeId ∈ₘ
              Sₘ(certificates ·ₘ index)) ∧ₘ
            (((certificates ·ₘ index) ≐ₘ
                CertifiedProof.logical_certificate_code
                  (x#certificateCodeId)) ∧ₘ
              CertifiedProof.logical_certificate_condition_with_ids
                (sequence ·ₘ index) (x#certificateCodeId)
                logicalCertificateSequenceId logicalFormulaTraceId
                logicalLastIndexId logicalLineIndexId
                logicalCodeTraceId logicalCodeIndexId)) := by
    simpa using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set certificateCodeId
        (Formula.IsSigma1.conj
          (Formula.IsSigma1.delta0
            (Formula.IsDelta0.rel
              RelationSymbol.membership
              [x#certificateCodeId,
                Sₘ(certificates ·ₘ index)]))
          (Formula.IsSigma1.conj
            (Formula.IsSigma1.delta0
              (Formula.IsDelta0.equal
                (certificates ·ₘ index)
                (CertifiedProof.logical_certificate_code
                  (x#certificateCodeId))))
            hLogical))
  have hTheoryLine :=
    theory_certificate_line_condition_with_id_sigma1
      verifier sequence certificates index certificateCodeId
      hCertificateFresh hTheory
  have hModusPonensLine :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.modus_ponens_line_condition_with_ids
          sequence certificates index implicationIndex premiseIndex) :=
    (Delta0Encoding.modus_ponens_line_condition_with_ids_delta0
      sequence certificates index implicationIndex premiseIndex
      hImplicationFresh hPremiseFresh).to_sigma1
  simpa [CertifiedProof.line_condition_with_ids] using
    Formula.IsSigma1.disj hLogicalLine
      (Formula.IsSigma1.disj hTheoryLine hModusPonensLine)

theorem sequence_condition_with_ids_sigma1_of_parts
    (verifier : ObjectCertificateVerifier)
    (sequence certificates : SetTerm)
    (legalityIndexId certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId)
    (hLegalityFresh :
      (SetSort.set, legalityIndexId) ∉
        Term.freeSupport (domₘ(sequence)))
    (hFormulaCondition :
      ∀ index,
        Formula.IsSigma1 set_levy_bound
          (verifier.formula_condition
            (sequence ·ₘ index)))
    (hLineCondition :
      ∀ index,
        Formula.IsSigma1 set_levy_bound
          (CertifiedProof.line_condition_with_ids
            verifier sequence certificates index
            certificateCodeId
            logicalCertificateSequenceId logicalFormulaTraceId
            logicalLastIndexId logicalLineIndexId
            logicalCodeTraceId logicalCodeIndexId
            implicationIndex premiseIndex)) :
    Formula.IsSigma1 set_levy_bound
      (CertifiedProof.sequence_condition_with_ids
        verifier sequence certificates
        legalityIndexId certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId
        logicalLastIndexId logicalLineIndexId
        logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex) := by
  let legalityBody : SetFormula :=
    (verifier.formula_condition
        (sequence ·ₘ x#legalityIndexId)) ∧ₘ
      CertifiedProof.line_condition_with_ids
        verifier sequence certificates (x#legalityIndexId)
        certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId
        logicalLastIndexId logicalLineIndexId
        logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex
  have hLegalityBody :
      Formula.IsSigma1 set_levy_bound legalityBody := by
    simpa [legalityBody] using
      Formula.IsSigma1.conj
        (hFormulaCondition (x#legalityIndexId))
        (hLineCondition (x#legalityIndexId))
  let legalityCondition : SetFormula :=
    ∀ₘ[SetSort.set, legalityIndexId],
      (x#legalityIndexId ∈ₘ domₘ(sequence)) ⟶ₘ legalityBody
  have hLegalityCondition :
      Formula.IsSigma1 set_levy_bound legalityCondition := by
    simpa [legalityCondition] using
      Formula.IsSigma1.bounded_forall_closeFreeAt
        legalityIndexId (domₘ(sequence))
        hLegalityFresh hLegalityBody
  have hPrefix :
      Formula.IsSigma1 set_levy_bound
        (((((sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
            (certificates ∈ₘ seq₊_spaceₘ(ωₘ))) ∧ₘ
          (domₘ(sequence) ≐ₘ domₘ(certificates))) ∧ₘ
          (numₘ(0) ∈ₘ domₘ(sequence)))) :=
    (Formula.IsDelta0.conj
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.rel
            RelationSymbol.membership
            [sequence, seq₊_spaceₘ(FormulaCodeₘ)])
          (Formula.IsDelta0.rel
            RelationSymbol.membership
            [certificates, seq₊_spaceₘ(ωₘ)]))
        (Formula.IsDelta0.equal
          (domₘ(sequence)) (domₘ(certificates))))
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [numₘ(0), domₘ(sequence)])).to_sigma1
  simpa [CertifiedProof.sequence_condition_with_ids,
    legalityCondition, legalityBody] using
    Formula.IsSigma1.conj hPrefix hLegalityCondition

/-! ## 完整证明码与固定编号 Rosser 条件 -/

theorem code_condition_with_ids_sigma1_of_parts
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (sequenceId certificatesId formulaCodeId certificateCodeId
      legalityIndexId certificatePayloadId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex
      proofTraceId proofIndexId proofRowCodeId proofRowTraceId proofRowIndexId
      certificateTraceId certificateIndexId : FreeVarId)
    (_hSequenceFresh :
      (SetSort.set, sequenceId) ∉
        Term.freeSupport (seq₊_spaceₘ(FormulaCodeₘ)))
    (_hCertificatesFresh :
      (SetSort.set, certificatesId) ∉
        Term.freeSupport (seq₊_spaceₘ(ωₘ)))
    (_hFormulaCodeFresh :
      (SetSort.set, formulaCodeId) ∉
        Term.freeSupport (Sₘ(proofCode)))
    (_hCertificateCodeFresh :
      (SetSort.set, certificateCodeId) ∉
        Term.freeSupport (Sₘ(proofCode)))
    (hSequenceCondition :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.sequence_condition_with_ids
          verifier (x#sequenceId) (x#certificatesId)
          legalityIndexId certificatePayloadId
          logicalCertificateSequenceId logicalFormulaTraceId
          logicalLastIndexId logicalLineIndexId
          logicalCodeTraceId logicalCodeIndexId
          implicationIndex premiseIndex))
    (hProofSequenceCondition :
      Formula.IsDelta0 set_levy_bound
        (proof_sequence_code_condition_with_ids
          (x#sequenceId) (x#formulaCodeId)
          proofTraceId proofIndexId proofRowCodeId
          proofRowTraceId proofRowIndexId))
    (hCertificateSequenceCondition :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          (x#certificatesId) (x#certificateCodeId)
          certificateTraceId certificateIndexId))
    (hFormulaBound :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.proof_code_component_bound
          proofCode (x#formulaCodeId)))
    (hCertificateBound :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.proof_code_component_bound
          proofCode (x#certificateCodeId)))
    (hProofCodeEquality :
      Formula.IsDelta0 set_levy_bound
        (proofCode ≐ₘ
          godel_pairₘ(⟨x#formulaCodeId, x#certificateCodeId⟩ₘ)))
    (hTerminal :
      Formula.IsDelta0 set_levy_bound
        (proof_sequence_terminal_condition
          (x#sequenceId) conclusion)) :
    Formula.IsSigma1 set_levy_bound
      (CertifiedProof.code_condition_with_ids
        verifier proofCode conclusion
        sequenceId certificatesId formulaCodeId certificateCodeId
        legalityIndexId certificatePayloadId
        logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
        logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex
        proofTraceId proofIndexId proofRowCodeId proofRowTraceId proofRowIndexId
        certificateTraceId certificateIndexId) := by
  let leftFormula : SetFormula :=
    (CertifiedProof.sequence_condition_with_ids
      verifier (x#sequenceId) (x#certificatesId)
      legalityIndexId certificatePayloadId
      logicalCertificateSequenceId logicalFormulaTraceId
      logicalLastIndexId logicalLineIndexId
      logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex) ∧ₘ
      proof_sequence_code_condition_with_ids
        (x#sequenceId) (x#formulaCodeId)
        proofTraceId proofIndexId proofRowCodeId
        proofRowTraceId proofRowIndexId
  let core : SetFormula :=
    (leftFormula ∧ₘ
      nat_sequence_code_condition_with_ids
        (x#certificatesId) (x#certificateCodeId)
        certificateTraceId certificateIndexId) ∧ₘ
       ((CertifiedProof.proof_code_component_bound
           proofCode (x#formulaCodeId) ∧ₘ
         CertifiedProof.proof_code_component_bound
           proofCode (x#certificateCodeId)) ∧ₘ
        ((proofCode ≐ₘ
            godel_pairₘ(⟨x#formulaCodeId, x#certificateCodeId⟩ₘ)) ∧ₘ
           proof_sequence_terminal_condition
             (x#sequenceId) conclusion))
  have hCore :
      Formula.IsSigma1 set_levy_bound core := by
    have hLeft :
        Formula.IsSigma1 set_levy_bound leftFormula := by
      simpa [leftFormula] using
        Formula.IsSigma1.conj
          hSequenceCondition hProofSequenceCondition.to_sigma1
    have hCertificatePart :
        Formula.IsSigma1 set_levy_bound
          (leftFormula ∧ₘ
            nat_sequence_code_condition_with_ids
              (x#certificatesId) (x#certificateCodeId)
              certificateTraceId certificateIndexId) :=
      Formula.IsSigma1.conj
        hLeft hCertificateSequenceCondition.to_sigma1
    have hBounds :
        Formula.IsSigma1 set_levy_bound
          (CertifiedProof.proof_code_component_bound
              proofCode (x#formulaCodeId) ∧ₘ
            CertifiedProof.proof_code_component_bound
              proofCode (x#certificateCodeId)) :=
      Formula.IsSigma1.conj
        hFormulaBound.to_sigma1 hCertificateBound.to_sigma1
    have hTail :
        Formula.IsSigma1 set_levy_bound
          ((proofCode ≐ₘ
              godel_pairₘ(⟨x#formulaCodeId, x#certificateCodeId⟩ₘ)) ∧ₘ
            proof_sequence_terminal_condition
              (x#sequenceId) conclusion) :=
      Formula.IsSigma1.conj
        hProofCodeEquality.to_sigma1 hTerminal.to_sigma1
    simpa [core, leftFormula] using
      Formula.IsSigma1.conj hCertificatePart
        (Formula.IsSigma1.conj hBounds hTail)
  let certificateBody : SetFormula :=
    (CertifiedProof.proof_code_component_bound
        proofCode (x#certificateCodeId)) ∧ₘ core
  have hCertificateBody :
      Formula.IsSigma1 set_levy_bound certificateBody := by
    simpa [certificateBody] using
      Formula.IsSigma1.conj
        hCertificateBound.to_sigma1 hCore
  have hCertificate :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, certificateCodeId], certificateBody) := by
    simpa [certificateBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set certificateCodeId hCertificateBody
  let formulaBody : SetFormula :=
    (CertifiedProof.proof_code_component_bound
        proofCode (x#formulaCodeId)) ∧ₘ
      (∃ₘ[SetSort.set, certificateCodeId],
        (CertifiedProof.proof_code_component_bound
            proofCode (x#certificateCodeId)) ∧ₘ core)
  have hFormulaBody :
      Formula.IsSigma1 set_levy_bound formulaBody := by
    simpa [formulaBody] using
      Formula.IsSigma1.conj hFormulaBound.to_sigma1
        (Formula.IsSigma1.exists_closeFreeAt
          SetSort.set certificateCodeId
          (Formula.IsSigma1.conj
            hCertificateBound.to_sigma1 hCore))
  have hFormula :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, formulaCodeId], formulaBody) := by
    simpa [formulaBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set formulaCodeId hFormulaBody
  let certificatesBody : SetFormula :=
    (x#certificatesId ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
      (∃ₘ[SetSort.set, formulaCodeId],
        (CertifiedProof.proof_code_component_bound
            proofCode (x#formulaCodeId)) ∧ₘ
          (∃ₘ[SetSort.set, certificateCodeId],
            (CertifiedProof.proof_code_component_bound
                proofCode (x#certificateCodeId)) ∧ₘ core))
  have hCertificatesBody :
      Formula.IsSigma1 set_levy_bound certificatesBody :=
    Formula.IsSigma1.conj
      (Formula.IsSigma1.delta0
        (Formula.IsDelta0.rel
          RelationSymbol.membership
          [x#certificatesId, seq₊_spaceₘ(ωₘ)]))
      hFormula
  have hCertificates :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, certificatesId], certificatesBody) := by
    simpa [certificatesBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set certificatesId hCertificatesBody
  let sequenceBody : SetFormula :=
    (x#sequenceId ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
      (∃ₘ[SetSort.set, certificatesId],
        (x#certificatesId ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
          (∃ₘ[SetSort.set, formulaCodeId],
            (CertifiedProof.proof_code_component_bound
                proofCode (x#formulaCodeId)) ∧ₘ
              (∃ₘ[SetSort.set, certificateCodeId],
                (CertifiedProof.proof_code_component_bound
                    proofCode (x#certificateCodeId)) ∧ₘ core)))
  have hSequenceBody :
      Formula.IsSigma1 set_levy_bound sequenceBody :=
    Formula.IsSigma1.conj
      (Formula.IsSigma1.delta0
        (Formula.IsDelta0.rel
          RelationSymbol.membership
          [x#sequenceId, seq₊_spaceₘ(FormulaCodeₘ)]))
      hCertificates
  have hSequence :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, sequenceId], sequenceBody) := by
    simpa [sequenceBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set sequenceId hSequenceBody
  have hPrefix :
      Formula.IsSigma1 set_levy_bound
        ((formula_codeₘ(conclusion) ∧ₘ proofCode ∈ₘ ωₘ)) :=
    (Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.isFormulaCode [conclusion])
      (Formula.IsDelta0.rel
        RelationSymbol.membership [proofCode, ωₘ])).to_sigma1
  simpa [CertifiedProof.code_condition_with_ids, core,
    sequenceBody, certificatesBody, formulaBody, certificateBody] using
    Formula.IsSigma1.conj hPrefix hSequence

theorem proof_condition_sigma1_of_parts
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (base : FreeVarId)
    (hSequenceFresh :
      (SetSort.set, base) ∉
        Term.freeSupport (seq₊_spaceₘ(FormulaCodeₘ)))
    (hCertificatesFresh :
      (SetSort.set, base + 1) ∉
        Term.freeSupport (seq₊_spaceₘ(ωₘ)))
    (hFormulaCodeFresh :
      (SetSort.set, base + 2) ∉
        Term.freeSupport (Sₘ(proofCode)))
    (hCertificateCodeFresh :
      (SetSort.set, base + 3) ∉
        Term.freeSupport (Sₘ(proofCode)))
    (hSequenceCondition :
      Formula.IsSigma1 set_levy_bound
        (CertifiedProof.sequence_condition_with_ids
          verifier (x#base) (x#(base + 1))
          (base + 20) (base + 23)
          (base + 11) (base + 12) (base + 13)
          (base + 14) (base + 15) (base + 16)
          (base + 21) (base + 22)))
    (hProofSequenceCondition :
      Formula.IsDelta0 set_levy_bound
        (proof_sequence_code_condition_with_ids
          (x#base) (x#(base + 2))
          (base + 4) (base + 5) (base + 6)
          (base + 7) (base + 8)))
    (hCertificateSequenceCondition :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          (x#(base + 1)) (x#(base + 3))
          (base + 9) (base + 10)))
    (hFormulaBound :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.proof_code_component_bound
          proofCode (x#(base + 2))))
    (hCertificateBound :
      Formula.IsDelta0 set_levy_bound
        (CertifiedProof.proof_code_component_bound
          proofCode (x#(base + 3))))
    (hProofCodeEquality :
      Formula.IsDelta0 set_levy_bound
        (proofCode ≐ₘ
          godel_pairₘ(⟨x#(base + 2), x#(base + 3)⟩ₘ)))
    (hTerminal :
      Formula.IsDelta0 set_levy_bound
        (proof_sequence_terminal_condition
          (x#base) conclusion)) :
    Formula.IsSigma1 set_levy_bound
      (Rosser.proof_condition verifier proofCode conclusion base) := by
  simpa [Rosser.proof_condition] using
    code_condition_with_ids_sigma1_of_parts
      verifier proofCode conclusion
      base (base + 1) (base + 2) (base + 3)
      (base + 20) (base + 23)
      (base + 11) (base + 12) (base + 13)
      (base + 14) (base + 15) (base + 16)
      (base + 21) (base + 22)
      (base + 4) (base + 5) (base + 6)
      (base + 7) (base + 8)
      (base + 9) (base + 10)
      hSequenceFresh hCertificatesFresh
      hFormulaCodeFresh hCertificateCodeFresh
      hSequenceCondition hProofSequenceCondition
      hCertificateSequenceCondition hFormulaBound
      hCertificateBound hProofCodeEquality hTerminal

end Sigma1Encoding
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
