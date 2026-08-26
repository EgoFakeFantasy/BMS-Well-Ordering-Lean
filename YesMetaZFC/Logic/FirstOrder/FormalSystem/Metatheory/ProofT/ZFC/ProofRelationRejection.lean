import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedCompleteness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ProofCodeRejection

/-!
# ZFC checked 二元证明码关系的对象层拒绝

本模块只完成终局失败适配：宿主 terminal-aware checked 二元关系不成立时，对象理论否定相同
numeral 与真实 quotation 上的 `certified_code_condition`。成功 replay 的内容反演
只调用既有 alignment；失败 replay 只调用既有直接拒绝接口。
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
terminal-aware checked 二元关系的补集在真实 quotation 上逐点内部化为对象证明码
条件的否定。
-/
theorem ProofT.ZFC.code_neg_of_terminal_unchecked
    (number : Nat)
    {formula : SetFormula}
    {code : SetTerm}
    (hFormula : Formula.Admissible formula)
    (hQuote :
      GodelQuotation.Numbered.quote? formula = some code)
    (hNot :
      ¬ fs_terminal_checked_hilbertized_proof_code_for
        ProofCode.fs_zfc_support_enumeration
        number formula) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ proof_condition
        fs_zfc_object_certificate_verifier
        (numₘ(number)) code
        ProofT.condition_base) := by
  have hCode :
      GodelQuotation.Numbered.CodeBoundary code :=
    GodelQuotation.Numbered.quote?_code_boundary hQuote
  cases hReplay :
      fs_replay_code
        ProofCode.fs_zfc_support_enumeration number with
  | none =>
      exact
        ProofT.ZFC.code_neg_of_replay_failure
          number code hCode
          (fs_replay_code_failure_of_none
            ProofCode.fs_zfc_support_enumeration number hReplay)
  | some state =>
      have hTargetLastNot :
          state.proof.getLast? ≠
            some (Formula.hilbertize SetSort.set formula) := by
        intro hLast
        exact hNot ⟨state, hReplay, hLast⟩
      let decoded :=
        fs_certified_proof_code_decode number
      cases hCertificates : decoded.2 with
      | none =>
          simp [fs_replay_code, decoded, hCertificates] at hReplay
      | some certificates =>
          have hRawReplay :
              fs_replay_raw_rows
                  ProofCode.fs_zfc_support_enumeration number
                  (fs_replay_nil
                    ProofCode.fs_zfc_support_enumeration number)
                  decoded.1 certificates =
                some state := by
            simpa [fs_replay_code, decoded, hCertificates] using hReplay
          rcases
              fs_replay_raw_rows_nil_some_alignment
                ProofCode.fs_zfc_support_enumeration number state
                decoded.1 certificates hRawReplay with
            ⟨decodedRows, hDecode, hStateProof, _⟩
          rcases
              GodelQuotation.Numbered.quote_tokens?_exists hFormula with
            ⟨targetTokens, hTargetTokens⟩
          have hTargetDecode :
              fs_formula_row_decode number targetTokens =
                some {
                  formula := Formula.hilbertize SetSort.set formula
                  h_admissible :=
                    Formula.Admissible.hilbertize hFormula
                } :=
            fs_formula_row_decode_quote
              number hFormula hTargetTokens
          have hMismatch :
              ∀ index (hIndex : index < decoded.1.length),
                decoded.1.length = index + 1 →
                  targetTokens ≠ decoded.1[index] := by
            intro index hIndex hIndexLast hEqual
            have hRow :
                decoded.1[index]? = some decoded.1[index] :=
              List.getElem?_eq_getElem hIndex
            rcases fs_mapM_getElem?_of_some
                (by
                  simpa [fs_formula_rows_decode_payload] using hDecode)
                hRow with
              ⟨decodedRow, hDecodedRow, hRowDecode⟩
            have hDecodedEq :
                decodedRow.formula =
                  Formula.hilbertize SetSort.set formula := by
              rw [← hEqual] at hRowDecode
              exact congrArg FSDecodedFormula.formula <|
                Option.some.inj <| hRowDecode.symm.trans hTargetDecode
            have hDecodedLength :
                decodedRows.length = decoded.1.length :=
              GodelQuotation.fs_option_mapM_length <| by
                simpa [fs_formula_rows_decode_payload] using hDecode
            have hDecodedLastIndex :
                decodedRows.length = index + 1 :=
              hDecodedLength.trans hIndexLast
            have hDecodedLast :
                decodedRows.getLast? = some decodedRow := by
              rw [List.getLast?_eq_getElem?]
              have hDecodedLastEq :
                  decodedRows.length - 1 = index := by
                omega
              rw [hDecodedLastEq]
              exact hDecodedRow
            rcases List.getLast?_eq_some_iff.mp hDecodedLast with
              ⟨initialRows, hDecodedSplit⟩
            apply hTargetLastNot
            rw [hStateProof, hDecodedSplit]
            simp [hDecodedEq]
          apply
            ProofT.code_neg_of_witness
              ProofT.ZFC.certificate_core.toFiniteCore
              fs_zfc_object_certificate_verifier
              number code ProofT.condition_base hCode
          have hWitnessAdmissible :
              Formula.Admissible
                (ProofT.ZFC.witness number code) :=
            ProofT.ZFC.witness_admissible
              number code hCode.1
          apply FirstOrder.Derives.impIntro
            (hAntecedentCheck :=
              Formula.check_admissible_complete hWitnessAdmissible)
          let Γ : Context signature :=
            [ProofT.ZFC.witness number code]
          have hWitness :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                ProofT.ZFC.witness number code :=
            FirstOrder.Derives.assumption (by simp [Γ])
          have hTerminal :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                proof_sequence_terminal_condition
                  (ProofT.ZFC.proof_sequence number) code :=
            FirstOrder.Derives.conjElimRight <|
              ProofT.ZFC.content_of_witness
                number code hCode hWitness
          have hCodeToTokens :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                code ≐ₘ standard_token_sequence targetTokens :=
            FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Γ) (by simp) <|
                fs_zfc_support_raw_derives_of_godel_quotation
                  (GodelQuotation.quote?_eq_standard_token_sequence
                    hTargetTokens hQuote)
          have hTerminalTokens :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                proof_sequence_terminal_condition
                  (ProofT.ZFC.proof_sequence number)
                  (standard_token_sequence targetTokens) :=
            ProofT.terminal_of_conclusion_eq
              (ProofT.ZFC.proof_sequence number)
              code (standard_token_sequence targetTokens)
              hCode.1
              (standard_token_sequence_admissible targetTokens)
              (ProofT.ZFC.proof_sequence_boundary number).2
              hCodeToTokens hTerminal
          simpa [ProofT.ZFC.proof_sequence, decoded] using
            ProofT.rows_terminal_falsum
              ProofT.ZFC.certificate_core.toFiniteCore
              ProofT.ZFC.object_replay
              decoded.1 targetTokens hMismatch hTerminalTokens

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
