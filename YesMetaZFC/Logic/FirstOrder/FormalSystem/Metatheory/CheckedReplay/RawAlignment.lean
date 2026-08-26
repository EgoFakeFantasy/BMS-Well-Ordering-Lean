import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay

/-!
# 原始行 checked replay 的前缀对齐

本模块只描述宿主层可计算 replay 的结构：单行成功严格追加一个公式和一个证书；
多行成功严格对应逐行解码所得的公式列表。对象理论拒绝证明可据此读取失败位置
之前的已验证前缀，而不重新执行或假定任何语义反演。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace Rosser

open Nonlogical.BasicSetTheory
open ProofCode

set_option autoImplicit false

/-- 证书解码成功时，输入自然数必为该证书的规范值。 -/
theorem fs_certificate_code_value_eq_of_decode
    {raw : Nat}
    {certificate : HilbertLineCertificateCode}
    (hDecode :
      HilbertLineCertificateCode.decode raw =
        some certificate) :
    raw = certificate.value := by
  cases certificate with
  | logical payload =>
      by_cases hTag :
          (godel_unpair_value raw).1 = 0
      · simp [HilbertLineCertificateCode.decode, hTag] at hDecode
        have hPayload :
            (godel_unpair_value raw).2 = payload := by
          simpa using hDecode
        rw [← godel_unpair_value_spec raw]
        simp [HilbertLineCertificateCode.value, hTag, hPayload]
      · simp [HilbertLineCertificateCode.decode, hTag] at hDecode
        by_cases hTag1 :
            (godel_unpair_value raw).1 = 1
        · simp [hTag1] at hDecode
        · by_cases hTag2 :
              (godel_unpair_value raw).1 = 2
          · simp [hTag2]
              at hDecode
          · simp [hTag1, hTag2]
              at hDecode
  | theory payload =>
      by_cases hTag0 :
          (godel_unpair_value raw).1 = 0
      · simp [HilbertLineCertificateCode.decode, hTag0] at hDecode
      · by_cases hTag1 :
            (godel_unpair_value raw).1 = 1
        · simp [HilbertLineCertificateCode.decode, hTag1] at hDecode
          have hPayload :
              (godel_unpair_value raw).2 = payload := by
            simpa using hDecode
          rw [← godel_unpair_value_spec raw]
          simp [HilbertLineCertificateCode.value, hTag1,
            hPayload]
        · simp [HilbertLineCertificateCode.decode, hTag0, hTag1] at hDecode
  | modusPonens implicationIndex premiseIndex =>
      by_cases hTag0 :
          (godel_unpair_value raw).1 = 0
      · simp [HilbertLineCertificateCode.decode, hTag0] at hDecode
      · by_cases hTag1 :
            (godel_unpair_value raw).1 = 1
        · simp [HilbertLineCertificateCode.decode, hTag1] at hDecode
        · by_cases hTag2 :
              (godel_unpair_value raw).1 = 2
          · simp [HilbertLineCertificateCode.decode, hTag2]
              at hDecode
            have hInnerCode :
                (godel_unpair_value raw).2 =
                  godel_pair_value implicationIndex premiseIndex := by
              rw [← godel_unpair_value_spec
                (godel_unpair_value raw).2]
              simp [hDecode.1, hDecode.2]
            rw [← godel_unpair_value_spec raw]
            simp only [HilbertLineCertificateCode.value]
            rw [hTag2, hInnerCode]
          · simp [HilbertLineCertificateCode.decode, hTag0, hTag1, hTag2]
              at hDecode

private theorem fs_certificate_values_of_mapM
    {tokens : List Nat}
    {certificates : List HilbertLineCertificateCode}
    (hDecode :
      tokens.mapM HilbertLineCertificateCode.decode =
        some certificates) :
    tokens = certificates.map HilbertLineCertificateCode.value := by
  induction tokens generalizing certificates with
  | nil =>
      cases certificates with
      | nil =>
          rfl
      | cons certificate certificates =>
          simp at hDecode
  | cons head tail ih =>
      cases certificates with
      | nil =>
          simp only [List.mapM_cons] at hDecode
          rcases Option.bind_eq_some_iff.mp hDecode with
            ⟨headResult, hHead, hRest⟩
          rcases Option.bind_eq_some_iff.mp hRest with
            ⟨tailResult, hTail, hPure⟩
          simp at hPure
      | cons certificate certificates =>
          simp only [List.mapM_cons] at hDecode
          rcases Option.bind_eq_some_iff.mp hDecode with
            ⟨headResult, hHead, hRest⟩
          rcases Option.bind_eq_some_iff.mp hRest with
            ⟨tailResult, hTail, hPure⟩
          simp at hPure
          rcases hPure with ⟨rfl, rfl⟩
          have hHeadValue :=
            fs_certificate_code_value_eq_of_decode hHead
          have hTailValues := ih hTail
          simp [hHeadValue, hTailValues]

/-- 证书序列解码成功时，恢复其输入自然数序列。 -/
theorem fs_certificate_sequence_decode_some_values
    {code : Nat}
    {certificates : List HilbertLineCertificateCode}
    (hDecode :
      fs_certificate_sequence_decode code =
        some certificates) :
    nat_sequence_decode code =
      certificates.map HilbertLineCertificateCode.value := by
  unfold fs_certificate_sequence_decode at hDecode
  exact fs_certificate_values_of_mapM hDecode

/-- 单行 replay 成功时，状态只追加当前公式与当前证书。 -/
theorem fs_replay_row_some_shape
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    {freeBase : Nat}
    (state next :
      FSReplayState enumeration freeBase)
    (formula : SetFormula)
    (certificate : HilbertLineCertificateCode)
    (hAdmissible : Formula.Admissible formula)
    (hReplay :
      fs_replay_row enumeration state formula
          certificate hAdmissible =
        some next) :
    next.proof = state.proof ++ [formula] ∧
      next.certificates =
        state.certificates ++ [certificate] := by
  cases certificate with
  | logical code =>
      by_cases hCheck :
          fs_logical_axiom_check
            freeBase code formula = true
      · simp [fs_replay_row, fs_replay_logical_row,
          hCheck] at hReplay
        subst next
        exact ⟨rfl, rfl⟩
      · simp [fs_replay_row, fs_replay_logical_row,
          hCheck] at hReplay
  | theory code =>
      by_cases hCheck :
          enumeration.certificate_verifier code formula = true
      · simp [fs_replay_row, fs_replay_theory_row,
          hCheck] at hReplay
        subst next
        exact ⟨rfl, rfl⟩
      · simp [fs_replay_row, fs_replay_theory_row,
          hCheck] at hReplay
  | modusPonens implicationIndex premiseIndex =>
      by_cases hCheck :
          fs_modus_ponens_check state.proof formula
              implicationIndex premiseIndex =
            true
      · simp [fs_replay_row, fs_replay_modus_ponens_row,
          hCheck] at hReplay
        subst next
        exact ⟨rfl, rfl⟩
      · simp [fs_replay_row, fs_replay_modus_ponens_row,
          hCheck] at hReplay

/--
原始 token 行 replay 成功时，存在精确的逐行解码列表；最终状态恰为初始状态
追加这些公式和输入证书。
-/
theorem fs_replay_raw_rows_some_alignment
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat)
    (state final :
      FSReplayState enumeration freeBase)
    (rows : List (List Nat))
    (certificates : List HilbertLineCertificateCode)
    (hReplay :
      fs_replay_raw_rows enumeration freeBase state rows certificates =
        some final) :
    ∃ decodedRows,
      fs_formula_rows_decode_payload freeBase rows =
          some decodedRows ∧
        final.proof =
          state.proof ++
            decodedRows.map FSDecodedFormula.formula ∧
        final.certificates =
          state.certificates ++ certificates := by
  induction rows generalizing state certificates with
  | nil =>
      cases certificates with
      | nil =>
          simp [fs_replay_raw_rows] at hReplay
          subst final
          exact
            ⟨([] : List FSDecodedFormula), rfl,
              by simp, by simp⟩
      | cons certificate certificates =>
          simp [fs_replay_raw_rows] at hReplay
  | cons row rows ih =>
      cases certificates with
      | nil =>
          simp [fs_replay_raw_rows] at hReplay
      | cons certificate certificates =>
          cases hDecode : fs_formula_row_decode freeBase row with
          | none =>
              simp [fs_replay_raw_rows, hDecode] at hReplay
          | some decoded =>
              cases hStep :
                  fs_replay_row enumeration state
                    decoded.formula certificate
                    decoded.h_admissible with
              | none =>
                  simp [fs_replay_raw_rows, hDecode,
                    hStep] at hReplay
              | some next =>
                  have hTail :
                      fs_replay_raw_rows enumeration freeBase next
                          rows certificates =
                        some final := by
                    simpa [fs_replay_raw_rows, hDecode,
                      hStep] using hReplay
                  rcases ih next certificates hTail with
                    ⟨tail, hTailDecode, hProof, hCertificates⟩
                  have hShape :=
                    fs_replay_row_some_shape
                      enumeration state next decoded.formula
                      certificate decoded.h_admissible hStep
                  refine ⟨decoded :: tail, ?_, ?_, ?_⟩
                  · change
              List.mapM (fs_formula_row_decode freeBase) rows =
                        some tail at hTailDecode
                    simp [fs_formula_rows_decode_payload,
                      hDecode, hTailDecode]
                  · calc
                      final.proof =
                          next.proof ++
                            tail.map FSDecodedFormula.formula :=
                        hProof
                      _ =
                          (state.proof ++ [decoded.formula]) ++
                            tail.map FSDecodedFormula.formula := by
                        rw [hShape.1]
                      _ =
                          state.proof ++
                            (decoded :: tail).map
                              FSDecodedFormula.formula := by
                        simp [List.append_assoc]
                  · calc
                      final.certificates =
                          next.certificates ++ certificates :=
                        hCertificates
                      _ =
                          (state.certificates ++ [certificate]) ++
                            certificates := by
                        rw [hShape.2]
                      _ =
                          state.certificates ++
                            (certificate :: certificates) := by
                        simp [List.append_assoc]

/-- 从空状态成功回放的 proof 与证书列表正好等于输入逐行数据。 -/
theorem fs_replay_raw_rows_nil_some_alignment
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat)
    (final :
      FSReplayState enumeration freeBase)
    (rows : List (List Nat))
    (certificates : List HilbertLineCertificateCode)
    (hReplay :
      fs_replay_raw_rows enumeration
          freeBase (fs_replay_nil enumeration freeBase)
          rows certificates =
        some final) :
    ∃ decodedRows,
      fs_formula_rows_decode_payload freeBase rows =
          some decodedRows ∧
        final.proof =
          decodedRows.map FSDecodedFormula.formula ∧
        final.certificates = certificates := by
  rcases fs_replay_raw_rows_some_alignment
      enumeration freeBase
      (fs_replay_nil enumeration freeBase)
      final rows certificates hReplay with
    ⟨decodedRows, hDecode, hProof, hCertificates⟩
  exact ⟨decodedRows, hDecode,
    by simpa [fs_replay_nil] using hProof,
    by simpa [fs_replay_nil] using hCertificates⟩

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
