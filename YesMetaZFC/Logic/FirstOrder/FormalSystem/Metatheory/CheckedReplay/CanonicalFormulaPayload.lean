import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.RosserFinite
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.SyntaxCoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoder

/-!
# checked replay 的规范公式 payload

本模块集中维护带 canonical re-quote 检查的公式 token-code 解码，以及固定长度
payload 的构造性反演。它独立于 Hilbert 回放状态机，可由证书构造和对象层
内部化共同复用。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace Rosser

open Nonlogical.BasicSetTheory
open ProofCode
open GodelQuotation

set_option autoImplicit false

/-- 公式 token 序列的自然数解码。 -/
def fs_formula_token_code_decode (code : Nat) :
    Option SetFormula :=
  let tokens := nat_sequence_decode code
  match GodelQuotation.fs_hilbert_tokens_decode tokens with
  | none =>
      none
  | some formula =>
      if GodelQuotation.Numbered.quote_tokens? formula =
          some tokens then
        some formula
      else
        none

/-- 规范 token-code 经过自然数序列解码后精确恢复 Hilbert 公式。 -/
theorem fs_formula_token_code_decode_quote
    {formula : SetFormula}
    {tokens : List Nat}
    (hFormula : Formula.Admissible formula)
    (hQuote : GodelQuotation.Numbered.quote_tokens? formula =
      some tokens) :
    fs_formula_token_code_decode
        (nat_sequence_code_value tokens) =
      some (Formula.hilbertize SetSort.set formula) := by
  unfold fs_formula_token_code_decode
  rw [nat_sequence_decode_code_value]
  have hDecode :
      GodelQuotation.fs_hilbert_tokens_decode tokens =
        some (Formula.hilbertize SetSort.set formula) :=
    GodelQuotation.fs_hilbert_tokens_decode_quote
      hFormula hQuote
  have hCanonical :
      GodelQuotation.Numbered.quote_tokens?
          (Formula.hilbertize SetSort.set formula) =
        some tokens := by
    unfold GodelQuotation.Numbered.quote_tokens?
      GodelQuotation.Numbered.quote_tokens_with? at hQuote ⊢
    change
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize SetSort.set
            (Formula.hilbertize SetSort.set formula)) =
        some tokens
    rw [Formula.hilbertize_idempotent]
    exact hQuote
  simp [hDecode, hCanonical]

/-- token-code 解码成功时，所得公式满足公共 admissibility 边界。 -/
theorem fs_formula_token_code_decode_admissible
    {code : Nat} {formula : SetFormula}
    (hDecode :
      fs_formula_token_code_decode code =
        some formula) :
    Formula.Admissible formula := by
  unfold fs_formula_token_code_decode at hDecode
  generalize hTokens :
      nat_sequence_decode code = tokens at hDecode
  cases hParsed :
      GodelQuotation.fs_hilbert_tokens_decode tokens with
  | none =>
      simp [hParsed] at hDecode
  | some parsed =>
      by_cases hCanonical :
          GodelQuotation.Numbered.quote_tokens? parsed =
            some tokens
      · simp [hParsed, hCanonical] at hDecode
        subst formula
        exact GodelQuotation.fs_hilbert_tokens_decode_admissible
          hParsed
      · simp [hParsed, hCanonical] at hDecode

/-- token-code 解码成功时，原 token 串正是结果公式的规范 quotation。 -/
theorem fs_formula_token_code_decode_quote_tokens
    {code : Nat} {formula : SetFormula}
    (hDecode :
      fs_formula_token_code_decode code =
        some formula) :
    GodelQuotation.Numbered.quote_tokens? formula =
      some (nat_sequence_decode code) := by
  unfold fs_formula_token_code_decode at hDecode
  generalize hTokens :
      nat_sequence_decode code = tokens at hDecode ⊢
  cases hParsed :
      GodelQuotation.fs_hilbert_tokens_decode tokens with
  | none =>
      simp [hParsed] at hDecode
  | some parsed =>
      by_cases hCanonical :
          GodelQuotation.Numbered.quote_tokens? parsed =
            some tokens
      · simp [hParsed, hCanonical] at hDecode
        subst formula
        exact hCanonical
      · simp [hParsed, hCanonical] at hDecode

/-- 逻辑公理 base payload 中的公式序列解码。 -/
def fs_formula_payload_decode (code : Nat) :
    Option (List SetFormula) :=
  (nat_sequence_decode code).mapM
    fs_formula_token_code_decode

/-- `mapM` 的非空成功结果可构造性拆出首项与尾项。 -/
theorem fs_option_mapM_cons_eq_some
    {α β : Type}
    (transform : α → Option β)
    {head : α} {tail : List α}
    {headResult : β} {tailResults : List β}
    (hMap :
      (head :: tail).mapM transform =
        some (headResult :: tailResults)) :
    transform head = some headResult ∧
      tail.mapM transform = some tailResults := by
  simp only [List.mapM_cons] at hMap
  rcases Option.bind_eq_some_iff.mp hMap with
    ⟨first, hFirst, hRest⟩
  rcases Option.bind_eq_some_iff.mp hRest with
    ⟨rest, hTail, hPure⟩
  simp at hPure
  rcases hPure with ⟨rfl, rfl⟩
  exact ⟨hFirst, hTail⟩

/-- 单公式 payload 解码成功时恢复唯一的数值字段及其逐项解码。 -/
theorem fs_formula_payload_decode_one
    {code : Nat} {formula : SetFormula}
    (hDecode :
      fs_formula_payload_decode code = some [formula]) :
    ∃ formulaCode,
      nat_sequence_decode code = [formulaCode] ∧
      fs_formula_token_code_decode formulaCode = some formula := by
  have hMap :
      (nat_sequence_decode code).mapM
          fs_formula_token_code_decode =
        some [formula] := by
    simpa [fs_formula_payload_decode] using hDecode
  have hLength :
      (nat_sequence_decode code).length = 1 := by
    have hMapLength :=
      GodelQuotation.fs_option_mapM_length hMap
    simpa using hMapLength.symm
  rcases List.length_eq_one_iff.mp hLength with
    ⟨formulaCode, hCodes⟩
  rw [hCodes] at hMap
  rcases fs_option_mapM_cons_eq_some
      fs_formula_token_code_decode hMap with
    ⟨hFormulaCode, _⟩
  exact ⟨formulaCode, hCodes, hFormulaCode⟩

/-- 双公式 payload 解码成功时恢复两个数值字段及其逐项解码。 -/
theorem fs_formula_payload_decode_two
    {code : Nat} {left right : SetFormula}
    (hDecode :
      fs_formula_payload_decode code =
        some [left, right]) :
    ∃ leftCode rightCode,
      nat_sequence_decode code = [leftCode, rightCode] ∧
      fs_formula_token_code_decode leftCode = some left ∧
      fs_formula_token_code_decode rightCode = some right := by
  have hMap :
      (nat_sequence_decode code).mapM
          fs_formula_token_code_decode =
        some [left, right] := by
    simpa [fs_formula_payload_decode] using hDecode
  have hLength :
      (nat_sequence_decode code).length = 2 := by
    have hMapLength :=
      GodelQuotation.fs_option_mapM_length hMap
    simpa using hMapLength.symm
  cases hCodes : nat_sequence_decode code with
  | nil =>
      simp [hCodes] at hLength
  | cons leftCode rest =>
      rw [hCodes] at hMap
      have hRestLength : rest.length = 1 := by
        simpa [hCodes] using hLength
      rcases List.length_eq_one_iff.mp hRestLength with
        ⟨rightCode, rfl⟩
      rcases fs_option_mapM_cons_eq_some
          fs_formula_token_code_decode hMap with
        ⟨hLeftCode, hTailMap⟩
      rcases fs_option_mapM_cons_eq_some
          fs_formula_token_code_decode hTailMap with
        ⟨hRightCode, _⟩
      exact ⟨leftCode, rightCode, rfl,
        hLeftCode, hRightCode⟩

/-- 三公式 payload 解码成功时恢复三个数值字段及其逐项解码。 -/
theorem fs_formula_payload_decode_three
    {code : Nat}
    {first second third : SetFormula}
    (hDecode :
      fs_formula_payload_decode code =
        some [first, second, third]) :
    ∃ firstCode secondCode thirdCode,
      nat_sequence_decode code =
        [firstCode, secondCode, thirdCode] ∧
      fs_formula_token_code_decode firstCode = some first ∧
      fs_formula_token_code_decode secondCode = some second ∧
      fs_formula_token_code_decode thirdCode = some third := by
  have hMap :
      (nat_sequence_decode code).mapM
          fs_formula_token_code_decode =
        some [first, second, third] := by
    simpa [fs_formula_payload_decode] using hDecode
  have hLength :
      (nat_sequence_decode code).length = 3 := by
    have hMapLength :=
      GodelQuotation.fs_option_mapM_length hMap
    simpa using hMapLength.symm
  cases hCodes : nat_sequence_decode code with
  | nil =>
      simp [hCodes] at hLength
  | cons firstCode rest =>
      rw [hCodes] at hMap
      have hRestLength : rest.length = 2 := by
        simpa [hCodes] using hLength
      cases rest with
      | nil =>
          simp at hRestLength
      | cons secondCode tail =>
          have hTailLength : tail.length = 1 := by
            simpa using hRestLength
          rcases List.length_eq_one_iff.mp hTailLength with
            ⟨thirdCode, rfl⟩
          rcases fs_option_mapM_cons_eq_some
              fs_formula_token_code_decode hMap with
            ⟨hFirstCode, hTailMap⟩
          rcases fs_option_mapM_cons_eq_some
              fs_formula_token_code_decode hTailMap with
            ⟨hSecondCode, hLastMap⟩
          rcases fs_option_mapM_cons_eq_some
              fs_formula_token_code_decode hLastMap with
            ⟨hThirdCode, _⟩
          exact ⟨firstCode, secondCode, thirdCode,
            rfl, hFirstCode, hSecondCode, hThirdCode⟩

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
