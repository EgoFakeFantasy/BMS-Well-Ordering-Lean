import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.RosserFinite
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoder
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderComposition

/-!
# checked replay 的具名公式 payload

本模块集中维护 proof 行与逻辑证书 payload 共用的具名解码环境。规范 quotation
对任意 `freeBase` 精确解码；任意成功解码只承诺公式 admissibility，不承诺原
token 串等于解码结果的 canonical re-quotation。
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

/-- 显式名字环境解码成功时保留公式的 admissibility。 -/
theorem fs_named_hilbert_tokens_decode_with_env_admissible
    (freeBase : Nat) (boundNames : List Nat)
    {tokens : List Nat} {formula : SetFormula}
    (hDecode :
      GodelQuotation.fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        some formula) :
    Formula.AdmissibleAt
      (GodelQuotation.Numbered.scope_of_names boundNames)
      formula := by
  rcases
      (GodelQuotation.fs_named_hilbert_tokens_decode_with_env_iff
        freeBase boundNames tokens formula).mp hDecode with
    ⟨tree, _, hTree⟩
  exact
    GodelQuotation.fs_named_hilbert_token_tree_decode_admissible
      freeBase hTree

/-- 固定环境下的规范 quotation 解码。 -/
theorem fs_named_hilbert_tokens_decode_with_env_quote
    (freeBase : Nat)
    {formula : SetFormula}
    {tokens : List Nat}
    (hFormula : Formula.Admissible formula)
    (hQuote :
      GodelQuotation.Numbered.quote_tokens? formula =
        some tokens) :
    GodelQuotation.fs_named_hilbert_tokens_decode_with_env
        freeBase [] tokens =
      some (Formula.hilbertize SetSort.set formula) := by
  have hCanonical :
      GodelQuotation.fs_hilbert_tokens_decode tokens =
        some (Formula.hilbertize SetSort.set formula) :=
    GodelQuotation.fs_hilbert_tokens_decode_quote
      hFormula hQuote
  unfold GodelQuotation.fs_hilbert_tokens_decode at hCanonical
  cases hParse :
      GodelQuotation.RawHilbertTokenTree.parse? tokens with
  | none =>
      simp [hParse] at hCanonical
  | some tree =>
      cases hTree :
          GodelQuotation.fs_hilbert_token_tree_decode 0 tree with
      | none =>
          simp [hParse, hTree] at hCanonical
      | some decoded =>
          have hDecoded :
              decoded =
                Formula.hilbertize SetSort.set formula := by
            simp [hParse, hTree] at hCanonical
            exact hCanonical.2
          have hNamedTree :=
            GodelQuotation.fs_named_hilbert_token_tree_decode_of_canonical
              freeBase 0 hTree
          have hNamedTree' :
              GodelQuotation.fs_named_hilbert_token_tree_decode
                  freeBase [] tree =
                some
                  (Formula.hilbertize SetSort.set formula) := by
            simpa [GodelQuotation.canonical_bound_names,
              hDecoded] using hNamedTree
          have hWhole :=
            GodelQuotation.fs_named_hilbert_tokens_decode_with_env_of_tree
              freeBase [] hNamedTree'
          have hTokens :
              tree.tokens = tokens :=
            GodelQuotation.RawHilbertTokenTree.parse?_sound hParse
          simpa [hTokens] using hWhole

/-- 在 proof 行共享的自由变量基址下解码单个公式 token-code。 -/
def fs_named_formula_token_code_decode
    (freeBase code : Nat) :
    Option SetFormula :=
  GodelQuotation.fs_named_hilbert_tokens_decode_with_env
    freeBase [] (nat_sequence_decode code)

/-- 具名环境下的逻辑 base payload 公式序列解码。 -/
def fs_named_formula_payload_decode
    (freeBase code : Nat) :
    Option (List SetFormula) :=
  (nat_sequence_decode code).mapM
    (fs_named_formula_token_code_decode freeBase)

/-- 具名 token-code 解码成功时，所得公式满足公共 admissibility 边界。 -/
theorem fs_named_formula_token_code_decode_admissible
    {freeBase code : Nat} {formula : SetFormula}
    (hDecode :
      fs_named_formula_token_code_decode freeBase code =
        some formula) :
    Formula.Admissible formula := by
  exact
    fs_named_hilbert_tokens_decode_with_env_admissible
      freeBase [] hDecode

/-- 规范 quotation 在任意具名自由变量基址下都精确解码。 -/
theorem fs_named_formula_token_code_decode_quote
    (freeBase : Nat)
    {formula : SetFormula}
    {tokens : List Nat}
    (hFormula : Formula.Admissible formula)
    (hQuote :
      GodelQuotation.Numbered.quote_tokens? formula =
        some tokens) :
    fs_named_formula_token_code_decode freeBase
        (nat_sequence_code_value tokens) =
      some (Formula.hilbertize SetSort.set formula) := by
  unfold fs_named_formula_token_code_decode
  rw [nat_sequence_decode_code_value]
  exact
    fs_named_hilbert_tokens_decode_with_env_quote
      freeBase hFormula hQuote

private theorem fs_named_option_mapM_cons_eq_some
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

/-- 具名单公式 payload 解码成功时恢复唯一数值字段。 -/
theorem fs_named_formula_payload_decode_one
    {freeBase code : Nat} {formula : SetFormula}
    (hDecode :
      fs_named_formula_payload_decode freeBase code =
        some [formula]) :
    ∃ formulaCode,
      nat_sequence_decode code = [formulaCode] ∧
      fs_named_formula_token_code_decode
        freeBase formulaCode = some formula := by
  have hMap :
      (nat_sequence_decode code).mapM
          (fs_named_formula_token_code_decode freeBase) =
        some [formula] := by
    simpa [fs_named_formula_payload_decode] using hDecode
  have hLength :
      (nat_sequence_decode code).length = 1 := by
    have hMapLength :=
      GodelQuotation.fs_option_mapM_length hMap
    simpa using hMapLength.symm
  rcases List.length_eq_one_iff.mp hLength with
    ⟨formulaCode, hCodes⟩
  rw [hCodes] at hMap
  rcases fs_named_option_mapM_cons_eq_some
      (fs_named_formula_token_code_decode freeBase) hMap with
    ⟨hFormulaCode, _⟩
  exact ⟨formulaCode, hCodes, hFormulaCode⟩

/-- 具名双公式 payload 解码成功时恢复两个数值字段。 -/
theorem fs_named_formula_payload_decode_two
    {freeBase code : Nat} {left right : SetFormula}
    (hDecode :
      fs_named_formula_payload_decode freeBase code =
        some [left, right]) :
    ∃ leftCode rightCode,
      nat_sequence_decode code = [leftCode, rightCode] ∧
      fs_named_formula_token_code_decode freeBase leftCode =
        some left ∧
      fs_named_formula_token_code_decode freeBase rightCode =
        some right := by
  have hMap :
      (nat_sequence_decode code).mapM
          (fs_named_formula_token_code_decode freeBase) =
        some [left, right] := by
    simpa [fs_named_formula_payload_decode] using hDecode
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
      rcases fs_named_option_mapM_cons_eq_some
          (fs_named_formula_token_code_decode freeBase) hMap with
        ⟨hLeftCode, hTailMap⟩
      rcases fs_named_option_mapM_cons_eq_some
          (fs_named_formula_token_code_decode freeBase)
          hTailMap with
        ⟨hRightCode, _⟩
      exact ⟨leftCode, rightCode, rfl,
        hLeftCode, hRightCode⟩

/-- 具名三公式 payload 解码成功时恢复三个数值字段。 -/
theorem fs_named_formula_payload_decode_three
    {freeBase code : Nat}
    {first second third : SetFormula}
    (hDecode :
      fs_named_formula_payload_decode freeBase code =
        some [first, second, third]) :
    ∃ firstCode secondCode thirdCode,
      nat_sequence_decode code =
        [firstCode, secondCode, thirdCode] ∧
      fs_named_formula_token_code_decode freeBase firstCode =
        some first ∧
      fs_named_formula_token_code_decode freeBase secondCode =
        some second ∧
      fs_named_formula_token_code_decode freeBase thirdCode =
        some third := by
  have hMap :
      (nat_sequence_decode code).mapM
          (fs_named_formula_token_code_decode freeBase) =
        some [first, second, third] := by
    simpa [fs_named_formula_payload_decode] using hDecode
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
          rcases fs_named_option_mapM_cons_eq_some
              (fs_named_formula_token_code_decode freeBase) hMap with
            ⟨hFirstCode, hTailMap⟩
          rcases fs_named_option_mapM_cons_eq_some
              (fs_named_formula_token_code_decode freeBase)
              hTailMap with
            ⟨hSecondCode, hLastMap⟩
          rcases fs_named_option_mapM_cons_eq_some
              (fs_named_formula_token_code_decode freeBase)
              hLastMap with
            ⟨hThirdCode, _⟩
          exact ⟨firstCode, secondCode, thirdCode,
            rfl, hFirstCode, hSecondCode, hThirdCode⟩

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
