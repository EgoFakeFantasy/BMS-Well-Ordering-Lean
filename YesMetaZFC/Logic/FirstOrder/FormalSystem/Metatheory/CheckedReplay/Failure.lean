import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.RawAlignment
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.LogicalFailure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaBinderCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaTokenDecision

/-!
# checked replay 的可计算失败见证

本模块把 `Option = none` 反演为有限、结构化的失败数据：

* `List.mapM` 失败精确定位到首个无法解码的输入位置；
* 单行 replay 失败精确落入逻辑公理、理论公理或 MP checker；
* 多行 replay 失败精确记录长度耗尽或某一步拒绝；
* 总 proof code 失败精确记录公式解码、证书解码或逐行 replay 失败。

这些类型只描述 Lean 元层的可计算轨迹，不携带具体对象理论假设。
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

universe u v

/-- `List.mapM` 失败时的具体输入位置。 -/
def FSMapMFailure
    {α : Type u} {β : Type v}
    (decode : α → Option β)
    (items : List α) : Prop :=
  ∃ index,
    ∃ hIndex : index < items.length,
      decode items[index] = none

/--
`List.mapM` 成功时，每个输入位置都有唯一对齐的输出，并保留该位置的解码等式。
-/
theorem fs_mapM_getElem?_of_some
    {α : Type u} {β : Type v}
    {decode : α → Option β}
    {items : List α} {results : List β}
    (hMap : items.mapM decode = some results)
    {index : Nat} {item : α}
    (hItem : items[index]? = some item) :
    ∃ result,
      results[index]? = some result ∧
        decode item = some result := by
  induction items generalizing results index with
  | nil =>
      simp at hItem
  | cons head tail ih =>
      cases hHead : decode head with
      | none =>
          simp [List.mapM_cons, hHead] at hMap
      | some headResult =>
          cases hTail :
              tail.mapM decode with
          | none =>
              simp [List.mapM_cons, hHead, hTail] at hMap
          | some tailResults =>
              have hResults :
                  results = headResult :: tailResults := by
                simpa [List.mapM_cons, hHead, hTail] using
                  hMap.symm
              subst results
              cases index with
              | zero =>
                  simp only [List.getElem?_cons_zero] at hItem
                  have hItemEq : head = item :=
                    Option.some.inj hItem
                  subst item
                  exact ⟨headResult, by simp, hHead⟩
              | succ index =>
                  have hTailItem :
                      tail[index]? = some item := by
                    simpa only [List.getElem?_cons_succ] using
                      hItem
                  rcases ih hTail hTailItem with
                    ⟨result, hResult, hDecode⟩
                  exact
                    ⟨result,
                      by
                        simpa only [List.getElem?_cons_succ] using
                          hResult,
                      hDecode⟩

/--
若输入列的某个已定位元素解码失败，则整列 `mapM` 必然失败。
-/
theorem fs_mapM_eq_none_of_getElem?_decode_none
    {α : Type u} {β : Type v}
    {decode : α → Option β}
    {items : List α}
    {index : Nat} {item : α}
    (hItem : items[index]? = some item)
    (hDecode : decode item = none) :
    items.mapM decode = none := by
  cases hMap : items.mapM decode with
  | none =>
      rfl
  | some results =>
      rcases fs_mapM_getElem?_of_some hMap hItem with
        ⟨result, _, hResult⟩
      rw [hDecode] at hResult
      contradiction

/-- 单行 payload 解码成功时，恢复底层具名 token 解码等式。 -/
theorem fs_formula_row_decode_named_of_some
    {freeBase : Nat}
    {row : List Nat}
    {decoded : FSDecodedFormula}
    (hDecode :
      fs_formula_row_decode freeBase row = some decoded) :
    GodelQuotation.fs_named_hilbert_tokens_decode_with_env
        freeBase [] row =
      some decoded.formula := by
  unfold fs_formula_row_decode at hDecode
  split at hDecode
  · simp at hDecode
  · next formula hParsed =>
      have hDecoded :
          ({
            formula := formula
            h_admissible := by
              simpa [GodelQuotation.Numbered.scope_of_names,
                Scope.empty] using
                fs_named_hilbert_tokens_decode_with_env_admissible
                  freeBase [] hParsed
          } : FSDecodedFormula) = decoded :=
        Option.some.inj hDecode
      subst decoded
      exact hParsed

/--
成功公式行不是全称式时，其 token 头部必然在首位左括号或第二位全称符号处
给出一个具体 mismatch。
-/
inductive FSFormulaUniversalHeadMismatch :
    List Nat → Prop
  | first
      {tokens : List Nat}
      (actual : Nat)
      (h_get : tokens[0]? = some actual)
      (h_ne :
        actual ≠
          GodelQuotation.Numbered.logical_token
            .leftParenthesis) :
      FSFormulaUniversalHeadMismatch tokens
  | second
      {tokens : List Nat}
      (actual : Nat)
      (h_get : tokens[1]? = some actual)
      (h_ne :
        actual ≠
          GodelQuotation.Numbered.logical_token
            .universal) :
      FSFormulaUniversalHeadMismatch tokens

/-- 词法分离的 Hilbert 树首 token 不可能是全称逻辑符号。 -/
private theorem fs_raw_hilbert_tree_head_ne_universal
    (tree : GodelQuotation.RawHilbertTokenTree)
    (hSeparated : tree.LexicallySeparated) :
    ∃ actual tail,
      tree.tokens = actual :: tail ∧
        actual ≠
          GodelQuotation.Numbered.logical_token
            .universal := by
  cases tree with
  | equality left right =>
      refine
        ⟨GodelQuotation.Numbered.logical_token .leftParenthesis,
          left.tokens ++
            GodelQuotation.Numbered.logical_token .equality ::
              (right.tokens ++
                [GodelQuotation.Numbered.logical_token
                  .rightParenthesis]),
          ?_, ?_⟩
      · simp [GodelQuotation.RawHilbertTokenTree.tokens,
          List.append_assoc]
      · native_decide
  | membership left right =>
      refine
        ⟨GodelQuotation.Numbered.logical_token .leftParenthesis,
          left.tokens ++
            GodelQuotation.Numbered.membership_token ::
              (right.tokens ++
                [GodelQuotation.Numbered.logical_token
                  .rightParenthesis]),
          ?_, ?_⟩
      · simp [GodelQuotation.RawHilbertTokenTree.tokens,
          List.append_assoc]
      · native_decide
  | predicate head arguments =>
      refine
        ⟨head,
          GodelQuotation.Numbered.logical_token
              .leftParenthesis ::
            (GodelQuotation.RawTermTokenTree.list_tokens
                arguments ++
              [GodelQuotation.Numbered.logical_token
                .rightParenthesis]),
          rfl, ?_⟩
      exact GodelQuotation.odd_token_ne_logical
        hSeparated.1 .universal
  | negation body =>
      refine
        ⟨GodelQuotation.Numbered.logical_token .leftParenthesis,
          GodelQuotation.Numbered.logical_token .negation ::
            (body.tokens ++
              [GodelQuotation.Numbered.logical_token
                .rightParenthesis]),
          rfl, ?_⟩
      native_decide
  | implication left right =>
      refine
        ⟨GodelQuotation.Numbered.logical_token .leftParenthesis,
          left.tokens ++
            GodelQuotation.Numbered.logical_token .implication ::
              (right.tokens ++
                [GodelQuotation.Numbered.logical_token
                  .rightParenthesis]),
          ?_, ?_⟩
      · simp [GodelQuotation.RawHilbertTokenTree.tokens,
          List.append_assoc]
      · native_decide
  | universal variableToken body =>
      refine
        ⟨GodelQuotation.Numbered.logical_token .leftParenthesis,
          GodelQuotation.Numbered.logical_token .universal ::
            variableToken ::
              (body.tokens ++
                [GodelQuotation.Numbered.logical_token
                  .rightParenthesis]),
          rfl, ?_⟩
      native_decide

/-- checked 行解码成功且结果非全称时，计算出最外层 token mismatch。 -/
theorem fs_formula_row_decode_non_forall_head_mismatch
    {freeBase : Nat}
    {row : List Nat}
    {decoded : FSDecodedFormula}
    (hDecode :
      fs_formula_row_decode freeBase row =
        some decoded)
    (hShape :
      ¬ ∃ body,
        decoded.formula =
          Formula.forallE SetSort.set body) :
    FSFormulaUniversalHeadMismatch row := by
  have hNamed :=
    fs_formula_row_decode_named_of_some hDecode
  rcases
      (GodelQuotation.fs_named_hilbert_tokens_decode_with_env_iff
        freeBase [] row decoded.formula).mp hNamed with
    ⟨tree, hParse, hTree⟩
  have hTokens :
      tree.tokens = row :=
    GodelQuotation.RawHilbertTokenTree.parse?_sound
      hParse
  have hSeparated :
      tree.LexicallySeparated :=
    GodelQuotation.fs_named_hilbert_token_tree_decode_lexically_separated
      freeBase hTree
  rw [← hTokens]
  cases tree with
  | equality left right =>
      rcases
          GodelQuotation.RawTermTokenTree.tokens_eq_head_cons
            hSeparated.1 with
        ⟨head, tail, hOdd, hLeft⟩
      exact .second head
        (by
          simp [GodelQuotation.RawHilbertTokenTree.tokens,
            hLeft])
        (GodelQuotation.odd_token_ne_logical
          hOdd .universal)
  | membership left right =>
      rcases
          GodelQuotation.RawTermTokenTree.tokens_eq_head_cons
            hSeparated.1 with
        ⟨head, tail, hOdd, hLeft⟩
      exact .second head
        (by
          simp [GodelQuotation.RawHilbertTokenTree.tokens,
            hLeft])
        (GodelQuotation.odd_token_ne_logical
          hOdd .universal)
  | predicate head arguments =>
      exact .first head
        (by
          simp [GodelQuotation.RawHilbertTokenTree.tokens])
        (GodelQuotation.odd_token_ne_logical
          hSeparated.1 .leftParenthesis)
  | negation body =>
      exact .second
        (GodelQuotation.Numbered.logical_token .negation)
        (by
          simp [GodelQuotation.RawHilbertTokenTree.tokens])
        (by native_decide)
  | implication left right =>
      rcases
          fs_raw_hilbert_tree_head_ne_universal
            left hSeparated.1 with
        ⟨head, tail, hHead, hNe⟩
      exact .second head
        (by
          simp [GodelQuotation.RawHilbertTokenTree.tokens,
            hHead])
        hNe
  | universal variableToken body =>
      cases hName :
          GodelQuotation.fs_variable_name_decode
            variableToken with
      | none =>
          simp [GodelQuotation.fs_named_hilbert_token_tree_decode,
            hName] at hTree
      | some name =>
          cases hBody :
              GodelQuotation.fs_named_hilbert_token_tree_decode
                freeBase (name :: []) body with
          | none =>
              simp [GodelQuotation.fs_named_hilbert_token_tree_decode,
                hName, hBody] at hTree
          | some bodyFormula =>
              simp [GodelQuotation.fs_named_hilbert_token_tree_decode,
                hName, hBody] at hTree
              exact False.elim <|
                hShape ⟨bodyFormula, hTree.symm⟩

/-- `List.mapM = none` 总能定位到一个具体失败项。 -/
theorem fs_mapM_failure_of_none
    {α : Type u} {β : Type v}
    {decode : α → Option β}
    {items : List α}
    (hDecode : items.mapM decode = none) :
    FSMapMFailure decode items := by
  induction items with
  | nil =>
      simp at hDecode
  | cons head tail ih =>
      cases hHead : decode head with
      | none =>
          exact ⟨0, by simp, hHead⟩
      | some headResult =>
          have hTail :
              tail.mapM decode = none := by
            cases hTailMap : tail.mapM decode with
            | none =>
                rfl
            | some tailResults =>
                simp [List.mapM_cons, hHead,
                  hTailMap] at hDecode
          rcases ih hTail with
            ⟨index, hIndex, hNone⟩
          refine ⟨index + 1, ?_, ?_⟩
          · simp [hIndex]
          · simpa only [List.getElem_cons_succ] using hNone

/-- 证书序列解码失败时定位到一个非法自然数标签。 -/
theorem fs_certificate_sequence_decode_failure_of_none
    {code : Nat}
    (hDecode :
      fs_certificate_sequence_decode code = none) :
    FSMapMFailure
      HilbertLineCertificateCode.decode
      (nat_sequence_decode code) := by
  exact fs_mapM_failure_of_none <| by
    simpa [fs_certificate_sequence_decode] using hDecode

/-- 解码失败的自然数不可能是任何合法行证书的规范值。 -/
theorem fs_certificate_code_ne_value_of_decode_none
    {code : Nat}
    (hDecode :
      HilbertLineCertificateCode.decode code = none)
    (certificate : HilbertLineCertificateCode) :
    code ≠ HilbertLineCertificateCode.value certificate := by
  intro hEquality
  rw [hEquality, HilbertLineCertificateCode.decode_value] at hDecode
  contradiction

/-- 证书序列成功解码不改变序列长度。 -/
theorem fs_certificate_sequence_decode_length
    {code : Nat}
    {certificates : List HilbertLineCertificateCode}
    (hDecode :
      fs_certificate_sequence_decode code =
        some certificates) :
    certificates.length =
      (nat_sequence_decode code).length := by
  exact GodelQuotation.fs_option_mapM_length <| by
    simpa [fs_certificate_sequence_decode] using hDecode

/-- 公式行 payload 解码失败时定位到一个非法 token 行。 -/
theorem fs_formula_rows_decode_payload_failure_of_none
    (freeBase : Nat) {rows : List (List Nat)}
    (hDecode :
      fs_formula_rows_decode_payload freeBase rows = none) :
    FSMapMFailure
      (fs_formula_row_decode freeBase) rows := by
  exact fs_mapM_failure_of_none <| by
    simpa [fs_formula_rows_decode_payload] using hDecode

/--
单个公式行的 checked 解码失败按最小结构信息分为三类：

* 缺少第一号位置；
* 第零、第一位均不是左括号；
* 至少一个规范左括号已出现，但 parser 仍然失败。

第三类是后续结构 parser 反演唯一需要继续处理的残余。
-/
inductive FSFormulaRowDecodeFailureView
    (freeBase : Nat) (row : List Nat) : Prop
  | one_absent
      (h_decode :
        fs_formula_row_decode freeBase row = none)
      (h_one : row[1]? = none) :
      FSFormulaRowDecodeFailureView freeBase row
  | no_left_opening
      (h_decode :
        fs_formula_row_decode freeBase row = none)
      (h_one_present : row[1]? ≠ none)
      (h_zero :
        row[0]? ≠
          some (GodelQuotation.Numbered.logical_token
            .leftParenthesis))
      (h_one :
        row[1]? ≠
          some (GodelQuotation.Numbered.logical_token
            .leftParenthesis)) :
      FSFormulaRowDecodeFailureView freeBase row
  | opening_present
      (h_decode :
        fs_formula_row_decode freeBase row = none)
      (h_one_present : row[1]? ≠ none)
      (h_opening :
        row[0]? =
            some (GodelQuotation.Numbered.logical_token
              .leftParenthesis) ∨
          row[1]? =
            some (GodelQuotation.Numbered.logical_token
              .leftParenthesis)) :
      FSFormulaRowDecodeFailureView freeBase row

/-- 任意单行解码失败都具有上述三分视图。 -/
theorem fs_formula_row_decode_failure_view_of_none
    {freeBase : Nat} {row : List Nat}
    (hDecode :
      fs_formula_row_decode freeBase row = none) :
    FSFormulaRowDecodeFailureView freeBase row := by
  by_cases hOneAbsent : row[1]? = none
  · exact
      FSFormulaRowDecodeFailureView.one_absent
        hDecode hOneAbsent
  · by_cases hZero :
        row[0]? =
          some (GodelQuotation.Numbered.logical_token
            .leftParenthesis)
    · exact
        FSFormulaRowDecodeFailureView.opening_present
          hDecode hOneAbsent (Or.inl hZero)
    · by_cases hOne :
          row[1]? =
            some (GodelQuotation.Numbered.logical_token
              .leftParenthesis)
      · exact
          FSFormulaRowDecodeFailureView.opening_present
            hDecode hOneAbsent (Or.inr hOne)
      · exact
          FSFormulaRowDecodeFailureView.no_left_opening
            hDecode hOneAbsent hZero hOne

/-- 多行 payload 解码失败时，定位失败行并给出其最小结构视图。 -/
theorem fs_formula_rows_decode_payload_failure_view_of_none
    (freeBase : Nat) {rows : List (List Nat)}
    (hDecode :
      fs_formula_rows_decode_payload freeBase rows = none) :
    ∃ index,
      ∃ hIndex : index < rows.length,
        FSFormulaRowDecodeFailureView
          freeBase rows[index] := by
  rcases
      fs_formula_rows_decode_payload_failure_of_none
        freeBase hDecode with
    ⟨index, hIndex, hRow⟩
  exact
    ⟨index, hIndex,
      fs_formula_row_decode_failure_view_of_none hRow⟩

/--
公式行 payload 中仍待 parser 反演的精确残余：失败行全部 token 都属于当前有限
签名，每个全称 token 都具有可解码的变量后继，至少具有两个位置，并且第零或
第一位已经是规范左括号。
-/
def FSFormulaRowsDecodeStructuralResidual
    (freeBase : Nat) (rows : List (List Nat)) : Prop :=
  ∃ index,
    ∃ hIndex : index < rows.length,
      fs_formula_row_decode freeBase rows[index] = none ∧
        GodelQuotation.FSFormulaTokens rows[index] ∧
          GodelQuotation.FSFormulaBinderTokens rows[index] ∧
            rows[index][1]? ≠ none ∧
            (rows[index][0]? =
                  some (GodelQuotation.Numbered.logical_token
                    .leftParenthesis) ∨
              rows[index][1]? =
                  some (GodelQuotation.Numbered.logical_token
                    .leftParenthesis))

/-! ## MP checker 的精确失败 -/

/-- 公式码相等检查失败时，两条宿主公式确实不同。 -/
theorem fs_formula_code_eq_ne_of_false
    {left right : SetFormula}
    (hCheck : fs_formula_code_eq left right = false) :
    left ≠ right := by
  intro hEquality
  subst right
  simp [fs_formula_code_eq] at hCheck

/--
成功前缀后的严格 MP 检查失败时，若两个引用索引次序有效，则原始蕴含行不可能
等于前件行和当前行构造出的规范蕴含 token 串。
-/
theorem fs_modus_ponens_raw_shape_ne_of_check_false
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat)
    (rows : List (List Nat))
    (certificates : List HilbertLineCertificateCode)
    (index implicationIndex premiseIndex : Nat)
    (row implicationRow premiseRow : List Nat)
    (decoded : FSDecodedFormula)
    (prefixState :
      FSReplayState enumeration freeBase)
    (hImplicationRow :
      rows[implicationIndex]? = some implicationRow)
    (hPremiseRow :
      rows[premiseIndex]? = some premiseRow)
    (hPrefix :
      fs_replay_raw_rows enumeration freeBase
          (fs_replay_nil enumeration freeBase)
          (rows.take index)
          (certificates.take index) =
        some prefixState)
    (hDecode :
      fs_formula_row_decode freeBase row = some decoded)
    (hOrder :
      premiseIndex < implicationIndex ∧
        implicationIndex < index)
    (hCheck :
      fs_modus_ponens_check
          prefixState.proof decoded.formula
          implicationIndex premiseIndex =
        false) :
    implicationRow ≠
      GodelQuotation.Numbered.implication_tokens
        premiseRow row := by
  rcases fs_replay_raw_rows_nil_some_alignment
      enumeration freeBase prefixState
      (rows.take index) (certificates.take index)
      hPrefix with
    ⟨decodedRows, hRowsDecode, hProof, _⟩
  have hPremiseOrder :
      premiseIndex < index := by
    omega
  have hImplicationTake :
      (rows.take index)[implicationIndex]? =
        some implicationRow := by
    rw [List.getElem?_take_of_lt hOrder.2]
    exact hImplicationRow
  have hPremiseTake :
      (rows.take index)[premiseIndex]? =
        some premiseRow := by
    rw [List.getElem?_take_of_lt hPremiseOrder]
    exact hPremiseRow
  rcases fs_mapM_getElem?_of_some
      (by
        simpa [fs_formula_rows_decode_payload] using
          hRowsDecode)
      hImplicationTake with
    ⟨implicationDecoded, hImplicationDecoded, hImplicationDecode⟩
  rcases fs_mapM_getElem?_of_some
      (by
        simpa [fs_formula_rows_decode_payload] using
          hRowsDecode)
      hPremiseTake with
    ⟨premiseDecoded, hPremiseDecoded, hPremiseDecode⟩
  have hImplicationProof :
      prefixState.proof[implicationIndex]? =
        some implicationDecoded.formula := by
    rw [hProof]
    simpa using
      congrArg
        (Option.map FSDecodedFormula.formula)
        hImplicationDecoded
  have hPremiseProof :
      prefixState.proof[premiseIndex]? =
        some premiseDecoded.formula := by
    rw [hProof]
    simpa using
      congrArg
        (Option.map FSDecodedFormula.formula)
        hPremiseDecoded
  have hImplicationNamed :=
    fs_formula_row_decode_named_of_some
      hImplicationDecode
  have hPremiseNamed :=
    fs_formula_row_decode_named_of_some
      hPremiseDecode
  have hConclusionNamed :=
    fs_formula_row_decode_named_of_some hDecode
  intro hShape
  rw [hShape] at hImplicationNamed
  have hWholeNamed :=
    GodelQuotation.fs_named_hilbert_tokens_decode_with_env_implication
      freeBase [] hPremiseNamed hConclusionNamed
  have hImplicationFormula :
      implicationDecoded.formula =
        Formula.imp premiseDecoded.formula decoded.formula :=
    Option.some.inj <|
      hImplicationNamed.symm.trans hWholeNamed
  have hCheckTrue :
      fs_modus_ponens_check
          prefixState.proof decoded.formula
          implicationIndex premiseIndex =
        true := by
    simp [fs_modus_ponens_check, hOrder.1,
      hImplicationProof, hPremiseProof,
      hImplicationFormula, fs_formula_code_eq]
  rw [hCheckTrue] at hCheck
  contradiction

/-- 单行 checked replay 的三类精确失败。 -/
inductive FSReplayRowFailure
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat)
    (state : FSReplayState enumeration freeBase)
    (formula : SetFormula) :
    HilbertLineCertificateCode → Prop
  | logical
      {certificateCode : Nat}
      (h_failure :
        FSLogicalAxiomCheckFailure freeBase
          (nat_sequence_decode certificateCode)
          formula) :
      FSReplayRowFailure
        enumeration freeBase state formula
        (.logical certificateCode)
  | theory
      {certificateCode : Nat}
      (h_check :
        enumeration.certificate_verifier
            certificateCode formula =
          false) :
      FSReplayRowFailure
        enumeration freeBase state formula
        (.theory certificateCode)
  | modus_ponens
      {implicationIndex premiseIndex : Nat}
      (h_check :
        fs_modus_ponens_check
            state.proof formula
            implicationIndex premiseIndex =
          false) :
      FSReplayRowFailure
        enumeration freeBase state formula
        (.modusPonens implicationIndex premiseIndex)

/-- 单行 replay 的 `none` 精确反演为对应 checker 的 `false`。 -/
theorem fs_replay_row_failure_of_none
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    {freeBase : Nat}
    (state : FSReplayState enumeration freeBase)
    (formula : SetFormula)
    (certificate : HilbertLineCertificateCode)
    (hAdmissible : Formula.Admissible formula)
    (hReplay :
      fs_replay_row enumeration state formula
          certificate hAdmissible =
        none) :
    FSReplayRowFailure
      enumeration freeBase state formula certificate := by
  cases certificate with
  | logical certificateCode =>
      cases hCheck :
          fs_logical_axiom_check
            freeBase certificateCode formula with
      | false =>
          exact FSReplayRowFailure.logical <|
            fs_logical_axiom_check_rows_failure_of_false
              (by
                simpa [fs_logical_axiom_check] using
                  hCheck)
      | true =>
          simp [fs_replay_row, fs_replay_logical_row,
            hCheck] at hReplay
  | theory certificateCode =>
      cases hCheck :
          enumeration.certificate_verifier
            certificateCode formula with
      | false =>
          exact FSReplayRowFailure.theory hCheck
      | true =>
          simp [fs_replay_row, fs_replay_theory_row,
            hCheck] at hReplay
  | modusPonens implicationIndex premiseIndex =>
      cases hCheck :
          fs_modus_ponens_check
            state.proof formula
            implicationIndex premiseIndex with
      | false =>
          exact FSReplayRowFailure.modus_ponens hCheck
      | true =>
          simp [fs_replay_row,
            fs_replay_modus_ponens_row,
            hCheck] at hReplay

/-- 结构化单行失败重新计算为 `none`。 -/
theorem FSReplayRowFailure.replay_eq_none
    {theory : SetTheory}
    {enumeration :
      ProofCode.HilbertTheoryEnumeration theory}
    {freeBase : Nat}
    {state : FSReplayState enumeration freeBase}
    {formula : SetFormula}
    {certificate : HilbertLineCertificateCode}
    (hFailure :
      FSReplayRowFailure
        enumeration freeBase state formula certificate)
    (hAdmissible : Formula.Admissible formula) :
    fs_replay_row enumeration state formula
        certificate hAdmissible =
      none := by
  cases hFailure with
  | @logical certificateCode hFailure =>
      have hCheck :
          fs_logical_axiom_check
              freeBase certificateCode formula =
            false := by
        simpa [fs_logical_axiom_check] using
          hFailure.check_eq_false
      simp [fs_replay_row, fs_replay_logical_row,
        hCheck]
  | theory hCheck =>
      simp [fs_replay_row, fs_replay_theory_row,
        hCheck]
  | modus_ponens hCheck =>
      simp [fs_replay_row,
        fs_replay_modus_ponens_row, hCheck]

/--
原始 token 行逐行 replay 的精确失败树。

公式解码失败发生在当前证书已经对齐之后；递归 `tail` 同时保存本行解码结果和
成功 replay，因而不会丢失失败点之前的状态。
-/
inductive FSReplayRawRowsFailure
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat) :
    FSReplayState enumeration freeBase →
      List (List Nat) →
      List HilbertLineCertificateCode → Prop
  | extra_certificates
      (state : FSReplayState enumeration freeBase)
      (certificate : HilbertLineCertificateCode)
      (certificates : List HilbertLineCertificateCode) :
      FSReplayRawRowsFailure enumeration freeBase state []
        (certificate :: certificates)
  | missing_certificate
      (state : FSReplayState enumeration freeBase)
      (row : List Nat)
      (rows : List (List Nat)) :
      FSReplayRawRowsFailure enumeration freeBase state
        (row :: rows) []
  | formula_decode
      {state : FSReplayState enumeration freeBase}
      {row : List Nat}
      {rows : List (List Nat)}
      {certificate : HilbertLineCertificateCode}
      {certificates : List HilbertLineCertificateCode}
      (h_decode :
        fs_formula_row_decode freeBase row = none) :
      FSReplayRawRowsFailure enumeration freeBase state
        (row :: rows) (certificate :: certificates)
  | rejected_row
      {state : FSReplayState enumeration freeBase}
      {row : List Nat}
      {rows : List (List Nat)}
      {certificate : HilbertLineCertificateCode}
      {certificates : List HilbertLineCertificateCode}
      {decoded : FSDecodedFormula}
      (h_decode :
        fs_formula_row_decode freeBase row = some decoded)
      (h_failure :
        FSReplayRowFailure enumeration freeBase state
          decoded.formula certificate) :
      FSReplayRawRowsFailure enumeration freeBase state
        (row :: rows) (certificate :: certificates)
  | tail
      {state next :
        FSReplayState enumeration freeBase}
      {row : List Nat}
      {rows : List (List Nat)}
      {certificate : HilbertLineCertificateCode}
      {certificates : List HilbertLineCertificateCode}
      {decoded : FSDecodedFormula}
      (h_decode :
        fs_formula_row_decode freeBase row = some decoded)
      (h_replay :
        fs_replay_row enumeration state decoded.formula
            certificate decoded.h_admissible =
          some next)
      (h_failure :
        FSReplayRawRowsFailure enumeration freeBase next
          rows certificates) :
      FSReplayRawRowsFailure enumeration freeBase state
        (row :: rows) (certificate :: certificates)

/-- 原始 token 行 replay 的 `none` 精确反演为有限失败树。 -/
theorem fs_replay_raw_rows_failure_of_none
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat)
    (state : FSReplayState enumeration freeBase)
    (rows : List (List Nat))
    (certificates : List HilbertLineCertificateCode)
    (hReplay :
      fs_replay_raw_rows enumeration freeBase state
          rows certificates =
        none) :
    FSReplayRawRowsFailure enumeration freeBase state
      rows certificates := by
  induction rows generalizing state certificates with
  | nil =>
      cases certificates with
      | nil =>
          simp [fs_replay_raw_rows] at hReplay
      | cons certificate certificates =>
          exact
            FSReplayRawRowsFailure.extra_certificates
              state certificate certificates
  | cons row rows ih =>
      cases certificates with
      | nil =>
          exact
            FSReplayRawRowsFailure.missing_certificate
              state row rows
      | cons certificate certificates =>
          cases hDecode : fs_formula_row_decode freeBase row with
          | none =>
              exact
                FSReplayRawRowsFailure.formula_decode
                  hDecode
          | some decoded =>
              cases hStep :
                  fs_replay_row enumeration state
                    decoded.formula certificate
                    decoded.h_admissible with
              | none =>
                  exact
                    FSReplayRawRowsFailure.rejected_row
                      hDecode
                      (fs_replay_row_failure_of_none
                        enumeration state decoded.formula
                        certificate decoded.h_admissible hStep)
              | some next =>
                  have hTail :
                      fs_replay_raw_rows enumeration freeBase next
                          rows certificates =
                        none := by
                    simpa [fs_replay_raw_rows, hDecode,
                      hStep] using hReplay
                  exact
                    FSReplayRawRowsFailure.tail
                      hDecode hStep
                      (ih next certificates hTail)

/-- 结构化原始行失败重新计算为 `none`。 -/
theorem FSReplayRawRowsFailure.replay_eq_none
    {theory : SetTheory}
    {enumeration :
      ProofCode.HilbertTheoryEnumeration theory}
    {freeBase : Nat}
    {state : FSReplayState enumeration freeBase}
    {rows : List (List Nat)}
    {certificates : List HilbertLineCertificateCode}
    (hFailure :
      FSReplayRawRowsFailure enumeration freeBase state
        rows certificates) :
    fs_replay_raw_rows enumeration freeBase state
        rows certificates =
      none := by
  induction hFailure with
  | extra_certificates =>
      rfl
  | missing_certificate =>
      rfl
  | formula_decode hDecode =>
      simp [fs_replay_raw_rows, hDecode]
  | @rejected_row _ row _ certificate _ decoded
      hDecode hFailure =>
      simp [fs_replay_raw_rows, hDecode,
        hFailure.replay_eq_none decoded.h_admissible]
  | tail hDecode hReplay hFailure ih =>
      simp [fs_replay_raw_rows, hDecode, hReplay, ih]

/-- 完整 proof code replay 的两层精确失败。 -/
inductive FSReplayCodeFailure
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (proofCode : Nat) : Prop
  | certificate_decode
      (h_decode :
        (fs_certified_proof_code_decode proofCode).2 =
          none) :
      FSReplayCodeFailure enumeration proofCode
  | rows
      {certificates : List HilbertLineCertificateCode}
      (h_certificates :
        (fs_certified_proof_code_decode proofCode).2 =
          some certificates)
      (h_failure :
        FSReplayRawRowsFailure enumeration proofCode
          (fs_replay_nil enumeration proofCode)
          (fs_certified_proof_code_decode proofCode).1
          certificates) :
      FSReplayCodeFailure enumeration proofCode

/-- 总 replay 返回 `none` 时，精确恢复其两层失败视图。 -/
theorem fs_replay_code_failure_of_none
    {theory : SetTheory}
    (enumeration :
      ProofCode.HilbertTheoryEnumeration theory)
    (proofCode : Nat)
    (hReplay :
      fs_replay_code enumeration proofCode = none) :
    FSReplayCodeFailure enumeration proofCode := by
  cases hCertificates :
      (fs_certified_proof_code_decode proofCode).2 with
  | none =>
      exact FSReplayCodeFailure.certificate_decode hCertificates
  | some certificates =>
      exact FSReplayCodeFailure.rows hCertificates <|
        fs_replay_raw_rows_failure_of_none
          enumeration proofCode
          (fs_replay_nil enumeration proofCode)
          (fs_certified_proof_code_decode proofCode).1
          certificates <| by
            simpa [fs_replay_code, hCertificates] using hReplay

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
