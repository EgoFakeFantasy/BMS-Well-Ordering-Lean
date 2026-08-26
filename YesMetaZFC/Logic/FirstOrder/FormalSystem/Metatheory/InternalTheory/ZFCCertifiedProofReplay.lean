import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.RosserFinite

/-!
# ZFC 证书化证明码的对象层回放

本模块只处理固定 `fs_zfc_support_theory` 的具体有限回放。证明序列仍然是
`CertifiedProof` 已定义的对象公式；这里不再引入第二个证明谓词，也不改变
证明码的外部数值编码。
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

/-! ## 公式行代码的标准 token 对齐 -/

/-- 可用公式的对象 quotation 与其规范 token 序列相等。 -/
theorem ProofT.ZFC.formula_code_eq_tokens
    {T : SetTheory}
    (hQuotation :
      ∀ {candidate : SetFormula},
        godel_quotation_theory candidate → T candidate)
    {formula : SetFormula}
    (hFormula : Formula.Admissible formula) :
    Derives T [] (
      fs_zfc_formula_code_term formula ≐ₘ
        standard_token_sequence (certified_row_tokens formula)) := by
  unfold fs_zfc_formula_code_term
  cases hTokens : GodelQuotation.Numbered.quote_tokens? formula with
  | none =>
      rcases GodelQuotation.Numbered.quote_tokens?_exists hFormula with
        ⟨tokens, hTokens'⟩
      simp [hTokens] at hTokens'
  | some tokens =>
      cases hCode : GodelQuotation.Numbered.quote? formula with
      | none =>
          rcases GodelQuotation.Numbered.quote?_exists hFormula with
            ⟨code, hCode'⟩
          simp [hCode] at hCode'
      | some code =>
          have hEquality :
              Derives godel_quotation_theory [] (
                code ≐ₘ standard_token_sequence tokens) :=
            GodelQuotation.quote?_eq_standard_token_sequence
              hTokens hCode
          have hEqualityAt :
              Derives T [] (
                code ≐ₘ standard_token_sequence tokens) :=
            FirstOrder.Derives.theory_weaken
              (fun _ hCandidate => hQuotation hCandidate)
              hEquality
          simpa [certified_row_tokens, hTokens, hCode] using hEqualityAt

/-! ## 公式行序列的对象空间 -/

/-- 公式 token 序列本身属于对象公式码集合。 -/
theorem fs_zfc_support_raw_standard_formula_code_mem
    {formula : SetFormula}
    (hFormula : Formula.Admissible formula) :
    Derives fs_zfc_support_raw_theory [] (
      standard_token_sequence (certified_row_tokens formula) ∈ₘ
        FormulaCodeₘ) := by
  cases hTokens : GodelQuotation.Numbered.quote_tokens? formula with
  | none =>
      rcases GodelQuotation.Numbered.quote_tokens?_exists hFormula with
        ⟨tokens, hTokens'⟩
      simp [hTokens] at hTokens'
  | some tokens =>
      cases hCode : GodelQuotation.Numbered.quote? formula with
      | none =>
          rcases GodelQuotation.Numbered.quote?_exists hFormula with
            ⟨code, hCode'⟩
          simp [hCode] at hCode'
      | some code =>
          have hCodeMember :
              Derives godel_quotation_theory [] (
                code ∈ₘ FormulaCodeₘ) :=
            GodelQuotation.Numbered.quote?_formula_code_mem hCode
          have hEquality :
              Derives godel_quotation_theory [] (
                code ≐ₘ standard_token_sequence tokens) :=
            GodelQuotation.quote?_eq_standard_token_sequence
              hTokens hCode
          have hTransport :
              Derives godel_quotation_theory [] (
                (code ∈ₘ FormulaCodeₘ) ↔ₘ
                  (standard_token_sequence tokens ∈ₘ
                    FormulaCodeₘ)) :=
            membership_left_iff_of_equality
              code (standard_token_sequence tokens) FormulaCodeₘ
              (GodelQuotation.Numbered.quote?_code_boundary hCode).1
              (standard_token_sequence_admissible tokens)
              formula_code_set_term_admissible
              hEquality
          have hMember :
              Derives godel_quotation_theory [] (
                standard_token_sequence tokens ∈ₘ
                  FormulaCodeₘ) :=
            FirstOrder.Derives.iffElimRight hTransport hCodeMember
          have hMemberRaw :=
            fs_zfc_support_raw_derives_of_godel_quotation hMember
          simpa [certified_row_tokens, hTokens] using hMemberRaw

theorem fs_zfc_support_raw_standard_formula_code_sequence_space
    {proof : List SetFormula}
    (hRows :
      ∀ formula, formula ∈ proof →
        Formula.Admissible formula)
    (hNonempty : proof ≠ []) :
    Derives fs_zfc_support_raw_theory [] (
      standard_sequence
          (proof.map
            (fun formula =>
              standard_token_sequence
                (certified_row_tokens formula))) ∈ₘ
        seq₊_spaceₘ(FormulaCodeₘ)) := by
  let elements :=
    proof.map
      (fun formula =>
        standard_token_sequence (certified_row_tokens formula))
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact standard_token_sequence_admissible
      (certified_row_tokens formula)
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact standard_token_sequence_freeSupport_nil
      (certified_row_tokens formula)
  have hTargetNonempty :
      Derives fs_zfc_support_raw_theory [] (
        FormulaCodeₘ ≠ₘ ∅ₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      GodelQuotation.formula_code_set_nonempty_derives
  have hTargetClosed :
      Term.freeSupport FormulaCodeₘ = [] := by
    native_decide
  have hElementsNonempty : elements ≠ [] := by
    simpa [elements] using hNonempty
  have hTargetMember :
      ∀ element, element ∈ elements →
        Derives fs_zfc_support_raw_theory [] (
          element ∈ₘ FormulaCodeₘ) := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact fs_zfc_support_raw_standard_formula_code_mem
      (hRows formula hFormula)
  have hSpace :=
    GodelQuotation.standard_sequence_mem_nonempty_sequence_space_of_theory
      (T := fs_zfc_support_raw_theory)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_standard_sequence_semantics hFormula)
      (fun _ hFormula =>
        fs_zfc_support_raw_theory_sentence hFormula)
      FormulaCodeₘ hElements hElementsClosed
      formula_code_set_term_admissible
      hTargetClosed
      hTargetNonempty hTargetMember hElementsNonempty
  simpa [elements] using hSpace

/-- 二维自然数行列表的外层折叠轨迹在一个具体位置上的递推。 -/
private theorem fs_zfc_support_raw_proof_sequence_outer_step_at_numeral
    (rows : List (List Nat))
    (index : Nat)
    (row : List Nat)
    (hIndex : index < rows.length)
    (hRow : rows[index]? = some row) :
    Derives fs_zfc_support_raw_theory [] (
      let trace :=
        standard_token_sequence (proof_sequence_code_trace rows)
      (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
        Sₘ(godel_pairₘ(⟨
          trace ·ₘ numₘ(index),
          numₘ(nat_sequence_code_value row)⟩ₘ))) := by
  let trace : SetTerm :=
    standard_token_sequence (proof_sequence_code_trace rows)
  let prefixCode : Nat :=
    proof_sequence_code_from 0 (rows.take index)
  let rowCode : Nat :=
    nat_sequence_code_value row
  have hTrace :
      Term.Admissible trace SetSort.set := by
    simpa [trace] using
      standard_token_sequence_admissible
        (proof_sequence_code_trace rows)
  have hPrefix :
      Term.Admissible (numₘ(prefixCode)) SetSort.set :=
    finite_numeral_term_admissible prefixCode
  have hRowCode :
      Term.Admissible (numₘ(rowCode)) SetSort.set :=
    finite_numeral_term_admissible rowCode
  have hIndexTerm :
      Term.Admissible (numₘ(index)) SetSort.set :=
    finite_numeral_term_admissible index
  have hTraceCurrentGet :
      (proof_sequence_code_trace rows)[index]? =
        some prefixCode := by
    simpa [prefixCode, proof_sequence_code_trace] using
      proof_sequence_code_trace_from_getElem?
        0 rows index (Nat.le_of_lt hIndex)
  have hTraceNextGet :
      (proof_sequence_code_trace rows)[index + 1]? =
        some (nat_sequence_code_step prefixCode rowCode) := by
    simpa [prefixCode, rowCode] using
      proof_sequence_code_trace_step rows index row hRow
  have hCurrentStd :
      Derives standard_sequence_semantics_theory [] (
        trace ·ₘ numₘ(index) ≐ₘ numₘ(prefixCode)) := by
    simpa [trace] using
      standard_token_sequence_apply_getElem?
        (proof_sequence_code_trace rows) hTraceCurrentGet
  have hNextStd :
      Derives standard_sequence_semantics_theory [] (
        trace ·ₘ numₘ(index + 1) ≐ₘ
          numₘ(nat_sequence_code_step prefixCode rowCode)) := by
    simpa [trace] using
      standard_token_sequence_apply_getElem?
        (proof_sequence_code_trace rows) hTraceNextGet
  have hCurrent :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(index) ≐ₘ numₘ(prefixCode)) :=
    fs_zfc_support_raw_derives_of_standard_sequence hCurrentStd
  have hNext :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(index + 1) ≐ₘ
          numₘ(nat_sequence_code_step prefixCode rowCode)) :=
    fs_zfc_support_raw_derives_of_standard_sequence hNextStd
  have hTraceCurrent :
      Term.Admissible (trace ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      trace (numₘ(index)) hTrace hIndexTerm
  have hPairLeft :
      Term.Admissible
        (⟨trace ·ₘ numₘ(index), numₘ(rowCode)⟩ₘ)
        SetSort.set :=
    ordered_pair_term_admissible
      (trace ·ₘ numₘ(index)) (numₘ(rowCode))
      hTraceCurrent hRowCode
  have hPairRight :
      Term.Admissible
        (⟨numₘ(prefixCode), numₘ(rowCode)⟩ₘ)
        SetSort.set :=
    ordered_pair_term_admissible
      (numₘ(prefixCode)) (numₘ(rowCode))
      hPrefix hRowCode
  have hPairEquality :
      Derives fs_zfc_support_raw_theory [] (
        ⟨trace ·ₘ numₘ(index), numₘ(rowCode)⟩ₘ ≐ₘ
          ⟨numₘ(prefixCode), numₘ(rowCode)⟩ₘ) :=
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun left right => ⟨left, right⟩ₘ)
      (fun left right hLeft hRight =>
        ordered_pair_term_admissible left right hLeft hRight)
      (by intros; simp [Term.substituteFree])
      (trace ·ₘ numₘ(index)) (numₘ(prefixCode))
      (numₘ(rowCode)) (numₘ(rowCode))
      hTraceCurrent hPrefix hRowCode hRowCode
      hCurrent
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(rowCode)))
  have hGodelPairEquality :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairₘ(⟨trace ·ₘ numₘ(index), numₘ(rowCode)⟩ₘ) ≐ₘ
          godel_pairₘ(⟨numₘ(prefixCode), numₘ(rowCode)⟩ₘ)) :=
    Metatheory.Derives.unary_term_constructor_congr_of_equality
      (fun pair => godel_pairₘ(pair))
      (fun pair hPair => godel_pairing_term_admissible pair hPair)
      (by intros; simp [Term.substituteFree])
      (⟨trace ·ₘ numₘ(index), numₘ(rowCode)⟩ₘ)
      (⟨numₘ(prefixCode), numₘ(rowCode)⟩ₘ)
      hPairLeft hPairRight hPairEquality
  have hGodelPairValue :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairₘ(⟨numₘ(prefixCode), numₘ(rowCode)⟩ₘ) ≐ₘ
          numₘ(godel_pair_value prefixCode rowCode)) :=
    fs_zfc_support_raw_godel_pair_value_eq prefixCode rowCode
  have hPairValue :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairₘ(⟨trace ·ₘ numₘ(index), numₘ(rowCode)⟩ₘ) ≐ₘ
          numₘ(godel_pair_value prefixCode rowCode)) :=
    Metatheory.Derives.equality_trans
      hGodelPairEquality hGodelPairValue
  have hSuccessorPairValue :
      Derives fs_zfc_support_raw_theory [] (
        Sₘ(godel_pairₘ(
          ⟨trace ·ₘ numₘ(index), numₘ(rowCode)⟩ₘ)) ≐ₘ
          Sₘ(numₘ(godel_pair_value prefixCode rowCode))) :=
    successor_term_congr_of_equality
      (godel_pairₘ(
        ⟨trace ·ₘ numₘ(index), numₘ(rowCode)⟩ₘ))
      (numₘ(godel_pair_value prefixCode rowCode))
      (godel_pairing_term_admissible
        (⟨trace ·ₘ numₘ(index), numₘ(rowCode)⟩ₘ)
        hPairLeft)
      (finite_numeral_term_admissible
        (godel_pair_value prefixCode rowCode))
      hPairValue
  have hNextValue :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(index + 1) ≐ₘ
          Sₘ(numₘ(godel_pair_value prefixCode rowCode))) := by
    simpa [nat_sequence_code_step, finite_numeral_term,
      successor_term] using hNext
  have hSuccessorPairValueBack :
      Derives fs_zfc_support_raw_theory [] (
        Sₘ(numₘ(godel_pair_value prefixCode rowCode)) ≐ₘ
          Sₘ(godel_pairₘ(
            ⟨trace ·ₘ numₘ(index), numₘ(rowCode)⟩ₘ))) :=
    Metatheory.Derives.equality_symm
      hSuccessorPairValue
  have hResult :=
    Metatheory.Derives.equality_trans
      hNextValue hSuccessorPairValueBack
  simpa [trace, rowCode, finite_numeral_term,
    successor_term] using hResult

/-- 公式行序列的一步同时满足行码递推与内层 token 序列递推。 -/
private theorem fs_zfc_support_raw_proof_sequence_step_at_numeral
    {proof : List SetFormula}
    (index : Nat)
    (formula : SetFormula)
    (hIndex : index < proof.length)
    (hGet : proof[index]? = some formula)
    (rowTraceId rowIndexId : FreeVarId)
    (hRowIds : rowTraceId ≠ rowIndexId) :
    Derives fs_zfc_support_raw_theory [] (
      proof_sequence_code_step_condition_with_ids
        (standard_sequence
          (proof.map
            (fun formula =>
              standard_token_sequence
                (certified_row_tokens formula))))
        (standard_token_sequence
          (proof_sequence_code_trace
            (proof.map certified_row_tokens)))
        (numₘ(index))
        (numₘ(nat_sequence_code_value
          (certified_row_tokens formula)))
        rowTraceId rowIndexId) := by
  let rows : List (List Nat) :=
    proof.map certified_row_tokens
  let elements : List SetTerm :=
    proof.map
      (fun formula =>
        standard_token_sequence (certified_row_tokens formula))
  let sequence : SetTerm :=
    standard_sequence elements
  let trace : SetTerm :=
    standard_token_sequence (proof_sequence_code_trace rows)
  let rowCode : Nat :=
    nat_sequence_code_value (certified_row_tokens formula)
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, hRow, rfl⟩
    exact standard_token_sequence_admissible
      (certified_row_tokens row)
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, hRow, rfl⟩
    exact standard_token_sequence_freeSupport_nil
      (certified_row_tokens row)
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence, elements] using
      seq_admissible_m 0 hElements
  have hSequenceClosed :
      Term.freeSupport sequence = [] := by
    simpa [sequence, elements] using
      seq_support_nil_m 0 hElementsClosed
  have hIndexTerm :
      Term.Admissible (numₘ(index)) SetSort.set :=
    finite_numeral_term_admissible index
  have hSequenceAt :
      Term.Admissible (sequence ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      sequence (numₘ(index)) hSequence hIndexTerm
  have hSequenceAtClosed :
      Term.freeSupport (sequence ·ₘ numₘ(index)) = [] := by
    simp [Term.freeSupport, Term.freeSupportList,
      hSequenceClosed, finite_numeral_term_freeSupport]
  have hSequenceAtBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (sequence ·ₘ numₘ(index)) :=
    ⟨hSequenceAt, hSequenceAtClosed⟩
  have hRightBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (standard_token_sequence
          (certified_row_tokens formula)) :=
    ⟨standard_token_sequence_admissible
        (certified_row_tokens formula),
      standard_token_sequence_freeSupport_nil
        (certified_row_tokens formula)⟩
  have hCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary (numₘ(rowCode)) :=
    ⟨finite_numeral_term_admissible rowCode,
      finite_numeral_term_freeSupport rowCode⟩
  have hSequenceValue :
      Derives fs_zfc_support_raw_theory [] (
        sequence ·ₘ numₘ(index) ≐ₘ
          standard_token_sequence
            (certified_row_tokens formula)) := by
    have hMapped :
        elements[index]? =
          some (standard_token_sequence
            (certified_row_tokens formula)) := by
      simpa [elements] using congrArg
        (Option.map
          (fun formula =>
            standard_token_sequence
              (certified_row_tokens formula)))
        hGet
    have hElement :
        Term.Admissible
          (standard_token_sequence
            (certified_row_tokens formula))
          SetSort.set :=
      standard_token_sequence_admissible
        (certified_row_tokens formula)
    have hStandard :=
      GodelQuotation.standard_sequence_from_apply_getElem?
        0 hMapped hElements hElementsClosed hElement
    have hRaw :=
      fs_zfc_support_raw_derives_of_standard_sequence hStandard
    simpa [sequence, elements, standard_sequence] using hRaw
  have hInnerStd :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (standard_token_sequence
            (certified_row_tokens formula))
          (numₘ(rowCode))
          rowTraceId rowIndexId) := by
    simpa [rowCode] using
      fs_zfc_support_raw_nat_sequence_code_condition_with_ids
        (certified_row_tokens formula)
        rowTraceId rowIndexId hRowIds
  have hInnerTransport :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (sequence ·ₘ numₘ(index))
          (numₘ(rowCode))
          rowTraceId rowIndexId ↔ₘ
        nat_sequence_code_condition_with_ids
          (standard_token_sequence
            (certified_row_tokens formula))
          (numₘ(rowCode))
          rowTraceId rowIndexId) :=
    fs_zfc_support_raw_nat_sequence_code_condition_with_ids_iff_of_sequence_equality
      (sequence ·ₘ numₘ(index))
      (standard_token_sequence
        (certified_row_tokens formula))
      (numₘ(rowCode))
      rowTraceId rowIndexId
      hSequenceAtBoundary hRightBoundary hCodeBoundary
      hSequenceValue
  have hInner :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (sequence ·ₘ numₘ(index))
          (numₘ(rowCode))
          rowTraceId rowIndexId) :=
    FirstOrder.Derives.iffElimLeft hInnerTransport hInnerStd
  have hOuter :
      Derives fs_zfc_support_raw_theory [] (
        let trace :=
          standard_token_sequence
            (proof_sequence_code_trace rows)
        (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
          Sₘ(godel_pairₘ(⟨
            trace ·ₘ numₘ(index),
            numₘ(rowCode)⟩ₘ))) :=
    by
      simpa [rows, rowCode] using
        fs_zfc_support_raw_proof_sequence_outer_step_at_numeral
          rows index (certified_row_tokens formula)
          (by simpa [rows] using hIndex)
          (by
            simpa [rows] using congrArg
              (Option.map certified_row_tokens) hGet)
  simpa [proof_sequence_code_step_condition_with_ids,
    rows, sequence, trace, rowCode] using
    FirstOrder.Derives.conjIntro hInner hOuter

/-! ## 外层 index 等式与行码见证 -/

/-- 外层 index 等于具体 numeral 时，可引入对应的行码见证。 -/
private theorem fs_zfc_support_raw_proof_sequence_step_of_index_equality
    (index : Nat)
    (sequence trace totalCode point rowCode : SetTerm)
    (rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hSequence :
      GodelQuotation.Numbered.CodeBoundary sequence)
    (hTrace :
      GodelQuotation.Numbered.CodeBoundary trace)
    (hTotalCode :
      GodelQuotation.Numbered.CodeBoundary totalCode)
    (hPoint :
      Term.Admissible point SetSort.set)
    (hPointFreshRowCode :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport point)
    (hPointFreshRowTrace :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport point)
    (hPointFreshRowIndex :
      (SetSort.set, rowIndexId) ∉ Term.freeSupport point)
    (hRowCode :
      GodelQuotation.Numbered.CodeBoundary rowCode)
    (hRowCodeNeRowTrace : rowCodeId ≠ rowTraceId)
    (hRowCodeNeRowIndex : rowCodeId ≠ rowIndexId)
    (hRowCodeBound :
      Derives fs_zfc_support_raw_theory [] (
        rowCode ∈ₘ totalCode))
    (hConcrete :
      Derives fs_zfc_support_raw_theory [] (
        proof_sequence_code_step_condition_with_ids
          sequence trace (numₘ(index)) rowCode
          rowTraceId rowIndexId)) :
    Derives fs_zfc_support_raw_theory [] (
      (point ≐ₘ numₘ(index)) ⟶ₘ
        (∃ₘ[SetSort.set, rowCodeId],
          ((x#rowCodeId ∈ₘ totalCode) ∧ₘ
            proof_sequence_code_step_condition_with_ids
              sequence trace point (x#rowCodeId)
              rowTraceId rowIndexId))) := by
  let parameter : FreeVarId :=
    rowCodeId + rowTraceId + rowIndexId + 1
  let stepBody : SetFormula :=
    (x#rowCodeId ∈ₘ totalCode) ∧ₘ
      proof_sequence_code_step_condition_with_ids
        sequence trace (x#parameter) (x#rowCodeId)
        rowTraceId rowIndexId
  let body : SetFormula :=
    ∃ₘ[SetSort.set, rowCodeId], stepBody
  let equality : SetFormula :=
    point ≐ₘ numₘ(index)
  let Γ : Context signature :=
    [equality]
  have hParameterNeRowCode :
      parameter ≠ rowCodeId := by
    change rowCodeId + rowTraceId + rowIndexId + 1 ≠ rowCodeId
    intro hEquality
    have hLess :
        rowCodeId < rowCodeId + rowTraceId + rowIndexId + 1 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.lt_add_right (rowTraceId + rowIndexId)
          (Nat.lt_succ_self rowCodeId)
    exact (Nat.ne_of_lt hLess) hEquality.symm
  have hParameterNeRowTrace :
      parameter ≠ rowTraceId := by
    change rowCodeId + rowTraceId + rowIndexId + 1 ≠ rowTraceId
    intro hEquality
    have hLess :
        rowTraceId < rowCodeId + rowTraceId + rowIndexId + 1 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.lt_add_right (rowCodeId + rowIndexId)
          (Nat.lt_succ_self rowTraceId)
    exact (Nat.ne_of_lt hLess) hEquality.symm
  have hParameterNeRowIndex :
      parameter ≠ rowIndexId := by
    change rowCodeId + rowTraceId + rowIndexId + 1 ≠ rowIndexId
    intro hEquality
    have hLess :
        rowIndexId < rowCodeId + rowTraceId + rowIndexId + 1 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.lt_add_right (rowCodeId + rowTraceId)
          (Nat.lt_succ_self rowIndexId)
    exact (Nat.ne_of_lt hLess) hEquality.symm
  have hStepBodyAdmissible :
      Formula.Admissible stepBody := by
    simpa [stepBody] using
      Formula.Admissible.conj
        (membership_formula_admissible
          (set_variable_admissible rowCodeId) hTotalCode.1)
        (proof_sequence_code_step_condition_with_ids_admissible
          sequence trace (x#parameter) (x#rowCodeId)
          rowTraceId rowIndexId
          hSequence.1 hTrace.1
          (set_variable_admissible parameter)
          (set_variable_admissible rowCodeId))
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set rowCodeId hStepBodyAdmissible
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] equality := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (φ := equality)
        (by simp [Γ]))
  have hSequenceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement sequence =
        sequence :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hSequence parameter replacement
  have hTraceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement trace =
        trace :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hTrace parameter replacement
  have hTotalCodeFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement totalCode =
        totalCode :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hTotalCode parameter replacement
  have hSubstitution (replacement : SetTerm)
      (hReplacement : Term.Admissible replacement SetSort.set)
      (hReplacementFreshRowCode :
        (SetSort.set, rowCodeId) ∉ Term.freeSupport replacement)
      (hReplacementFreshRowTrace :
        (SetSort.set, rowTraceId) ∉ Term.freeSupport replacement)
      (hReplacementFreshRowIndex :
        (SetSort.set, rowIndexId) ∉ Term.freeSupport replacement) :
      Formula.substituteFree SetSort.set parameter replacement body =
        (∃ₘ[SetSort.set, rowCodeId],
          ((x#rowCodeId ∈ₘ totalCode) ∧ₘ
            proof_sequence_code_step_condition_with_ids
              sequence trace replacement (x#rowCodeId)
              rowTraceId rowIndexId)) := by
    have hRowCodeComm (subformula : SetFormula) :
        Formula.closeFreeAt SetSort.set rowCodeId 0
            (Formula.substituteFree SetSort.set parameter replacement
              subformula) =
          Formula.substituteFree SetSort.set parameter replacement
            (Formula.closeFreeAt SetSort.set rowCodeId 0 subformula) :=
      Formula.closeFreeAt_substituteFree_comm
        SetSort.set parameter rowCodeId 0 replacement subformula
        hParameterNeRowCode hReplacement.2
        hReplacementFreshRowCode
    have hRowTraceComm (subformula : SetFormula) :
        Formula.closeFreeAt SetSort.set rowTraceId 0
            (Formula.substituteFree SetSort.set parameter replacement
              subformula) =
          Formula.substituteFree SetSort.set parameter replacement
            (Formula.closeFreeAt SetSort.set rowTraceId 0 subformula) :=
      Formula.closeFreeAt_substituteFree_comm
        SetSort.set parameter rowTraceId 0 replacement subformula
        hParameterNeRowTrace hReplacement.2
        hReplacementFreshRowTrace
    have hRowIndexComm (subformula : SetFormula) :
        Formula.closeFreeAt SetSort.set rowIndexId 0
            (Formula.substituteFree SetSort.set parameter replacement
              subformula) =
          Formula.substituteFree SetSort.set parameter replacement
            (Formula.closeFreeAt SetSort.set rowIndexId 0 subformula) :=
      Formula.closeFreeAt_substituteFree_comm
        SetSort.set parameter rowIndexId 0 replacement subformula
        hParameterNeRowIndex hReplacement.2
        hReplacementFreshRowIndex
    have hParameterSubstitution :
        Term.substituteFree SetSort.set parameter replacement
            (x#parameter) =
          replacement := by
      simp [Term.substituteFree, set_variable]
    have hRowCodeFixed :
        Term.substituteFree SetSort.set parameter replacement
            (x#rowCodeId) =
          x#rowCodeId := by
      simp [Term.substituteFree, set_variable,
        Ne.symm hParameterNeRowCode]
    have hNumeralFixed (value : Nat) :
        Term.substituteFree SetSort.set parameter replacement
            (numₘ(value)) =
          numₘ(value) := by
      apply Term.substituteFree_eq_self_of_not_mem
      rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil
    have hInnerStepSubstitution :
        Formula.substituteFree SetSort.set parameter replacement
            (nat_sequence_code_step_condition
              (sequence ·ₘ (x#parameter))
              (x#rowTraceId) (x#rowIndexId)) =
          nat_sequence_code_step_condition
            (sequence ·ₘ replacement)
            (x#rowTraceId) (x#rowIndexId) := by
      simp [nat_sequence_code_step_condition,
        Formula.substituteFree, Term.substituteFree, set_variable,
        hSequenceFixed replacement, hParameterSubstitution,
        Ne.symm hParameterNeRowTrace,
        Ne.symm hParameterNeRowIndex]
    have hStepSubstitution :
        Formula.substituteFree SetSort.set parameter replacement stepBody =
          ((x#rowCodeId ∈ₘ totalCode) ∧ₘ
            proof_sequence_code_step_condition_with_ids
              sequence trace replacement (x#rowCodeId)
              rowTraceId rowIndexId) := by
      simp [stepBody, proof_sequence_code_step_condition_with_ids,
        nat_sequence_code_condition_with_ids,
        sequence_domain_code_bound,
        nat_sequence_value_code_bound_with_id,
        sequence_trace_code_bound_with_id,
        Formula.substituteFree, Term.substituteFree, set_variable,
        hSequenceFixed replacement, hTraceFixed replacement,
        hTotalCodeFixed replacement,
        hParameterSubstitution, hRowCodeFixed, hNumeralFixed 0,
        hInnerStepSubstitution,

        Ne.symm hParameterNeRowTrace,
        Ne.symm hParameterNeRowIndex,
        ← hRowTraceComm, ← hRowIndexComm]
    simp [body, Formula.substituteFree,
      hStepSubstitution, ← hRowCodeComm]
  have hTransport :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (∃ₘ[SetSort.set, rowCodeId],
          ((x#rowCodeId ∈ₘ totalCode) ∧ₘ
            proof_sequence_code_step_condition_with_ids
              sequence trace point (x#rowCodeId)
              rowTraceId rowIndexId)) ↔ₘ
        (∃ₘ[SetSort.set, rowCodeId],
          ((x#rowCodeId ∈ₘ totalCode) ∧ₘ
            proof_sequence_code_step_condition_with_ids
              sequence trace (numₘ(index)) (x#rowCodeId)
              rowTraceId rowIndexId)) := by
    have hIff :=
      Metatheory.Derives.equality_iff_of_equality
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (sort := SetSort.set)
        (eigen := parameter)
        (left := point)
        (right := numₘ(index))
        (body := body)
        hEquality
    simpa [hSubstitution point hPoint
        hPointFreshRowCode hPointFreshRowTrace hPointFreshRowIndex,
      hSubstitution (numₘ(index))
        (finite_numeral_term_admissible index)
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)] using hIff
  have hConcreteContext :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        proof_sequence_code_step_condition_with_ids
          sequence trace (numₘ(index)) rowCode
          rowTraceId rowIndexId :=
    FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp [Γ])
      hConcrete
  have hRowTraceWitnessComm (subformula : SetFormula) :
      Formula.closeFreeAt SetSort.set rowTraceId 0
          (Formula.substituteFree SetSort.set rowCodeId rowCode
            subformula) =
        Formula.substituteFree SetSort.set rowCodeId rowCode
          (Formula.closeFreeAt SetSort.set rowTraceId 0 subformula) :=
    Formula.closeFreeAt_substituteFree_comm
      SetSort.set rowCodeId rowTraceId 0 rowCode subformula
      hRowCodeNeRowTrace hRowCode.1.2
      (by rw [hRowCode.2]; exact List.not_mem_nil)
  have hRowIndexWitnessComm (subformula : SetFormula) :
      Formula.closeFreeAt SetSort.set rowIndexId 0
          (Formula.substituteFree SetSort.set rowCodeId rowCode
            subformula) =
        Formula.substituteFree SetSort.set rowCodeId rowCode
          (Formula.closeFreeAt SetSort.set rowIndexId 0 subformula) :=
    Formula.closeFreeAt_substituteFree_comm
      SetSort.set rowCodeId rowIndexId 0 rowCode subformula
      hRowCodeNeRowIndex hRowCode.1.2
      (by rw [hRowCode.2]; exact List.not_mem_nil)
  have hSequenceWitnessFixed :
      Term.substituteFree SetSort.set rowCodeId rowCode sequence =
        sequence :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hSequence rowCodeId rowCode
  have hTraceWitnessFixed :
      Term.substituteFree SetSort.set rowCodeId rowCode trace =
        trace :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hTrace rowCodeId rowCode
  have hTotalCodeWitnessFixed :
      Term.substituteFree SetSort.set rowCodeId rowCode totalCode =
        totalCode :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hTotalCode rowCodeId rowCode
  have hNumeralWitnessFixed (value : Nat) :
      Term.substituteFree SetSort.set rowCodeId rowCode (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hRowCodeWitnessVariable :
      Term.substituteFree SetSort.set rowCodeId rowCode
          (x#rowCodeId) =
        rowCode := by
    simp [Term.substituteFree, set_variable]
  have hInnerWitnessSubstitution :
      Formula.substituteFree SetSort.set rowCodeId rowCode
          (nat_sequence_code_step_condition
            (sequence ·ₘ numₘ(index))
            (x#rowTraceId) (x#rowIndexId)) =
        nat_sequence_code_step_condition
          (sequence ·ₘ numₘ(index))
          (x#rowTraceId) (x#rowIndexId) := by
    simp [nat_sequence_code_step_condition,
      Formula.substituteFree, Term.substituteFree, set_variable,
      hSequenceWitnessFixed, hNumeralWitnessFixed index,
      Ne.symm hRowCodeNeRowTrace,
      Ne.symm hRowCodeNeRowIndex]
  have hStepWitnessSubstitution :
      Formula.substituteFree SetSort.set rowCodeId rowCode
          (proof_sequence_code_step_condition_with_ids
            sequence trace (numₘ(index)) (x#rowCodeId)
            rowTraceId rowIndexId) =
        proof_sequence_code_step_condition_with_ids
          sequence trace (numₘ(index)) rowCode
          rowTraceId rowIndexId := by
    simp [proof_sequence_code_step_condition_with_ids,
      nat_sequence_code_condition_with_ids,
      sequence_domain_code_bound,
      nat_sequence_value_code_bound_with_id,
      sequence_trace_code_bound_with_id,
      Formula.substituteFree, Term.substituteFree, set_variable,
      hSequenceWitnessFixed, hTraceWitnessFixed,
      hNumeralWitnessFixed index, hNumeralWitnessFixed 0,
      hRowCodeWitnessVariable,
      hInnerWitnessSubstitution,
      Ne.symm hRowCodeNeRowTrace,
      Ne.symm hRowCodeNeRowIndex,
      ← hRowTraceWitnessComm, ← hRowIndexWitnessComm]
  have hConcreteSubstituted :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Formula.substituteFree SetSort.set rowCodeId rowCode
          ((x#rowCodeId ∈ₘ totalCode) ∧ₘ
            proof_sequence_code_step_condition_with_ids
              sequence trace (numₘ(index)) (x#rowCodeId)
              rowTraceId rowIndexId) := by
    simpa [Formula.substituteFree,
      hRowCodeWitnessVariable, hTotalCodeWitnessFixed,
      hStepWitnessSubstitution] using
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp [Γ]) hRowCodeBound)
        hConcreteContext)
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (∃ₘ[SetSort.set, rowCodeId],
          ((x#rowCodeId ∈ₘ totalCode) ∧ₘ
            proof_sequence_code_step_condition_with_ids
              sequence trace (numₘ(index)) (x#rowCodeId)
              rowTraceId rowIndexId)) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := rowCode) rowCodeId hConcreteSubstituted
  exact FirstOrder.Derives.iffElimLeft hTransport hExists

/-! ## 完整公式证明序列条件 -/

/-- 具体有限公式序列的二维 Gödel 证明码条件。 -/
theorem fs_zfc_support_raw_proof_sequence_code_condition_with_ids
    {proof : List SetFormula}
    (hRows :
      ∀ formula, formula ∈ proof →
        Formula.Admissible formula)
    (hNonempty : proof ≠ [])
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceNeRowCode : traceId ≠ rowCodeId)
    (hTraceNeRowTrace : traceId ≠ rowTraceId)
    (hTraceNeRowIndex : traceId ≠ rowIndexId)
    (hIndexNeRowCode : indexId ≠ rowCodeId)
    (hIndexNeRowTrace : indexId ≠ rowTraceId)
    (hIndexNeRowIndex : indexId ≠ rowIndexId)
    (hRowCodeNeRowTrace : rowCodeId ≠ rowTraceId)
    (hRowCodeNeRowIndex : rowCodeId ≠ rowIndexId)
    (hRowTraceNeRowIndex : rowTraceId ≠ rowIndexId) :
    Derives fs_zfc_support_raw_theory [] (
      proof_sequence_code_condition_with_ids
        (standard_sequence
          (proof.map (fun formula =>
            standard_token_sequence (certified_row_tokens formula))))
        (numₘ(proof_sequence_code_value
          (proof.map certified_row_tokens)))
        traceId indexId rowCodeId rowTraceId rowIndexId) := by
  let rows : List (List Nat) :=
    proof.map certified_row_tokens
  let elements : List SetTerm :=
    proof.map (fun formula =>
      standard_token_sequence (certified_row_tokens formula))
  let sequence : SetTerm :=
    standard_sequence elements
  let code : SetTerm :=
    numₘ(proof_sequence_code_value rows)
  let trace : SetTerm :=
    standard_token_sequence (proof_sequence_code_trace rows)
  let index : SetTerm :=
    x#indexId
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact standard_token_sequence_admissible
      (certified_row_tokens formula)
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact standard_token_sequence_freeSupport_nil
      (certified_row_tokens formula)
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence, elements] using
      seq_admissible_m 0 hElements
  have hSequenceClosed :
      Term.freeSupport sequence = [] := by
    simpa [sequence, elements] using
      seq_support_nil_m 0 hElementsClosed
  have hSequenceBoundary :
      GodelQuotation.Numbered.CodeBoundary sequence :=
    ⟨hSequence, hSequenceClosed⟩
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      finite_numeral_term_admissible
        (proof_sequence_code_value rows)
  have hCodeBoundary :
      GodelQuotation.Numbered.CodeBoundary code :=
    ⟨hCode, by
      simpa [code] using
        finite_numeral_term_freeSupport
          (proof_sequence_code_value rows)⟩
  have hTrace :
      Term.Admissible trace SetSort.set := by
    simpa [trace] using
      standard_token_sequence_admissible
        (proof_sequence_code_trace rows)
  have hTraceClosed :
      Term.freeSupport trace = [] := by
    simp [trace]
  have hTraceBoundary :
      GodelQuotation.Numbered.CodeBoundary trace :=
    ⟨hTrace, hTraceClosed⟩
  have hSequenceSpacePositive :
      Derives fs_zfc_support_raw_theory [] (
        sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) := by
    simpa [sequence, elements] using
      fs_zfc_support_raw_standard_formula_code_sequence_space
        hRows hNonempty
  have hSequenceSpace :
      Derives fs_zfc_support_raw_theory [] (
        sequence ∈ₘ seq_spaceₘ(FormulaCodeₘ)) := by
    have hFormulaCodeNonempty :
        Derives fs_zfc_support_raw_theory [] (
          FormulaCodeₘ ≠ₘ ∅ₘ) :=
      fs_zfc_support_raw_derives_of_godel_quotation
        GodelQuotation.formula_code_set_nonempty_derives
    have hConversion :
        Derives fs_zfc_support_raw_theory [] (
          (FormulaCodeₘ ≠ₘ ∅ₘ) ⟶ₘ
            ((sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ⟶ₘ
              (sequence ∈ₘ seq_spaceₘ(FormulaCodeₘ)))) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (nonempty_sequence_space_member_implies_sequence_space
          FormulaCodeₘ sequence formula_code_set_term_admissible
          hSequence)
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        hConversion hFormulaCodeNonempty)
      hSequenceSpacePositive
  have hCodeOmega :
      Derives fs_zfc_support_raw_theory [] (code ∈ₘ ωₘ) := by
    have hCodeOmegaStd :
        Derives standard_sequence_semantics_theory [] (
          numₘ(proof_sequence_code_value rows) ∈ₘ ωₘ) :=
      standard_sequence_finite_numeral_mem_omega
        (proof_sequence_code_value rows)
    exact fs_zfc_support_raw_derives_of_standard_sequence
      (by simpa [code] using hCodeOmegaStd)
  have hSequenceDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ numₘ(proof.length)) := by
    have hSequenceDomainStd :
        Derives standard_sequence_semantics_theory [] (
          domₘ(standard_sequence elements) ≐ₘ
            numₘ(elements.length)) :=
      standard_sequence_domain_eq_numeral_length
        hElements
        (stdseq_element_fresh_of_support_nil hElementsClosed 0)
        (stdseq_element_fresh_of_support_nil hElementsClosed 1)
    simpa [sequence, elements] using
      fs_zfc_support_raw_derives_of_standard_sequence
        hSequenceDomainStd
  have hSequenceDomainBound :
      Derives fs_zfc_support_raw_theory [] (
        sequence_domain_code_bound sequence code) := by
    apply fs_zfc_support_raw_sequence_domain_code_bound_of_domain_eq
      sequence proof.length (proof_sequence_code_value rows)
      hSequence hSequenceDomain
    simpa [rows] using proof_sequence_length_le_code rows
  have hTraceDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(trace) ≐ₘ
          numₘ((proof_sequence_code_trace rows).length)) := by
    have hTraceDomainStd :
        Derives standard_sequence_semantics_theory [] (
          domₘ(standard_token_sequence
            (proof_sequence_code_trace rows)) ≐ₘ
            numₘ((proof_sequence_code_trace rows).length)) :=
      standard_token_sequence_domain_eq_length
        (proof_sequence_code_trace rows)
    simpa [trace] using
      fs_zfc_support_raw_derives_of_standard_sequence
        hTraceDomainStd
  have hTraceDomainNumeral :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(trace) ≐ₘ Sₘ(numₘ(proof.length))) := by
    simpa [proof_sequence_code_trace_length, rows,
      finite_numeral_term, successor_term] using
      hTraceDomain
  have hSequenceDomainSymm :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(proof.length) ≐ₘ domₘ(sequence)) :=
    Metatheory.Derives.equality_symm
      hSequenceDomain
  have hSuccessorDomain :
      Derives fs_zfc_support_raw_theory [] (
        Sₘ(numₘ(proof.length)) ≐ₘ Sₘ(domₘ(sequence))) :=
    successor_term_congr_of_equality
      (numₘ(proof.length)) (domₘ(sequence))
      (finite_numeral_term_admissible proof.length)
      (domain_term_admissible sequence hSequence)
      hSequenceDomainSymm
  have hTraceDomainFinal :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))) :=
    Metatheory.Derives.equality_trans
      hTraceDomainNumeral hSuccessorDomain
  have hInitial :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(0) ≐ₘ numₘ(0)) := by
    have hTraceZero :
        (proof_sequence_code_trace rows)[0]? = some 0 := by
      simpa [proof_sequence_code_trace, proof_sequence_code_from,
        nat_sequence_code_from] using
        proof_sequence_code_trace_from_getElem?
          0 rows 0 (Nat.zero_le _)
    have hInitialStd :
        Derives standard_sequence_semantics_theory [] (
          standard_token_sequence (proof_sequence_code_trace rows) ·ₘ
              numₘ(0) ≐ₘ numₘ(0)) :=
      standard_token_sequence_apply_getElem?
        (proof_sequence_code_trace rows) hTraceZero
    exact fs_zfc_support_raw_derives_of_standard_sequence
      (by simpa [trace] using hInitialStd)
  have hPoint :
      Term.Admissible index SetSort.set := by
    simpa [index] using set_variable_admissible indexId
  have hDomainIff :
      Derives fs_zfc_support_raw_theory [] (
        (index ∈ₘ domₘ(sequence)) ↔ₘ
          (index ∈ₘ numₘ(proof.length))) :=
    membership_right_iff_of_equality
      index (domₘ(sequence)) (numₘ(proof.length))
      hPoint
      (domain_term_admissible sequence hSequence)
      (finite_numeral_term_admissible proof.length)
      hSequenceDomain
  let stepConclusion : SetFormula :=
    ∃ₘ[SetSort.set, rowCodeId],
      ((x#rowCodeId ∈ₘ code) ∧ₘ
        proof_sequence_code_step_condition_with_ids
          sequence trace index (x#rowCodeId)
          rowTraceId rowIndexId)
  have hStepConclusion :
      Formula.Admissible stepConclusion := by
    have hStepBody :=
      Formula.Admissible.conj
        (membership_formula_admissible
          (set_variable_admissible rowCodeId) hCode)
        (proof_sequence_code_step_condition_with_ids_admissible
          sequence trace index (x#rowCodeId)
          rowTraceId rowIndexId
          hSequence hTrace hPoint
          (set_variable_admissible rowCodeId))
    simpa [stepConclusion] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set rowCodeId hStepBody
  have hNumeralStep :
      Derives fs_zfc_support_raw_theory [] (
        (stdseq_numeral_member_condition proof.length index) ⟶ₘ
          stepConclusion) := by
    simpa [stepConclusion] using
      stdseq_numeral_member_condition_elim_of_theory
        proof.length index stepConclusion
        (fun branch hBranch => by
          let formula : SetFormula := proof[branch]
          have hGet : proof[branch]? = some formula :=
            List.getElem?_eq_some_iff.mpr
              ⟨hBranch, rfl⟩
          have hConcrete :
              Derives fs_zfc_support_raw_theory [] (
                proof_sequence_code_step_condition_with_ids
                  sequence trace (numₘ(branch))
                  (numₘ(nat_sequence_code_value
                    (certified_row_tokens formula)))
                  rowTraceId rowIndexId) := by
            simpa [sequence, elements, trace, rows, formula] using
              fs_zfc_support_raw_proof_sequence_step_at_numeral
                branch formula hBranch hGet
                rowTraceId rowIndexId hRowTraceNeRowIndex
          let rowCode : SetTerm :=
            numₘ(nat_sequence_code_value
              (certified_row_tokens formula))
          have hRowCodeBoundary :
              GodelQuotation.Numbered.CodeBoundary rowCode := by
            simpa [rowCode] using
              (show GodelQuotation.Numbered.CodeBoundary
                  (numₘ(nat_sequence_code_value
                    (certified_row_tokens formula))) from
                ⟨finite_numeral_term_admissible _,
                  finite_numeral_term_freeSupport _⟩)
          have hFormulaMem : formula ∈ proof := by
            simp [formula]
          have hRowMem :
              certified_row_tokens formula ∈ rows := by
            simpa [rows] using
              List.mem_map.mpr
                ⟨formula, hFormulaMem, rfl⟩
          have hRowCodeBound :
              Derives fs_zfc_support_raw_theory [] (
                rowCode ∈ₘ code) := by
            simpa [rowCode, code] using
              fs_zfc_support_raw_derives_of_standard_sequence
                (standard_sequence_finite_numeral_mem_of_lt
                  (nat_sequence_code_value
                    (certified_row_tokens formula))
                  (proof_sequence_code_value rows)
                  (row_code_lt_proof_sequence_code_value hRowMem))
          have hPointFresh (binderId : FreeVarId)
              (hIndexNeBinder : indexId ≠ binderId) :
              (SetSort.set, binderId) ∉ Term.freeSupport index := by
            intro hMember
            change (SetSort.set, binderId) ∈
              [(SetSort.set, indexId)] at hMember
            have hPair :
                (SetSort.set, binderId) =
                  (SetSort.set, indexId) :=
              List.mem_singleton.mp hMember
            exact hIndexNeBinder
              (congrArg Prod.snd hPair).symm
          have hConcrete' :=
            fs_zfc_support_raw_proof_sequence_step_of_index_equality
              branch sequence trace code index rowCode
              rowCodeId rowTraceId rowIndexId
              hSequenceBoundary hTraceBoundary hCodeBoundary hPoint
              (hPointFresh rowCodeId hIndexNeRowCode)
              (hPointFresh rowTraceId hIndexNeRowTrace)
              (hPointFresh rowIndexId hIndexNeRowIndex)
              hRowCodeBoundary
              hRowCodeNeRowTrace hRowCodeNeRowIndex
              hRowCodeBound
              (by simpa [rowCode] using hConcrete)
          simpa [rowCode, stepConclusion] using hConcrete'
        )
  have hDomainStep :
      Derives fs_zfc_support_raw_theory [] (
        (index ∈ₘ domₘ(sequence)) ⟶ₘ stepConclusion) := by
    have hDomainToNumeral :
        Derives fs_zfc_support_raw_theory [] (
          (index ∈ₘ domₘ(sequence)) ⟶ₘ
            (index ∈ₘ numₘ(proof.length))) := by
      nd_apply FirstOrder.Derives.impIntro
      have hMember :
          [index ∈ₘ domₘ(sequence)] ⊢ₘ[fs_zfc_support_raw_theory]
            index ∈ₘ domₘ(sequence) :=
        .assumption (by simp)
      exact FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken_cons hDomainIff)
        hMember
    have hNumeralToCondition :
        Derives fs_zfc_support_raw_theory [] (
          (index ∈ₘ numₘ(proof.length)) ⟶ₘ
            (stdseq_numeral_member_condition proof.length index)) := by
      have hNumeralIff :
          Derives fs_zfc_support_raw_theory [] (
            (index ∈ₘ numₘ(proof.length)) ↔ₘ
              stdseq_numeral_member_condition proof.length index) :=
        fs_zfc_support_raw_derives_of_standard_sequence
          (stdseq_numeral_member_iff proof.length index hPoint)
      nd_apply FirstOrder.Derives.impIntro
      have hMember :
          [index ∈ₘ numₘ(proof.length)]
            ⊢ₘ[fs_zfc_support_raw_theory]
              index ∈ₘ numₘ(proof.length) :=
        .assumption (by simp)
      exact FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken_cons hNumeralIff)
        hMember
    exact Metatheory.Derives.imp_trans
      hDomainToNumeral
      (Metatheory.Derives.imp_trans
        hNumeralToCondition hNumeralStep)
  have hAllSteps :
      Derives fs_zfc_support_raw_theory [] (
        ∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ domₘ(sequence)) ⟶ₘ
            (∃ₘ[SetSort.set, rowCodeId],
              ((x#rowCodeId ∈ₘ code) ∧ₘ
                proof_sequence_code_step_condition_with_ids
                  sequence trace (bₛ#0) (x#rowCodeId)
                  rowTraceId rowIndexId))) := by
    have hTheoryFresh :
        ∀ formula, fs_zfc_support_raw_theory formula →
          (SetSort.set, indexId) ∉ Formula.freeSupport formula := by
      intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    have hSequenceFresh :
        (SetSort.set, indexId) ∉ Term.freeSupport sequence := by
      rw [hSequenceClosed]
      exact List.not_mem_nil
    have hTraceFresh :
        (SetSort.set, indexId) ∉ Term.freeSupport trace := by
      rw [hTraceClosed]
      exact List.not_mem_nil
    have hSequenceClose :
        Term.closeFreeAt SetSort.set indexId 0 sequence = sequence :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set indexId 0 sequence hSequence.2 hSequenceFresh
    have hTraceClose :
        Term.closeFreeAt SetSort.set indexId 0 trace = trace :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set indexId 0 trace hTrace.2 hTraceFresh
    have hSequenceCloseAt (binderId : FreeVarId) (depth : Nat) :
        Term.closeFreeAt SetSort.set binderId depth sequence =
          sequence :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set binderId depth sequence hSequence.2 (by
          rw [hSequenceClosed]
          exact List.not_mem_nil)
    have hTraceCloseAt (binderId : FreeVarId) (depth : Nat) :
        Term.closeFreeAt SetSort.set binderId depth trace = trace :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set binderId depth trace hTrace.2 (by
          rw [hTraceClosed]
          exact List.not_mem_nil)
    have hNumeralCloseAt (value : Nat) (binderId : FreeVarId)
        (depth : Nat) :
        Term.closeFreeAt SetSort.set binderId depth numₘ(value) =
          numₘ(value) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set binderId depth (numₘ(value))
        (finite_numeral_term_admissible value).2 (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    have hGeneralized :=
      FirstOrder.Derives.forall_intro
        (T := fs_zfc_support_raw_theory)
        (Γ := [])
        (sort := SetSort.set)
        (eigen := indexId)
        hTheoryFresh
        (by simp)
        hDomainStep
    simpa [index, stepConclusion, code, rows,
      proof_sequence_code_step_condition_with_ids,
      nat_sequence_code_condition_with_ids,
      sequence_domain_code_bound,
      nat_sequence_value_code_bound_with_id,
      sequence_trace_code_bound_with_id,
      nat_sequence_code_step_condition,
      Formula.closeFreeAt, Formula.freeSupport, Formula.next_depth,
      Term.closeFreeAt, set_variable,
      hSequenceClose, hTraceClose, hSequenceCloseAt, hTraceCloseAt,
      hNumeralCloseAt,
      hSequenceCloseAt rowCodeId 0,
      hSequenceCloseAt rowCodeId 1,
      hSequenceCloseAt rowCodeId 2,
      hSequenceCloseAt rowCodeId 3,
      hSequenceCloseAt rowTraceId 0,
      hSequenceCloseAt rowTraceId 1,
      hSequenceCloseAt rowTraceId 2,
      hSequenceCloseAt rowTraceId 3,
      hSequenceCloseAt rowIndexId 0,
      hSequenceCloseAt rowIndexId 1,
      hSequenceCloseAt rowIndexId 2,
      hSequenceCloseAt rowIndexId 3,
      hSequenceCloseAt indexId 0,
      hSequenceCloseAt indexId 1,
      hSequenceCloseAt indexId 2,
      hSequenceCloseAt indexId 3,
      hTraceCloseAt rowCodeId 0,
      hTraceCloseAt rowCodeId 1,
      hTraceCloseAt rowCodeId 2,
      hTraceCloseAt rowCodeId 3,
      hTraceCloseAt rowTraceId 0,
      hTraceCloseAt rowTraceId 1,
      hTraceCloseAt rowTraceId 2,
      hTraceCloseAt rowTraceId 3,
      hTraceCloseAt rowIndexId 0,
      hTraceCloseAt rowIndexId 1,
      hTraceCloseAt rowIndexId 2,
      hTraceCloseAt rowIndexId 3,
      hTraceCloseAt indexId 0,
      hTraceCloseAt indexId 1,
      hTraceCloseAt indexId 2,
      hTraceCloseAt indexId 3,
      hNumeralCloseAt 0 rowCodeId 0,
      hNumeralCloseAt 0 rowCodeId 1,
      hNumeralCloseAt 0 rowCodeId 2,
      hNumeralCloseAt 0 rowCodeId 3,
      hNumeralCloseAt 0 rowTraceId 0,
      hNumeralCloseAt 0 rowTraceId 1,
      hNumeralCloseAt 0 rowTraceId 2,
      hNumeralCloseAt 0 rowTraceId 3,
      hNumeralCloseAt 0 rowIndexId 0,
      hNumeralCloseAt 0 rowIndexId 1,
      hNumeralCloseAt 0 rowIndexId 2,
      hNumeralCloseAt 0 rowIndexId 3,
      hNumeralCloseAt 0 indexId 0,
      hNumeralCloseAt 0 indexId 1,
      hNumeralCloseAt 0 indexId 2,
      hNumeralCloseAt 0 indexId 3,
      hIndexNeRowCode, Ne.symm hIndexNeRowCode,
      hIndexNeRowTrace, Ne.symm hIndexNeRowTrace,
      hIndexNeRowIndex, Ne.symm hIndexNeRowIndex,
      hRowCodeNeRowTrace, Ne.symm hRowCodeNeRowTrace,
      hRowCodeNeRowIndex, Ne.symm hRowCodeNeRowIndex,
      hRowTraceNeRowIndex, Ne.symm hRowTraceNeRowIndex] using
      hGeneralized
  have hTraceFinal :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(proof.length) ≐ₘ code) := by
    have hTraceLast :
        (proof_sequence_code_trace rows)[rows.length]? =
          some (proof_sequence_code_value rows) :=
      proof_sequence_code_trace_last rows
    simpa [trace, code, rows] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_apply_getElem?
          (proof_sequence_code_trace rows) hTraceLast)
  have hTraceAtDomain :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(proof.length) ≐ₘ
          trace ·ₘ domₘ(sequence)) :=
    function_application_term_congr_argument_of_equality
      trace (numₘ(proof.length)) (domₘ(sequence))
      hTrace
      (finite_numeral_term_admissible proof.length)
      (domain_term_admissible sequence hSequence)
      hSequenceDomainSymm
  have hFinal :
      Derives fs_zfc_support_raw_theory [] (
        code ≐ₘ trace ·ₘ domₘ(sequence)) := by
    have hTraceFinalSymm :
        Derives fs_zfc_support_raw_theory [] (
          code ≐ₘ trace ·ₘ numₘ(proof.length)) :=
      Metatheory.Derives.equality_symm
        hTraceFinal
    exact Metatheory.Derives.equality_trans
      hTraceFinalSymm hTraceAtDomain
  have hTraceSpace :
      Derives fs_zfc_support_raw_theory [] (
        trace ∈ₘ seq_spaceₘ(ωₘ)) := by
    let hTraceSpaceStd :
        Derives standard_sequence_semantics_theory [] (
          standard_token_sequence (proof_sequence_code_trace rows) ∈ₘ
            seq_spaceₘ(ωₘ)) :=
      standard_token_sequence_mem_sequence_space
        (proof_sequence_code_trace rows)
    exact fs_zfc_support_raw_derives_of_standard_sequence
      (by simpa [trace] using hTraceSpaceStd)
  have hTraceValueBound :
      Derives fs_zfc_support_raw_theory [] (
        sequence_trace_code_bound_with_id trace code indexId) := by
    simpa [trace, code] using
      fs_zfc_support_raw_standard_token_sequence_trace_code_bound_with_id
        (proof_sequence_code_trace rows)
        (proof_sequence_code_value rows)
        indexId
        (fun value hValue =>
          proof_trace_mem_le_proof_sequence_code_value hValue)
  let stepBody : SetFormula :=
    (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
      (∃ₘ[SetSort.set, rowCodeId],
        ((x#rowCodeId ∈ₘ code) ∧ₘ
          proof_sequence_code_step_condition_with_ids
            sequence (x#traceId) (x#indexId) (x#rowCodeId)
            rowTraceId rowIndexId))
  let body : SetFormula :=
    (((x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        (domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence)))) ∧ₘ
      sequence_trace_code_bound_with_id
        (x#traceId) code indexId) ∧ₘ
      (((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
        ((∀ₘ[SetSort.set, indexId],
            stepBody) ∧ₘ
          (code ≐ₘ (x#traceId ·ₘ domₘ(sequence)))))
  have hTraceFresh :
      (SetSort.set, indexId) ∉ Term.freeSupport trace := by
    rw [hTraceClosed]
    exact List.not_mem_nil
  have hSequenceFresh :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence := by
    rw [hSequenceClosed]
    exact List.not_mem_nil
  have hSequenceClose :
      Term.closeFreeAt SetSort.set indexId 0 sequence = sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 sequence hSequence.2 hSequenceFresh
  have hSequenceSubstitute :
      Term.substituteFree SetSort.set traceId trace sequence =
        sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set traceId trace sequence (by
        rw [hSequenceClosed]
        exact List.not_mem_nil)
  have hTraceClose :
      Term.closeFreeAt SetSort.set indexId 0 trace = trace :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 trace hTrace.2 hTraceFresh
  have hSequenceCloseAt (binderId : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set binderId depth sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set binderId depth sequence hSequence.2 (by
        rw [hSequenceClosed]
        exact List.not_mem_nil)
  have hTraceCloseAt (binderId : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set binderId depth trace = trace :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set binderId depth trace hTrace.2 (by
        rw [hTraceClosed]
        exact List.not_mem_nil)
  have hNumeralCloseAt (value : Nat) (binderId : FreeVarId)
      (depth : Nat) :
      Term.closeFreeAt SetSort.set binderId depth numₘ(value) =
        numₘ(value) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set binderId depth (numₘ(value))
      (finite_numeral_term_admissible value).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hZeroSubstitute :
      Term.substituteFree SetSort.set traceId trace numₘ(0) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set traceId trace (numₘ(0)) (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hNumeralSubstitute (value : Nat) :
      Term.substituteFree SetSort.set traceId trace numₘ(value) =
        numₘ(value) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set traceId trace (numₘ(value)) (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hTraceSubstitute :
      Term.substituteFree SetSort.set traceId trace trace = trace :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set traceId trace trace (by
        rw [hTraceClosed]
        exact List.not_mem_nil)
  have hVariableSubstitute (variableId : FreeVarId)
      (hVariableNe : traceId ≠ variableId) :
      Term.substituteFree SetSort.set traceId trace (x#variableId) =
        x#variableId := by
      simp [Term.substituteFree, set_variable,
      Ne.symm hVariableNe]
  have hTraceVariableSubstitute :
      Term.substituteFree SetSort.set traceId trace (x#traceId) =
        trace := by
    simp [Term.substituteFree, set_variable]
  have hCodeSubstitute :
      Term.substituteFree SetSort.set traceId trace code = code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set traceId trace code (by
        rw [hCodeBoundary.2]
        exact List.not_mem_nil)
  have hSequenceSubstituteRaw :
      Term.substituteFree SetSort.set traceId trace
          (standard_sequence
            (proof.map
              (fun formula =>
                standard_token_sequence (certified_row_tokens formula)))) =
        standard_sequence
          (proof.map
            (fun formula =>
              standard_token_sequence (certified_row_tokens formula))) := by
    simpa [sequence, elements] using hSequenceSubstitute
  have hCodeSubstituteRaw :
      Term.substituteFree SetSort.set traceId trace
          (numₘ(proof_sequence_code_value
            (proof.map certified_row_tokens))) =
        numₘ(proof_sequence_code_value
          (proof.map certified_row_tokens)) := by
    simpa [code, rows] using hCodeSubstitute
  have hInnerComm :
      Formula.closeFreeAt SetSort.set indexId 0
          (Formula.substituteFree SetSort.set traceId trace stepBody) =
        Formula.substituteFree SetSort.set traceId trace
          (Formula.closeFreeAt SetSort.set indexId 0 stepBody) :=
    Formula.closeFreeAt_substituteFree_comm
      SetSort.set traceId indexId 0 trace stepBody
      hTraceNeIndex hTrace.2 hTraceFresh
  have hRowCodeComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set traceId trace
          (Formula.closeFreeAt SetSort.set rowCodeId 0 subformula) =
        Formula.closeFreeAt SetSort.set rowCodeId 0
          (Formula.substituteFree SetSort.set traceId trace subformula) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set traceId rowCodeId 0 trace subformula
      hTraceNeRowCode hTrace.2
      (by rw [hTraceClosed]; exact List.not_mem_nil)).symm
  have hRowTraceComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set traceId trace
          (Formula.closeFreeAt SetSort.set rowTraceId 0 subformula) =
        Formula.closeFreeAt SetSort.set rowTraceId 0
          (Formula.substituteFree SetSort.set traceId trace subformula) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set traceId rowTraceId 0 trace subformula
      hTraceNeRowTrace hTrace.2
      (by rw [hTraceClosed]; exact List.not_mem_nil)).symm
  have hRowIndexComm (subformula : SetFormula) :
      Formula.substituteFree SetSort.set traceId trace
          (Formula.closeFreeAt SetSort.set rowIndexId 0 subformula) =
        Formula.closeFreeAt SetSort.set rowIndexId 0
          (Formula.substituteFree SetSort.set traceId trace subformula) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set traceId rowIndexId 0 trace subformula
      hTraceNeRowIndex hTrace.2
      (by rw [hTraceClosed]; exact List.not_mem_nil)).symm
  have hSequenceSubstituteCloseAt (binderId : FreeVarId)
      (depth : Nat) :
      Term.substituteFree SetSort.set traceId trace
          (Term.closeFreeAt SetSort.set binderId depth sequence) =
        sequence := by
    rw [hSequenceCloseAt binderId depth]
    exact hSequenceSubstitute
  have hTraceSubstituteCloseAt (binderId : FreeVarId)
      (depth : Nat) :
      Term.substituteFree SetSort.set traceId trace
          (Term.closeFreeAt SetSort.set binderId depth trace) =
        trace := by
    rw [hTraceCloseAt binderId depth]
    exact hTraceSubstitute
  have hNumeralSubstituteCloseAt (value : Nat)
      (binderId : FreeVarId) (depth : Nat) :
      Term.substituteFree SetSort.set traceId trace
          (Term.closeFreeAt SetSort.set binderId depth numₘ(value)) =
        numₘ(value) := by
    rw [hNumeralCloseAt value binderId depth]
    exact hNumeralSubstitute value
  have hAllStepsSubstituted :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set traceId trace
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set indexId 0 stepBody))) := by
    simp only [Formula.substituteFree]
    rw [← hInnerComm]
    simp [stepBody, Formula.substituteFree, Formula.closeFreeAt,
      Formula.next_depth, proof_sequence_code_step_condition_with_ids,
      nat_sequence_code_condition_with_ids,
      sequence_domain_code_bound,
      nat_sequence_value_code_bound_with_id,
      sequence_trace_code_bound_with_id,
      nat_sequence_code_step_condition,
      Term.closeFreeAt, set_variable,
      trace, sequence, hTraceNeIndex,
      hTraceNeRowCode,
      hVariableSubstitute,
      hSequenceCloseAt rowCodeId 0,
      hSequenceCloseAt rowCodeId 1,
      hSequenceCloseAt rowCodeId 2,
      hSequenceCloseAt rowTraceId 0,
      hSequenceCloseAt rowTraceId 1,
      hSequenceCloseAt rowIndexId 0,
      hNumeralCloseAt 0 rowCodeId 1,
      hNumeralCloseAt 0 rowTraceId 0,
      hIndexNeRowCode, hIndexNeRowTrace, hIndexNeRowIndex,
      hRowCodeNeRowTrace, hRowTraceNeRowIndex]
    simpa [Formula.closeFreeAt, Formula.freeSupport, Formula.next_depth,
      code, rows,
      proof_sequence_code_step_condition_with_ids,
      nat_sequence_code_condition_with_ids,
      sequence_domain_code_bound,
      nat_sequence_value_code_bound_with_id,
      sequence_trace_code_bound_with_id,
      nat_sequence_code_step_condition,
      Term.closeFreeAt, Term.substituteFree, set_variable,
      trace, sequence, hTraceNeIndex, Ne.symm hTraceNeIndex,
      hTraceNeRowCode, Ne.symm hTraceNeRowCode,
      hTraceNeRowTrace, Ne.symm hTraceNeRowTrace,
      hTraceNeRowIndex, Ne.symm hTraceNeRowIndex,
      hSequenceSubstitute, hTraceSubstitute,
      hTraceVariableSubstitute, hVariableSubstitute,
      hNumeralSubstitute, hCodeSubstitute,
      hSequenceCloseAt, hTraceCloseAt, hNumeralCloseAt,
      hNumeralSubstituteCloseAt,
      hSequenceCloseAt indexId 0,
      hSequenceCloseAt indexId 1,
      hSequenceCloseAt indexId 2,
      hSequenceCloseAt indexId 3,
      hTraceCloseAt indexId 1,
      hTraceCloseAt indexId 2,
      hTraceCloseAt indexId 3,
      hNumeralCloseAt 0 indexId 0,
      hNumeralCloseAt 0 indexId 1,
      hNumeralCloseAt 0 indexId 2,
      hNumeralCloseAt 0 indexId 3,
      hIndexNeRowCode, Ne.symm hIndexNeRowCode,
      hIndexNeRowTrace, Ne.symm hIndexNeRowTrace,
      hIndexNeRowIndex, Ne.symm hIndexNeRowIndex,
      hRowCodeNeRowTrace, Ne.symm hRowCodeNeRowTrace,
      hRowCodeNeRowIndex, Ne.symm hRowCodeNeRowIndex,
      hRowTraceNeRowIndex, Ne.symm hRowTraceNeRowIndex] using
      hAllSteps
  unfold proof_sequence_code_condition_with_ids
  apply FirstOrder.Derives.conjIntro
    (FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        hSequenceSpace hCodeOmega)
      hSequenceDomainBound)
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := trace) traceId
  simpa [body, stepBody, Formula.substituteFree,
    Formula.freeSupport,
    Formula.closeFreeAt, Formula.next_depth,
    proof_sequence_code_step_condition_with_ids,
    nat_sequence_code_condition_with_ids,
    sequence_domain_code_bound,
    nat_sequence_value_code_bound_with_id,
    sequence_trace_code_bound_with_id,
    nat_sequence_code_step_condition,
     Term.closeFreeAt, Term.substituteFree, set_variable,
      trace, sequence, elements, rows, code,
      hTraceNeIndex, Ne.symm hTraceNeIndex,
    hTraceNeRowCode, Ne.symm hTraceNeRowCode,
    hTraceNeRowTrace, Ne.symm hTraceNeRowTrace,
    hTraceNeRowIndex, Ne.symm hTraceNeRowIndex,
    hIndexNeRowCode, Ne.symm hIndexNeRowCode,
    hIndexNeRowTrace, Ne.symm hIndexNeRowTrace,
    hIndexNeRowIndex, Ne.symm hIndexNeRowIndex,
    hRowCodeNeRowTrace, Ne.symm hRowCodeNeRowTrace,
    hRowCodeNeRowIndex, Ne.symm hRowCodeNeRowIndex,
    hRowTraceNeRowIndex, Ne.symm hRowTraceNeRowIndex,
     hSequenceClose, hSequenceSubstitute, hTraceClose,
     hTraceSubstitute, hTraceVariableSubstitute,
     hVariableSubstitute,
     hSequenceCloseAt indexId 0,
     hSequenceCloseAt indexId 1,
     hSequenceCloseAt indexId 2,
     hSequenceCloseAt indexId 3,
     hTraceCloseAt indexId 1,
     hTraceCloseAt indexId 2,
     hTraceCloseAt indexId 3,
     hNumeralCloseAt 0 indexId 0,
     hNumeralCloseAt 0 indexId 1,
     hNumeralCloseAt 0 indexId 2,
     hNumeralCloseAt 0 indexId 3,
     hSequenceSubstituteCloseAt rowCodeId 0,
    hSequenceSubstituteCloseAt rowCodeId 1,
    hSequenceSubstituteCloseAt rowCodeId 2,
    hSequenceSubstituteCloseAt rowCodeId 3,
    hSequenceSubstituteCloseAt rowTraceId 0,
    hSequenceSubstituteCloseAt rowTraceId 1,
    hSequenceSubstituteCloseAt rowTraceId 2,
    hSequenceSubstituteCloseAt rowTraceId 3,
    hSequenceSubstituteCloseAt rowIndexId 0,
    hSequenceSubstituteCloseAt rowIndexId 1,
    hSequenceSubstituteCloseAt rowIndexId 2,
    hSequenceSubstituteCloseAt rowIndexId 3,
    hSequenceSubstituteCloseAt indexId 0,
    hSequenceSubstituteCloseAt indexId 1,
    hSequenceSubstituteCloseAt indexId 2,
    hSequenceSubstituteCloseAt indexId 3,
    hTraceSubstituteCloseAt rowCodeId 0,
    hTraceSubstituteCloseAt rowCodeId 1,
    hTraceSubstituteCloseAt rowCodeId 2,
    hTraceSubstituteCloseAt rowCodeId 3,
    hTraceSubstituteCloseAt rowTraceId 0,
    hTraceSubstituteCloseAt rowTraceId 1,
    hTraceSubstituteCloseAt rowTraceId 2,
    hTraceSubstituteCloseAt rowTraceId 3,
    hTraceSubstituteCloseAt rowIndexId 0,
    hTraceSubstituteCloseAt rowIndexId 1,
    hTraceSubstituteCloseAt rowIndexId 2,
    hTraceSubstituteCloseAt rowIndexId 3,
    hTraceSubstituteCloseAt indexId 0,
    hTraceSubstituteCloseAt indexId 1,
    hTraceSubstituteCloseAt indexId 2,
    hTraceSubstituteCloseAt indexId 3,
    hNumeralSubstituteCloseAt 0 rowCodeId 0,
    hNumeralSubstituteCloseAt 0 rowCodeId 1,
    hNumeralSubstituteCloseAt 0 rowCodeId 2,
    hNumeralSubstituteCloseAt 0 rowCodeId 3,
    hNumeralSubstituteCloseAt 0 rowTraceId 0,
    hNumeralSubstituteCloseAt 0 rowTraceId 1,
    hNumeralSubstituteCloseAt 0 rowTraceId 2,
    hNumeralSubstituteCloseAt 0 rowIndexId 0,
    hNumeralSubstituteCloseAt 0 rowIndexId 1,
    hNumeralSubstituteCloseAt 0 rowIndexId 2,
    hNumeralSubstituteCloseAt 0 rowIndexId 3,
    hNumeralSubstituteCloseAt 0 indexId 0,
    hNumeralSubstituteCloseAt 0 indexId 1,
    hNumeralSubstituteCloseAt 0 indexId 2,
     hNumeralSubstituteCloseAt 0 indexId 3,
     hNumeralCloseAt, hNumeralSubstituteCloseAt,
     hZeroSubstitute, hCodeSubstitute,
     hSequenceSubstituteRaw, hCodeSubstituteRaw] using
    (FirstOrder.Derives.conjIntro
      hTraceSpace
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro
          hTraceDomainFinal hTraceValueBound)
        (FirstOrder.Derives.conjIntro
          hInitial
          (FirstOrder.Derives.conjIntro
            hAllStepsSubstituted hFinal))))

/-- 外部证明列表的公式码序列在每个有效位置上回放到对应 token 序列。 -/
theorem ProofT.ZFC.formula_sequence_apply
    {T : SetTheory}
    (hStandardSequence :
      ∀ {candidate : SetFormula},
        standard_sequence_semantics_theory candidate → T candidate)
    {proof : List SetFormula}
    {index : Nat} {formula : SetFormula}
    (hGet : proof[index]? = some formula) :
    Derives T [] (
      (standard_sequence
          (proof.map
            (fun formula =>
              standard_token_sequence
                (certified_row_tokens formula))) ·ₘ
          numₘ(index)) ≐ₘ
        standard_token_sequence (certified_row_tokens formula)) := by
  have hMapped :
      (proof.map
          (fun formula =>
            standard_token_sequence
              (certified_row_tokens formula)))[index]? =
        some (standard_token_sequence (certified_row_tokens formula)) := by
    simpa using congrArg
      (Option.map
        (fun formula =>
          standard_token_sequence (certified_row_tokens formula)))
      hGet
  have hElements :
      ∀ element,
        element ∈
            proof.map
              (fun formula =>
                standard_token_sequence
                  (certified_row_tokens formula)) →
          Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, hRow, rfl⟩
    exact standard_token_sequence_admissible
      (certified_row_tokens row)
  have hElementsClosed :
      ∀ element,
        element ∈
            proof.map
              (fun formula =>
                standard_token_sequence
                  (certified_row_tokens formula)) →
          Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, hRow, rfl⟩
    exact standard_token_sequence_freeSupport_nil
      (certified_row_tokens row)
  have hElement :
      Term.Admissible
        (standard_token_sequence (certified_row_tokens formula))
        SetSort.set :=
    standard_token_sequence_admissible
      (certified_row_tokens formula)
  have hStandard :=
    GodelQuotation.standard_sequence_from_apply_getElem?
      0 hMapped hElements hElementsClosed hElement
  have hAt :=
    FirstOrder.Derives.theory_weaken
      (fun _ hCandidate => hStandardSequence hCandidate)
      hStandard
  simpa [standard_sequence] using hAt

/-- 证书标签序列的自然数编码条件直接复用一维 checked replay。 -/
theorem fs_zfc_support_raw_certificate_code_condition_with_ids
    (certificates : List HilbertLineCertificateCode)
    (traceId indexId : FreeVarId)
    (hIds : traceId ≠ indexId) :
    Derives fs_zfc_support_raw_theory [] (
      nat_sequence_code_condition_with_ids
        (standard_token_sequence
          (certificates.map HilbertLineCertificateCode.value))
        (numₘ(nat_sequence_code_value
          (certificates.map HilbertLineCertificateCode.value)))
        traceId indexId) :=
  fs_zfc_support_raw_nat_sequence_code_condition_with_ids
    (certificates.map HilbertLineCertificateCode.value)
    traceId indexId hIds

/-- 外部规范证明码的二元 Gödel 配对在对象层回放到其自然数值。 -/
theorem fs_zfc_support_raw_certified_hilbert_proof_code_pair_eq
    {proof : List SetFormula}
    (certificates : List HilbertLineCertificateCode) :
    Derives fs_zfc_support_raw_theory [] (
      godel_pairₘ(⟨
        numₘ(proof_sequence_code_value
          (proof.map certified_row_tokens)),
        numₘ(nat_sequence_code_value
          (certificates.map HilbertLineCertificateCode.value))⟩ₘ) ≐ₘ
        numₘ(godel_pair_value
          (proof_sequence_code_value
            (proof.map certified_row_tokens))
          (nat_sequence_code_value
            (certificates.map HilbertLineCertificateCode.value)))) :=
  fs_zfc_support_raw_godel_pair_value_eq
    (proof_sequence_code_value (proof.map certified_row_tokens))
    (nat_sequence_code_value
      (certificates.map HilbertLineCertificateCode.value))

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
