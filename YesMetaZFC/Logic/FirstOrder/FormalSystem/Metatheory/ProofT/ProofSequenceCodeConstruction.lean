import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceCodeConstruction

/-!
# 内在证明序列编码的正向构造

外部 `List (List Nat)` 直接生产二维证明序列的 Quine 条件。调用方只需提供每一行
属于公式码承载集合的事实；行码的自然数条件、轨迹递推和所有有限界均由宿主递归
与公共内在序列接口自动装配。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open IntrinsicPairing
open ProofCode

set_option autoImplicit false

private theorem membership_body_instantiateTop
    {free : SetContext}
    (left right : SetOpenTerm free)
    (index : Nat) :
    Formula.instantiateTop (numₘ(index))
        (((left.weakenBound SetSort.set ·ₘ
            (.bvar .here : SetTerm [SetSort.set] free)) ∈ₘ
          right.weakenBound SetSort.set)) =
      (left ·ₘ numₘ(index)) ∈ₘ right := by
  rw [Formula.instantiateTop_rel]
  simp only [Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_app,
    Term.instantiateTop_weakenBound]
  rw [Term.instantiateTop_bvar_here]

private theorem successor_membership_body_instantiateTop
    {free : SetContext}
    (left right : SetOpenTerm free)
    (index : Nat) :
    Formula.instantiateTop (numₘ(index))
        (((left.weakenBound SetSort.set ·ₘ
            (.bvar .here : SetTerm [SetSort.set] free)) ∈ₘ
          Sₘ(right.weakenBound SetSort.set))) =
      (left ·ₘ numₘ(index)) ∈ₘ Sₘ(right) := by
  rw [Formula.instantiateTop_rel]
  simp only [Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_app,
    Term.instantiateTop_weakenBound]
  repeat rw [Term.instantiateTop_bvar_here]

private theorem nat_step_condition_instantiateTop
    {free : SetContext}
    (sequence trace : SetOpenTerm free)
    (index : Nat) :
    Formula.instantiateTop (numₘ(index))
        (nat_sequence_code_step_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (.bvar .here)) =
      nat_sequence_code_step_condition sequence trace (numₘ(index)) := by
  unfold nat_sequence_code_step_condition
  rw [Formula.instantiateTop_equal]
  simp only [Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_app,
    Term.instantiateTop_weakenBound]
  repeat rw [Term.instantiateTop_bvar_here]

private theorem standard_proof_sequence_space
    {T : SetTheory}
    (R : IntrinsicProofRowSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (rows : List (List Nat))
    (hLengthOmega :
      Γ ⊢ₘ[T] (numₘ(rows.length) : SetOpenTerm free) ∈ₘ ωₘ)
    (hRowMember : ∀ row, row ∈ rows →
      Γ ⊢ₘ[T]
        nat_sequence_graph_term (bound := []) (free := free) row ∈ₘ
          syntax_formula_code_set_term) :
    Γ ⊢ₘ[T]
      proof_sequence_graph_term (bound := []) (free := free) rows ∈ₘ
        seq_spaceₘ(syntax_formula_code_set_term) := by
  let elements : List (SetOpenTerm free) :=
    rows.map (fun row =>
      nat_sequence_graph_term (bound := []) (free := free) row)
  have hSpace : Γ ⊢ₘ[T]
      standard_sequence elements ∈ₘ
        seq_spaceₘ(syntax_formula_code_set_term) :=
    standard_sequence_mem_sequence_space
      R.toFiniteSequenceSpaceSupport elements
      syntax_formula_code_set_term (by
        simpa [elements] using hLengthOmega)
      (R.formula_code_nonempty (Γ := Γ)) (by
        intro element hElement
        rcases List.mem_map.mp hElement with ⟨row, hRow, rfl⟩
        exact hRowMember row hRow)
  simpa [elements, proof_sequence_graph_term, standard_sequence] using hSpace

private theorem standard_proof_sequence_value
    {T : SetTheory}
    (R : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (rows : List (List Nat))
    (index : Nat)
    (hIndex : index < rows.length) :
    Γ ⊢ₘ[T]
      (proof_sequence_graph_term (bound := []) (free := free) rows ·ₘ
        numₘ(index)) ≐ₘ
        nat_sequence_graph_term (bound := []) (free := free)
          (rows[index]'hIndex) := by
  exact Metatheory.Derives.equality_symm <|
    proof_row_value_of_graph R rows index hIndex

private theorem standard_proof_trace_value
    {T : SetTheory}
    (R : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (rows : List (List Nat))
    (index : Nat)
    (hIndex : index ≤ rows.length) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free)
          (proof_sequence_code_trace rows) ·ₘ numₘ(index)) ≐ₘ
        numₘ(proof_sequence_code_from 0 (rows.take index)) := by
  let values : List Nat := proof_sequence_code_trace rows
  let elements : List (SetOpenTerm free) :=
    values.map (fun value => numₘ(value))
  have hGetNat : values[index]? =
      some (proof_sequence_code_from 0 (rows.take index)) := by
    simpa [values] using!
      proof_sequence_code_trace_from_getElem?
        0 rows index hIndex
  have hGet : elements[index]? =
      some (numₘ(proof_sequence_code_from 0 (rows.take index)) :
        SetOpenTerm free) := by
    simpa [elements] using
      congrArg (Option.map (fun value =>
        (numₘ(value) : SetOpenTerm free))) hGetNat
  have hApply := standard_sequence_from_getElem?_apply_eq
    (Γ := Γ) R 0 hGet
  exact Metatheory.Derives.equality_symm <| by
    simpa [values, elements, nat_sequence_graph_term, standard_sequence] using
      hApply

private theorem standard_proof_trace_last_value
    {T : SetTheory}
    (R : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (rows : List (List Nat)) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free)
          (proof_sequence_code_trace rows) ·ₘ numₘ(rows.length)) ≐ₘ
        numₘ(proof_sequence_code_value rows) := by
  have hGetNat : (proof_sequence_code_trace rows)[rows.length]? =
      some (proof_sequence_code_value rows) :=
    proof_sequence_code_trace_last rows
  let elements : List (SetOpenTerm free) :=
    (proof_sequence_code_trace rows).map (fun value => numₘ(value))
  have hGet : elements[rows.length]? =
      some (numₘ(proof_sequence_code_value rows) : SetOpenTerm free) := by
    simpa [elements] using
      congrArg (Option.map (fun value =>
        (numₘ(value) : SetOpenTerm free))) hGetNat
  have hApply := standard_sequence_from_getElem?_apply_eq
    (Γ := Γ) R 0 hGet
  exact Metatheory.Derives.equality_symm <| by
    simpa [elements, nat_sequence_graph_term, standard_sequence] using hApply

private theorem standard_proof_trace_step
    {T : SetTheory}
    (C : CertificateCore T)
    (R : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (rows : List (List Nat))
    (index : Nat)
    (hIndex : index < rows.length) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free)
          (proof_sequence_code_trace rows) ·ₘ Sₘ(numₘ(index))) ≐ₘ
        Sₘ(godel_pairₘ(
          nat_sequence_graph_term (bound := []) (free := free)
            (proof_sequence_code_trace rows) ·ₘ numₘ(index),
          numₘ(nat_sequence_code_value (rows[index]'hIndex)))) := by
  let trace : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free)
      (proof_sequence_code_trace rows)
  let row : List Nat := rows[index]'hIndex
  have hRowGet : rows[index]? = some row :=
    List.getElem?_eq_getElem hIndex
  have hTraceNextNat := proof_sequence_code_trace_step
    rows index row hRowGet
  let traceValues : List Nat := proof_sequence_code_trace rows
  let traceElements : List (SetOpenTerm free) :=
    traceValues.map (fun value => numₘ(value))
  have hTraceNextGet : traceElements[index + 1]? =
      some (numₘ(nat_sequence_code_step
        (proof_sequence_code_from 0 (rows.take index))
        (nat_sequence_code_value row)) : SetOpenTerm free) := by
    simpa [traceElements, traceValues] using
      congrArg (Option.map (fun value =>
        (numₘ(value) : SetOpenTerm free))) hTraceNextNat
  have hTraceNextRaw := standard_sequence_from_getElem?_apply_eq
    (Γ := Γ) R 0 hTraceNextGet
  have hTraceNext : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(index + 1) ≐ₘ
        numₘ(nat_sequence_code_step
          (proof_sequence_code_from 0 (rows.take index))
          (nat_sequence_code_value row)) := by
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace, traceElements, traceValues,
        nat_sequence_graph_term, standard_sequence] using hTraceNextRaw
  have hTraceCurrent := standard_proof_trace_value
    (Γ := Γ) R rows index (Nat.le_of_lt hIndex)
  have hTraceCurrent' : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(index) ≐ₘ
        numₘ(proof_sequence_code_from 0 (rows.take index)) := by
    simpa [trace] using hTraceCurrent
  have hPair := IntrinsicPairing.pair_congr_of_equalities
    (trace ·ₘ numₘ(index))
    (numₘ(proof_sequence_code_from 0 (rows.take index)))
    (numₘ(nat_sequence_code_value row))
    (numₘ(nat_sequence_code_value row))
    hTraceCurrent' (Metatheory.Derives.equality_refl _)
  have hSuccessor := successor_term_congr_of_equality
    (godel_pairₘ(trace ·ₘ numₘ(index),
      numₘ(nat_sequence_code_value row)))
    (godel_pairₘ(
      numₘ(proof_sequence_code_from 0 (rows.take index)),
      numₘ(nat_sequence_code_value row))) hPair
  have hGround := nat_sequence_code_step_numeral_at C
    (proof_sequence_code_from 0 (rows.take index))
    (nat_sequence_code_value row) (Γ := Γ)
  have hRight : Γ ⊢ₘ[T]
      Sₘ(godel_pairₘ(trace ·ₘ numₘ(index),
        numₘ(nat_sequence_code_value row))) ≐ₘ
      Sₘ(godel_pairₘ(
          numₘ(proof_sequence_code_from 0 (rows.take index)),
          numₘ(nat_sequence_code_value row))) :=
    hSuccessor
  have hRight' : Γ ⊢ₘ[T]
      Sₘ(godel_pairₘ(trace ·ₘ numₘ(index),
        numₘ(nat_sequence_code_value row))) ≐ₘ
        numₘ(nat_sequence_code_step
          (proof_sequence_code_from 0 (rows.take index))
          (nat_sequence_code_value row)) :=
    Metatheory.Derives.equality_trans hRight hGround
  have hLeft : Γ ⊢ₘ[T]
      trace ·ₘ Sₘ(numₘ(index)) ≐ₘ
        numₘ(nat_sequence_code_step
          (proof_sequence_code_from 0 (rows.take index))
          (nat_sequence_code_value row)) := by
    simpa [finite_numeral_term, successor_term] using hTraceNext
  exact Metatheory.Derives.equality_trans hLeft
    (Metatheory.Derives.equality_symm hRight')

private theorem proof_sequence_row_condition_intro
    {T : SetTheory}
    (C : CertificateCore T)
    (R : IntrinsicProofRowSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (rows : List (List Nat))
    (index : Nat)
    (hIndex : index < rows.length)
    (hNumeralOmega : ∀ number,
      Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      proof_sequence_code_row_condition
        (proof_sequence_graph_term (bound := []) (free := free) rows)
        (nat_sequence_graph_term (bound := []) (free := free)
          (proof_sequence_code_trace rows))
        (numₘ(proof_sequence_code_value rows)) (numₘ(index)) := by
  let sequence : SetOpenTerm free :=
    proof_sequence_graph_term (bound := []) (free := free) rows
  let trace : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free)
      (proof_sequence_code_trace rows)
  let code : SetOpenTerm free :=
    numₘ(proof_sequence_code_value rows)
  let row : List Nat := rows[index]'hIndex
  let rowCode : SetOpenTerm free := numₘ(nat_sequence_code_value row)
  let body : SetFormula [SetSort.set] free :=
    proof_sequence_code_step_condition
      (sequence.weakenBound SetSort.set)
      (trace.weakenBound SetSort.set)
      ((numₘ(index) : SetOpenTerm free).weakenBound SetSort.set)
      (.bvar .here)
  have hRowCodeBound : Γ ⊢ₘ[T] rowCode ∈ₘ code := by
    have hRowBoundClosed : ([] : Context signature free) ⊢ₘ[T]
        numₘ(nat_sequence_code_value row) ∈ₘ
          numₘ(proof_sequence_code_value rows) := by
      simpa [row] using
        (numeral_mem_of_lt
          R.toFiniteSequenceSpaceSupport.toArithmeticSupport.contains_successor
          (row_code_lt_proof_sequence_code_value
              (List.getElem_mem hIndex)))
    have hRowBound : Γ ⊢ₘ[T]
        numₘ(nat_sequence_code_value row) ∈ₘ
          numₘ(proof_sequence_code_value rows) :=
      FirstOrder.Derives.context_weaken
        (Γ := ([] : Context signature free)) (Δ := Γ) (by simp)
        hRowBoundClosed
    simpa [rowCode, code] using hRowBound
  have hInner : Γ ⊢ₘ[T]
      nat_sequence_code_condition
        (nat_sequence_graph_term (bound := []) (free := free) row)
        rowCode := by
    simpa [rowCode] using
      nat_sequence_code_condition_intro_standard
        C R.toFiniteSequenceSpaceSupport row hNumeralOmega
  have hOuter := standard_proof_trace_step
    (Γ := Γ) C
      R.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
      rows index hIndex
  have hStep : Γ ⊢ₘ[T]
      proof_sequence_code_step_condition sequence trace
        (numₘ(index)) rowCode := by
    have hInner' : Γ ⊢ₘ[T]
        nat_sequence_code_condition
          (sequence ·ₘ numₘ(index)) rowCode := by
      have hValue := standard_proof_sequence_value
        (Γ := Γ)
          R.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
          rows index hIndex
      let body : SetFormula [SetSort.set] free :=
        nat_sequence_code_condition
          (.bvar .here : SetTerm [SetSort.set] free)
          (rowCode.weakenBound SetSort.set)
      have hIffRaw := Metatheory.Derives.equality_iff_of_equality
        (T := T) (Γ := Γ) (sort := SetSort.set)
        (body := body) hValue
      have hIff : Γ ⊢ₘ[T]
          nat_sequence_code_condition
              (sequence ·ₘ numₘ(index)) rowCode ↔ₘ
            nat_sequence_code_condition
              (nat_sequence_graph_term row) rowCode := by
        simpa [body, sequence, row] using! hIffRaw
      exact FirstOrder.Derives.iff_elim_right hIff hInner
    have hStep' := FirstOrder.Derives.conj_intro hInner' (by
      simpa [sequence, trace, row, rowCode] using hOuter)
    simpa [proof_sequence_code_step_condition,
      ProofT.proof_sequence_code_step_condition_template,
      FormulaTemplate.apply_four, FormulaTemplate.instantiate,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.empty, sequence, trace, row, rowCode] using hStep'
  have hExists := bounded_exists_intro
    code body rowCode hRowCodeBound (by
      rw [proof_sequence_code_step_condition_instantiateTop_bvar]
      exact hStep)
  change Γ ⊢ₘ[T]
    Formula.LevyBound.boundedExists ProofT.set_levy_bound code body
  exact hExists

theorem proof_sequence_code_condition_intro_standard
    {T : SetTheory}
    (C : CertificateCore T)
    (R : IntrinsicProofRowSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (rows : List (List Nat))
    (hNumeralOmega : ∀ number,
      Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ)
    (hRowMember : ∀ row, row ∈ rows →
      Γ ⊢ₘ[T]
        nat_sequence_graph_term (bound := []) (free := free) row ∈ₘ
          syntax_formula_code_set_term) :
    Γ ⊢ₘ[T]
      proof_sequence_code_condition
        (proof_sequence_graph_term (bound := []) (free := free) rows)
        (numₘ(proof_sequence_code_value rows)) := by
  let sequence : SetOpenTerm free :=
    proof_sequence_graph_term (bound := []) (free := free) rows
  let code : SetOpenTerm free :=
    numₘ(proof_sequence_code_value rows)
  let trace : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free)
      (proof_sequence_code_trace rows)
  have hSequenceSpace : Γ ⊢ₘ[T]
      sequence ∈ₘ seq_spaceₘ(syntax_formula_code_set_term) := by
    simpa [sequence] using
      standard_proof_sequence_space R rows
        (hNumeralOmega rows.length) hRowMember
  have hCodeOmega : Γ ⊢ₘ[T] code ∈ₘ ωₘ := by
    simpa [code] using hNumeralOmega (proof_sequence_code_value rows)
  have hSequenceDomain : Γ ⊢ₘ[T]
      domₘ(sequence) ≐ₘ numₘ(rows.length) := by
    simpa [sequence] using
      proof_sequence_graph_domain_eq
        (Γ := Γ)
        R.toFiniteSequenceSpaceSupport.toFiniteSequenceGraphSupport rows
  have hDomainBound : Γ ⊢ₘ[T]
      sequence_domain_code_bound sequence code := by
    have hLengthMember : Γ ⊢ₘ[T]
        numₘ(rows.length) ∈ₘ Sₘ(code) := by
      simpa [code, finite_numeral_term, successor_term] using
        (FirstOrder.Derives.context_weaken
          (Γ := ([] : Context signature free)) (Δ := Γ) (by simp)
          (numeral_mem_of_lt
            R.toFiniteSequenceSpaceSupport.toArithmeticSupport.contains_successor
            (Nat.lt_succ_of_le (proof_sequence_length_le_code rows))))
    exact FirstOrder.Derives.iff_elim_right
      (membership_left_iff_of_equality
        (domₘ(sequence)) (numₘ(rows.length)) (Sₘ(code))
        hSequenceDomain) hLengthMember
  have hTraceSpace : Γ ⊢ₘ[T]
      trace ∈ₘ seq_spaceₘ(ωₘ) := by
    let elements : List (SetOpenTerm free) :=
      (proof_sequence_code_trace rows).map (fun value => numₘ(value))
    have hLengthOmega : Γ ⊢ₘ[T]
        numₘ(elements.length) ∈ₘ (ωₘ : SetOpenTerm free) := by
      simpa [elements, proof_sequence_code_trace_length] using
        hNumeralOmega ((proof_sequence_code_trace rows).length)
    have hSpace := standard_sequence_mem_sequence_space
      R.toFiniteSequenceSpaceSupport elements ωₘ hLengthOmega
      (by
        have hZero := hNumeralOmega 0
        have hImp : Γ ⊢ₘ[T]
            (numₘ(0) ∈ₘ (ωₘ : SetOpenTerm free)) ⟶ₘ
              (ωₘ ≠ₘ (∅ₘ : SetOpenTerm free)) :=
          FirstOrder.Derives.theory_weaken
            (fun hSentence =>
              R.toFiniteSequenceSpaceSupport.toArithmeticSupport.contains_empty_set
                hSentence)
            (member_implies_set_nonempty
              (Γ := Γ)
              (numₘ(0) : SetOpenTerm free)
              (ωₘ : SetOpenTerm free))
        exact FirstOrder.Derives.imp_elim hImp hZero)
      (by
        intro element hElement
        rcases List.mem_map.mp hElement with ⟨value, _, rfl⟩
        exact hNumeralOmega value)
    simpa [trace, elements, nat_sequence_graph_term, standard_sequence] using hSpace
  have hTraceDomain : Γ ⊢ₘ[T]
      domₘ(trace) ≐ₘ Sₘ(domₘ(sequence)) := by
    have hRaw : Γ ⊢ₘ[T]
        domₘ(trace) ≐ₘ
          numₘ((proof_sequence_code_trace rows).length) := by
      simpa [trace] using
        (nat_sequence_graph_domain_eq
          (Γ := Γ)
          R.toFiniteSequenceSpaceSupport.toFiniteSequenceGraphSupport
          (proof_sequence_code_trace rows))
    have hTraceNumeral : Γ ⊢ₘ[T]
        domₘ(trace) ≐ₘ Sₘ(numₘ(rows.length)) := by
      simpa [proof_sequence_code_trace_length, finite_numeral_term,
        successor_term] using hRaw
    have hSequenceSuccessor := successor_term_congr_of_equality
      (domₘ(sequence)) (numₘ(rows.length)) hSequenceDomain
    exact Metatheory.Derives.equality_trans hTraceNumeral
      (Metatheory.Derives.equality_symm hSequenceSuccessor)
  have hTraceBound : Γ ⊢ₘ[T]
      sequence_trace_code_bound trace code := by
    let body : SetFormula [SetSort.set] free :=
      ((trace.weakenBound SetSort.set ·ₘ
          (.bvar .here : SetTerm [SetSort.set] free)) ∈ₘ
        Sₘ(code.weakenBound SetSort.set))
    have hNumeralBound : Γ ⊢ₘ[T]
        Formula.LevyBound.boundedForall set_levy_bound
          (numₘ((proof_sequence_code_trace rows).length)) body :=
      bounded_forall_numeral_intro
        C.toFiniteCore (proof_sequence_code_trace rows).length body (by
          intro index hIndex
          have hIndexLt : index < rows.length + 1 := by
            simpa [proof_sequence_code_trace_length] using hIndex
          have hIndexLe : index ≤ rows.length := by omega
          have hValue := standard_proof_trace_value
            (Γ := Γ)
              R.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
              rows index hIndexLe
          have hTraceMember :
              proof_sequence_code_from 0 (rows.take index) ≤
                proof_sequence_code_value rows := by
            apply take_proof_code_le_proof_sequence_code_value
            exact hIndexLe
          have hNumeralMember : ([] : Context signature free) ⊢ₘ[T]
              numₘ(proof_sequence_code_from 0 (rows.take index)) ∈ₘ
                Sₘ(numₘ(proof_sequence_code_value rows)) := by
            simpa [finite_numeral_term, successor_term] using
              (numeral_mem_of_lt
                R.toFiniteSequenceSpaceSupport.toArithmeticSupport.contains_successor
                (Nat.lt_succ_of_le hTraceMember))
          have hMember : Γ ⊢ₘ[T]
              (trace ·ₘ numₘ(index)) ∈ₘ Sₘ(code) :=
            FirstOrder.Derives.iff_elim_right
              (membership_left_iff_of_equality
                (trace ·ₘ numₘ(index))
                (numₘ(proof_sequence_code_from 0 (rows.take index)))
                (Sₘ(code)) hValue)
              (by
                simpa [code] using
                  FirstOrder.Derives.context_weaken
                    (Γ := ([] : Context signature free)) (Δ := Γ) (by simp)
                    hNumeralMember)
          change Γ ⊢ₘ[T]
            Formula.instantiateTop (numₘ(index))
              body
          rw [successor_membership_body_instantiateTop]
          exact hMember)
    let boundTemplate : SetFormula [SetSort.set] free :=
      Formula.LevyBound.boundedForall set_levy_bound
        ((.bvar .here) : SetTerm [SetSort.set] free)
        (body.weakenBoundUnderTop SetSort.set)
    have hNumeralAt : Γ ⊢ₘ[T]
        boundTemplate.instantiateTop
          (numₘ((proof_sequence_code_trace rows).length)) := by
      change Γ ⊢ₘ[T]
        (Formula.LevyBound.boundedForall set_levy_bound
          ((.bvar .here) : SetTerm [SetSort.set] free)
          (body.weakenBoundUnderTop SetSort.set)).instantiateTop
            (numₘ((proof_sequence_code_trace rows).length))
      rw [Formula.LevyBound.boundedForall_instantiateTop_bvar]
      exact hNumeralBound
    have hDomainRaw := FirstOrder.Derives.eq_subst
      (body := boundTemplate)
      (Metatheory.Derives.equality_symm <| by
        simpa [trace] using
          (nat_sequence_graph_domain_eq
            (Γ := Γ)
            R.toFiniteSequenceSpaceSupport.toFiniteSequenceGraphSupport
            (proof_sequence_code_trace rows))) hNumeralAt
    change Γ ⊢ₘ[T]
      (Formula.LevyBound.boundedForall set_levy_bound
        ((.bvar .here) : SetTerm [SetSort.set] free)
        (body.weakenBoundUnderTop SetSort.set)).instantiateTop
          (domₘ(trace)) at hDomainRaw
    rw [Formula.LevyBound.boundedForall_instantiateTop_bvar] at hDomainRaw
    simpa [sequence_trace_code_bound, body] using hDomainRaw
  have hZero : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(0) ≐ₘ numₘ(0) := by
    have hGetNat : (proof_sequence_code_trace rows)[0]? = some 0 := by
      simpa [proof_sequence_code_trace, proof_sequence_code_trace_from,
        proof_sequence_code_from, nat_sequence_code_from] using
        proof_sequence_code_trace_from_getElem?
          0 rows 0 (Nat.zero_le _)
    let elements : List (SetOpenTerm free) :=
      (proof_sequence_code_trace rows).map (fun value => numₘ(value))
    have hGet : elements[0]? = some (numₘ(0) : SetOpenTerm free) := by
      simpa [elements] using
        congrArg (Option.map (fun value =>
          (numₘ(value) : SetOpenTerm free))) hGetNat
    have hApply := standard_sequence_from_getElem?_apply_eq
      (Γ := Γ) R.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
      0 hGet
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace, elements, nat_sequence_graph_term, standard_sequence] using hApply
  let rowBody : SetFormula [SetSort.set] free :=
    proof_sequence_code_row_condition
      (sequence.weakenBound SetSort.set)
      (trace.weakenBound SetSort.set)
      (code.weakenBound SetSort.set)
      (.bvar .here)
  have hRowsNumeral : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (numₘ(rows.length)) rowBody :=
    bounded_forall_numeral_intro C.toFiniteCore rows.length rowBody (by
      intro index hIndex
      have hRow := proof_sequence_row_condition_intro
        (Γ := Γ) C R rows index hIndex hNumeralOmega
      change Γ ⊢ₘ[T]
        Formula.instantiateTop (numₘ(index))
          (proof_sequence_code_row_condition
            (sequence.weakenBound SetSort.set)
            (trace.weakenBound SetSort.set)
            (code.weakenBound SetSort.set)
            (.bvar .here))
      rw [proof_sequence_code_row_condition_instantiateTop]
      simp only [Term.instantiateTop_weakenBound]
      simpa [rowBody, sequence, trace, code] using! hRow)
  have hRows : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (domₘ(sequence)) rowBody := by
    let boundTemplate : SetFormula [SetSort.set] free :=
      Formula.LevyBound.boundedForall set_levy_bound
        ((.bvar .here) : SetTerm [SetSort.set] free)
        (rowBody.weakenBoundUnderTop SetSort.set)
    have hNumeralAt : Γ ⊢ₘ[T]
        boundTemplate.instantiateTop (numₘ(rows.length)) := by
      change Γ ⊢ₘ[T]
        (Formula.LevyBound.boundedForall set_levy_bound
          ((.bvar .here) : SetTerm [SetSort.set] free)
          (rowBody.weakenBoundUnderTop SetSort.set)).instantiateTop
            (numₘ(rows.length))
      rw [Formula.LevyBound.boundedForall_instantiateTop_bvar]
      exact hRowsNumeral
    have hDomainRaw := FirstOrder.Derives.eq_subst
      (body := boundTemplate)
      (Metatheory.Derives.equality_symm hSequenceDomain) hNumeralAt
    change Γ ⊢ₘ[T]
      (Formula.LevyBound.boundedForall set_levy_bound
        ((.bvar .here) : SetTerm [SetSort.set] free)
        (rowBody.weakenBoundUnderTop SetSort.set)).instantiateTop
          (domₘ(sequence)) at hDomainRaw
    rw [Formula.LevyBound.boundedForall_instantiateTop_bvar] at hDomainRaw
    exact hDomainRaw
  have hPointwise : Γ ⊢ₘ[T]
      proof_sequence_code_pointwise_condition sequence trace code := by
    change Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (domₘ(sequence))
        (proof_sequence_code_row_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here))
    exact hRows
  have hTraceFinal : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(rows.length) ≐ₘ code := by
    simpa [trace, code] using
      standard_proof_trace_last_value
        (Γ := Γ)
          R.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport rows
  have hTraceAtDomain : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(rows.length) ≐ₘ trace ·ₘ domₘ(sequence) :=
    function_application_term_congr_argument_of_equality
      trace (numₘ(rows.length)) (domₘ(sequence))
      (Metatheory.Derives.equality_symm hSequenceDomain)
  have hFinal : Γ ⊢ₘ[T] code ≐ₘ trace ·ₘ domₘ(sequence) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hTraceFinal) hTraceAtDomain
  have hTraceBody : Γ ⊢ₘ[T]
      (trace ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        (((domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
          sequence_trace_code_bound trace code) ∧ₘ
          ((trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
            (proof_sequence_code_pointwise_condition sequence trace code ∧ₘ
              (code ≐ₘ trace ·ₘ domₘ(sequence)))) := by
    exact FirstOrder.Derives.conj_intro hTraceSpace <|
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hTraceDomain hTraceBound)
        (FirstOrder.Derives.conj_intro hZero <|
          FirstOrder.Derives.conj_intro hPointwise hFinal)
  have hTraceBodyCompact : Γ ⊢ₘ[T]
      (trace ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        proof_sequence_code_trace_body sequence code trace := by
    change Γ ⊢ₘ[T]
      (trace ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        (((domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
          sequence_trace_code_bound trace code) ∧ₘ
          ((trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
            (proof_sequence_code_pointwise_condition sequence trace code ∧ₘ
              (code ≐ₘ trace ·ₘ domₘ(sequence))))
    exact hTraceBody
  change Γ ⊢ₘ[T]
    ((((sequence ∈ₘ seq_spaceₘ(syntax_formula_code_set_term)) ∧ₘ
      (code ∈ₘ ωₘ)) ∧ₘ sequence_domain_code_bound sequence code) ∧ₘ
      proof_sequence_code_trace_condition sequence code)
  have hPrefix : Γ ⊢ₘ[T]
      ((sequence ∈ₘ seq_spaceₘ(syntax_formula_code_set_term)) ∧ₘ
        (code ∈ₘ ωₘ)) ∧ₘ sequence_domain_code_bound sequence code :=
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hSequenceSpace hCodeOmega)
      hDomainBound
  have hCore : Γ ⊢ₘ[T]
      (((sequence ∈ₘ seq_spaceₘ(syntax_formula_code_set_term)) ∧ₘ
        (code ∈ₘ ωₘ)) ∧ₘ sequence_domain_code_bound sequence code) :=
    hPrefix
  apply FirstOrder.Derives.conj_intro hCore
  apply FirstOrder.Derives.exists_intro trace
  change Γ ⊢ₘ[T]
    Formula.instantiateTop trace
      ((Formula.LevyBound.membership ProofT.set_levy_bound
          (.bvar .here)
          ((seq_spaceₘ(ωₘ)).weakenBound ProofT.set_levy_bound.sort)) ∧ₘ
        proof_sequence_code_trace_body
          (sequence.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here))
  rw [Formula.instantiateTop_conj]
  change Γ ⊢ₘ[T]
    Formula.instantiateTop trace
        (Formula.LevyBound.membership ProofT.set_levy_bound
          (.bvar .here)
          ((seq_spaceₘ(ωₘ)).weakenBound ProofT.set_levy_bound.sort)) ∧ₘ
      Formula.instantiateTop trace
        (ProofT.proof_sequence_code_trace_body_template
          (sequence.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here))
  rw [ProofT.FormulaTemplate.apply_three_instantiateTop_arguments]
  simp only [
    Term.instantiateTop_weakenBound]
  simpa only [proof_sequence_code_trace_body] using! hTraceBodyCompact

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
