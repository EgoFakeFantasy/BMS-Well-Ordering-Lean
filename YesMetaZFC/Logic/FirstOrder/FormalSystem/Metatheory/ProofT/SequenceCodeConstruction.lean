import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ArithmeticEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatSequenceInversion

/-!
# 内在自然数序列编码的正向构造

本模块把外部 `List Nat` 直接装配为内在自然数序列编码条件。序列图、轨迹图和
有限穷尽均由宿主递归与类型化 bound 上下文承载，不恢复旧的自由变量编号或
`Admissible` 桥接层。
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

private theorem omega_nonempty_of_numeral_member
    {T : SetTheory}
    (S : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (number : Nat)
    (hNumber : Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ) :
    Γ ⊢ₘ[T] ωₘ ≠ₘ ∅ₘ := by
  have hImp : Γ ⊢ₘ[T]
      (numₘ(number) ∈ₘ (ωₘ : SetOpenTerm free)) ⟶ₘ
        (ωₘ ≠ₘ (∅ₘ : SetOpenTerm free)) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.toArithmeticSupport.contains_empty_set hSentence)
      (member_implies_set_nonempty
        (Γ := Γ)
        (numₘ(number) : SetOpenTerm free)
        (ωₘ : SetOpenTerm free))
  exact FirstOrder.Derives.imp_elim hImp hNumber

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

private theorem nat_sequence_code_step_condition_instantiateTop
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

private theorem standard_nat_sequence_space
    {T : SetTheory}
    (S : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat)
    (hNumeralOmega : ∀ number,
      Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      nat_sequence_graph_term (bound := []) (free := free) tokens ∈ₘ
        seq_spaceₘ(ωₘ) := by
  let elements : List (SetOpenTerm free) :=
    tokens.map (fun token => numₘ(token))
  have hLengthOmega : Γ ⊢ₘ[T]
      numₘ(elements.length) ∈ₘ (ωₘ : SetOpenTerm free) := by
    simpa [elements] using hNumeralOmega tokens.length
  have hOmegaNonempty : Γ ⊢ₘ[T] ωₘ ≠ₘ ∅ₘ :=
    omega_nonempty_of_numeral_member S elements.length hLengthOmega
  have hSpace : Γ ⊢ₘ[T]
      standard_sequence elements ∈ₘ seq_spaceₘ(ωₘ) :=
    standard_sequence_mem_sequence_space
      S elements ωₘ hLengthOmega hOmegaNonempty (by
        intro element hElement
        rcases List.mem_map.mp hElement with ⟨number, _, rfl⟩
        exact hNumeralOmega number)
  simpa [elements, nat_sequence_graph_term, standard_sequence] using hSpace

private theorem standard_nat_sequence_value
    {T : SetTheory}
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat)
    (index : Nat)
    (hIndex : index < tokens.length) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free) tokens ·ₘ
        numₘ(index)) ≐ₘ
        numₘ(tokens[index]'hIndex) := by
  let elements : List (SetOpenTerm free) :=
    tokens.map (fun token => numₘ(token))
  have hGet : elements[index]? =
      some (numₘ(tokens[index]'hIndex) : SetOpenTerm free) := by
    simp [elements, hIndex]
  have hApply := standard_sequence_from_getElem?_apply_eq
    (Γ := Γ) S 0 hGet
  exact Metatheory.Derives.equality_symm <| by
    simpa [elements, nat_sequence_graph_term, standard_sequence] using hApply

private theorem standard_nat_sequence_trace_value
    {T : SetTheory}
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat)
    (index : Nat)
    (hIndex : index ≤ tokens.length) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free)
          (nat_sequence_code_trace tokens) ·ₘ numₘ(index)) ≐ₘ
        numₘ(nat_sequence_code_from 0 (tokens.take index)) := by
  let values : List Nat := nat_sequence_code_trace tokens
  let elements : List (SetOpenTerm free) :=
    values.map (fun value => numₘ(value))
  have hGetNat : values[index]? =
      some (nat_sequence_code_from 0 (tokens.take index)) := by
    simpa [values] using!
      nat_sequence_code_trace_from_getElem? 0 tokens index hIndex
  have hGet : elements[index]? =
      some (numₘ(nat_sequence_code_from 0 (tokens.take index)) :
        SetOpenTerm free) := by
    simpa [elements] using
      congrArg (Option.map (fun value =>
        (numₘ(value) : SetOpenTerm free))) hGetNat
  have hApply := standard_sequence_from_getElem?_apply_eq
    (Γ := Γ) S 0 hGet
  exact Metatheory.Derives.equality_symm <| by
    simpa [values, elements, nat_sequence_graph_term, standard_sequence] using hApply

private theorem standard_nat_sequence_trace_last_value
    {T : SetTheory}
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free)
          (nat_sequence_code_trace tokens) ·ₘ numₘ(tokens.length)) ≐ₘ
        numₘ(nat_sequence_code_value tokens) := by
  have hGetNat : (nat_sequence_code_trace tokens)[tokens.length]? =
      some (nat_sequence_code_value tokens) :=
    nat_sequence_code_trace_last tokens
  let elements : List (SetOpenTerm free) :=
    (nat_sequence_code_trace tokens).map (fun value => numₘ(value))
  have hGet : elements[tokens.length]? =
      some (numₘ(nat_sequence_code_value tokens) : SetOpenTerm free) := by
    simpa [elements] using
      congrArg (Option.map (fun value =>
        (numₘ(value) : SetOpenTerm free))) hGetNat
  have hApply := standard_sequence_from_getElem?_apply_eq
    (Γ := Γ) S 0 hGet
  exact Metatheory.Derives.equality_symm <| by
    simpa [elements, nat_sequence_graph_term, standard_sequence] using hApply

private theorem standard_nat_sequence_step
    {T : SetTheory}
    (C : CertificateCore T)
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat)
    (index : Nat)
    (hIndex : index < tokens.length) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free)
          (nat_sequence_code_trace tokens) ·ₘ Sₘ(numₘ(index))) ≐ₘ
        Sₘ(godel_pairₘ(
          nat_sequence_graph_term (bound := []) (free := free)
            (nat_sequence_code_trace tokens) ·ₘ numₘ(index),
          nat_sequence_graph_term (bound := []) (free := free) tokens ·ₘ
            numₘ(index))) := by
  let sequence : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free) tokens
  let trace : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free)
      (nat_sequence_code_trace tokens)
  have hTokenGet : tokens[index]? = some (tokens[index]'hIndex) :=
    List.getElem?_eq_getElem hIndex
  have hTraceNextNat := nat_sequence_code_trace_step
    tokens index (tokens[index]'hIndex) hTokenGet
  let traceValues : List Nat := nat_sequence_code_trace tokens
  let traceElements : List (SetOpenTerm free) :=
    traceValues.map (fun value => numₘ(value))
  have hTraceNextGet : traceElements[index + 1]? =
      some (numₘ(nat_sequence_code_step
        (nat_sequence_code_from 0 (tokens.take index))
        (tokens[index]'hIndex)) : SetOpenTerm free) := by
    simpa [traceElements, traceValues] using
      congrArg (Option.map (fun value =>
        (numₘ(value) : SetOpenTerm free))) hTraceNextNat
  have hTraceNextRaw := standard_sequence_from_getElem?_apply_eq
    (Γ := Γ) S 0 hTraceNextGet
  have hTraceNext : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(index + 1) ≐ₘ
        numₘ(nat_sequence_code_step
          (nat_sequence_code_from 0 (tokens.take index))
          (tokens[index]'hIndex)) := by
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace, traceElements, traceValues,
        nat_sequence_graph_term, standard_sequence] using hTraceNextRaw
  have hTraceCurrent := standard_nat_sequence_trace_value
    (Γ := Γ) S tokens index (Nat.le_of_lt hIndex)
  have hSequenceCurrent := standard_nat_sequence_value
    (Γ := Γ) S tokens index hIndex
  have hTraceCurrent' : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(index) ≐ₘ
        numₘ(nat_sequence_code_from 0 (tokens.take index)) := by
    simpa [trace] using hTraceCurrent
  have hSequenceCurrent' : Γ ⊢ₘ[T]
      sequence ·ₘ numₘ(index) ≐ₘ
        numₘ(tokens[index]'hIndex) := by
    simpa [sequence] using hSequenceCurrent
  have hPair := IntrinsicPairing.pair_congr_of_equalities
    (trace ·ₘ numₘ(index))
    (numₘ(nat_sequence_code_from 0 (tokens.take index)))
    (sequence ·ₘ numₘ(index))
    (numₘ(tokens[index]'hIndex)
      : SetOpenTerm free)
    hTraceCurrent' hSequenceCurrent'
  have hSuccessor := successor_term_congr_of_equality
    (godel_pairₘ(trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)))
    (godel_pairₘ(
      numₘ(nat_sequence_code_from 0 (tokens.take index)),
      numₘ(tokens[index]'hIndex))) hPair
  have hGround := nat_sequence_code_step_numeral_at C
    (nat_sequence_code_from 0 (tokens.take index))
    (tokens[index]'hIndex) (Γ := Γ)
  have hRight : Γ ⊢ₘ[T]
      Sₘ(godel_pairₘ(trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index))) ≐ₘ
        numₘ(nat_sequence_code_step
          (nat_sequence_code_from 0 (tokens.take index))
          (tokens[index]'hIndex)) :=
    Metatheory.Derives.equality_trans hSuccessor hGround
  have hLeft : Γ ⊢ₘ[T]
      trace ·ₘ Sₘ(numₘ(index)) ≐ₘ
        numₘ(nat_sequence_code_step
          (nat_sequence_code_from 0 (tokens.take index))
          (tokens[index]'hIndex)) := by
    simpa [finite_numeral_term, successor_term] using hTraceNext
  exact Metatheory.Derives.equality_trans hLeft
    (Metatheory.Derives.equality_symm hRight)

/-! ## 自然数序列总码 -/

theorem nat_sequence_code_condition_intro_standard
    {T : SetTheory}
    (C : CertificateCore T)
    (R : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat)
    (hNumeralOmega : ∀ number,
      Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      nat_sequence_code_condition
        (nat_sequence_graph_term (bound := []) (free := free) tokens)
        (numₘ(nat_sequence_code_value tokens)) := by
  let sequence : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free) tokens
  let code : SetOpenTerm free :=
    numₘ(nat_sequence_code_value tokens)
  let trace : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free)
      (nat_sequence_code_trace tokens)
  let sequenceElements : List (SetOpenTerm free) :=
    tokens.map (fun token => numₘ(token))
  let traceElements : List (SetOpenTerm free) :=
    (nat_sequence_code_trace tokens).map (fun value => numₘ(value))
  have hSequenceSpace : Γ ⊢ₘ[T] sequence ∈ₘ seq_spaceₘ(ωₘ) := by
    simpa [sequence] using standard_nat_sequence_space R tokens hNumeralOmega
  have hCodeOmega : Γ ⊢ₘ[T] code ∈ₘ ωₘ := by
    simpa [code] using hNumeralOmega (nat_sequence_code_value tokens)
  have hSequenceDomain : Γ ⊢ₘ[T]
      domₘ(sequence) ≐ₘ numₘ(tokens.length) := by
    simpa [sequence, sequenceElements, nat_sequence_graph_term,
      standard_sequence] using
      (standard_sequence_domain_eq
        (Γ := Γ) R.toFiniteSequenceGraphSupport
        (elements := sequenceElements))
  have hSequenceDomainBound : Γ ⊢ₘ[T]
      domₘ(sequence) ∈ₘ Sₘ(code) := by
    have hLengthMember : Γ ⊢ₘ[T]
        numₘ(tokens.length) ∈ₘ
          Sₘ(numₘ(nat_sequence_code_value tokens)) := by
      simpa [code, finite_numeral_term, successor_term] using
        (FirstOrder.Derives.context_weaken
          (Γ := ([] : Context signature free))
          (Δ := Γ) (by simp)
          (numeral_mem_of_lt
            R.toArithmeticSupport.contains_successor
            (Nat.lt_succ_of_le (nat_sequence_length_le_code tokens))))
    exact FirstOrder.Derives.iff_elim_right
      (membership_left_iff_of_equality
        (domₘ(sequence)) (numₘ(tokens.length))
        (Sₘ(code)) hSequenceDomain)
      hLengthMember
  have hSequenceValueBound : Γ ⊢ₘ[T]
      nat_sequence_value_code_bound sequence code := by
    let body : SetFormula [SetSort.set] free :=
      ((sequence.weakenBound SetSort.set ·ₘ
          (.bvar .here : SetTerm [SetSort.set] free)) ∈ₘ
        code.weakenBound SetSort.set)
    have hNumeralBound : Γ ⊢ₘ[T]
        Formula.LevyBound.boundedForall set_levy_bound
          (numₘ(tokens.length)) body :=
      bounded_forall_numeral_intro
        C.toFiniteCore tokens.length body (by
          intro index hIndex
          have hValue := standard_nat_sequence_value
            (Γ := Γ) R.toFiniteSequenceEvaluationSupport
            tokens index hIndex
          have hMember : Γ ⊢ₘ[T]
              (sequence ·ₘ numₘ(index)) ∈ₘ code := by
            exact FirstOrder.Derives.iff_elim_right
              (membership_left_iff_of_equality
                (sequence ·ₘ numₘ(index))
                (numₘ(tokens[index]'hIndex)) code hValue)
              (by
                simpa [code] using
                  (FirstOrder.Derives.context_weaken
                    (Γ := ([] : Context signature free))
                    (Δ := Γ) (by simp)
                    (numeral_mem_of_lt
                      R.toArithmeticSupport.contains_successor
                      (mem_lt_nat_sequence_code_value
                        (List.getElem_mem hIndex)))))
          change Γ ⊢ₘ[T]
            Formula.instantiateTop (numₘ(index))
              (((sequence.weakenBound SetSort.set ·ₘ
                  (.bvar .here : SetTerm [SetSort.set] free)) ∈ₘ
                code.weakenBound SetSort.set))
          rw [membership_body_instantiateTop]
          exact hMember)
    let boundTemplate : SetFormula [SetSort.set] free :=
      Formula.LevyBound.boundedForall set_levy_bound
        ((.bvar .here) : SetTerm [SetSort.set] free)
        (body.weakenBoundUnderTop SetSort.set)
    have hNumeralAt : Γ ⊢ₘ[T]
        boundTemplate.instantiateTop (numₘ(tokens.length)) := by
      change Γ ⊢ₘ[T]
        (Formula.LevyBound.boundedForall set_levy_bound
          ((.bvar .here) : SetTerm [SetSort.set] free)
          (body.weakenBoundUnderTop SetSort.set)).instantiateTop
            (numₘ(tokens.length))
      rw [Formula.LevyBound.boundedForall_instantiateTop_bvar]
      exact hNumeralBound
    have hDomainRaw := FirstOrder.Derives.eq_subst
      (body := boundTemplate)
      (FirstOrder.Derives.eq_symm hSequenceDomain) hNumeralAt
    have hDomain : Γ ⊢ₘ[T]
        Formula.LevyBound.boundedForall set_levy_bound
          (domₘ(sequence)) body := by
      change Γ ⊢ₘ[T]
        (Formula.LevyBound.boundedForall set_levy_bound
          ((.bvar .here) : SetTerm [SetSort.set] free)
          (body.weakenBoundUnderTop SetSort.set)).instantiateTop
            (domₘ(sequence)) at hDomainRaw
      rw [Formula.LevyBound.boundedForall_instantiateTop_bvar] at hDomainRaw
      exact hDomainRaw
    simpa [nat_sequence_value_code_bound, body] using hDomain
  have hTraceSpace : Γ ⊢ₘ[T] trace ∈ₘ seq_spaceₘ(ωₘ) := by
    have hLengthOmega : Γ ⊢ₘ[T]
        numₘ(traceElements.length) ∈ₘ
          (ωₘ : SetOpenTerm free) := by
      simpa [traceElements, nat_sequence_code_trace_length] using
        hNumeralOmega ((nat_sequence_code_trace tokens).length)
    have hSpace := standard_sequence_mem_sequence_space
      R traceElements ωₘ hLengthOmega
      (omega_nonempty_of_numeral_member R 0 (hNumeralOmega 0)) (by
        intro element hElement
        rcases List.mem_map.mp hElement with ⟨number, _, rfl⟩
        exact hNumeralOmega number)
    simpa [trace, traceElements, nat_sequence_graph_term, standard_sequence] using hSpace
  have hTraceDomain : Γ ⊢ₘ[T]
      domₘ(trace) ≐ₘ Sₘ(domₘ(sequence)) := by
    have hRaw : Γ ⊢ₘ[T]
        domₘ(trace) ≐ₘ
          numₘ((nat_sequence_code_trace tokens).length) := by
      simpa [trace, traceElements, nat_sequence_graph_term,
        standard_sequence] using
        (standard_sequence_domain_eq
          (Γ := Γ) R.toFiniteSequenceGraphSupport
          (elements := traceElements))
    have hTraceNumeral : Γ ⊢ₘ[T]
        domₘ(trace) ≐ₘ Sₘ(numₘ(tokens.length)) := by
      simpa [nat_sequence_code_trace_length, finite_numeral_term,
        successor_term] using hRaw
    have hSequenceSuccessor := successor_term_congr_of_equality
      (domₘ(sequence)) (numₘ(tokens.length)) hSequenceDomain
    exact Metatheory.Derives.equality_trans hTraceNumeral
      (Metatheory.Derives.equality_symm hSequenceSuccessor)
  have hTraceValueBound : Γ ⊢ₘ[T]
      sequence_trace_code_bound trace code := by
    let body : SetFormula [SetSort.set] free :=
      ((trace.weakenBound SetSort.set ·ₘ
          (.bvar .here : SetTerm [SetSort.set] free)) ∈ₘ
        Sₘ(code.weakenBound SetSort.set))
    have hNumeralBound : Γ ⊢ₘ[T]
        Formula.LevyBound.boundedForall set_levy_bound
          (numₘ((nat_sequence_code_trace tokens).length)) body :=
      bounded_forall_numeral_intro
        C.toFiniteCore (nat_sequence_code_trace tokens).length body (by
          intro index hIndex
          have hTraceLength :
              (nat_sequence_code_trace tokens).length = tokens.length + 1 :=
            nat_sequence_code_trace_length tokens
          have hIndexLe : index ≤ tokens.length := by
            omega
          have hValue := standard_nat_sequence_trace_value
            (Γ := Γ) R.toFiniteSequenceEvaluationSupport
            tokens index hIndexLe
          have hTraceMember :
              nat_sequence_code_from 0 (tokens.take index) ≤
                nat_sequence_code_value tokens := by
            apply trace_mem_le_nat_sequence_code_value
            have hGet :
                (nat_sequence_code_trace tokens)[index]? =
                  some (nat_sequence_code_from 0 (tokens.take index)) :=
              nat_sequence_code_trace_from_getElem?
                0 tokens index hIndexLe
            exact List.mem_of_getElem? hGet
          have hNumeralMember : ([] : Context signature free) ⊢ₘ[T]
              numₘ(nat_sequence_code_from 0 (tokens.take index)) ∈ₘ
                Sₘ(numₘ(nat_sequence_code_value tokens)) := by
            simpa [finite_numeral_term, successor_term] using
              (numeral_mem_of_lt
                R.toArithmeticSupport.contains_successor
                (Nat.lt_succ_of_le hTraceMember))
          have hNumeralMemberΓ : Γ ⊢ₘ[T]
              numₘ(nat_sequence_code_from 0 (tokens.take index)) ∈ₘ
                Sₘ(numₘ(nat_sequence_code_value tokens)) :=
            FirstOrder.Derives.context_weaken
              (Γ := ([] : Context signature free))
              (Δ := Γ) (by simp) hNumeralMember
          have hMember : Γ ⊢ₘ[T]
              (trace ·ₘ numₘ(index)) ∈ₘ Sₘ(code) := by
            exact FirstOrder.Derives.iff_elim_right
              (membership_left_iff_of_equality
                (trace ·ₘ numₘ(index))
                (numₘ(nat_sequence_code_from 0 (tokens.take index)))
                (Sₘ(code)) hValue)
              (by simpa [code] using hNumeralMemberΓ)
          change Γ ⊢ₘ[T]
            Formula.instantiateTop (numₘ(index))
              (((trace.weakenBound SetSort.set ·ₘ
                  (.bvar .here : SetTerm [SetSort.set] free)) ∈ₘ
                Sₘ(code.weakenBound SetSort.set)))
          rw [successor_membership_body_instantiateTop]
          exact hMember)
    let boundTemplate : SetFormula [SetSort.set] free :=
      Formula.LevyBound.boundedForall set_levy_bound
        ((.bvar .here) : SetTerm [SetSort.set] free)
        (body.weakenBoundUnderTop SetSort.set)
    have hNumeralAt : Γ ⊢ₘ[T]
        boundTemplate.instantiateTop
          (numₘ((nat_sequence_code_trace tokens).length)) := by
      change Γ ⊢ₘ[T]
        (Formula.LevyBound.boundedForall set_levy_bound
          ((.bvar .here) : SetTerm [SetSort.set] free)
          (body.weakenBoundUnderTop SetSort.set)).instantiateTop
            (numₘ((nat_sequence_code_trace tokens).length))
      rw [Formula.LevyBound.boundedForall_instantiateTop_bvar]
      exact hNumeralBound
    have hDomainRaw := FirstOrder.Derives.eq_subst
      (body := boundTemplate)
      (FirstOrder.Derives.eq_symm
        (show Γ ⊢ₘ[T]
          domₘ(trace) ≐ₘ
            numₘ((nat_sequence_code_trace tokens).length) by
          simpa [trace, traceElements, nat_sequence_graph_term,
            standard_sequence] using
            (standard_sequence_domain_eq
              (Γ := Γ) R.toFiniteSequenceGraphSupport
              (elements := traceElements)))) hNumeralAt
    have hDomain : Γ ⊢ₘ[T]
        Formula.LevyBound.boundedForall set_levy_bound
          (domₘ(trace)) body := by
      change Γ ⊢ₘ[T]
        (Formula.LevyBound.boundedForall set_levy_bound
          ((.bvar .here) : SetTerm [SetSort.set] free)
          (body.weakenBoundUnderTop SetSort.set)).instantiateTop
            (domₘ(trace)) at hDomainRaw
      rw [Formula.LevyBound.boundedForall_instantiateTop_bvar] at hDomainRaw
      exact hDomainRaw
    simpa [sequence_trace_code_bound, body] using hDomain
  have hZero : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(0) ≐ₘ numₘ(0) := by
    have hGetNat : (nat_sequence_code_trace tokens)[0]? = some 0 := by
      cases tokens <;> simp [nat_sequence_code_trace, nat_sequence_code_trace_from]
    let elements : List (SetOpenTerm free) :=
      (nat_sequence_code_trace tokens).map (fun value => numₘ(value))
    have hGet : elements[0]? = some (numₘ(0) : SetOpenTerm free) := by
      simpa [elements] using
        congrArg (Option.map (fun value =>
          (numₘ(value) : SetOpenTerm free))) hGetNat
    have hApply := standard_sequence_from_getElem?_apply_eq
      (Γ := Γ) R.toFiniteSequenceEvaluationSupport
      0 hGet
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace, elements, nat_sequence_graph_term, standard_sequence] using hApply
  have hStepNumeral : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (numₘ(tokens.length))
        (nat_sequence_code_step_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (.bvar .here)) :=
    bounded_forall_numeral_intro C.toFiniteCore tokens.length _ (by
      intro index hIndex
      have hStep := standard_nat_sequence_step (Γ := Γ) C
        R.toFiniteSequenceEvaluationSupport
        tokens index hIndex
      rw [nat_sequence_code_step_condition_instantiateTop sequence trace index]
      simpa [sequence, trace] using! hStep)
  have hStep : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (domₘ(sequence))
        (nat_sequence_code_step_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (.bvar .here)) := by
    let body : SetFormula [SetSort.set] free :=
      nat_sequence_code_step_condition
        (sequence.weakenBound SetSort.set)
        (trace.weakenBound SetSort.set)
        (.bvar .here)
    let boundTemplate : SetFormula [SetSort.set] free :=
      Formula.LevyBound.boundedForall set_levy_bound
        ((.bvar .here) : SetTerm [SetSort.set] free)
        (body.weakenBoundUnderTop SetSort.set)
    have hNumeralAt : Γ ⊢ₘ[T]
        boundTemplate.instantiateTop (numₘ(tokens.length)) := by
      change Γ ⊢ₘ[T]
        (Formula.LevyBound.boundedForall set_levy_bound
          ((.bvar .here) : SetTerm [SetSort.set] free)
          (body.weakenBoundUnderTop SetSort.set)).instantiateTop
            (numₘ(tokens.length))
      rw [Formula.LevyBound.boundedForall_instantiateTop_bvar]
      exact hStepNumeral
    have hDomainRaw := FirstOrder.Derives.eq_subst
      (body := boundTemplate)
      (FirstOrder.Derives.eq_symm hSequenceDomain) hNumeralAt
    change Γ ⊢ₘ[T]
      (Formula.LevyBound.boundedForall set_levy_bound
        ((.bvar .here) : SetTerm [SetSort.set] free)
        (body.weakenBoundUnderTop SetSort.set)).instantiateTop
          (domₘ(sequence)) at hDomainRaw
    rw [Formula.LevyBound.boundedForall_instantiateTop_bvar] at hDomainRaw
    simpa [body] using hDomainRaw
  have hFinalTrace : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(tokens.length) ≐ₘ code := by
    simpa [trace, code] using
      (standard_nat_sequence_trace_last_value
        (Γ := Γ)
        R.toFiniteSequenceEvaluationSupport tokens)
  have hTraceAtDomain : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(tokens.length) ≐ₘ trace ·ₘ domₘ(sequence) :=
    function_application_term_congr_argument_of_equality
      trace (numₘ(tokens.length)) (domₘ(sequence))
      (Metatheory.Derives.equality_symm hSequenceDomain)
  have hFinal : Γ ⊢ₘ[T] code ≐ₘ trace ·ₘ domₘ(sequence) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hFinalTrace) hTraceAtDomain
  have hTraceBody : Γ ⊢ₘ[T]
      (trace ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        (((domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
          sequence_trace_code_bound trace code) ∧ₘ
          ((trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
            (Formula.LevyBound.boundedForall set_levy_bound
              (domₘ(sequence))
              (nat_sequence_code_step_condition
                (sequence.weakenBound SetSort.set)
                (trace.weakenBound SetSort.set)
                (.bvar .here)) ∧ₘ
              (code ≐ₘ trace ·ₘ domₘ(sequence)))) := by
    exact FirstOrder.Derives.conj_intro hTraceSpace <|
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hTraceDomain hTraceValueBound)
        (FirstOrder.Derives.conj_intro hZero <|
          FirstOrder.Derives.conj_intro hStep hFinal)
  change Γ ⊢ₘ[T]
    ((((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
      sequence_domain_code_bound sequence code) ∧ₘ
      nat_sequence_value_code_bound sequence code) ∧ₘ
      ((nat_sequence_code_trace_condition
        (sequence.weakenBound SetSort.set)
        (code.weakenBound SetSort.set)
        (.bvar .here)).existsE SetSort.set)
  have hPrefix : Γ ⊢ₘ[T]
      ((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
        sequence_domain_code_bound sequence code :=
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hSequenceSpace hCodeOmega)
      hSequenceDomainBound
  have hCore : Γ ⊢ₘ[T]
      (((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
        sequence_domain_code_bound sequence code) ∧ₘ
        nat_sequence_value_code_bound sequence code :=
    FirstOrder.Derives.conj_intro hPrefix hSequenceValueBound
  apply FirstOrder.Derives.conj_intro hCore
  apply FirstOrder.Derives.exists_intro trace
  change Γ ⊢ₘ[T]
    Formula.instantiateTop trace
      (nat_sequence_code_trace_condition
        (sequence.weakenBound SetSort.set)
        (code.weakenBound SetSort.set)
        (.bvar .here))
  simpa [nat_sequence_code_trace_condition, sequence, code, trace,
    nat_sequence_code_step_condition, sequence_trace_code_bound,
    Formula.instantiateTop, Substitution.instantiateTop,
    Formula.substitute, Formula.substituteMapped,
    Term.instantiateTop, Term.substituteMapped,
    Arguments.instantiateTop, Arguments.substituteMapped,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    VariableSubstitution.instantiateTop, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftBound,
    VariableSubstitution.weakenBound,
    Term.substituteMapped_weakenBound,
    Arguments.substituteMapped_weakenBound] using hTraceBody

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
