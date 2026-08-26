import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ObjectReplay

/-!
# ProofT 证明序列末行反演

本模块只处理规范二维证明序列的 terminal 条件。匿名末行索引由公式中的
定义域成员 guard 直接压入有限 numeral；随后有限分支唯一锁定最后一个
外部索引。空序列或末行 token 不匹配都会在对象层直接推出矛盾。
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

set_option autoImplicit false

/-- 规范二维证明行序列的定义域等于外部行数。 -/
theorem ProofT.rows_domain
    {T : SetTheory}
    (R : ProofT.ObjectReplay T)
    {Γ : Context signature}
    (rows : List (List Nat)) :
    Γ ⊢ₘ[T]
      domₘ(standard_sequence
        (rows.map standard_token_sequence)) ≐ₘ
        numₘ(rows.length) := by
  let elements : List SetTerm :=
    rows.map standard_token_sequence
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_admissible tokens
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_freeSupport_nil tokens
  apply FirstOrder.Derives.context_weaken
    (Γ := [])
    (Δ := Γ)
    (by simp)
  simpa [elements] using
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula => R.standard_sequence hFormula)
      (standard_sequence_domain_eq_numeral_length
        hElements
        (stdseq_element_fresh_of_support_nil hElementsClosed 0)
        (stdseq_element_fresh_of_support_nil hElementsClosed 1))

/-- 规范二维证明行序列在有效 numeral 索引处等于对应外部行。 -/
theorem ProofT.row_apply
    {T : SetTheory}
    (R : ProofT.ObjectReplay T)
    {Γ : Context signature}
    (rows : List (List Nat))
    (index : Nat)
    (hIndex : index < rows.length) :
    Γ ⊢ₘ[T]
      (standard_sequence
          (rows.map standard_token_sequence) ·ₘ
        numₘ(index)) ≐ₘ
        standard_token_sequence rows[index] := by
  let elements : List SetTerm :=
    rows.map standard_token_sequence
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_admissible tokens
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_freeSupport_nil tokens
  have hGet :
      elements[index]? =
        some (standard_token_sequence rows[index]) := by
    simp [elements, hIndex]
  apply FirstOrder.Derives.context_weaken
    (Γ := [])
    (Δ := Γ)
    (by simp)
  simpa [elements] using
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula => R.standard_sequence hFormula)
      (standard_sequence_from_apply_getElem?
        0 hGet hElements hElementsClosed
        (standard_token_sequence_admissible rows[index]))

/-- terminal 条件沿闭序列上的目标码等式运输。 -/
theorem ProofT.terminal_of_conclusion_eq
    {T : SetTheory}
    {Γ : Context signature}
    (sequence left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hSequenceClosed :
      Term.freeSupport sequence = [])
    (hEquality :
      Γ ⊢ₘ[T]
        left ≐ₘ right)
    (hTerminal :
      Γ ⊢ₘ[T]
        proof_sequence_terminal_condition
          sequence left) :
    Γ ⊢ₘ[T]
      proof_sequence_terminal_condition
        sequence right := by
  let basis : List SetFormula :=
    [sequence ≐ₘ sequence, left ≐ₘ left, right ≐ₘ right]
  let parameter : FreeVarId :=
    FreshVariable.fresh_id SetSort.set basis
  let body : SetFormula :=
    proof_sequence_terminal_condition
      sequence (x#parameter)
  have hParameter :
      Term.Admissible (x#parameter) SetSort.set :=
    set_variable_admissible parameter
  have hSequenceFresh :
      (SetSort.set, parameter) ∉
        Term.freeSupport sequence := by
    rw [hSequenceClosed]
    exact List.not_mem_nil
  have hSequenceFixed
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter
          replacement sequence =
        sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement
      sequence hSequenceFresh
  have hLeftSubstitution :
      Formula.substituteFree SetSort.set parameter left body =
        proof_sequence_terminal_condition
          sequence left := by
    simpa [body] using
      proof_sequence_terminal_condition_substitute
        sequence (x#parameter) left
        sequence left parameter
        (hSequenceFixed left)
        (by simp [Term.substituteFree, set_variable])
  have hRightSubstitution :
      Formula.substituteFree SetSort.set parameter right body =
        proof_sequence_terminal_condition
          sequence right := by
    simpa [body] using
      proof_sequence_terminal_condition_substitute
        sequence (x#parameter) right
        sequence right parameter
        (hSequenceFixed right)
        (by simp [Term.substituteFree, set_variable])
  have hAtLeft :
      Γ ⊢ₘ[T]
        Formula.substituteFree SetSort.set
          parameter left body := by
    rw [hLeftSubstitution]
    exact hTerminal
  have hTransport :
      Γ ⊢ₘ[T]
        Formula.substituteFree SetSort.set
          parameter right body :=
    FirstOrder.Derives.eq_subst_m
      (sort := SetSort.set)
      (eigen := parameter)
      (left := left)
      (right := right)
      (body := body)
      hEquality hAtLeft
  rw [hRightSubstitution] at hTransport
  exact hTransport

theorem ProofT.rows_terminal_falsum
    {T : SetTheory}
    (C : ProofT.FiniteCore T)
    (R : ProofT.ObjectReplay T)
    {Γ : Context signature}
    (rows : List (List Nat))
    (targetTokens : List Nat)
    (hMismatch :
      ∀ index (hIndex : index < rows.length),
        rows.length = index + 1 →
          targetTokens ≠ rows[index])
    (hTerminal :
      Γ ⊢ₘ[T]
        proof_sequence_terminal_condition
          (standard_sequence
            (rows.map standard_token_sequence))
          (standard_token_sequence targetTokens)) :
    Γ ⊢ₘ[T] Formula.falsum := by
  let sequence : SetTerm :=
    standard_sequence
      (rows.map standard_token_sequence)
  let conclusion : SetTerm :=
    standard_token_sequence targetTokens
  let terminalFormula : SetFormula :=
    proof_sequence_terminal_condition sequence conclusion
  let basis : List SetFormula :=
    Formula.falsum ::
      (sequence ≐ₘ sequence) ::
      (conclusion ≐ₘ conclusion) ::
      terminalFormula :: Γ
  let terminalId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set basis
  let body : SetFormula :=
    (x#terminalId ∈ₘ domₘ(sequence)) ∧ₘ
      ((domₘ(sequence) ≐ₘ Sₘ(x#terminalId)) ∧ₘ
        (conclusion ≐ₘ (sequence ·ₘ x#terminalId)))
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    dsimp [sequence]
    apply seq_admissible_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_admissible tokens
  have hSequenceClosed :
      Term.freeSupport sequence = [] := by
    dsimp [sequence]
    apply seq_support_nil_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_freeSupport_nil tokens
  have hConclusion :
      Term.Admissible conclusion SetSort.set := by
    simpa [conclusion] using
      standard_token_sequence_admissible targetTokens
  have hConclusionClosed :
      Term.freeSupport conclusion = [] := by
    simp [conclusion]
  have hTerminalAt :
      Γ ⊢ₘ[T]
        terminalFormula := by
    simpa [terminalFormula, sequence, conclusion] using hTerminal
  have hBody :
      Formula.Admissible body := by
    simpa [body] using
      Formula.Admissible.conj
        (membership_formula_admissible
          (set_variable_admissible terminalId)
          (domain_term_admissible sequence hSequence))
        (Formula.Admissible.conj
          (Formula.Admissible.equal
            (domain_term_admissible sequence hSequence)
            (successor_term_admissible
              (x#terminalId)
              (set_variable_admissible terminalId)))
          (Formula.Admissible.equal
            hConclusion
            (function_application_term_admissible
              sequence (x#terminalId) hSequence
              (set_variable_admissible terminalId))))
  have hSequenceClose :
      Term.closeFreeAt SetSort.set terminalId 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set terminalId 0 sequence hSequence.2 (by
        rw [hSequenceClosed]
        exact List.not_mem_nil)
  have hConclusionClose :
      Term.closeFreeAt SetSort.set terminalId 0 conclusion =
        conclusion :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set terminalId 0 conclusion hConclusion.2 (by
        rw [hConclusionClosed]
        exact List.not_mem_nil)
  have hExists :
      Γ ⊢ₘ[T]
        ∃ₘ[SetSort.set, terminalId], body := by
    simpa [terminalFormula, proof_sequence_terminal_condition,
      body, Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable,
      hSequenceClose, hConclusionClose] using hTerminalAt
  nd_apply FirstOrder.Derives.exists_elim
    (T := T)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := terminalId)
    (body := body)
    (conclusion := Formula.falsum)
  · intro formula hFormula
    rw [(C.theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    dsimp [terminalId]
    apply FreshVariable.fresh_id_not_mem_m
      (sort := SetSort.set)
      (formulas := basis)
      (formula := formula)
    simp [basis, hFormula]
  · change (SetSort.set, terminalId) ∉
      Formula.freeSupport (Formula.falsum : SetFormula)
    intro hMember
    exact List.not_mem_nil hMember
  · exact hExists
  · let Δ : Context signature := body :: Γ
    have hBodyAt :
        Δ ⊢ₘ[T] body :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hTail :
        Δ ⊢ₘ[T]
          (domₘ(sequence) ≐ₘ Sₘ(x#terminalId)) ∧ₘ
            (conclusion ≐ₘ (sequence ·ₘ x#terminalId)) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight hBodyAt
    have hDomainWitness :
        Δ ⊢ₘ[T]
          domₘ(sequence) ≐ₘ Sₘ(x#terminalId) := by
      exact FirstOrder.Derives.conjElimLeft hTail
    have hConclusionWitness :
        Δ ⊢ₘ[T]
          conclusion ≐ₘ (sequence ·ₘ x#terminalId) := by
      exact FirstOrder.Derives.conjElimRight hTail
    have hIndexDomain :
        Δ ⊢ₘ[T]
          (x#terminalId) ∈ₘ domₘ(sequence) :=
      FirstOrder.Derives.conjElimLeft hBodyAt
    have hDomain :
        Δ ⊢ₘ[T]
          domₘ(sequence) ≐ₘ numₘ(rows.length) := by
      simpa [sequence] using
        ProofT.rows_domain
          R
          (Γ := Δ) rows
    have hIndexMember :
        Δ ⊢ₘ[T]
          (x#terminalId) ∈ₘ numₘ(rows.length) :=
      FirstOrder.Derives.iffElimRight
        (membership_right_iff_of_equality
          (x#terminalId)
          (domₘ(sequence)) (numₘ(rows.length))
          (set_variable_admissible terminalId)
          (domain_term_admissible sequence hSequence)
          (finite_numeral_term_admissible rows.length)
          hDomain)
        hIndexDomain
    apply
      C.member_elim
        rows.length
        (x#terminalId)
        Formula.falsum
        (set_variable_admissible terminalId)
        Formula.Admissible.falsum
        hIndexMember
    intro index hIndex
    let Ε : Context signature :=
      ((x#terminalId) ≐ₘ numₘ(index)) :: Δ
    have hIndexEquality :
        Ε ⊢ₘ[T]
          (x#terminalId) ≐ₘ numₘ(index) :=
      FirstOrder.Derives.assumption (by simp [Ε])
    have hDomainWitnessAt :
        Ε ⊢ₘ[T]
          domₘ(sequence) ≐ₘ Sₘ(x#terminalId) :=
      FirstOrder.Derives.context_weaken_cons hDomainWitness
    have hSuccessorEquality :
        Ε ⊢ₘ[T]
          Sₘ(x#terminalId) ≐ₘ Sₘ(numₘ(index)) :=
      successor_term_congr_of_equality
        (x#terminalId) (numₘ(index))
        (set_variable_admissible terminalId)
        (finite_numeral_term_admissible index)
        hIndexEquality
    have hDomainIndex :
        Ε ⊢ₘ[T]
          domₘ(sequence) ≐ₘ numₘ(index + 1) := by
      simpa [finite_numeral_term, successor_term] using
        Metatheory.Derives.equality_trans
          hDomainWitnessAt hSuccessorEquality
    have hDomainAt :
        Ε ⊢ₘ[T]
          domₘ(sequence) ≐ₘ numₘ(rows.length) :=
      FirstOrder.Derives.context_weaken_cons hDomain
    have hLengthEquality :
        Ε ⊢ₘ[T]
          numₘ(rows.length) ≐ₘ numₘ(index + 1) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm hDomainAt)
        hDomainIndex
    by_cases hLast : rows.length = index + 1
    · have hConclusionWitnessAt :
          Ε ⊢ₘ[T]
            conclusion ≐ₘ (sequence ·ₘ x#terminalId) :=
        FirstOrder.Derives.context_weaken_cons
          hConclusionWitness
      have hApplicationEquality :
          Ε ⊢ₘ[T]
            (sequence ·ₘ x#terminalId) ≐ₘ
              (sequence ·ₘ numₘ(index)) :=
        function_application_term_congr_argument_of_equality
          sequence (x#terminalId) (numₘ(index))
          hSequence
          (set_variable_admissible terminalId)
          (finite_numeral_term_admissible index)
          hIndexEquality
      have hApplication :
          Ε ⊢ₘ[T]
            (sequence ·ₘ numₘ(index)) ≐ₘ
              standard_token_sequence rows[index] := by
        simpa [sequence] using
          ProofT.row_apply
            R
            (Γ := Ε) rows index hIndex
      have hTargetEquality :
          Ε ⊢ₘ[T]
            standard_token_sequence targetTokens ≐ₘ
              standard_token_sequence rows[index] := by
        simpa [conclusion] using
          Metatheory.Derives.equality_trans
            hConclusionWitnessAt
            (Metatheory.Derives.equality_trans
              hApplicationEquality hApplication)
      have hNotEquality :
          Ε ⊢ₘ[T]
            ¬ₘ (standard_token_sequence targetTokens ≐ₘ
              standard_token_sequence rows[index]) := by
        apply FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := Ε)
          (by simp)
        exact FirstOrder.Derives.theory_weaken
          (fun _ hFormula => R.standard_sequence hFormula)
          (standard_token_sequence_ne
            (hMismatch index hIndex hLast))
      exact FirstOrder.Derives.negElim
        hTargetEquality hNotEquality
    · exact
        FirstOrder.Derives.negElim hLengthEquality <|
          FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ε) (by simp) (C.numeral_ne hLast)

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
