import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequenceConcatenation
/-!
# 标准 token 序列族的对象折叠语义
本模块用全部有限前缀组成的标准序列作为 `flattenₘ` 的累积器见证，证明任意
token 串族的对象折叠与 `List.flatten` 严格对应。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-- 闭项族在需要时降格为单编号新鲜性。 -/
private theorem stdflat_fresh_of_closed
    {elements : List SetTerm}
    (hClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = [])
    (id : FreeVarId) :
    ∀ element, element ∈ elements →
      (SetSort.set, id) ∉ Term.freeSupport element := by
  intro element hElement
  rw [hClosed element hElement]
  exact List.not_mem_nil
/-- 有限序列折叠项的合法性由序列项证书直接计算。 -/
@[term_check]
theorem finite_sequence_flatten_term_check
    {sequence : SetTerm}
    (hSequence : Term.CheckCertificate sequence SetSort.set) :
    Term.CheckCertificate (flattenₘ(sequence)) SetSort.set :=
  Term.check_admissible_complete <|
    finite_sequence_flatten_term_admissible
      sequence hSequence.admissible
/-! ## 外部前缀累积器 -/
private def stdflat_prefixes_from (accumulator : List Nat) : List (List Nat) → List (List Nat)
  | [] => [accumulator]
  | head :: tail =>
      accumulator ::
        stdflat_prefixes_from (accumulator ++ head) tail
private def stdflat_prefixes (pieces : List (List Nat)) : List (List Nat) :=
  stdflat_prefixes_from [] pieces
private theorem stdflat_prefixes_from_length (accumulator : List Nat) (pieces : List (List Nat)) : (stdflat_prefixes_from accumulator pieces).length =
      pieces.length + 1 := by
  induction pieces generalizing accumulator with
  | nil => rfl
  | cons head tail ih =>
      simp [stdflat_prefixes_from, ih]
private theorem stdflat_prefixes_length (pieces : List (List Nat)) : (stdflat_prefixes pieces).length =
      pieces.length + 1 := by
  exact stdflat_prefixes_from_length [] pieces
private theorem stdflat_prefixes_from_terminal (accumulator : List Nat) (pieces : List (List Nat)) :
    (stdflat_prefixes_from accumulator pieces)[pieces.length]? =
      some (accumulator ++ pieces.flatten) := by
  induction pieces generalizing accumulator with
  | nil =>
      simp [stdflat_prefixes_from]
  | cons head tail ih =>
      simpa [stdflat_prefixes_from, List.flatten_cons,
        List.append_assoc] using ih (accumulator ++ head)
private theorem stdflat_prefixes_from_head (accumulator : List Nat) (pieces : List (List Nat)) : (stdflat_prefixes_from accumulator pieces)[0]? =
      some accumulator := by
  cases pieces <;> rfl
private theorem stdflat_prefixes_terminal (pieces : List (List Nat)) : (stdflat_prefixes pieces)[pieces.length]? =
      some pieces.flatten := by
  simpa [stdflat_prefixes] using
    stdflat_prefixes_from_terminal [] pieces
private theorem stdflat_prefixes_from_step (accumulator : List Nat) (pieces : List (List Nat))
    {index : Nat} {piece : List Nat} (hGet : pieces[index]? = some piece) :
    ∃ current, (stdflat_prefixes_from accumulator pieces)[index]? =
          some current ∧ (stdflat_prefixes_from accumulator pieces)[index + 1]? =
          some (current ++ piece) := by
  induction pieces generalizing accumulator index piece with
  | nil =>
      simp at hGet
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at hGet
          subst piece
          refine ⟨accumulator, ?_, ?_⟩
          · simp [stdflat_prefixes_from]
          · simpa [stdflat_prefixes_from] using
              stdflat_prefixes_from_head (accumulator ++ head) tail
      | succ index =>
          have hTail : tail[index]? = some piece := by
            simpa using hGet
          rcases ih (accumulator ++ head) hTail with
            ⟨current, hCurrent, hNext⟩
          exact ⟨current, by
            simpa [stdflat_prefixes_from] using hCurrent, by
            simpa [stdflat_prefixes_from, Nat.add_assoc] using hNext⟩
private theorem stdflat_prefixes_step (pieces : List (List Nat))
    {index : Nat} {piece : List Nat} (hGet : pieces[index]? = some piece) :
    ∃ current, (stdflat_prefixes pieces)[index]? = some current ∧ (stdflat_prefixes pieces)[index + 1]? =
          some (current ++ piece) := by
  simpa [stdflat_prefixes] using
    stdflat_prefixes_from_step [] pieces hGet
/-! ## 对象累积器的逐点语义 -/
private def stdflat_prefix_terms (pieces : List (List Nat)) : List SetTerm := (stdflat_prefixes pieces).map standard_token_sequence
private theorem stdflat_prefix_terms_check
    (pieces : List (List Nat)) :
    ∀ term, term ∈ stdflat_prefix_terms pieces →
      Term.CheckCertificate term SetSort.set := by
  intro term hTerm
  rcases List.mem_map.mp hTerm with ⟨tokens, _, rfl⟩
  exact standard_token_sequence_check tokens
private theorem stdflat_prefix_terms_closed (pieces : List (List Nat)) :
    ∀ term, term ∈ stdflat_prefix_terms pieces →
      Term.freeSupport term = [] := by
  intro term hTerm
  rcases List.mem_map.mp hTerm with ⟨tokens, _, rfl⟩
  exact standard_token_sequence_freeSupport_nil tokens
private theorem stdflat_piece_terms_check
    (pieces : List (List Nat)) :
    ∀ term, term ∈ pieces.map standard_token_sequence →
      Term.CheckCertificate term SetSort.set := by
  intro term hTerm
  rcases List.mem_map.mp hTerm with ⟨tokens, _, rfl⟩
  exact standard_token_sequence_check tokens
private theorem stdflat_piece_terms_closed (pieces : List (List Nat)) :
    ∀ term, term ∈ pieces.map standard_token_sequence →
      Term.freeSupport term = [] := by
  intro term hTerm
  rcases List.mem_map.mp hTerm with ⟨tokens, _, rfl⟩
  exact standard_token_sequence_freeSupport_nil tokens
private theorem stdflat_accumulator_apply_getElem? (pieces : List (List Nat))
    {index : Nat} {tokens : List Nat} (hGet : (stdflat_prefixes pieces)[index]? = some tokens) :
    ⊢ₘ[standard_sequence_semantics_theory] (standard_sequence (stdflat_prefix_terms pieces) ·ₘ
          numₘ(index)) ≐ₘ
        standard_token_sequence tokens := by
  have hMapped : (stdflat_prefix_terms pieces)[index]? =
        some (standard_token_sequence tokens) := by
    simpa [stdflat_prefix_terms] using
      congrArg (Option.map standard_token_sequence) hGet
  simpa using (standard_sequence_from_apply_getElem?
      0 hMapped
      (fun term hTerm =>
        (stdflat_prefix_terms_check
          pieces term hTerm).admissible)
      (stdflat_prefix_terms_closed pieces)
      (standard_token_sequence_check tokens).admissible)
private theorem stdflat_piece_family_apply_getElem? (pieces : List (List Nat))
    {index : Nat} {piece : List Nat} (hGet : pieces[index]? = some piece) :
    ⊢ₘ[standard_sequence_semantics_theory] (standard_sequence (pieces.map standard_token_sequence) ·ₘ
          numₘ(index)) ≐ₘ
        standard_token_sequence piece := by
  have hMapped : (pieces.map standard_token_sequence)[index]? =
        some (standard_token_sequence piece) := by
    simpa using congrArg (Option.map standard_token_sequence) hGet
  simpa using (standard_sequence_from_apply_getElem?
      0 hMapped
      (fun term hTerm =>
        (stdflat_piece_terms_check
          pieces term hTerm).admissible)
      (stdflat_piece_terms_closed pieces)
      (standard_token_sequence_check piece).admissible)
private theorem stdflat_step_at_numeral (pieces : List (List Nat)) (index : Nat) {piece : List Nat} (hGet : pieces[index]? = some piece) :
    ⊢ₘ[standard_sequence_semantics_theory] (standard_sequence (stdflat_prefix_terms pieces) ·ₘ
          Sₘ(numₘ(index))) ≐ₘ ((standard_sequence (stdflat_prefix_terms pieces) ·ₘ
            numₘ(index)) ⌢ₘ (standard_sequence (pieces.map standard_token_sequence) ·ₘ
            numₘ(index))) := by
  rcases stdflat_prefixes_step pieces hGet with
    ⟨current, hCurrentGet, hNextGet⟩
  let accumulator :=
    standard_sequence (stdflat_prefix_terms pieces)
  let family :=
    standard_sequence (pieces.map standard_token_sequence)
  have hCurrent :=
    stdflat_accumulator_apply_getElem? pieces hCurrentGet
  have hNext :=
    stdflat_accumulator_apply_getElem? pieces hNextGet
  have hPiece :=
    stdflat_piece_family_apply_getElem? pieces hGet
  have hAppend := standard_token_sequence_append current piece
  have hAccumulator :
      Term.CheckCertificate accumulator SetSort.set := by
    exact standard_sequence_from_check 0
      (stdflat_prefix_terms_check pieces)
  have hFamily :
      Term.CheckCertificate family SetSort.set := by
    exact standard_sequence_from_check 0
      (stdflat_piece_terms_check pieces)
  have hAtCurrent :
      Term.CheckCertificate
        (accumulator ·ₘ numₘ(index)) SetSort.set := by
    prove_term_check
  have hAtPiece :
      Term.CheckCertificate
        (family ·ₘ numₘ(index)) SetSort.set := by
    prove_term_check
  have hConcatCongruence :
      ⊢ₘ[standard_sequence_semantics_theory] ((accumulator ·ₘ numₘ(index)) ⌢ₘ (family ·ₘ numₘ(index))) ≐ₘ (standard_token_sequence current ⌢ₘ
            standard_token_sequence piece) :=
    finite_sequence_concatenation_term_congr_of_equalities (accumulator ·ₘ numₘ(index)) (standard_token_sequence current) (family ·ₘ numₘ(index))
      (standard_token_sequence piece)
      hAtCurrent.admissible
      (standard_token_sequence_check current).admissible
      hAtPiece.admissible
      (standard_token_sequence_check piece).admissible
      (by simpa [accumulator] using hCurrent)
      (by simpa [family] using hPiece)
  have hConcatBack :
      ⊢ₘ[standard_sequence_semantics_theory] (standard_token_sequence current ⌢ₘ
            standard_token_sequence piece) ≐ₘ ((accumulator ·ₘ numₘ(index)) ⌢ₘ (family ·ₘ numₘ(index))) :=
    Metatheory.Derives.equality_symm hConcatCongruence
  have hThroughAppend :
      ⊢ₘ[standard_sequence_semantics_theory] (accumulator ·ₘ numₘ(index + 1)) ≐ₘ (standard_token_sequence current ⌢ₘ
            standard_token_sequence piece) :=
    Metatheory.Derives.equality_trans
      (by simpa [accumulator] using hNext) hAppend
  have hResult :=
    Metatheory.Derives.equality_trans
      hThroughAppend hConcatBack
  simpa [accumulator, family, finite_numeral_term] using hResult
private theorem stdflat_step_at_equality
    (pieces : List (List Nat)) (point : SetTerm)
    (hPoint : Term.CheckCertificate point SetSort.set)
    (index : Nat) {piece : List Nat} (hGet : pieces[index]? = some piece) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((standard_sequence (stdflat_prefix_terms pieces) ·ₘ
            Sₘ(point)) ≐ₘ ((standard_sequence (stdflat_prefix_terms pieces) ·ₘ
              point) ⌢ₘ (standard_sequence (pieces.map standard_token_sequence) ·ₘ
              point))) := by
  let accumulator :=
    standard_sequence (stdflat_prefix_terms pieces)
  let family :=
    standard_sequence (pieces.map standard_token_sequence)
  let parameter : FreeVarId := 396
  let body : SetFormula := (accumulator ·ₘ Sₘ(x#parameter)) ≐ₘ ((accumulator ·ₘ x#parameter) ⌢ₘ (family ·ₘ x#parameter))
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  have hAccumulator :
      Term.CheckCertificate accumulator SetSort.set := by
    exact standard_sequence_from_check 0
      (stdflat_prefix_terms_check pieces)
  have hFamily :
      Term.CheckCertificate family SetSort.set := by
    exact standard_sequence_from_check 0
      (stdflat_piece_terms_check pieces)
  have hBodyCheck :
      Formula.CheckCertificate body := by
    prove_formula_check
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hAccumulatorFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement accumulator =
        accumulator := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport accumulator = [] by
      simpa [accumulator] using
        seq_support_nil_m 0 (stdflat_prefix_terms_closed pieces)]
    simp
  have hFamilyFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement family =
        family := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport family = [] by
      simpa [family] using
        seq_support_nil_m 0 (stdflat_piece_terms_closed pieces)]
    simp
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := standard_sequence_semantics_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameter)
      (left := point) (right := numₘ(index)) (body := body)
      hEquality
  have hTransport :
      Γ ⊢ₘ[standard_sequence_semantics_theory] ((accumulator ·ₘ Sₘ(point)) ≐ₘ ((accumulator ·ₘ point) ⌢ₘ (family ·ₘ point))) ↔ₘ
          ((accumulator ·ₘ Sₘ(numₘ(index))) ≐ₘ ((accumulator ·ₘ numₘ(index)) ⌢ₘ (family ·ₘ numₘ(index)))) := by
    simpa [body, Formula.substituteFree, Term.substituteFree,
      successor_term, function_application_term,
      finite_sequence_concatenation_term, set_variable,
      hAccumulatorFixed, hFamilyFixed] using hIff
  have hConcrete :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (accumulator ·ₘ Sₘ(numₘ(index))) ≐ₘ ((accumulator ·ₘ numₘ(index)) ⌢ₘ (family ·ₘ numₘ(index))) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (by
        simpa [accumulator, family] using
          stdflat_step_at_numeral pieces index hGet)
  simpa [Γ, equality, accumulator, family] using
    FirstOrder.Derives.iffElimLeft hTransport hConcrete
private theorem stdflat_step_forall (pieces : List (List Nat)) :
    ⊢ₘ[standard_sequence_semantics_theory]
      ∀ₘ[SetSort.set],
        finite_sequence_flatten_step_condition (standard_sequence (pieces.map standard_token_sequence)) (standard_sequence (stdflat_prefix_terms pieces))
          bₛ#0 := by
  let family :=
    standard_sequence (pieces.map standard_token_sequence)
  let accumulator :=
    standard_sequence (stdflat_prefix_terms pieces)
  let point : SetTerm := x#395
  let conclusion : SetFormula := (accumulator ·ₘ Sₘ(point)) ≐ₘ ((accumulator ·ₘ point) ⌢ₘ (family ·ₘ point))
  have hPoint :
      Term.CheckCertificate point SetSort.set := by
    prove_term_check
  have hFamily :
      Term.CheckCertificate family SetSort.set := by
    exact standard_sequence_from_check 0
      (stdflat_piece_terms_check pieces)
  have hAccumulator :
      Term.CheckCertificate accumulator SetSort.set := by
    exact standard_sequence_from_check 0
      (stdflat_prefix_terms_check pieces)
  have hCases :
      ⊢ₘ[standard_sequence_semantics_theory]
        stdseq_numeral_member_condition pieces.length point ⟶ₘ
          conclusion :=
    stdseq_numeral_member_condition_elim
      pieces.length point conclusion (fun index hIndex => by
        let piece := pieces[index]
        have hGet : pieces[index]? = some piece :=
          List.getElem?_eq_getElem hIndex
        simpa [conclusion, accumulator, family, point] using
          stdflat_step_at_equality pieces point hPoint index hGet)
  have hDomainCheck :
      Term.CheckCertificate (domₘ(family)) SetSort.set := by
    prove_term_check
  have hNumeral :
      Term.CheckCertificate
        (numₘ(pieces.length)) SetSort.set := by
    prove_term_check
  have hDomainEq :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(family) ≐ₘ numₘ(pieces.length) := by
    simpa [family] using
      (standard_sequence_domain_eq_numeral_length
        (fun term hTerm =>
          (stdflat_piece_terms_check
            pieces term hTerm).admissible)
        (stdflat_fresh_of_closed
          (stdflat_piece_terms_closed pieces) 0)
        (stdflat_fresh_of_closed
          (stdflat_piece_terms_closed pieces) 1))
  have hDomainIff :=
    membership_right_iff_of_equality
      point (domₘ(family)) (numₘ(pieces.length))
      hPoint.admissible hDomainCheck.admissible
      hNumeral.admissible hDomainEq
  have hNumeralIff :=
    stdseq_numeral_member_iff
      pieces.length point hPoint.admissible
  have hOpen :
      ⊢ₘ[standard_sequence_semantics_theory] (point ∈ₘ domₘ(family)) ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ domₘ(family)]
          ⊢ₘ[standard_sequence_semantics_theory]
            point ∈ₘ domₘ(family) :=
      FirstOrder.Derives.assumption (by simp)
    have hNumeralMembership := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hDomainIff)
      hMembership
    have hCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hNumeralIff)
      hNumeralMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hTheoryFresh :
      ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 395) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence hFormula).2]
    intro hMember
    cases hMember
  have hFamilyClose :
      Term.closeFreeAt SetSort.set 395 0 family = family :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 395 0 family hFamily.admissible.2 (by
        rw [show Term.freeSupport family = [] by
          simpa [family] using
            seq_support_nil_m 0 (stdflat_piece_terms_closed pieces)]
        simp)
  have hAccumulatorClose :
      Term.closeFreeAt SetSort.set 395 0 accumulator = accumulator :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 395 0 accumulator
      hAccumulator.admissible.2 (by
        rw [show Term.freeSupport accumulator = [] by
          simpa [accumulator] using
            seq_support_nil_m 0 (stdflat_prefix_terms_closed pieces)]
        simp)
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 395)
      hTheoryFresh (by simp) hOpen
  simpa [finite_sequence_flatten_step_condition,
    conclusion, point, Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, successor_term, function_application_term,
    finite_sequence_concatenation_term, domain_term, set_variable,
    hFamilyClose, hAccumulatorClose] using hGeneralized
/-! ## 完整 `flattenₘ` 合同 -/
/--
任意标准 token 序列族的对象折叠等于全部外部 token 串的 `List.flatten`。
-/
theorem standard_token_sequence_family_flatten (pieces : List (List Nat)) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_token_sequence pieces.flatten ≐ₘ
        flattenₘ(standard_sequence (pieces.map standard_token_sequence)) := by
  let family :=
    standard_sequence (pieces.map standard_token_sequence)
  let accumulator :=
    standard_sequence (stdflat_prefix_terms pieces)
  let candidate := standard_token_sequence pieces.flatten
  have hFamily :
      Term.CheckCertificate family SetSort.set := by
    exact standard_sequence_from_check 0
      (stdflat_piece_terms_check pieces)
  have hAccumulator :
      Term.CheckCertificate accumulator SetSort.set := by
    exact standard_sequence_from_check 0
      (stdflat_prefix_terms_check pieces)
  have hCandidate :
      Term.CheckCertificate candidate SetSort.set := by
    prove_term_check
  have hCandidateFinite :
      ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_condition candidate := by
    simpa [candidate] using
      standard_token_sequence_finite_sequence_condition pieces.flatten
  have hFamilyDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(family) ≐ₘ numₘ(pieces.length) := by
    simpa [family] using
      (standard_sequence_domain_eq_numeral_length
        (fun term hTerm =>
          (stdflat_piece_terms_check
            pieces term hTerm).admissible)
        (stdflat_fresh_of_closed
          (stdflat_piece_terms_closed pieces) 0)
        (stdflat_fresh_of_closed
          (stdflat_piece_terms_closed pieces) 1))
  have hAccumulatorDomainRaw :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(accumulator) ≐ₘ
          numₘ((stdflat_prefix_terms pieces).length) := by
    simpa [accumulator] using
      (standard_sequence_domain_eq_numeral_length
        (fun term hTerm =>
          (stdflat_prefix_terms_check
            pieces term hTerm).admissible)
        (stdflat_fresh_of_closed
          (stdflat_prefix_terms_closed pieces) 0)
        (stdflat_fresh_of_closed
          (stdflat_prefix_terms_closed pieces) 1))
  have hAccumulatorDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(accumulator) ≐ₘ Sₘ(numₘ(pieces.length)) := by
    simpa [stdflat_prefix_terms,
      stdflat_prefixes_length, finite_numeral_term] using
      hAccumulatorDomainRaw
  have hFamilyDomainBack :
      ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(pieces.length) ≐ₘ domₘ(family) :=
    Metatheory.Derives.equality_symm hFamilyDomain
  have hSuccessorDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        Sₘ(numₘ(pieces.length)) ≐ₘ Sₘ(domₘ(family)) :=
    successor_term_congr_of_equality
      (numₘ(pieces.length)) (domₘ(family))
      (finite_numeral_term_admissible pieces.length)
      (domain_term_admissible family hFamily.admissible)
      hFamilyDomainBack
  have hDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(accumulator) ≐ₘ Sₘ(domₘ(family)) :=
    Metatheory.Derives.equality_trans
      hAccumulatorDomain hSuccessorDomain
  have hInitialGet : (stdflat_prefixes pieces)[0]? = some [] := by
    simpa [stdflat_prefixes] using
      stdflat_prefixes_from_head [] pieces
  have hInitialRaw :=
    stdflat_accumulator_apply_getElem? pieces hInitialGet
  have hInitial :
      ⊢ₘ[standard_sequence_semantics_theory] (accumulator ·ₘ numₘ(0)) ≐ₘ ∅ₘ := by
    simpa [accumulator, standard_token_sequence,
      standard_sequence, standard_sequence_from] using hInitialRaw
  have hStep := stdflat_step_forall pieces
  have hTerminalGet := stdflat_prefixes_terminal pieces
  have hTerminalAt :=
    stdflat_accumulator_apply_getElem? pieces hTerminalGet
  have hTerminalArgument :
      ⊢ₘ[standard_sequence_semantics_theory] (accumulator ·ₘ numₘ(pieces.length)) ≐ₘ (accumulator ·ₘ domₘ(family)) :=
    function_application_term_congr_argument_of_equality
      accumulator (numₘ(pieces.length)) (domₘ(family))
      hAccumulator.admissible
      (finite_numeral_term_admissible pieces.length)
      (domain_term_admissible family hFamily.admissible)
      hFamilyDomainBack
  have hTerminalAtBack :
      ⊢ₘ[standard_sequence_semantics_theory]
        candidate ≐ₘ (accumulator ·ₘ numₘ(pieces.length)) :=
    Metatheory.Derives.equality_symm
      (by simpa [accumulator, candidate] using hTerminalAt)
  have hTerminal :
      ⊢ₘ[standard_sequence_semantics_theory]
        candidate ≐ₘ (accumulator ·ₘ domₘ(family)) :=
    Metatheory.Derives.equality_trans
      hTerminalAtBack hTerminalArgument
  have hAccumulatorFinite :
      ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_condition accumulator := by
    simpa [accumulator] using
      (standard_sequence_finite_sequence_condition
        (fun term hTerm =>
          (stdflat_prefix_terms_check
            pieces term hTerm).admissible)
        (stdflat_fresh_of_closed
          (stdflat_prefix_terms_closed pieces) 0)
        (stdflat_fresh_of_closed
          (stdflat_prefix_terms_closed pieces) 1)
        (stdflat_fresh_of_closed
          (stdflat_prefix_terms_closed pieces) 2))
  have hFamilyOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement family = family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement
      family hFamily.admissible.2
  have hCandidateOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement candidate = candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement
      candidate hCandidate.admissible.2
  have hZeroOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (numₘ(0)) =
        numₘ(0) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(0)) (finite_numeral_term_admissible 0).2
  have hContract :
      ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_flatten_definition_instance family candidate := by
    exact FirstOrder.Derives.theory_weaken (fun _ hFormula => Or.inr (Or.inl hFormula)) (finite_sequence_flatten_definition_instance_derives
        family candidate
        hFamily.admissible hCandidate.admissible)
  have hSpec :
      ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_flatten_spec family candidate := by
    apply FirstOrder.Derives.conjIntro hCandidateFinite
    nd_apply FirstOrder.Derives.exists_intro (term := accumulator)
    simpa [finite_sequence_flatten_spec,
      finite_sequence_flatten_step_condition,
      finite_sequence_condition, is_function_formula,
      Formula.openAt, Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.substituteFree, domain_term,
      set_bound_variable, hFamilyOpen, hCandidateOpen, hZeroOpen] using (FirstOrder.Derives.conjIntro hAccumulatorFinite <|
        FirstOrder.Derives.conjIntro hDomain <|
          FirstOrder.Derives.conjIntro hInitial <|
            FirstOrder.Derives.conjIntro (by simpa [family, accumulator] using hStep)
              hTerminal)
  have hElementFinite :
      ∀ term, term ∈ pieces.map standard_token_sequence →
        ⊢ₘ[standard_sequence_semantics_theory]
          finite_sequence_condition term := by
    intro term hTerm
    rcases List.mem_map.mp hTerm with ⟨tokens, _, rfl⟩
    exact standard_token_sequence_finite_sequence_condition tokens
  have hFamilyCondition :
      ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_family_condition family := by
    simpa [family] using
      (standard_sequence_family_condition_derives
        (fun term hTerm =>
          (stdflat_piece_terms_check
            pieces term hTerm).admissible)
        (stdflat_piece_terms_closed pieces)
        hElementFinite)
  have hIff := FirstOrder.Derives.impElim hContract hFamilyCondition
  simpa [family, candidate] using
    FirstOrder.Derives.iffElimLeft hIff hSpec
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
