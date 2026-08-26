import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequence
/-!
# 标准 token 序列的对象拼接语义
本模块证明标准 token 序列与对象有限序列拼接运算严格对应。证明完全展开
`finite_sequence_concatenation_spec`：候选定义域由具体 numeral 加法计算，
左右两段则由有限 numeral 成员条件逐点验证。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-- 有限序列拼接项的合法性由左右项证书直接计算。 -/
@[term_check]
theorem finite_sequence_concatenation_term_check
    {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Term.CheckCertificate (left ⌢ₘ right) SetSort.set :=
  Term.check_admissible_complete <|
    finite_sequence_concatenation_term_admissible
      left right hLeft.admissible hRight.admissible
/-- 有限序列拼接理论嵌入标准序列语义理论。 -/
theorem standard_sequence_weaken_concatenation
    {φ : SetFormula} (h : ⊢ₘ[finite_sequence_concatenation_theory] φ) :
    ⊢ₘ[standard_sequence_semantics_theory] φ := by
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      Or.inr (Or.inl <|
        nonempty_sequence_space_theory_subset_finite_sequence_flatten_theory <|
          nonempty_sequence_separation_theory_subset_nonempty_sequence_space_theory <|
            finite_sequence_concatenation_theory_subset_nonempty_sequence_separation_theory
              hFormula))
    h
/-- 具体 numeral 下标可沿标准序列的定义域等式运输。 -/
private theorem stdtok_domain_member_of_eq_numeral
    (tokens : List Nat) (point : SetTerm)
    (hPoint : Term.CheckCertificate point SetSort.set)
    (index : Nat) (hIndex : index < tokens.length) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ
        point ∈ₘ domₘ(standard_token_sequence tokens) := by
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ≐ₘ numₘ(index) :=
    FirstOrder.Derives.assumption (by simp [Γ, equality])
  have hNumeralDomain :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(index) ∈ₘ
          domₘ(standard_token_sequence tokens) := by
    have hDomainEquality :
        ⊢ₘ[standard_sequence_semantics_theory]
          domₘ(standard_token_sequence tokens) ≐ₘ
            numₘ(tokens.length) :=
      standard_token_sequence_domain_eq_length tokens
    have hTransport := membership_right_iff_of_equality (numₘ(index)) (domₘ(standard_token_sequence tokens)) (numₘ(tokens.length))
      (finite_numeral_term_admissible index) (domain_term_admissible (standard_token_sequence tokens) (standard_token_sequence_admissible tokens))
      (finite_numeral_term_admissible tokens.length)
      hDomainEquality
    exact FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.iffElimLeft hTransport (standard_sequence_finite_numeral_mem_of_lt
          index tokens.length hIndex)
  exact FirstOrder.Derives.iffElimLeft (membership_left_iff_of_equality
      point (numₘ(index)) (domₘ(standard_token_sequence tokens))
      hPoint.admissible (finite_numeral_term_admissible index)
      (domain_term_admissible (standard_token_sequence tokens)
        (standard_token_sequence_admissible tokens))
      hEquality)
    hNumeralDomain
private theorem stdtok_append_left_at_equality
    (left right : List Nat) (point : SetTerm)
    (hPoint : Term.CheckCertificate point SetSort.set)
    (index : Nat) (hIndex : index < left.length) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((standard_token_sequence (left ++ right) ·ₘ point) ≐ₘ
          (standard_token_sequence left ·ₘ point)) := by
  let candidate := standard_token_sequence (left ++ right)
  let leftSequence := standard_token_sequence left
  let token := left[index]
  have hGetLeft : left[index]? = some token :=
    List.getElem?_eq_getElem hIndex
  have hGetCandidate : (left ++ right)[index]? = some token := by
    rw [List.getElem?_append_left hIndex]
    exact hGetLeft
  have hCandidateValue :=
    standard_token_sequence_apply_getElem? (left ++ right) hGetCandidate
  have hLeftValue :=
    standard_token_sequence_apply_getElem? left hGetLeft
  have hLeftBack :
      ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(token) ≐ₘ (leftSequence ·ₘ numₘ(index)) :=
    Metatheory.Derives.equality_symm
      (by simpa [leftSequence, token] using hLeftValue)
  have hConcrete :
      ⊢ₘ[standard_sequence_semantics_theory] (candidate ·ₘ numₘ(index)) ≐ₘ (leftSequence ·ₘ numₘ(index)) :=
    Metatheory.Derives.equality_trans
      (by simpa [candidate, token] using hCandidateValue) hLeftBack
  let parameter : FreeVarId := 392
  let body : SetFormula := (candidate ·ₘ x#parameter) ≐ₘ (leftSequence ·ₘ x#parameter)
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
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
  have hCandidateFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement candidate =
        candidate := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport candidate = [] by
      simp [candidate]]
    simp
  have hLeftFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement leftSequence =
        leftSequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport leftSequence = [] by
      simp [leftSequence]]
    simp
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := standard_sequence_semantics_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameter)
      (left := point) (right := numₘ(index)) (body := body)
      hEquality
  have hTransport :
      Γ ⊢ₘ[standard_sequence_semantics_theory] ((candidate ·ₘ point) ≐ₘ (leftSequence ·ₘ point)) ↔ₘ ((candidate ·ₘ numₘ(index)) ≐ₘ
            (leftSequence ·ₘ numₘ(index))) := by
    simpa [body, Formula.substituteFree, Term.substituteFree,
      set_variable, hCandidateFixed, hLeftFixed] using hIff
  have hConcreteAt :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (candidate ·ₘ numₘ(index)) ≐ₘ (leftSequence ·ₘ numₘ(index)) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hConcrete
  simpa [Γ, equality, candidate, leftSequence] using
    FirstOrder.Derives.iffElimLeft hTransport hConcreteAt
/-- 左段具体下标同时进入结果定义域并保持求值。 -/
private theorem stdtok_append_left_at
    (left right : List Nat) (point : SetTerm)
    (hPoint : Term.CheckCertificate point SetSort.set)
    (index : Nat) (hIndex : index < left.length) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((point ∈ₘ
            domₘ(standard_token_sequence (left ++ right))) ∧ₘ ((standard_token_sequence (left ++ right) ·ₘ point) ≐ₘ
            (standard_token_sequence left ·ₘ point))) := by
  have hDomain :=
    stdtok_domain_member_of_eq_numeral (left ++ right) point hPoint index (by
        simpa using Nat.lt_add_right right.length hIndex)
  have hValue :=
    stdtok_append_left_at_equality
      left right point hPoint index hIndex
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory] equality :=
    FirstOrder.Derives.assumption (by simp [Γ])
  exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hDomain)
      hEquality) (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hValue)
      hEquality)
private theorem stdtok_append_left_forall (left right : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      ∀ₘ[SetSort.set],
        finite_sequence_concatenation_left_condition (standard_token_sequence left) (standard_token_sequence (left ++ right))
          bₛ#0 := by
  let leftSequence := standard_token_sequence left
  let candidate := standard_token_sequence (left ++ right)
  let point : SetTerm := x#391
  let conclusion : SetFormula := (point ∈ₘ domₘ(candidate)) ∧ₘ ((candidate ·ₘ point) ≐ₘ (leftSequence ·ₘ point))
  have hPoint :
      Term.CheckCertificate point SetSort.set := by
    prove_term_check
  have hCases :
      ⊢ₘ[standard_sequence_semantics_theory]
        stdseq_numeral_member_condition left.length point ⟶ₘ
          conclusion :=
    stdseq_numeral_member_condition_elim
      left.length point conclusion (fun index hIndex => by
        simpa [conclusion, candidate, leftSequence, point] using
          stdtok_append_left_at
            left right point hPoint index hIndex)
  have hDomain :
      Term.CheckCertificate (domₘ(leftSequence)) SetSort.set := by
    prove_term_check
  have hNumeral :
      Term.CheckCertificate (numₘ(left.length)) SetSort.set := by
    prove_term_check
  have hDomainEq :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(leftSequence) ≐ₘ numₘ(left.length) := by
    simpa [leftSequence] using
      standard_token_sequence_domain_eq_length left
  have hDomainIff :=
    membership_right_iff_of_equality
      point (domₘ(leftSequence)) (numₘ(left.length))
      hPoint.admissible hDomain.admissible
      hNumeral.admissible hDomainEq
  have hNumeralIff :=
    stdseq_numeral_member_iff
      left.length point hPoint.admissible
  have hOpen :
      ⊢ₘ[standard_sequence_semantics_theory] (point ∈ₘ domₘ(leftSequence)) ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ domₘ(leftSequence)]
          ⊢ₘ[standard_sequence_semantics_theory]
            point ∈ₘ domₘ(leftSequence) :=
      FirstOrder.Derives.assumption (by simp)
    have hNumeralMembership := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hDomainIff)
      hMembership
    have hCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hNumeralIff)
      hNumeralMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hTheoryFresh :
      ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 391) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence hFormula).2]
    intro hMember
    cases hMember
  have hLeftClose :
      Term.closeFreeAt SetSort.set 391 0 leftSequence = leftSequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 391 0 leftSequence
      (standard_token_sequence_check left).admissible.2 (by
        rw [show Term.freeSupport leftSequence = [] by
          simp [leftSequence]]
        simp)
  have hCandidateClose :
      Term.closeFreeAt SetSort.set 391 0 candidate = candidate :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 391 0 candidate
      (standard_token_sequence_check (left ++ right)).admissible.2 (by
        rw [show Term.freeSupport candidate = [] by
          simp [candidate]]
        simp)
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 391)
      hTheoryFresh (by simp) hOpen
  simpa [finite_sequence_concatenation_left_condition,
    conclusion, point, Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, set_variable, hLeftClose, hCandidateClose] using
    hGeneralized
/-- 右段具体下标平移为外部列表拼接中的对应 numeral。 -/
private theorem stdtok_append_right_shift_eq
    (left : List Nat) (point : SetTerm)
    (hPoint : Term.CheckCertificate point SetSort.set)
    (index : Nat) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((domₘ(standard_token_sequence left) +ₘ point) ≐ₘ
          numₘ(left.length + index)) := by
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ≐ₘ numₘ(index) :=
    FirstOrder.Derives.assumption (by simp [Γ, equality])
  have hLeftDomain :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(standard_token_sequence left) ≐ₘ
          numₘ(left.length) :=
    FirstOrder.Derives.context_weaken_cons (standard_token_sequence_domain_eq_length left)
  have hAdditionCongruence :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (domₘ(standard_token_sequence left) +ₘ point) ≐ₘ (numₘ(left.length) +ₘ numₘ(index)) :=
    natural_addition_term_congr_of_equalities (domₘ(standard_token_sequence left)) (numₘ(left.length)) point (numₘ(index)) (domain_term_admissible
        (standard_token_sequence left) (standard_token_sequence_admissible left)) (finite_numeral_term_admissible left.length)
      hPoint.admissible (finite_numeral_term_admissible index)
      hLeftDomain hEquality
  have hNumeralAddition :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (numₘ(left.length) +ₘ numₘ(index)) ≐ₘ
          numₘ(left.length + index) :=
    FirstOrder.Derives.context_weaken_cons <|
      Metatheory.Derives.equality_symm
        (standard_token_sequence_finite_numeral_addition
          left.length index)
  exact Metatheory.Derives.equality_trans
    hAdditionCongruence hNumeralAddition
/-- 右段具体下标的平移位置进入结果定义域。 -/
private theorem stdtok_append_right_at_domain
    (left right : List Nat) (point : SetTerm)
    (hPoint : Term.CheckCertificate point SetSort.set)
    (index : Nat) (hIndex : index < right.length) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((domₘ(standard_token_sequence left) +ₘ point) ∈ₘ
          domₘ(standard_token_sequence (left ++ right))) := by
  let shifted :=
    domₘ(standard_token_sequence left) +ₘ point
  have hShifted :
      Term.CheckCertificate shifted SetSort.set := by
    prove_term_check
  have hShift :=
    stdtok_append_right_shift_eq left point hPoint index
  have hDomain :=
    stdtok_domain_member_of_eq_numeral (left ++ right) shifted hShifted (left.length + index) (by
        simp only [List.length_append]
        omega)
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory] equality :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hShiftEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        shifted ≐ₘ numₘ(left.length + index) :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hShift)
      hEquality
  simpa [shifted] using
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hDomain)
      hShiftEquality
private theorem stdtok_append_right_at_equality
    (left right : List Nat) (point : SetTerm)
    (hPoint : Term.CheckCertificate point SetSort.set)
    (index : Nat) (hIndex : index < right.length) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((standard_token_sequence (left ++ right) ·ₘ
            (domₘ(standard_token_sequence left) +ₘ point)) ≐ₘ (standard_token_sequence right ·ₘ point)) := by
  let candidate := standard_token_sequence (left ++ right)
  let leftSequence := standard_token_sequence left
  let rightSequence := standard_token_sequence right
  let token := right[index]
  have hGetRight : right[index]? = some token :=
    List.getElem?_eq_getElem hIndex
  have hGetCandidate : (left ++ right)[left.length + index]? = some token := by
    rw [List.getElem?_append_right]
    · simp [token]
    · omega
  have hCandidateAt :=
    standard_token_sequence_apply_getElem? (left ++ right) hGetCandidate
  have hRightAt :=
    standard_token_sequence_apply_getElem? right hGetRight
  have hLeftDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(leftSequence) ≐ₘ numₘ(left.length) := by
    simpa [leftSequence] using
      standard_token_sequence_domain_eq_length left
  have hIndexRefl :
      ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(index) ≐ₘ numₘ(index) :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (numₘ(index))
  have hAdditionCongruence :
      ⊢ₘ[standard_sequence_semantics_theory] (domₘ(leftSequence) +ₘ numₘ(index)) ≐ₘ (numₘ(left.length) +ₘ numₘ(index)) :=
    natural_addition_term_congr_of_equalities (domₘ(leftSequence)) (numₘ(left.length)) (numₘ(index)) (numₘ(index)) (domain_term_admissible leftSequence
        (standard_token_sequence_admissible left)) (finite_numeral_term_admissible left.length) (finite_numeral_term_admissible index)
      (finite_numeral_term_admissible index)
      hLeftDomain hIndexRefl
  have hNumeralAddition :=
    standard_token_sequence_finite_numeral_addition left.length index
  have hAdditionBack :
      ⊢ₘ[standard_sequence_semantics_theory] (numₘ(left.length) +ₘ numₘ(index)) ≐ₘ
          numₘ(left.length + index) :=
    Metatheory.Derives.equality_symm hNumeralAddition
  have hShift :
      ⊢ₘ[standard_sequence_semantics_theory] (domₘ(leftSequence) +ₘ numₘ(index)) ≐ₘ
          numₘ(left.length + index) :=
    Metatheory.Derives.equality_trans
      hAdditionCongruence hAdditionBack
  have hCandidateShift :
      ⊢ₘ[standard_sequence_semantics_theory] (candidate ·ₘ (domₘ(leftSequence) +ₘ numₘ(index))) ≐ₘ (candidate ·ₘ numₘ(left.length + index)) :=
    function_application_term_congr_argument_of_equality
      candidate (domₘ(leftSequence) +ₘ numₘ(index)) (numₘ(left.length + index)) (standard_token_sequence_admissible (left ++ right))
      (natural_addition_term_admissible (domₘ(leftSequence)) (numₘ(index)) (domain_term_admissible leftSequence (standard_token_sequence_admissible left))
        (finite_numeral_term_admissible index)) (finite_numeral_term_admissible (left.length + index))
      hShift
  have hCandidateValue :
      ⊢ₘ[standard_sequence_semantics_theory] (candidate ·ₘ (domₘ(leftSequence) +ₘ numₘ(index))) ≐ₘ
          numₘ(token) :=
    Metatheory.Derives.equality_trans
      hCandidateShift (by simpa [candidate, token] using hCandidateAt)
  have hRightBack :
      ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(token) ≐ₘ (rightSequence ·ₘ numₘ(index)) :=
    Metatheory.Derives.equality_symm
      (by simpa [rightSequence, token] using hRightAt)
  have hConcrete :
      ⊢ₘ[standard_sequence_semantics_theory] (candidate ·ₘ (domₘ(leftSequence) +ₘ numₘ(index))) ≐ₘ (rightSequence ·ₘ numₘ(index)) :=
    Metatheory.Derives.equality_trans hCandidateValue hRightBack
  let parameter : FreeVarId := 394
  let body : SetFormula := (candidate ·ₘ (domₘ(leftSequence) +ₘ x#parameter)) ≐ₘ (rightSequence ·ₘ x#parameter)
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
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
  have hCandidateFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement candidate =
        candidate := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport candidate = [] by
      simp [candidate]]
    simp
  have hLeftFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement leftSequence =
        leftSequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport leftSequence = [] by
      simp [leftSequence]]
    simp
  have hRightFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement rightSequence =
        rightSequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport rightSequence = [] by
      simp [rightSequence]]
    simp
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := standard_sequence_semantics_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameter)
      (left := point) (right := numₘ(index)) (body := body)
      hEquality
  have hTransport :
      Γ ⊢ₘ[standard_sequence_semantics_theory] ((candidate ·ₘ (domₘ(leftSequence) +ₘ point)) ≐ₘ (rightSequence ·ₘ point)) ↔ₘ ((candidate ·ₘ
              (domₘ(leftSequence) +ₘ numₘ(index))) ≐ₘ (rightSequence ·ₘ numₘ(index))) := by
    simpa [body, Formula.substituteFree, Term.substituteFree,
      natural_addition_term, domain_term, function_application_term,
      set_variable, hCandidateFixed, hLeftFixed, hRightFixed] using hIff
  have hConcreteAt :
      Γ ⊢ₘ[standard_sequence_semantics_theory] (candidate ·ₘ (domₘ(leftSequence) +ₘ numₘ(index))) ≐ₘ (rightSequence ·ₘ numₘ(index)) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hConcrete
  simpa [Γ, equality, candidate, leftSequence, rightSequence] using
    FirstOrder.Derives.iffElimLeft hTransport hConcreteAt
/-- 右段具体下标同时进入结果定义域并保持求值。 -/
private theorem stdtok_append_right_at
    (left right : List Nat) (point : SetTerm)
    (hPoint : Term.CheckCertificate point SetSort.set)
    (index : Nat) (hIndex : index < right.length) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((((domₘ(standard_token_sequence left) +ₘ point) ∈ₘ
            domₘ(standard_token_sequence (left ++ right)))) ∧ₘ ((standard_token_sequence (left ++ right) ·ₘ (domₘ(standard_token_sequence left) +ₘ point)) ≐ₘ
            (standard_token_sequence right ·ₘ point))) := by
  have hDomain :=
    stdtok_append_right_at_domain
      left right point hPoint index hIndex
  have hValue :=
    stdtok_append_right_at_equality
      left right point hPoint index hIndex
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory] equality :=
    FirstOrder.Derives.assumption (by simp [Γ])
  exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hDomain)
      hEquality) (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hValue)
      hEquality)

/-!
## 外部中段的逐点证书

后续 occurrence 只需要知道外部列表分解中的中段在整串内逐点保持。
这里保持结论为普通全称式，不引入任何公式码或量词出现谓词。
-/

/-- 中段具体下标平移后进入整串定义域，并保持同一 token 值。 -/
private theorem stdtok_middle_at
    (prefixTokens middleTokens suffixTokens : List Nat)
    (point : SetTerm)
    (hPoint : Term.CheckCertificate point SetSort.set)
    (index : Nat) (hIndex : index < middleTokens.length) :
    ⊢ₘ[standard_sequence_semantics_theory]
      (point ≐ₘ numₘ(index)) ⟶ₘ
        ((((point +ₘ numₘ(prefixTokens.length)) ∈ₘ
              domₘ(standard_token_sequence
                (prefixTokens ++ middleTokens ++ suffixTokens)))) ∧ₘ
          ((standard_token_sequence
                (prefixTokens ++ middleTokens ++ suffixTokens) ·ₘ
              (point +ₘ numₘ(prefixTokens.length))) ≐ₘ
            (standard_token_sequence middleTokens ·ₘ point))) := by
  let whole :=
    standard_token_sequence
      (prefixTokens ++ middleTokens ++ suffixTokens)
  let segment := standard_token_sequence middleTokens
  let shifted := point +ₘ numₘ(prefixTokens.length)
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  have hWhole :
      Term.CheckCertificate whole SetSort.set := by
    prove_term_check
  have hSegment :
      Term.CheckCertificate segment SetSort.set := by
    prove_term_check
  have hShifted :
      Term.CheckCertificate shifted SetSort.set := by
    prove_term_check
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hPrefixRefl :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(prefixTokens.length) ≐ₘ
          numₘ(prefixTokens.length) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(prefixTokens.length))
  have hAddition :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        shifted ≐ₘ
          (numₘ(index) +ₘ numₘ(prefixTokens.length)) := by
    simpa [shifted] using
      natural_addition_term_congr_of_equalities
        point (numₘ(index))
        (numₘ(prefixTokens.length))
        (numₘ(prefixTokens.length))
        hPoint.admissible
        (finite_numeral_term_admissible index)
        (finite_numeral_term_admissible prefixTokens.length)
        (finite_numeral_term_admissible prefixTokens.length)
        hEquality hPrefixRefl
  have hNumeralAddition :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        (numₘ(index) +ₘ numₘ(prefixTokens.length)) ≐ₘ
          numₘ(prefixTokens.length + index) := by
    exact FirstOrder.Derives.context_weaken_cons <| by
      simpa [Nat.add_comm] using
        Metatheory.Derives.equality_symm
          (standard_token_sequence_finite_numeral_addition
            index prefixTokens.length)
  have hShift :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        shifted ≐ₘ numₘ(prefixTokens.length + index) :=
    Metatheory.Derives.equality_trans
      hAddition hNumeralAddition
  have hShiftDomain :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        shifted ∈ₘ domₘ(whole) := by
    have hDomain :=
      stdtok_domain_member_of_eq_numeral
        (prefixTokens ++ middleTokens ++ suffixTokens)
        shifted hShifted
        (prefixTokens.length + index) (by
          simp only [List.length_append]
          omega)
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken_cons hDomain)
      hShift
  let token := middleTokens[index]
  have hMiddleGet :
      middleTokens[index]? = some token :=
    List.getElem?_eq_getElem hIndex
  have hWholeGet :
      (prefixTokens ++ middleTokens ++ suffixTokens)[prefixTokens.length + index]? =
        some token := by
    rw [List.getElem?_append_left]
    · rw [List.getElem?_append_right]
      · simp [token]
      · omega
    · simp only [List.length_append]
      omega
  have hWholeAt :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        (whole ·ₘ numₘ(prefixTokens.length + index)) ≐ₘ
          numₘ(token) :=
    FirstOrder.Derives.context_weaken_cons <| by
      simpa [whole, token] using
        standard_token_sequence_apply_getElem?
          (prefixTokens ++ middleTokens ++ suffixTokens)
          hWholeGet
  have hSegmentAt :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        (segment ·ₘ numₘ(index)) ≐ₘ numₘ(token) :=
    FirstOrder.Derives.context_weaken_cons <| by
      simpa [segment, token] using
        standard_token_sequence_apply_getElem?
          middleTokens hMiddleGet
  have hWholeShift :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        (whole ·ₘ shifted) ≐ₘ
          (whole ·ₘ numₘ(prefixTokens.length + index)) :=
    function_application_term_congr_argument_of_equality
      whole shifted (numₘ(prefixTokens.length + index))
      hWhole.admissible hShifted.admissible
      (finite_numeral_term_admissible
        (prefixTokens.length + index))
      hShift
  have hSegmentPoint :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        (segment ·ₘ point) ≐ₘ
          (segment ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      segment point (numₘ(index))
      hSegment.admissible hPoint.admissible
      (finite_numeral_term_admissible index)
      hEquality
  have hValue :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        (whole ·ₘ shifted) ≐ₘ (segment ·ₘ point) :=
    Metatheory.Derives.equality_trans hWholeShift <|
      Metatheory.Derives.equality_trans hWholeAt <|
        Metatheory.Derives.equality_trans
          (Metatheory.Derives.equality_symm hSegmentAt)
          (Metatheory.Derives.equality_symm hSegmentPoint)
  simpa [whole, segment, shifted, Γ, equality] using
    FirstOrder.Derives.conjIntro hShiftDomain hValue

/--
标准序列中的外部中段在偏移 `prefix.length` 后逐点等于原中段。
该接口是对象子串、量词位置与自由出现位置的共同有限序列内核。
-/
theorem standard_token_sequence_middle_forall
    (prefixTokens middleTokens suffixTokens : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      ∀ₘ[SetSort.set, 320],
        ((x#320 ∈ₘ
              domₘ(standard_token_sequence middleTokens)) ⟶ₘ
          ((((x#320 +ₘ numₘ(prefixTokens.length)) ∈ₘ
                domₘ(standard_token_sequence
                  (prefixTokens ++ middleTokens ++ suffixTokens)))) ∧ₘ
            ((standard_token_sequence
                  (prefixTokens ++ middleTokens ++ suffixTokens) ·ₘ
                (x#320 +ₘ numₘ(prefixTokens.length))) ≐ₘ
              (standard_token_sequence middleTokens ·ₘ x#320)))) := by
  let whole :=
    standard_token_sequence
      (prefixTokens ++ middleTokens ++ suffixTokens)
  let segment := standard_token_sequence middleTokens
  let point : SetTerm := x#320
  let conclusion : SetFormula :=
    ((point +ₘ numₘ(prefixTokens.length)) ∈ₘ domₘ(whole)) ∧ₘ
      ((whole ·ₘ (point +ₘ numₘ(prefixTokens.length))) ≐ₘ
        (segment ·ₘ point))
  have hPoint :
      Term.CheckCertificate point SetSort.set := by
    prove_term_check
  have hCases :
      ⊢ₘ[standard_sequence_semantics_theory]
        stdseq_numeral_member_condition
            middleTokens.length point ⟶ₘ
          conclusion :=
    stdseq_numeral_member_condition_elim
      middleTokens.length point conclusion
      (fun index hIndex => by
        simpa [conclusion, whole, segment, point] using
          stdtok_middle_at
            prefixTokens middleTokens suffixTokens
            point hPoint index hIndex)
  have hDomainEq :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(segment) ≐ₘ numₘ(middleTokens.length) := by
    simpa [segment] using
      standard_token_sequence_domain_eq_length middleTokens
  have hDomainIff :=
    membership_right_iff_of_equality
      point (domₘ(segment)) (numₘ(middleTokens.length))
      hPoint.admissible
      (domain_term_admissible
        segment (standard_token_sequence_admissible middleTokens))
      (finite_numeral_term_admissible middleTokens.length)
      hDomainEq
  have hNumeralIff :=
    stdseq_numeral_member_iff
      middleTokens.length point hPoint.admissible
  have hOpen :
      ⊢ₘ[standard_sequence_semantics_theory]
        (point ∈ₘ domₘ(segment)) ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ domₘ(segment)]
          ⊢ₘ[standard_sequence_semantics_theory]
            point ∈ₘ domₘ(segment) :=
      FirstOrder.Derives.assumption (by simp)
    have hNumeralMembership :=
      FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken_cons hDomainIff)
        hMembership
    have hCondition :=
      FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken_cons hNumeralIff)
        hNumeralMembership
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hTheoryFresh :
      ∀ formula, standard_sequence_semantics_theory formula →
        (SetSort.set, 320) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hWholeClose :
      Term.closeFreeAt SetSort.set 320 0 whole = whole := by
    apply Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    · exact (standard_token_sequence_check
        (prefixTokens ++ middleTokens ++ suffixTokens)).admissible.2
    · rw [show Term.freeSupport whole = [] by
        simp [whole]]
      simp
  have hSegmentClose :
      Term.closeFreeAt SetSort.set 320 0 segment = segment := by
    apply Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    · exact
        (standard_token_sequence_check middleTokens).admissible.2
    · rw [show Term.freeSupport segment = [] by
        simp [segment]]
      simp
  have hNumeralClose :
      Term.closeFreeAt SetSort.set 320 0
          (numₘ(prefixTokens.length)) =
        numₘ(prefixTokens.length) := by
    apply Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    · exact
        (finite_numeral_term_admissible prefixTokens.length).2
    · rw [finite_numeral_term_freeSupport]
      simp
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := standard_sequence_semantics_theory)
      (Γ := []) (sort := SetSort.set) (eigen := 320)
      hTheoryFresh (by simp) hOpen
  simpa [whole, segment, point, conclusion,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, set_variable,
    hWholeClose, hSegmentClose, hNumeralClose] using
    hGeneralized

private theorem stdtok_append_right_forall (left right : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      ∀ₘ[SetSort.set],
        finite_sequence_concatenation_right_condition (standard_token_sequence left) (standard_token_sequence right) (standard_token_sequence (left ++ right))
          bₛ#0 := by
  let leftSequence := standard_token_sequence left
  let rightSequence := standard_token_sequence right
  let candidate := standard_token_sequence (left ++ right)
  let point : SetTerm := x#393
  let conclusion : SetFormula := ((domₘ(leftSequence) +ₘ point) ∈ₘ domₘ(candidate)) ∧ₘ ((candidate ·ₘ (domₘ(leftSequence) +ₘ point)) ≐ₘ
        (rightSequence ·ₘ point))
  have hPoint :
      Term.CheckCertificate point SetSort.set := by
    prove_term_check
  have hCases :
      ⊢ₘ[standard_sequence_semantics_theory]
        stdseq_numeral_member_condition right.length point ⟶ₘ
          conclusion :=
    stdseq_numeral_member_condition_elim
      right.length point conclusion (fun index hIndex => by
        simpa [conclusion, candidate, leftSequence,
          rightSequence, point] using
          stdtok_append_right_at
            left right point hPoint index hIndex)
  have hDomain :
      Term.CheckCertificate (domₘ(rightSequence)) SetSort.set := by
    prove_term_check
  have hNumeral :
      Term.CheckCertificate (numₘ(right.length)) SetSort.set := by
    prove_term_check
  have hDomainEq :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(rightSequence) ≐ₘ numₘ(right.length) := by
    simpa [rightSequence] using
      standard_token_sequence_domain_eq_length right
  have hDomainIff :=
    membership_right_iff_of_equality
      point (domₘ(rightSequence)) (numₘ(right.length))
      hPoint.admissible hDomain.admissible
      hNumeral.admissible hDomainEq
  have hNumeralIff :=
    stdseq_numeral_member_iff
      right.length point hPoint.admissible
  have hOpen :
      ⊢ₘ[standard_sequence_semantics_theory] (point ∈ₘ domₘ(rightSequence)) ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ domₘ(rightSequence)]
          ⊢ₘ[standard_sequence_semantics_theory]
            point ∈ₘ domₘ(rightSequence) :=
      FirstOrder.Derives.assumption (by simp)
    have hNumeralMembership := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hDomainIff)
      hMembership
    have hCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hNumeralIff)
      hNumeralMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hTheoryFresh :
      ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 393) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence hFormula).2]
    intro hMember
    cases hMember
  have hLeftClose :
      Term.closeFreeAt SetSort.set 393 0 leftSequence = leftSequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 393 0 leftSequence
      (standard_token_sequence_check left).admissible.2 (by
        rw [show Term.freeSupport leftSequence = [] by
          simp [leftSequence]]
        simp)
  have hRightClose :
      Term.closeFreeAt SetSort.set 393 0 rightSequence = rightSequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 393 0 rightSequence
      (standard_token_sequence_check right).admissible.2 (by
        rw [show Term.freeSupport rightSequence = [] by
          simp [rightSequence]]
        simp)
  have hCandidateClose :
      Term.closeFreeAt SetSort.set 393 0 candidate = candidate :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 393 0 candidate
      (standard_token_sequence_check (left ++ right)).admissible.2 (by
        rw [show Term.freeSupport candidate = [] by
          simp [candidate]]
        simp)
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 393)
      hTheoryFresh (by simp) hOpen
  simpa [finite_sequence_concatenation_right_condition,
    conclusion, point, Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, natural_addition_term, domain_term,
    function_application_term, set_variable,
    hLeftClose, hRightClose, hCandidateClose] using hGeneralized
/-- 标准 token 序列的对象拼接等于外部列表拼接后的标准序列。 -/
theorem standard_token_sequence_append (left right : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_token_sequence (left ++ right) ≐ₘ (standard_token_sequence left ⌢ₘ
          standard_token_sequence right) := by
  let leftSequence := standard_token_sequence left
  let rightSequence := standard_token_sequence right
  let candidate := standard_token_sequence (left ++ right)
  have hLeft :
      Term.CheckCertificate leftSequence SetSort.set := by
    prove_term_check
  have hRight :
      Term.CheckCertificate rightSequence SetSort.set := by
    prove_term_check
  have hCandidate :
      Term.CheckCertificate candidate SetSort.set := by
    prove_term_check
  have hCandidateFinite :
      ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_condition candidate := by
    simpa [candidate] using
      standard_token_sequence_finite_sequence_condition (left ++ right)
  have hCandidateDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(candidate) ≐ₘ numₘ(left.length + right.length) := by
    simpa [candidate] using
      standard_token_sequence_domain_eq_length (left ++ right)
  have hNumeralAddition :=
    standard_token_sequence_finite_numeral_addition
      left.length right.length
  have hLeftDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(leftSequence) ≐ₘ numₘ(left.length) := by
    simpa [leftSequence] using
      standard_token_sequence_domain_eq_length left
  have hRightDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(rightSequence) ≐ₘ numₘ(right.length) := by
    simpa [rightSequence] using
      standard_token_sequence_domain_eq_length right
  have hLeftDomainBack :
      ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(left.length) ≐ₘ domₘ(leftSequence) :=
    Metatheory.Derives.equality_symm hLeftDomain
  have hRightDomainBack :
      ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(right.length) ≐ₘ domₘ(rightSequence) :=
    Metatheory.Derives.equality_symm hRightDomain
  have hDomainAddition :
      ⊢ₘ[standard_sequence_semantics_theory] (numₘ(left.length) +ₘ numₘ(right.length)) ≐ₘ (domₘ(leftSequence) +ₘ domₘ(rightSequence)) :=
    natural_addition_term_congr_of_equalities (numₘ(left.length)) (domₘ(leftSequence)) (numₘ(right.length)) (domₘ(rightSequence))
      (finite_numeral_term_admissible left.length)
      (domain_term_admissible leftSequence hLeft.admissible)
      (finite_numeral_term_admissible right.length)
      (domain_term_admissible rightSequence hRight.admissible)
      hLeftDomainBack hRightDomainBack
  have hDomainMiddle :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(candidate) ≐ₘ (numₘ(left.length) +ₘ numₘ(right.length)) :=
    Metatheory.Derives.equality_trans
      hCandidateDomain hNumeralAddition
  have hDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(candidate) ≐ₘ (domₘ(leftSequence) +ₘ domₘ(rightSequence)) :=
    Metatheory.Derives.equality_trans
      hDomainMiddle hDomainAddition
  have hLeftPoint := stdtok_append_left_forall left right
  have hRightPoint := stdtok_append_right_forall left right
  have hSpec :
      ⊢ₘ[standard_sequence_semantics_theory]
        finite_sequence_concatenation_spec
          leftSequence rightSequence candidate := by
    exact FirstOrder.Derives.conjIntro hCandidateFinite <|
      FirstOrder.Derives.conjIntro hDomain <|
        FirstOrder.Derives.conjIntro (by simpa [leftSequence, candidate] using hLeftPoint) (by simpa [leftSequence, rightSequence, candidate] using hRightPoint)
  have hContract :=
    standard_sequence_weaken_concatenation <|
      finite_sequence_concatenation_definition_instance_derives
        leftSequence rightSequence candidate
        hLeft.admissible hRight.admissible
        hCandidate.admissible
  have hIff := FirstOrder.Derives.impElim hContract
    (FirstOrder.Derives.conjIntro
      (by simpa [leftSequence] using
        standard_token_sequence_finite_sequence_condition left)
      (by simpa [rightSequence] using
        standard_token_sequence_finite_sequence_condition right))
  simpa [leftSequence, rightSequence, candidate] using
    FirstOrder.Derives.iffElimLeft hIff hSpec
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
