import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCanonicalBinderShiftInversion.Arithmetic

/-!
# 规范 binder-shift 的单 token 函数性

本模块按对象关系的六个分支做有限反演。free/bound 分支直接消费 checked
guard；其余无限符号族由素数幂增长律导出有限界。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

/-! ## bound 分支 -/

/--
已知标准源 token 时，bound 分支唯一决定目标 token。

深度见证由 checked guard 限制在 `sourceToken + 1` 内；每个标准分支只比较
外部 token，不反演 `ω` 中的任意对象。
-/
theorem fs_zfc_support_raw_canonical_binder_bound_case_unique
    {Γ : Context signature}
    {sourceToken targetToken : Nat}
    (relation :
      CanonicalBinderShiftToken sourceToken targetToken)
    (sourceValue targetValue : SetTerm)
    (boundDepthId : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hTargetFresh :
      (SetSort.set, boundDepthId) ∉
        Term.freeSupport targetValue)
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, boundDepthId) ∉
          Formula.freeSupport formula)
    (hCase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, boundDepthId],
          ((((x#boundDepthId ∈ₘ ωₘ) ∧ₘ
                (x#boundDepthId ∈ₘ Sₘ(sourceValue))) ∧ₘ
              (sourceValue ≐ₘ
                variable_symbol_number_term
                  (canonical_binder_bound_name_term
                    (x#boundDepthId)))) ∧ₘ
            (targetValue ≐ₘ
              variable_symbol_number_term
                (canonical_binder_shifted_bound_name_term
                  (x#boundDepthId))))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken) := by
  let depth : SetTerm := x#boundDepthId
  let body : SetFormula :=
    ((((depth ∈ₘ ωₘ) ∧ₘ
          (depth ∈ₘ Sₘ(sourceValue))) ∧ₘ
        (sourceValue ≐ₘ
          variable_symbol_number_term
            (canonical_binder_bound_name_term depth))) ∧ₘ
      (targetValue ≐ₘ
        variable_symbol_number_term
          (canonical_binder_shifted_bound_name_term depth)))
  have hDepth :
      Term.Admissible depth SetSort.set :=
    set_variable_admissible boundDepthId
  have hDouble :
      Term.Admissible
        (canonical_binder_free_name_term depth)
        SetSort.set :=
    natural_multiplication_term_admissible _ _
      (finite_numeral_term_admissible 2) hDepth
  have hBody :
      Formula.Admissible body := by
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          (membership_formula_admissible
            hDepth omega_term_admissible)
          (membership_formula_admissible hDepth
            (successor_term_admissible
              sourceValue hSourceValue)))
        (Formula.Admissible.equal hSourceValue
          (variable_symbol_number_term_admissible _
            (successor_term_admissible _ hDouble))))
      (Formula.Admissible.equal hTargetValue
        (variable_symbol_number_term_admissible _
          (successor_term_admissible _
            (successor_term_admissible _
              (successor_term_admissible _ hDouble)))))
  have hConclusion :
      Formula.Admissible
        (targetValue ≐ₘ numₘ(targetToken)) :=
    Formula.Admissible.equal hTargetValue
      (finite_numeral_term_admissible targetToken)
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, boundDepthId], body := by
    simpa [body, depth] using hCase
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := boundDepthId)
    (body := body)
    (conclusion := targetValue ≐ₘ numₘ(targetToken))
    (hBodyCheck := Formula.check_admissible_complete hBody)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hContextFresh
  · simpa [Formula.freeSupport,
      finite_numeral_term_freeSupport] using hTargetFresh
  · exact hExists
  · let Δ : Context signature := body :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken)
    have hRaw :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hSourceData :=
      FirstOrder.Derives.conjElimLeft hRaw
    have hDepthData :=
      FirstOrder.Derives.conjElimLeft hSourceData
    have hDepthOmega :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          depth ∈ₘ ωₘ := by
      simpa [body] using
        FirstOrder.Derives.conjElimLeft hDepthData
    have hDepthBound :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          depth ∈ₘ Sₘ(sourceValue) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight hDepthData
    have hSourceEncoding :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ
            variable_symbol_number_term
              (canonical_binder_bound_name_term depth) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight hSourceData
    have hTargetEncoding :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ
            variable_symbol_number_term
              (canonical_binder_shifted_bound_name_term depth) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight hRaw
    have hSourceEqualityAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ numₘ(sourceToken) :=
      FirstOrder.Derives.context_weaken_cons hSourceEquality
    have hSuccessorEquality :=
      successor_term_congr_of_equality
        sourceValue (numₘ(sourceToken))
        hSourceValue
        (finite_numeral_term_admissible sourceToken)
        hSourceEqualityAt
    have hBoundIff :=
      membership_right_iff_of_equality
        depth (Sₘ(sourceValue))
        (Sₘ(numₘ(sourceToken)))
        hDepth
        (successor_term_admissible
          sourceValue hSourceValue)
        (successor_term_admissible
          (numₘ(sourceToken))
          (finite_numeral_term_admissible sourceToken))
        hSuccessorEquality
    have hFiniteBound :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          depth ∈ₘ numₘ(sourceToken + 1) := by
      simpa [finite_numeral_term] using
        FirstOrder.Derives.iffElimRight
          hBoundIff hDepthBound
    apply fs_zfc_support_raw_finite_numeral_member_elim_context
      (sourceToken + 1) depth
      (targetValue ≐ₘ numₘ(targetToken))
      hDepth hConclusion hFiniteBound
    intro index hIndex
    let Ε : Context signature :=
      (depth ≐ₘ numₘ(index)) :: Δ
    change Ε ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken)
    have hDepthEquality :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          depth ≐ₘ numₘ(index) :=
      FirstOrder.Derives.assumption (by simp [Ε])
    have hSourceEqualityBranch :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ numₘ(sourceToken) :=
      FirstOrder.Derives.context_weaken_cons
        hSourceEqualityAt
    have hSourceEncodingBranch :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ
            variable_symbol_number_term
              (canonical_binder_bound_name_term depth) :=
      FirstOrder.Derives.context_weaken_cons hSourceEncoding
    have hTargetEncodingBranch :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ
            variable_symbol_number_term
              (canonical_binder_shifted_bound_name_term depth) :=
      FirstOrder.Derives.context_weaken_cons hTargetEncoding
    cases relation with
    | logical symbol =>
        exact FirstOrder.Derives.falsumElim
          (φ := targetValue ≐ₘ
            numₘ(Numbered.logical_token symbol))
          (fs_zfc_support_raw_bound_source_token_falsum
            (Numbered.logical_token symbol) index
            sourceValue depth
            (logical_token_ne_variable_token
              symbol (bound_name index))
            hDepth hSourceEqualityBranch
            hSourceEncodingBranch hDepthEquality)
    | membership =>
        exact FirstOrder.Derives.falsumElim
          (φ := targetValue ≐ₘ
            numₘ(Numbered.membership_token))
          (fs_zfc_support_raw_bound_source_token_falsum
            Numbered.membership_token index
            sourceValue depth
            (membership_token_ne_variable_token
              (bound_name index))
            hDepth hSourceEqualityBranch
            hSourceEncodingBranch hDepthEquality)
    | free id =>
        exact FirstOrder.Derives.falsumElim
          (φ := targetValue ≐ₘ
            numₘ(Numbered.variable_token (free_name id)))
          (fs_zfc_support_raw_bound_source_token_falsum
            (Numbered.variable_token (free_name id))
            index sourceValue depth
            (variable_token_ne_variable_token
              (free_name_ne_bound_name id index))
            hDepth hSourceEqualityBranch
            hSourceEncodingBranch hDepthEquality)
    | bound expectedDepth =>
        by_cases hDepthIndex : index = expectedDepth
        · subst index
          exact fs_zfc_support_raw_bound_target_token_eq
            expectedDepth targetValue depth hDepth
            hTargetEncodingBranch hDepthEquality
        · exact FirstOrder.Derives.falsumElim
            (φ := targetValue ≐ₘ
              numₘ(Numbered.variable_token
                (bound_name (expectedDepth + 1))))
            (fs_zfc_support_raw_bound_source_token_falsum
              (Numbered.variable_token
                (bound_name expectedDepth))
              index sourceValue depth
              (variable_token_ne_variable_token <| by
                intro hNames
                exact hDepthIndex <|
                  (bound_name_injective hNames).symm)
              hDepth hSourceEqualityBranch
              hSourceEncodingBranch hDepthEquality)
    | constant constantIndex =>
        exact FirstOrder.Derives.falsumElim
          (φ := targetValue ≐ₘ
            numₘ(Numbered.constant_token constantIndex))
          (fs_zfc_support_raw_bound_source_token_falsum
            (Numbered.constant_token constantIndex)
            index sourceValue depth
            (constant_token_ne_variable_token
              constantIndex (bound_name index))
            hDepth hSourceEqualityBranch
            hSourceEncodingBranch hDepthEquality)
    | function arity functionIndex =>
        exact FirstOrder.Derives.falsumElim
          (φ := targetValue ≐ₘ
            numₘ(Numbered.function_token arity functionIndex))
          (fs_zfc_support_raw_bound_source_token_falsum
            (Numbered.function_token arity functionIndex)
            index sourceValue depth
            (function_token_ne_variable_token
              arity functionIndex (bound_name index))
            hDepth hSourceEqualityBranch
            hSourceEncodingBranch hDepthEquality)
    | predicate arity predicateIndex =>
        exact FirstOrder.Derives.falsumElim
          (φ := targetValue ≐ₘ
            numₘ(Numbered.predicate_token arity predicateIndex))
          (fs_zfc_support_raw_bound_source_token_falsum
            (Numbered.predicate_token arity predicateIndex)
            index sourceValue depth
            (predicate_token_ne_variable_token
              arity predicateIndex (bound_name index))
            hDepth hSourceEqualityBranch
            hSourceEncodingBranch hDepthEquality)

/-! ## bound 源 token 对其他分支的拒绝 -/

/-- 标准 bound token 不满足固定逻辑/隶属 token 枚举。 -/
theorem fs_zfc_support_raw_bound_token_fixed_falsum
    {Γ : Context signature}
    (depth : Nat)
    (sourceValue : SetTerm)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          numₘ(Numbered.variable_token
            (bound_name depth)))
    (hFixed :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_shift_fixed_token_condition
          sourceValue) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [sourceValue ≐ₘ sourceValue]
  let body : SetFormula :=
    canonical_binder_shift_fixed_token_condition
      (x#parameter)
  have hIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := parameter)
      (left := sourceValue)
      (right :=
        numₘ(Numbered.variable_token
          (bound_name depth)))
      (body := body)
      hSourceEquality
  have hFixedNumeral :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_shift_fixed_token_condition
          (numₘ(Numbered.variable_token
            (bound_name depth))) := by
    apply FirstOrder.Derives.iffElimRight
      (by
        simpa [body, parameter,
          Formula.substituteFree, Term.substituteFree,
          set_variable,
          GodelQuotation.gq_binder_shift_numeral_substitute] using
          hIffRaw)
    exact hFixed
  let sourceToken :=
    Numbered.variable_token (bound_name depth)
  change Γ ⊢ₘ[fs_zfc_support_raw_theory]
    ((numₘ(sourceToken) ≐ₘ
          logical_symbol_number_term .equality) ∨ₘ
      ((numₘ(sourceToken) ≐ₘ
          logical_symbol_number_term .negation) ∨ₘ
        ((numₘ(sourceToken) ≐ₘ
            logical_symbol_number_term .implication) ∨ₘ
          ((numₘ(sourceToken) ≐ₘ
              logical_symbol_number_term .universal) ∨ₘ
            ((numₘ(sourceToken) ≐ₘ
                logical_symbol_number_term .leftParenthesis) ∨ₘ
              ((numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis) ∨ₘ
                ((numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum))))))))) at hFixedNumeral
  rcases Formula.CheckCertificate.disj_iff.mp
      hFixedNumeral.formula_checked with
    ⟨hEqualityCheck, hTail₁Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp
      hTail₁Check with
    ⟨hNegationCheck, hTail₂Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp
      hTail₂Check with
    ⟨hImplicationCheck, hTail₃Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp
      hTail₃Check with
    ⟨hUniversalCheck, hTail₄Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp
      hTail₄Check with
    ⟨hLeftParenthesisCheck, hTail₅Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp
      hTail₅Check with
    ⟨hRightParenthesisCheck, hTail₆Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp
      hTail₆Check with
    ⟨hExistentialCheck, hTail₇Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp
      hTail₇Check with
    ⟨hConjunctionCheck, hTail₈Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp
      hTail₈Check with
    ⟨hMembershipCheck, hFalsumCheck⟩
  have hLogical
      (symbol : LogicalSymbolKind)
      {Δ : Context signature}
      (hValue :
        (numₘ(sourceToken) ≐ₘ
          logical_symbol_number_term symbol) :: Δ
          ⊢ₘ[fs_zfc_support_raw_theory]
            numₘ(sourceToken) ≐ₘ
              logical_symbol_number_term symbol) :
      (numₘ(sourceToken) ≐ₘ
          logical_symbol_number_term symbol) :: Δ
        ⊢ₘ[fs_zfc_support_raw_theory]
          Formula.falsum :=
    fs_zfc_support_raw_falsum_of_binder_symbol_value
      sourceToken (Numbered.logical_token symbol)
      (numₘ(sourceToken))
      (logical_symbol_number_term symbol)
      (logical_token_ne_variable_token
        symbol (bound_name depth)).symm
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(sourceToken)))
      hValue
      (GodelQuotation.gq_binder_shift_logical_symbol_value
        symbol)
  have hMembership
      {Δ : Context signature}
      (hValue :
        (numₘ(sourceToken) ≐ₘ
          membership_symbol_number_term) :: Δ
          ⊢ₘ[fs_zfc_support_raw_theory]
            numₘ(sourceToken) ≐ₘ
              membership_symbol_number_term) :
      (numₘ(sourceToken) ≐ₘ
          membership_symbol_number_term) :: Δ
        ⊢ₘ[fs_zfc_support_raw_theory]
          Formula.falsum :=
    fs_zfc_support_raw_falsum_of_binder_symbol_value
      sourceToken Numbered.membership_token
      (numₘ(sourceToken))
      membership_symbol_number_term
      (membership_token_ne_variable_token
        (bound_name depth)).symm
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(sourceToken)))
      hValue
      GodelQuotation.gq_binder_shift_membership_symbol_value
  apply FirstOrder.Derives.disjElim hFixedNumeral
  · exact hLogical .equality
      (FirstOrder.Derives.assumption
        (by simp) hEqualityCheck)
  · apply FirstOrder.Derives.disjElim
      (left :=
        numₘ(sourceToken) ≐ₘ
          logical_symbol_number_term .negation)
      (right :=
        (numₘ(sourceToken) ≐ₘ
            logical_symbol_number_term .implication) ∨ₘ
          ((numₘ(sourceToken) ≐ₘ
              logical_symbol_number_term .universal) ∨ₘ
            ((numₘ(sourceToken) ≐ₘ
                logical_symbol_number_term .leftParenthesis) ∨ₘ
              ((numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis) ∨ₘ
                ((numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum)))))))
      (FirstOrder.Derives.assumption
        (by simp) hTail₁Check)
    · exact hLogical .negation
        (FirstOrder.Derives.assumption
          (by simp) hNegationCheck)
    · apply FirstOrder.Derives.disjElim
        (left :=
          numₘ(sourceToken) ≐ₘ
            logical_symbol_number_term .implication)
        (right :=
          (numₘ(sourceToken) ≐ₘ
              logical_symbol_number_term .universal) ∨ₘ
            ((numₘ(sourceToken) ≐ₘ
                logical_symbol_number_term .leftParenthesis) ∨ₘ
              ((numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis) ∨ₘ
                ((numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum))))))
        (FirstOrder.Derives.assumption
          (by simp) hTail₂Check)
      · exact hLogical .implication
          (FirstOrder.Derives.assumption
            (by simp) hImplicationCheck)
      · apply FirstOrder.Derives.disjElim
          (left :=
            numₘ(sourceToken) ≐ₘ
              logical_symbol_number_term .universal)
          (right :=
            (numₘ(sourceToken) ≐ₘ
                logical_symbol_number_term .leftParenthesis) ∨ₘ
              ((numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis) ∨ₘ
                ((numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum)))))
          (FirstOrder.Derives.assumption
            (by simp) hTail₃Check)
        · exact hLogical .universal
            (FirstOrder.Derives.assumption
              (by simp) hUniversalCheck)
        · apply FirstOrder.Derives.disjElim
            (left :=
              numₘ(sourceToken) ≐ₘ
                logical_symbol_number_term .leftParenthesis)
            (right :=
              (numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis) ∨ₘ
                ((numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum))))
            (FirstOrder.Derives.assumption
              (by simp) hTail₄Check)
          · exact hLogical .leftParenthesis
              (FirstOrder.Derives.assumption
                (by simp) hLeftParenthesisCheck)
          · apply FirstOrder.Derives.disjElim
              (left :=
                numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis)
              (right :=
                (numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum)))
              (FirstOrder.Derives.assumption
                (by simp) hTail₅Check)
            · exact hLogical .rightParenthesis
                (FirstOrder.Derives.assumption
                  (by simp) hRightParenthesisCheck)
            · apply FirstOrder.Derives.disjElim
                (left :=
                  numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential)
                (right :=
                  (numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum))
                (FirstOrder.Derives.assumption
                  (by simp) hTail₆Check)
              · exact hLogical .existential
                  (FirstOrder.Derives.assumption
                    (by simp) hExistentialCheck)
              · apply FirstOrder.Derives.disjElim
                  (left :=
                    numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction)
                  (right :=
                    (numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum)
                  (FirstOrder.Derives.assumption
                    (by simp) hTail₇Check)
                · exact hLogical .conjunction
                    (FirstOrder.Derives.assumption
                      (by simp) hConjunctionCheck)
                · apply FirstOrder.Derives.disjElim
                    (left :=
                      numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term)
                    (right := Formula.falsum)
                    (FirstOrder.Derives.assumption
                      (by simp) hTail₈Check)
                  · exact hMembership
                      (FirstOrder.Derives.assumption
                        (by simp) hMembershipCheck)
                  · exact FirstOrder.Derives.assumption
                      (by simp) hFalsumCheck

/-- 标准 bound token 不可能落入 free 偶名字分支。 -/
theorem fs_zfc_support_raw_bound_token_free_case_falsum
    {Γ : Context signature}
    (depth : Nat)
    (sourceValue targetValue : SetTerm)
    (freeId : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          numₘ(Numbered.variable_token
            (bound_name depth)))
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, freeId) ∉
          Formula.freeSupport formula)
    (hCase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, freeId],
          ((((x#freeId ∈ₘ ωₘ) ∧ₘ
                (x#freeId ∈ₘ Sₘ(sourceValue))) ∧ₘ
              (sourceValue ≐ₘ
                variable_symbol_number_term
                  (canonical_binder_free_name_term
                    (x#freeId)))) ∧ₘ
            (targetValue ≐ₘ sourceValue))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let witness : SetTerm := x#freeId
  let body : SetFormula :=
    ((((witness ∈ₘ ωₘ) ∧ₘ
          (witness ∈ₘ Sₘ(sourceValue))) ∧ₘ
        (sourceValue ≐ₘ
          variable_symbol_number_term
            (canonical_binder_free_name_term witness))) ∧ₘ
      (targetValue ≐ₘ sourceValue))
  have hWitness :
      Term.Admissible witness SetSort.set :=
    set_variable_admissible freeId
  have hBody :
      Formula.Admissible body := by
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          (membership_formula_admissible
            hWitness omega_term_admissible)
          (membership_formula_admissible hWitness
            (successor_term_admissible
              sourceValue hSourceValue)))
      (Formula.Admissible.equal hSourceValue
          (variable_symbol_number_term_admissible _
            (natural_multiplication_term_admissible _ _
              (finite_numeral_term_admissible 2)
              hWitness))))
      (Formula.Admissible.equal hTargetValue hSourceValue)
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, freeId], body := by
    simpa [body, witness] using hCase
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := freeId)
    (body := body)
    (conclusion := Formula.falsum)
    (hBodyCheck := Formula.check_admissible_complete hBody)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hContextFresh
  · simp [Formula.freeSupport]
  · exact hExists
  · let Δ : Context signature := body :: Γ
    have hRaw :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hSourceData :=
      FirstOrder.Derives.conjElimLeft hRaw
    have hWitnessData :=
      FirstOrder.Derives.conjElimLeft hSourceData
    have hWitnessBound :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          witness ∈ₘ Sₘ(sourceValue) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight hWitnessData
    have hSourceEncoding :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ
            variable_symbol_number_term
              (canonical_binder_free_name_term witness) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight hSourceData
    have hSourceEqualityAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ
            numₘ(Numbered.variable_token
              (bound_name depth)) :=
      FirstOrder.Derives.context_weaken_cons hSourceEquality
    have hSuccessorEquality :=
      successor_term_congr_of_equality
        sourceValue
        (numₘ(Numbered.variable_token
          (bound_name depth)))
        hSourceValue
        (finite_numeral_term_admissible _)
        hSourceEqualityAt
    have hFiniteBound :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          witness ∈ₘ
            numₘ(Numbered.variable_token
              (bound_name depth) + 1) := by
      simpa [finite_numeral_term] using
        FirstOrder.Derives.iffElimRight
          (membership_right_iff_of_equality
            witness (Sₘ(sourceValue))
            (Sₘ(numₘ(Numbered.variable_token
              (bound_name depth))))
            hWitness
            (successor_term_admissible
              sourceValue hSourceValue)
            (successor_term_admissible _
              (finite_numeral_term_admissible _))
            hSuccessorEquality)
          hWitnessBound
    apply fs_zfc_support_raw_finite_numeral_member_elim_context
      (Numbered.variable_token (bound_name depth) + 1)
      witness Formula.falsum hWitness
      Formula.Admissible.falsum hFiniteBound
    intro index hIndex
    let Ε : Context signature :=
      (witness ≐ₘ numₘ(index)) :: Δ
    exact fs_zfc_support_raw_free_source_token_falsum
      (Numbered.variable_token (bound_name depth))
      index sourceValue witness
      (variable_token_ne_variable_token <|
        (free_name_ne_bound_name index depth).symm)
      hWitness
      (FirstOrder.Derives.context_weaken_cons
        hSourceEqualityAt)
      (FirstOrder.Derives.context_weaken_cons
        hSourceEncoding)
      (FirstOrder.Derives.assumption (by simp))

/-- 标准 bound token 不可能落入常元分支。 -/
theorem fs_zfc_support_raw_bound_token_constant_case_falsum
    {Γ : Context signature}
    (depth : Nat)
    (sourceValue targetValue : SetTerm)
    (constantId : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          numₘ(Numbered.variable_token
            (bound_name depth)))
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, constantId) ∉
          Formula.freeSupport formula)
    (hCase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, constantId],
          (((x#constantId ∈ₘ ωₘ) ∧ₘ
              (sourceValue ≐ₘ
                constant_symbol_number_term
                  (x#constantId))) ∧ₘ
            (targetValue ≐ₘ sourceValue))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let witness : SetTerm := x#constantId
  let body : SetFormula :=
    (((witness ∈ₘ ωₘ) ∧ₘ
        (sourceValue ≐ₘ
          constant_symbol_number_term witness)) ∧ₘ
      (targetValue ≐ₘ sourceValue))
  have hWitness :
      Term.Admissible witness SetSort.set :=
    set_variable_admissible constantId
  have hBody :
      Formula.Admissible body := by
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (membership_formula_admissible
          hWitness omega_term_admissible)
        (Formula.Admissible.equal hSourceValue
          (constant_symbol_number_term_admissible
            witness hWitness)))
      (Formula.Admissible.equal hTargetValue hSourceValue)
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, constantId], body := by
    simpa [body, witness] using hCase
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := constantId)
    (body := body)
    (conclusion := Formula.falsum)
    (hBodyCheck := Formula.check_admissible_complete hBody)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hContextFresh
  · simp [Formula.freeSupport]
  · exact hExists
  · let Δ : Context signature := body :: Γ
    have hRaw :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hSourceData :=
      FirstOrder.Derives.conjElimLeft hRaw
    have hWitnessOmega :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          witness ∈ₘ ωₘ := by
      simpa [body] using
        FirstOrder.Derives.conjElimLeft hSourceData
    have hSourceEncoding :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ
            constant_symbol_number_term witness := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight hSourceData
    have hSourceEqualityAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ
            numₘ(Numbered.variable_token
              (bound_name depth)) :=
      FirstOrder.Derives.context_weaken_cons hSourceEquality
    have hFiniteBound :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          witness ∈ₘ
            numₘ(Numbered.variable_token
              (bound_name depth)) := by
      simpa [constant_symbol_number_term] using
        fs_zfc_support_raw_index_mem_source_of_prime_power
          5 sourceValue witness (by omega)
          hWitness hSourceEqualityAt hWitnessOmega <| by
            simpa [constant_symbol_number_term] using
              hSourceEncoding
    apply fs_zfc_support_raw_finite_numeral_member_elim_context
      (Numbered.variable_token (bound_name depth))
      witness Formula.falsum hWitness
      Formula.Admissible.falsum hFiniteBound
    intro index hIndex
    let Ε : Context signature :=
      (witness ≐ₘ numₘ(index)) :: Δ
    exact fs_zfc_support_raw_constant_source_token_falsum
      (Numbered.variable_token (bound_name depth))
      index sourceValue witness
      (constant_token_ne_variable_token
        index (bound_name depth)).symm
      hWitness
      (FirstOrder.Derives.context_weaken_cons
        hSourceEqualityAt)
      (FirstOrder.Derives.context_weaken_cons
        hSourceEncoding)
      (FirstOrder.Derives.assumption (by simp))

/-- 标准 bound token 不可能落入函数分支。 -/
theorem fs_zfc_support_raw_bound_token_function_case_falsum
    {Γ : Context signature}
    (depth : Nat)
    (sourceValue targetValue : SetTerm)
    (arityId indexId : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          numₘ(Numbered.variable_token
            (bound_name depth)))
    (hArityFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, arityId) ∉
          Formula.freeSupport formula)
    (hIndexFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula)
    (hCase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, arityId],
          ∃ₘ[SetSort.set, indexId],
            ((((x#arityId ∈ₘ ωₘ) ∧ₘ
                  (x#indexId ∈ₘ ωₘ)) ∧ₘ
                (sourceValue ≐ₘ
                  coded_function_symbol_number_term
                    (x#arityId) (x#indexId))) ∧ₘ
              (targetValue ≐ₘ sourceValue))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let arity : SetTerm := x#arityId
  let index : SetTerm := x#indexId
  let body : SetFormula :=
    ((((arity ∈ₘ ωₘ) ∧ₘ
          (index ∈ₘ ωₘ)) ∧ₘ
        (sourceValue ≐ₘ
          coded_function_symbol_number_term arity index)) ∧ₘ
      (targetValue ≐ₘ sourceValue))
  let innerExists : SetFormula :=
    ∃ₘ[SetSort.set, indexId], body
  have hArity :
      Term.Admissible arity SetSort.set :=
    set_variable_admissible arityId
  have hIndex :
      Term.Admissible index SetSort.set :=
    set_variable_admissible indexId
  have hBody :
      Formula.Admissible body := by
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          (membership_formula_admissible hArity
            omega_term_admissible)
          (membership_formula_admissible hIndex
            omega_term_admissible))
        (Formula.Admissible.equal hSourceValue
          (coded_function_symbol_number_term_admissible
            arity index hArity hIndex)))
      (Formula.Admissible.equal hTargetValue hSourceValue)
  have hInnerExists :
      Formula.Admissible innerExists := by
    simpa [innerExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set indexId hBody
  have hOuterExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, arityId], innerExists := by
    simpa [innerExists, body, arity, index] using hCase
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := arityId)
    (body := innerExists)
    (conclusion := Formula.falsum)
    (hBodyCheck := Formula.check_admissible_complete hInnerExists)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hArityFresh
  · simp [Formula.freeSupport]
  · exact hOuterExists
  · let Δ₁ : Context signature := innerExists :: Γ
    have hInnerAt :
        Δ₁ ⊢ₘ[fs_zfc_support_raw_theory] innerExists :=
      FirstOrder.Derives.assumption (by simp [Δ₁])
    have hIndexFreshInner :
        (SetSort.set, indexId) ∉
          Formula.freeSupport innerExists := by
      simpa [innerExists] using
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set indexId 0 body
    apply FirstOrder.Derives.exists_elim
      (T := fs_zfc_support_raw_theory)
      (Γ := Δ₁)
      (sort := SetSort.set)
      (eigen := indexId)
      (body := body)
      (conclusion := Formula.falsum)
      (hBodyCheck := Formula.check_admissible_complete hBody)
    · intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Δ₁, List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · exact hIndexFreshInner
      · exact hIndexFresh formula hFormula
    · change
        (SetSort.set, indexId) ∉
          Formula.freeSupport (Formula.falsum : SetFormula)
      exact List.not_mem_nil
    · simpa [body] using hInnerAt
    · let Δ₂ : Context signature := body :: Δ₁
      have hRaw :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory] body :=
        FirstOrder.Derives.assumption (by simp [Δ₂])
      have hSourceData :=
        FirstOrder.Derives.conjElimLeft hRaw
      have hIndicesData :=
        FirstOrder.Derives.conjElimLeft hSourceData
      have hArityOmega :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            arity ∈ₘ ωₘ := by
        simpa [body] using
          FirstOrder.Derives.conjElimLeft hIndicesData
      have hIndexOmega :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            index ∈ₘ ωₘ := by
        simpa [body] using
          FirstOrder.Derives.conjElimRight hIndicesData
      have hSourceEncoding :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            sourceValue ≐ₘ
              coded_function_symbol_number_term arity index := by
        simpa [body] using
          FirstOrder.Derives.conjElimRight hSourceData
      have hSourceEqualityAt :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            sourceValue ≐ₘ
              numₘ(Numbered.variable_token
                (bound_name depth)) :=
        FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hSourceEquality)
      have hIndicesBound :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            ((arity ∈ₘ
                numₘ(Numbered.variable_token
                  (bound_name depth))) ∧ₘ
              (index ∈ₘ
                numₘ(Numbered.variable_token
                  (bound_name depth)))) := by
        simpa [coded_function_symbol_number_term,
          indexed_prime_power_code_term] using
          fs_zfc_support_raw_indices_mem_source_of_prime_power_product
            3 5 sourceValue arity index (by omega) (by omega)
            hArity hIndex hSourceEqualityAt
            hArityOmega hIndexOmega hSourceEncoding
      have hArityBound :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            arity ∈ₘ
              numₘ(Numbered.variable_token
                (bound_name depth)) :=
        FirstOrder.Derives.conjElimLeft hIndicesBound
      have hIndexBound :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            index ∈ₘ
              numₘ(Numbered.variable_token
                (bound_name depth)) :=
        FirstOrder.Derives.conjElimRight hIndicesBound
      apply fs_zfc_support_raw_finite_numeral_member_elim_context
        (Numbered.variable_token (bound_name depth))
        arity Formula.falsum hArity
        Formula.Admissible.falsum hArityBound
      intro arityValue hArityValue
      let Ε₁ : Context signature :=
        (arity ≐ₘ numₘ(arityValue)) :: Δ₂
      have hArityEquality :
          Ε₁ ⊢ₘ[fs_zfc_support_raw_theory]
            arity ≐ₘ numₘ(arityValue) :=
        FirstOrder.Derives.assumption (by simp [Ε₁])
      have hIndexBoundAt :
          Ε₁ ⊢ₘ[fs_zfc_support_raw_theory]
            index ∈ₘ
              numₘ(Numbered.variable_token
                (bound_name depth)) :=
        FirstOrder.Derives.context_weaken_cons hIndexBound
      apply fs_zfc_support_raw_finite_numeral_member_elim_context
        (Numbered.variable_token (bound_name depth))
        index Formula.falsum hIndex
        Formula.Admissible.falsum hIndexBoundAt
      intro indexValue hIndexValue
      let Ε₂ : Context signature :=
        (index ≐ₘ numₘ(indexValue)) :: Ε₁
      have hIndexEquality :
          Ε₂ ⊢ₘ[fs_zfc_support_raw_theory]
            index ≐ₘ numₘ(indexValue) :=
        FirstOrder.Derives.assumption (by simp [Ε₂])
      have hArityEqualityAt :
          Ε₂ ⊢ₘ[fs_zfc_support_raw_theory]
            arity ≐ₘ numₘ(arityValue) :=
        FirstOrder.Derives.context_weaken_cons hArityEquality
      have hSourceEqualityBranch :
          Ε₂ ⊢ₘ[fs_zfc_support_raw_theory]
            sourceValue ≐ₘ
              numₘ(Numbered.variable_token
                (bound_name depth)) :=
        FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hSourceEqualityAt)
      have hSourceEncodingBranch :
          Ε₂ ⊢ₘ[fs_zfc_support_raw_theory]
            sourceValue ≐ₘ
              coded_function_symbol_number_term arity index :=
        FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hSourceEncoding)
      exact fs_zfc_support_raw_function_source_token_falsum
        (Numbered.variable_token (bound_name depth))
        arityValue indexValue sourceValue arity index
        (function_token_ne_variable_token
          arityValue indexValue (bound_name depth)).symm
        hArity hIndex hSourceEqualityBranch
        hSourceEncodingBranch hArityEqualityAt hIndexEquality

/-- 标准 bound token 不可能落入谓词分支。 -/
theorem fs_zfc_support_raw_bound_token_predicate_case_falsum
    {Γ : Context signature}
    (depth : Nat)
    (sourceValue targetValue : SetTerm)
    (arityId indexId : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          numₘ(Numbered.variable_token
            (bound_name depth)))
    (hArityFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, arityId) ∉
          Formula.freeSupport formula)
    (hIndexFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula)
    (hCase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, arityId],
          ∃ₘ[SetSort.set, indexId],
            ((((x#arityId ∈ₘ ωₘ) ∧ₘ
                  (x#indexId ∈ₘ ωₘ)) ∧ₘ
                (sourceValue ≐ₘ
                  coded_predicate_symbol_number_term
                    (x#arityId) (x#indexId))) ∧ₘ
              (targetValue ≐ₘ sourceValue))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let arity : SetTerm := x#arityId
  let index : SetTerm := x#indexId
  let body : SetFormula :=
    ((((arity ∈ₘ ωₘ) ∧ₘ
          (index ∈ₘ ωₘ)) ∧ₘ
        (sourceValue ≐ₘ
          coded_predicate_symbol_number_term arity index)) ∧ₘ
      (targetValue ≐ₘ sourceValue))
  let innerExists : SetFormula :=
    ∃ₘ[SetSort.set, indexId], body
  have hArity :
      Term.Admissible arity SetSort.set :=
    set_variable_admissible arityId
  have hIndex :
      Term.Admissible index SetSort.set :=
    set_variable_admissible indexId
  have hBody :
      Formula.Admissible body := by
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          (membership_formula_admissible hArity
            omega_term_admissible)
          (membership_formula_admissible hIndex
            omega_term_admissible))
        (Formula.Admissible.equal hSourceValue
          (coded_predicate_symbol_number_term_admissible
            arity index hArity hIndex)))
      (Formula.Admissible.equal hTargetValue hSourceValue)
  have hInnerExists :
      Formula.Admissible innerExists := by
    simpa [innerExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set indexId hBody
  have hOuterExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, arityId], innerExists := by
    simpa [innerExists, body, arity, index] using hCase
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := arityId)
    (body := innerExists)
    (conclusion := Formula.falsum)
    (hBodyCheck := Formula.check_admissible_complete hInnerExists)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hArityFresh
  · simp [Formula.freeSupport]
  · exact hOuterExists
  · let Δ₁ : Context signature := innerExists :: Γ
    have hInnerAt :
        Δ₁ ⊢ₘ[fs_zfc_support_raw_theory] innerExists :=
      FirstOrder.Derives.assumption (by simp [Δ₁])
    have hIndexFreshInner :
        (SetSort.set, indexId) ∉
          Formula.freeSupport innerExists := by
      simpa [innerExists] using
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set indexId 0 body
    apply FirstOrder.Derives.exists_elim
      (T := fs_zfc_support_raw_theory)
      (Γ := Δ₁)
      (sort := SetSort.set)
      (eigen := indexId)
      (body := body)
      (conclusion := Formula.falsum)
      (hBodyCheck := Formula.check_admissible_complete hBody)
    · intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Δ₁, List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · exact hIndexFreshInner
      · exact hIndexFresh formula hFormula
    · change
        (SetSort.set, indexId) ∉
          Formula.freeSupport (Formula.falsum : SetFormula)
      exact List.not_mem_nil
    · simpa [body] using hInnerAt
    · let Δ₂ : Context signature := body :: Δ₁
      have hRaw :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory] body :=
        FirstOrder.Derives.assumption (by simp [Δ₂])
      have hSourceData :=
        FirstOrder.Derives.conjElimLeft hRaw
      have hIndicesData :=
        FirstOrder.Derives.conjElimLeft hSourceData
      have hArityOmega :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            arity ∈ₘ ωₘ := by
        simpa [body] using
          FirstOrder.Derives.conjElimLeft hIndicesData
      have hIndexOmega :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            index ∈ₘ ωₘ := by
        simpa [body] using
          FirstOrder.Derives.conjElimRight hIndicesData
      have hSourceEncoding :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            sourceValue ≐ₘ
              coded_predicate_symbol_number_term arity index := by
        simpa [body] using
          FirstOrder.Derives.conjElimRight hSourceData
      have hSourceEqualityAt :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            sourceValue ≐ₘ
              numₘ(Numbered.variable_token
                (bound_name depth)) :=
        FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hSourceEquality)
      have hIndicesBound :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            ((arity ∈ₘ
                numₘ(Numbered.variable_token
                  (bound_name depth))) ∧ₘ
              (index ∈ₘ
                numₘ(Numbered.variable_token
                  (bound_name depth)))) := by
        simpa [coded_predicate_symbol_number_term,
          indexed_prime_power_code_term] using
          fs_zfc_support_raw_indices_mem_source_of_prime_power_product
            3 7 sourceValue arity index (by omega) (by omega)
            hArity hIndex hSourceEqualityAt
            hArityOmega hIndexOmega hSourceEncoding
      have hArityBound :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            arity ∈ₘ
              numₘ(Numbered.variable_token
                (bound_name depth)) :=
        FirstOrder.Derives.conjElimLeft hIndicesBound
      have hIndexBound :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            index ∈ₘ
              numₘ(Numbered.variable_token
                (bound_name depth)) :=
        FirstOrder.Derives.conjElimRight hIndicesBound
      apply fs_zfc_support_raw_finite_numeral_member_elim_context
        (Numbered.variable_token (bound_name depth))
        arity Formula.falsum hArity
        Formula.Admissible.falsum hArityBound
      intro arityValue hArityValue
      let Ε₁ : Context signature :=
        (arity ≐ₘ numₘ(arityValue)) :: Δ₂
      have hArityEquality :
          Ε₁ ⊢ₘ[fs_zfc_support_raw_theory]
            arity ≐ₘ numₘ(arityValue) :=
        FirstOrder.Derives.assumption (by simp [Ε₁])
      have hIndexBoundAt :
          Ε₁ ⊢ₘ[fs_zfc_support_raw_theory]
            index ∈ₘ
              numₘ(Numbered.variable_token
                (bound_name depth)) :=
        FirstOrder.Derives.context_weaken_cons hIndexBound
      apply fs_zfc_support_raw_finite_numeral_member_elim_context
        (Numbered.variable_token (bound_name depth))
        index Formula.falsum hIndex
        Formula.Admissible.falsum hIndexBoundAt
      intro indexValue hIndexValue
      let Ε₂ : Context signature :=
        (index ≐ₘ numₘ(indexValue)) :: Ε₁
      have hIndexEquality :
          Ε₂ ⊢ₘ[fs_zfc_support_raw_theory]
            index ≐ₘ numₘ(indexValue) :=
        FirstOrder.Derives.assumption (by simp [Ε₂])
      have hArityEqualityAt :
          Ε₂ ⊢ₘ[fs_zfc_support_raw_theory]
            arity ≐ₘ numₘ(arityValue) :=
        FirstOrder.Derives.context_weaken_cons hArityEquality
      have hSourceEqualityBranch :
          Ε₂ ⊢ₘ[fs_zfc_support_raw_theory]
            sourceValue ≐ₘ
              numₘ(Numbered.variable_token
                (bound_name depth)) :=
        FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hSourceEqualityAt)
      have hSourceEncodingBranch :
          Ε₂ ⊢ₘ[fs_zfc_support_raw_theory]
            sourceValue ≐ₘ
              coded_predicate_symbol_number_term arity index :=
        FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hSourceEncoding)
      exact fs_zfc_support_raw_predicate_source_token_falsum
        (Numbered.variable_token (bound_name depth))
        arityValue indexValue sourceValue arity index
        (predicate_token_ne_variable_token
          arityValue indexValue (bound_name depth)).symm
        hArity hIndex hSourceEqualityBranch
        hSourceEncodingBranch hArityEqualityAt hIndexEquality

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
