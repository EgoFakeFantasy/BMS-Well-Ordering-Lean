import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCanonicalBinderShiftInversion.Token

/-!
# 规范 binder-shift 的单 token 关系唯一性

本模块只提供分支组装所需的存在消去接口，具体算术反演全部由 `Token` 模块消费。
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

private theorem fs_zfc_support_raw_exists_target_eq_source
    {Γ : Context signature}
    (eigen : FreeVarId)
    (body : SetFormula)
    (sourceValue targetValue : SetTerm)
    (hSourceFresh :
      (SetSort.set, eigen) ∉
        Term.freeSupport sourceValue)
    (hTargetFresh :
      (SetSort.set, eigen) ∉
        Term.freeSupport targetValue)
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, eigen) ∉
          Formula.freeSupport formula)
    (hBody :
      Formula.Admissible body)
    (hCase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, eigen], body)
    (hTargetCase :
      body :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ sourceValue) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ sourceValue := by
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := eigen)
    (body := body)
    (conclusion := targetValue ≐ₘ sourceValue)
    (hBodyCheck := Formula.check_admissible_complete hBody)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hContextFresh
  · change
      (SetSort.set, eigen) ∉
        Formula.freeSupport
          (targetValue ≐ₘ sourceValue)
    simp only [Formula.freeSupport]
    intro hMember
    rcases List.mem_append.mp hMember with hMember | hMember
    · exact hTargetFresh hMember
    · exact hSourceFresh hMember
  · exact hCase
  · exact hTargetCase

private theorem fs_zfc_support_raw_exists₂_target_eq_source
    {Γ : Context signature}
    (outerId innerId : FreeVarId)
    (body : SetFormula)
    (sourceValue targetValue : SetTerm)
    (hSourceOuterFresh :
      (SetSort.set, outerId) ∉
        Term.freeSupport sourceValue)
    (hTargetOuterFresh :
      (SetSort.set, outerId) ∉
        Term.freeSupport targetValue)
    (hSourceInnerFresh :
      (SetSort.set, innerId) ∉
        Term.freeSupport sourceValue)
    (hTargetInnerFresh :
      (SetSort.set, innerId) ∉
        Term.freeSupport targetValue)
    (hContextOuterFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, outerId) ∉
          Formula.freeSupport formula)
    (hContextInnerFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, innerId) ∉
          Formula.freeSupport formula)
    (hBody :
      Formula.Admissible body)
    (hCase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, outerId],
          ∃ₘ[SetSort.set, innerId], body)
    (hTargetCase :
      body ::
          (∃ₘ[SetSort.set, innerId], body) :: Γ
        ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ sourceValue) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ sourceValue := by
  let innerExists : SetFormula :=
    ∃ₘ[SetSort.set, innerId], body
  have hInnerExists :
      Formula.Admissible innerExists := by
    simpa [innerExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set innerId hBody
  have hOuterCase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, outerId], innerExists := by
    simpa [innerExists] using hCase
  have hInnerTarget :
      innerExists :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ sourceValue := by
    have hInnerAt :
        innerExists :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
          ∃ₘ[SetSort.set, innerId], body := by
      simpa [innerExists] using
        (FirstOrder.Derives.assumption
          (T := fs_zfc_support_raw_theory)
          (Γ := innerExists :: Γ)
          (φ := innerExists)
          (by simp))
    apply fs_zfc_support_raw_exists_target_eq_source
      innerId body sourceValue targetValue
      hSourceInnerFresh hTargetInnerFresh
    · intro formula hFormula
      simp only [List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · simpa [innerExists] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set innerId 0 body
      · exact hContextInnerFresh formula hFormula
    · exact hBody
    · exact hInnerAt
    · simpa [innerExists] using hTargetCase
  exact fs_zfc_support_raw_exists_target_eq_source
    outerId innerExists sourceValue targetValue
    hSourceOuterFresh hTargetOuterFresh
    hContextOuterFresh hInnerExists hOuterCase hInnerTarget

theorem fs_zfc_support_raw_canonical_binder_fixed_case_unique
    {Γ : Context signature}
    {sourceToken targetToken : Nat}
    (relation :
      CanonicalBinderShiftToken sourceToken targetToken)
    (sourceValue targetValue : SetTerm)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hCase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_shift_fixed_token_condition
            sourceValue ∧ₘ
          (targetValue ≐ₘ sourceValue)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken) := by
  have hTargetSource :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ sourceValue :=
    FirstOrder.Derives.conjElimRight hCase
  cases relation with
  | logical symbol =>
      exact Metatheory.Derives.equality_trans
        hTargetSource hSourceEquality
  | membership =>
      exact Metatheory.Derives.equality_trans
        hTargetSource hSourceEquality
  | free id =>
      exact Metatheory.Derives.equality_trans
        hTargetSource hSourceEquality
  | bound depth =>
      exact FirstOrder.Derives.falsumElim
        (φ := targetValue ≐ₘ
          numₘ(Numbered.variable_token
            (bound_name (depth + 1))))
        (fs_zfc_support_raw_bound_token_fixed_falsum
          depth sourceValue hSourceValue hSourceEquality
          (FirstOrder.Derives.conjElimLeft hCase))
  | constant index =>
      exact Metatheory.Derives.equality_trans
        hTargetSource hSourceEquality
  | function arity index =>
      exact Metatheory.Derives.equality_trans
        hTargetSource hSourceEquality
  | predicate arity index =>
      exact Metatheory.Derives.equality_trans
        hTargetSource hSourceEquality

theorem fs_zfc_support_raw_canonical_binder_free_case_unique
    {Γ : Context signature}
    {sourceToken targetToken : Nat}
    (relation :
      CanonicalBinderShiftToken sourceToken targetToken)
    (sourceValue targetValue : SetTerm)
    (freeId : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hSourceFresh :
      (SetSort.set, freeId) ∉
        Term.freeSupport sourceValue)
    (hTargetFresh :
      (SetSort.set, freeId) ∉
        Term.freeSupport targetValue)
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
                  (numₘ(2) *ₘ x#freeId))) ∧ₘ
            (targetValue ≐ₘ sourceValue))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken) := by
  let witness : SetTerm := x#freeId
  let body : SetFormula :=
    ((((witness ∈ₘ ωₘ) ∧ₘ
          (witness ∈ₘ Sₘ(sourceValue))) ∧ₘ
        (sourceValue ≐ₘ
          variable_symbol_number_term
            (numₘ(2) *ₘ witness))) ∧ₘ
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
  have hCase' :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, freeId], body := by
    simpa [body, witness] using hCase
  have hTargetCase :
      body :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ sourceValue := by
    exact FirstOrder.Derives.conjElimRight
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := body :: Γ)
        (φ := body)
        (by simp))
  have hDirect :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ sourceValue :=
    fs_zfc_support_raw_exists_target_eq_source
      freeId body sourceValue targetValue
      hSourceFresh hTargetFresh hContextFresh hBody
      hCase' hTargetCase
  cases relation with
  | logical symbol =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | membership =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | free id =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | bound depth =>
      exact FirstOrder.Derives.falsumElim
        (φ := targetValue ≐ₘ
          numₘ(Numbered.variable_token
            (bound_name (depth + 1))))
        (fs_zfc_support_raw_bound_token_free_case_falsum
          depth sourceValue targetValue freeId
          hSourceValue
          hTargetValue hSourceEquality hContextFresh hCase)
  | constant index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | function arity index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | predicate arity index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality

theorem fs_zfc_support_raw_canonical_binder_constant_case_unique
    {Γ : Context signature}
    {sourceToken targetToken : Nat}
    (relation :
      CanonicalBinderShiftToken sourceToken targetToken)
    (sourceValue targetValue : SetTerm)
    (constantId : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hSourceFresh :
      (SetSort.set, constantId) ∉
        Term.freeSupport sourceValue)
    (hTargetFresh :
      (SetSort.set, constantId) ∉
        Term.freeSupport targetValue)
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
      targetValue ≐ₘ numₘ(targetToken) := by
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
  have hCase' :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, constantId], body := by
    simpa [body, witness] using hCase
  have hTargetCase :
      body :: Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ sourceValue :=
    FirstOrder.Derives.conjElimRight
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := body :: Γ)
        (φ := body)
        (by simp))
  have hDirect :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ sourceValue :=
    fs_zfc_support_raw_exists_target_eq_source
      constantId body sourceValue targetValue
      hSourceFresh hTargetFresh hContextFresh hBody
      hCase' hTargetCase
  cases relation with
  | logical symbol =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | membership =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | free id =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | bound depth =>
      exact FirstOrder.Derives.falsumElim
        (φ := targetValue ≐ₘ
          numₘ(Numbered.variable_token
            (bound_name (depth + 1))))
        (fs_zfc_support_raw_bound_token_constant_case_falsum
          depth sourceValue targetValue constantId
          hSourceValue hTargetValue hSourceEquality
          hContextFresh hCase)
  | constant index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | function arity index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | predicate arity index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality

theorem fs_zfc_support_raw_canonical_binder_function_case_unique
    {Γ : Context signature}
    {sourceToken targetToken : Nat}
    (relation :
      CanonicalBinderShiftToken sourceToken targetToken)
    (sourceValue targetValue : SetTerm)
    (arityId indexId : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hSourceArityFresh :
      (SetSort.set, arityId) ∉
        Term.freeSupport sourceValue)
    (hTargetArityFresh :
      (SetSort.set, arityId) ∉
        Term.freeSupport targetValue)
    (hSourceIndexFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport sourceValue)
    (hTargetIndexFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport targetValue)
    (hContextArityFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, arityId) ∉
          Formula.freeSupport formula)
    (hContextIndexFresh :
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
      targetValue ≐ₘ numₘ(targetToken) := by
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
          (membership_formula_admissible
            hArity omega_term_admissible)
          (membership_formula_admissible
            hIndex omega_term_admissible))
        (Formula.Admissible.equal hSourceValue
          (coded_function_symbol_number_term_admissible
            arity index hArity hIndex)))
      (Formula.Admissible.equal hTargetValue hSourceValue)
  have hCase' :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, arityId],
          ∃ₘ[SetSort.set, indexId], body := by
    simpa [body, arity, index] using hCase
  have hTargetCase :
      body :: innerExists :: Γ
        ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ sourceValue :=
    FirstOrder.Derives.conjElimRight
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := body :: innerExists :: Γ)
        (φ := body)
        (by simp))
  have hDirect :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ sourceValue :=
    fs_zfc_support_raw_exists₂_target_eq_source
      arityId indexId body sourceValue targetValue
      hSourceArityFresh hTargetArityFresh
      hSourceIndexFresh hTargetIndexFresh
      hContextArityFresh hContextIndexFresh
      hBody hCase' (by
        simpa [innerExists] using hTargetCase)
  cases relation with
  | logical symbol =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | membership =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | free id =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | bound depth =>
      exact FirstOrder.Derives.falsumElim
        (φ := targetValue ≐ₘ
          numₘ(Numbered.variable_token
            (bound_name (depth + 1))))
        (fs_zfc_support_raw_bound_token_function_case_falsum
          depth sourceValue targetValue arityId indexId
          hSourceValue hTargetValue hSourceEquality
          hContextArityFresh hContextIndexFresh hCase)
  | constant index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | function arity index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | predicate arity index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality

theorem fs_zfc_support_raw_canonical_binder_predicate_case_unique
    {Γ : Context signature}
    {sourceToken targetToken : Nat}
    (relation :
      CanonicalBinderShiftToken sourceToken targetToken)
    (sourceValue targetValue : SetTerm)
    (arityId indexId : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hSourceArityFresh :
      (SetSort.set, arityId) ∉
        Term.freeSupport sourceValue)
    (hTargetArityFresh :
      (SetSort.set, arityId) ∉
        Term.freeSupport targetValue)
    (hSourceIndexFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport sourceValue)
    (hTargetIndexFresh :
      (SetSort.set, indexId) ∉
        Term.freeSupport targetValue)
    (hContextArityFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, arityId) ∉
          Formula.freeSupport formula)
    (hContextIndexFresh :
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
      targetValue ≐ₘ numₘ(targetToken) := by
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
          (membership_formula_admissible
            hArity omega_term_admissible)
          (membership_formula_admissible
            hIndex omega_term_admissible))
        (Formula.Admissible.equal hSourceValue
          (coded_predicate_symbol_number_term_admissible
            arity index hArity hIndex)))
      (Formula.Admissible.equal hTargetValue hSourceValue)
  have hCase' :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, arityId],
          ∃ₘ[SetSort.set, indexId], body := by
    simpa [body, arity, index] using hCase
  have hTargetCase :
      body :: innerExists :: Γ
        ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ sourceValue :=
    FirstOrder.Derives.conjElimRight
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := body :: innerExists :: Γ)
        (φ := body)
        (by simp))
  have hDirect :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ sourceValue :=
    fs_zfc_support_raw_exists₂_target_eq_source
      arityId indexId body sourceValue targetValue
      hSourceArityFresh hTargetArityFresh
      hSourceIndexFresh hTargetIndexFresh
      hContextArityFresh hContextIndexFresh
      hBody hCase' (by
        simpa [innerExists] using hTargetCase)
  cases relation with
  | logical symbol =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | membership =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | free id =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | bound depth =>
      exact FirstOrder.Derives.falsumElim
        (φ := targetValue ≐ₘ
          numₘ(Numbered.variable_token
            (bound_name (depth + 1))))
        (fs_zfc_support_raw_bound_token_predicate_case_falsum
          depth sourceValue targetValue arityId indexId
          hSourceValue hTargetValue hSourceEquality
          hContextArityFresh hContextIndexFresh hCase)
  | constant index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | function arity index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality
  | predicate arity index =>
      exact Metatheory.Derives.equality_trans hDirect
        hSourceEquality

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
