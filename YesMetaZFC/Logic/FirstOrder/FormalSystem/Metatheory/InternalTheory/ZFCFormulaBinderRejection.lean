import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCFormulaBinderReplay

/-!
# ZFC 中的公式 binder 有界拒绝

本模块在一个具体失败位置实例化对象层 binder 条件。后继缺失由标准序列定义域
拒绝，变量解码失败由有界变量 token 反向定理拒绝。
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

/-- 对象 binder 条件在一个具体全称位置给出后继域成员和变量 token 条件。 -/
private theorem
    fs_zfc_support_raw_standard_token_sequence_binder_consequent_at
    (tokens : List Nat)
    (index : Nat)
    (hUniversal :
      tokens[index]? =
        some (Numbered.logical_token .universal)) :
    [fs_formula_binder_condition
        (standard_token_sequence tokens)]
      ⊢ₘ[fs_zfc_support_raw_theory]
        (Sₘ(numₘ(index)) ∈ₘ
            domₘ(standard_token_sequence tokens)) ∧ₘ
          fs_variable_token_condition
            (standard_token_sequence tokens ·ₘ
              Sₘ(numₘ(index))) := by
  let sequence : SetTerm :=
    standard_token_sequence tokens
  let condition : SetFormula :=
    fs_formula_binder_condition sequence
  let Γ : Context signature := [condition]
  let tokenIndexId : FreeVarId := 700
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      standard_token_sequence_admissible tokens
  have hConditionAdmissible :
      Formula.Admissible condition := by
    simpa [condition] using
      fs_formula_binder_condition_admissible
        sequence hSequence
  have hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hConditionAdmissible)
  have hNamedEquality :
      fs_formula_binder_condition_with_id
          sequence tokenIndexId =
        condition := by
    simpa [condition] using
      fs_formula_binder_condition_with_id_eq
        sequence tokenIndexId hSequence (by
          rw [show
            Term.freeSupport sequence = [] by
              simp [sequence]]
          exact List.not_mem_nil)
  have hNamed :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_formula_binder_condition_with_id
          sequence tokenIndexId := by
    rw [hNamedEquality]
    exact hCondition
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hNamed
  rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    at hAtRaw
  have hSequenceFixed :
      Term.substituteFree SetSort.set tokenIndexId
          (numₘ(index)) sequence =
        sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set tokenIndexId
      (numₘ(index)) sequence (by
        rw [show
          Term.freeSupport sequence = [] by
            simp [sequence]]
        exact List.not_mem_nil)
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set tokenIndexId
          (numₘ(index)) (numₘ(number)) =
        numₘ(number) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set tokenIndexId
      (numₘ(index)) (numₘ(number)) (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (numₘ(index) ∈ₘ domₘ(sequence)) ⟶ₘ
          (((sequence ·ₘ numₘ(index)) ≐ₘ
              numₘ(Numbered.logical_token
                .universal)) ⟶ₘ
            ((Sₘ(numₘ(index)) ∈ₘ
                domₘ(sequence)) ∧ₘ
              fs_variable_token_condition
                (sequence ·ₘ Sₘ(numₘ(index))))) := by
    simpa [fs_formula_binder_condition_with_id,
      fs_formula_binder_condition_lifted,
      fs_variable_token_condition,
      Formula.substituteFree, Term.substituteFree,
      set_variable, tokenIndexId,
      hSequenceFixed, hNumeralFixed] using hAtRaw
  have hIndex :
      index < tokens.length :=
    (List.getElem?_eq_some_iff.mp hUniversal).1
  have hDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ
          numₘ(tokens.length)) := by
    simpa [sequence] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_domain_eq_length
          tokens)
  have hIndexMember :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(index) ∈ₘ
          numₘ(tokens.length)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_mem_of_lt
        index tokens.length hIndex)
  have hIndexDomain :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(index) ∈ₘ domₘ(sequence)) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(sequence))
        (numₘ(tokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible
          tokens.length)
        hDomain)
      hIndexMember
  have hCurrent :
      Derives fs_zfc_support_raw_theory [] (
        (sequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(Numbered.logical_token
            .universal)) := by
    simpa [sequence] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_apply_getElem?
          tokens hUniversal)
  have hInner :=
    FirstOrder.Derives.impElim hAt
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ)
        (by simp [Γ])
        hIndexDomain)
  have hResult :=
    FirstOrder.Derives.impElim hInner
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ)
        (by simp [Γ])
        hCurrent)
  simpa [Γ, condition, sequence] using hResult

/-- 末位裸全称 token 与标准序列定义域矛盾。 -/
theorem
    fs_zfc_support_raw_standard_token_sequence_binder_neg_of_successor_absent
    (tokens : List Nat)
    (index : Nat)
    (hUniversal :
      tokens[index]? =
        some (Numbered.logical_token .universal))
    (hNext :
      tokens[index + 1]? = none) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_formula_binder_condition
        (standard_token_sequence tokens)) := by
  let sequence : SetTerm :=
    standard_token_sequence tokens
  let condition : SetFormula :=
    fs_formula_binder_condition sequence
  let Γ : Context signature := [condition]
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      standard_token_sequence_admissible tokens
  have hConditionAdmissible :
      Formula.Admissible condition := by
    simpa [condition] using
      fs_formula_binder_condition_admissible
        sequence hSequence
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hConditionAdmissible)
  have hConsequence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (Sₘ(numₘ(index)) ∈ₘ domₘ(sequence)) ∧ₘ
          fs_variable_token_condition
            (sequence ·ₘ Sₘ(numₘ(index))) := by
    simpa [Γ, condition, sequence] using
      fs_zfc_support_raw_standard_token_sequence_binder_consequent_at
        tokens index hUniversal
  have hNextDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Sₘ(numₘ(index)) ∈ₘ domₘ(sequence) :=
    FirstOrder.Derives.conjElimLeft hConsequence
  have hNotLt :
      ¬ index + 1 < tokens.length := by
    intro hIndex
    have hSome :
        tokens[index + 1]? =
          some tokens[index + 1] :=
      List.getElem?_eq_getElem hIndex
    rw [hNext] at hSome
    cases hSome
  have hDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ
          numₘ(tokens.length)) := by
    simpa [sequence] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_domain_eq_length
          tokens)
  have hNextNumeralDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(index + 1) ∈ₘ domₘ(sequence) := by
    simpa [finite_numeral_term,
      successor_term] using hNextDomain
  have hNextNumeralMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(index + 1) ∈ₘ
          numₘ(tokens.length) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        (numₘ(index + 1))
        (domₘ(sequence))
        (numₘ(tokens.length))
        (finite_numeral_term_admissible
          (index + 1))
        (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible
          tokens.length)
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ)
          (by simp [Γ])
          hDomain))
      hNextNumeralDomain
  have hNotMember :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (numₘ(index + 1) ∈ₘ
          numₘ(tokens.length))) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_not_mem_of_not_lt
        (index + 1) tokens.length hNotLt)
  exact FirstOrder.Derives.negElim
    hNextNumeralMember
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ)
      (by simp [Γ])
      hNotMember)

/-- 全称后继 token 无法有界解码时，binder 条件被对象层拒绝。 -/
theorem
    fs_zfc_support_raw_standard_token_sequence_binder_neg_of_variable_decode
    (tokens : List Nat)
    (index token : Nat)
    (hUniversal :
      tokens[index]? =
        some (Numbered.logical_token .universal))
    (hNext :
      tokens[index + 1]? = some token)
    (hDecode :
      fs_variable_name_decode token = none) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_formula_binder_condition
        (standard_token_sequence tokens)) := by
  let sequence : SetTerm :=
    standard_token_sequence tokens
  let condition : SetFormula :=
    fs_formula_binder_condition sequence
  let Γ : Context signature := [condition]
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      standard_token_sequence_admissible tokens
  have hConditionAdmissible :
      Formula.Admissible condition := by
    simpa [condition] using
      fs_formula_binder_condition_admissible
        sequence hSequence
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hConditionAdmissible)
  have hConsequence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (Sₘ(numₘ(index)) ∈ₘ domₘ(sequence)) ∧ₘ
          fs_variable_token_condition
            (sequence ·ₘ Sₘ(numₘ(index))) := by
    simpa [Γ, condition, sequence] using
      fs_zfc_support_raw_standard_token_sequence_binder_consequent_at
        tokens index hUniversal
  have hVariableAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_variable_token_condition
          (sequence ·ₘ Sₘ(numₘ(index))) :=
    FirstOrder.Derives.conjElimRight hConsequence
  have hNextValue :
      Derives fs_zfc_support_raw_theory [] (
        (sequence ·ₘ Sₘ(numₘ(index))) ≐ₘ
          numₘ(token)) := by
    simpa [sequence, finite_numeral_term,
      successor_term] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_apply_getElem?
          tokens hNext)
  have hVariableNumeral :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_variable_token_condition
          (numₘ(token)) :=
    FirstOrder.Derives.iffElimRight
      (fs_variable_token_condition_iff_of_equality
        (sequence ·ₘ Sₘ(numₘ(index)))
        (numₘ(token))
        (function_application_term_admissible
          sequence (Sₘ(numₘ(index)))
          hSequence
          (successor_term_admissible
            (numₘ(index))
            (finite_numeral_term_admissible index)))
        (finite_numeral_term_admissible token)
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ)
          (by simp [Γ])
          hNextValue))
      hVariableAt
  have hVariableNot :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ fs_variable_token_condition
          (numₘ(token))) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (gq_fs_variable_token_condition_not
        token hDecode)
  exact FirstOrder.Derives.negElim
    hVariableNumeral
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ)
      (by simp [Γ])
      hVariableNot)

/-- 任意构造性 binder 失败都否定对象层 binder 条件。 -/
theorem
    fs_zfc_support_raw_standard_token_sequence_binder_neg_of_failure
    (tokens : List Nat)
    (hFailure :
      FSFormulaBinderTokenFailure tokens) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_formula_binder_condition
        (standard_token_sequence tokens)) := by
  cases hFailure with
  | successor_absent index hUniversal hNext =>
      exact
        fs_zfc_support_raw_standard_token_sequence_binder_neg_of_successor_absent
          tokens index hUniversal hNext
  | variable_decode index token
      hUniversal hNext hDecode =>
      exact
        fs_zfc_support_raw_standard_token_sequence_binder_neg_of_variable_decode
          tokens index token
          hUniversal hNext hDecode

/-- binder 布尔检查失败时，完整 replay 词法条件被对象层否定。 -/
theorem
    fs_zfc_support_raw_standard_token_sequence_replay_neg_of_binder_check
    (tokens : List Nat)
    (hCheck :
      fs_formula_binder_tokens_check tokens = false) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_formula_replay_condition
        (standard_token_sequence tokens)) := by
  have hBinderNot :=
    fs_zfc_support_raw_standard_token_sequence_binder_neg_of_failure
      tokens
      (fs_formula_binder_tokens_failure_of_false
        tokens hCheck)
  have hReplayAdmissible :
      Formula.Admissible
        (fs_formula_replay_condition
          (standard_token_sequence tokens)) :=
    fs_formula_replay_condition_admissible
      (standard_token_sequence tokens)
      (standard_token_sequence_admissible tokens)
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hReplayAdmissible)
  have hReplay :
      [fs_formula_replay_condition
          (standard_token_sequence tokens)]
        ⊢ₘ[fs_zfc_support_raw_theory]
          fs_formula_replay_condition
            (standard_token_sequence tokens) :=
    FirstOrder.Derives.assumption
      (by simp)
      (Formula.check_admissible_complete
        hReplayAdmissible)
  have hBinder :
      [fs_formula_replay_condition
          (standard_token_sequence tokens)]
        ⊢ₘ[fs_zfc_support_raw_theory]
          fs_formula_binder_condition
            (standard_token_sequence tokens) := by
    simpa [fs_formula_replay_condition] using
      FirstOrder.Derives.conjElimRight hReplay
  exact FirstOrder.Derives.negElim
    hBinder
    (FirstOrder.Derives.context_weaken_cons
      hBinderNot)

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
