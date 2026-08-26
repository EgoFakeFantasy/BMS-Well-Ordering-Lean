import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCFormulaSignatureReplay

/-!
# ZFC 中标准公式行的有限签名拒绝

本模块把一个具体坏 token 的闭否定提升到整条标准 token 序列。证明在坏位置
实例化 `fs_formula_signature_condition`，用标准序列逐点等式把对象值运输回
对应 numeral，然后调用通用 quotation 反向拒绝。
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

/--
标准 token 序列在一个宿主未分类位置上违反对象层有限签名全称条件。
-/
theorem
    fs_zfc_support_raw_standard_token_sequence_signature_neg_of_token
    (tokens : List Nat)
    (index : Nat)
    (hIndex : index < tokens.length)
    (hToken : ¬ FSFormulaToken tokens[index]) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_formula_signature_condition
        (standard_token_sequence tokens)) := by
  let sequence : SetTerm :=
    standard_token_sequence tokens
  let signatureCondition : SetFormula :=
    fs_formula_signature_condition sequence
  let Γ : Context signature := [signatureCondition]
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      standard_token_sequence_admissible tokens
  have hSignatureAdmissible :
      Formula.Admissible signatureCondition := by
    simpa [signatureCondition] using
      fs_formula_signature_condition_admissible
        sequence hSequence
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hSignatureAdmissible)
  have hSignature :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        signatureCondition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hSignatureAdmissible)
  have hSequenceOpen (depth : Nat)
      (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement
          sequence =
        sequence :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement sequence
      hSequence.2
  have hZeroOpen (depth : Nat)
      (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement
          (numₘ(0)) =
        numₘ(0) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(0))
      (finite_numeral_term_admissible 0).2
  have hThreeOpen (depth : Nat)
      (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement
          (numₘ(3)) =
        numₘ(3) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(3))
      (finite_numeral_term_admissible 3).2
  have hSymbolsOpen (depth : Nat)
      (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement
          fs_nonlogical_symbol_code_set_term =
        fs_nonlogical_symbol_code_set_term :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement
      fs_nonlogical_symbol_code_set_term
      fs_nonlogical_symbol_code_set_term_admissible.2
  have hAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ((numₘ(index) ∈ₘ domₘ(sequence)) ⟶ₘ
          fs_formula_token_condition
            (sequence ·ₘ numₘ(index))) := by
    have hRaw :=
      FirstOrder.Derives.forall_elim
        (term := numₘ(index)) hSignature
    simpa [signatureCondition,
      fs_formula_signature_condition,
      fs_formula_token_condition,
      fs_formula_token_condition_lifted,
      fs_variable_token_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hSequenceOpen,
      hZeroOpen, hThreeOpen,
      hSymbolsOpen] using hRaw
  have hDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ
          numₘ(tokens.length)) := by
    simpa [sequence] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_domain_eq_length
          tokens)
  have hNumeralMember :
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
      hNumeralMember
  have hTokenAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_formula_token_condition
          (sequence ·ₘ numₘ(index)) :=
    FirstOrder.Derives.impElim hAt
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ)
        (by simp [Γ])
        hIndexDomain)
  have hGet :
      tokens[index]? = some tokens[index] :=
    List.getElem?_eq_getElem hIndex
  have hValue :
      Derives fs_zfc_support_raw_theory [] (
        (sequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(tokens[index])) := by
    simpa [sequence] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_apply_getElem?
          tokens hGet)
  have hTokenIff :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (fs_formula_token_condition
            (sequence ·ₘ numₘ(index))) ↔ₘ
          fs_formula_token_condition
            (numₘ(tokens[index])) :=
    fs_formula_token_condition_iff_of_equality
      (sequence ·ₘ numₘ(index))
      (numₘ(tokens[index]))
      (function_application_term_admissible
        sequence (numₘ(index))
        hSequence
        (finite_numeral_term_admissible index))
      (finite_numeral_term_admissible
        tokens[index])
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ)
        (by simp [Γ])
        hValue)
  have hConcrete :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_formula_token_condition
          (numₘ(tokens[index])) :=
    FirstOrder.Derives.iffElimRight
      hTokenIff hTokenAt
  have hConcreteNot :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ fs_formula_token_condition
          (numₘ(tokens[index]))) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (gq_fs_formula_token_condition_not hToken)
  exact FirstOrder.Derives.negElim
    hConcrete
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ)
      (by simp [Γ])
      hConcreteNot)

/--
标准公式行含有一个宿主未分类 token 时，完整有限签名公式条件被对象层否定。
-/
theorem
    fs_zfc_support_raw_standard_token_sequence_formula_condition_neg_of_token
    (tokens : List Nat)
    (index : Nat)
    (hIndex : index < tokens.length)
    (hToken : ¬ FSFormulaToken tokens[index]) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_formula_code_condition
        (standard_token_sequence tokens)) := by
  have hSignatureNot :=
    fs_zfc_support_raw_standard_token_sequence_signature_neg_of_token
      tokens index hIndex hToken
  have hConditionAdmissible :
      Formula.Admissible
        (fs_formula_code_condition
          (standard_token_sequence tokens)) :=
    fs_formula_code_condition_admissible
      (standard_token_sequence tokens)
      (standard_token_sequence_admissible tokens)
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hConditionAdmissible)
  have hCondition :
      [fs_formula_code_condition
          (standard_token_sequence tokens)]
        ⊢ₘ[fs_zfc_support_raw_theory]
          fs_formula_code_condition
            (standard_token_sequence tokens) :=
    FirstOrder.Derives.assumption
      (by simp)
      (Formula.check_admissible_complete
        hConditionAdmissible)
  have hSignature :
      [fs_formula_code_condition
          (standard_token_sequence tokens)]
        ⊢ₘ[fs_zfc_support_raw_theory]
          fs_formula_signature_condition
            (standard_token_sequence tokens) := by
    simpa [fs_formula_code_condition] using
      FirstOrder.Derives.conjElimRight hCondition
  exact FirstOrder.Derives.negElim
    hSignature
    (FirstOrder.Derives.context_weaken_cons
      hSignatureNot)

/--
标准公式行的第零、第一位均不以左括号开头时，ZFC raw 支持理论拒绝其完整
公式条件。证明只是 quotation 结构拒绝的理论弱化。
-/
theorem
    fs_zfc_support_raw_standard_token_sequence_formula_condition_neg_of_no_left_opening
    (tokens : List Nat)
    (hZero :
      tokens[0]? ≠
        some (GodelQuotation.Numbered.logical_token
          .leftParenthesis))
    (hOne :
      tokens[1]? ≠
        some (GodelQuotation.Numbered.logical_token
          .leftParenthesis)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_formula_code_condition
        (standard_token_sequence tokens)) :=
  fs_zfc_support_raw_derives_of_godel_quotation <|
    gq_fs_formula_code_condition_not_of_no_left_opening
      tokens hZero hOne

/--
标准公式行缺少第一号位置时，ZFC raw 支持理论拒绝其完整公式条件。
-/
theorem
    fs_zfc_support_raw_standard_token_sequence_formula_condition_neg_of_one_absent
    (tokens : List Nat)
    (hOne : tokens[1]? = none) :
    ⊢ₘ[fs_zfc_support_raw_theory]
      ¬ₘ fs_formula_code_condition
        (standard_token_sequence tokens) :=
  fs_zfc_support_raw_derives_of_godel_quotation <|
    gq_fs_formula_code_condition_not_of_one_absent
      tokens hOne

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
