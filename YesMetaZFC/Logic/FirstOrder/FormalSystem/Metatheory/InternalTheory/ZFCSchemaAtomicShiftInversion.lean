import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaConditionInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.BracketedThreePartInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.HeadedApplicationInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FlattenInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.VariableSymbolInversion

/-!
# ZFC 规范原子移位反演

本模块只处理规范公式移位证书的原子骨架。它先从变量同步条件恢复项码边界，
再调用 quotation 的有限括号三段反演；不引入模型、标准性或对象层之外的解释。
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

/-- 规范变量同步条件一次恢复左变量码的项码与长度一序列边界。 -/
theorem fs_zfc_support_raw_canonical_shifted_variable_left_boundary
    {Γ : Context signature}
    (cutoff entryDepth : Nat)
    (leftVariable rightVariable : SetTerm)
    (variableDepthId : FreeVarId)
    (hLeftVariable : Term.Admissible leftVariable SetSort.set)
    (hRightVariable : Term.Admissible rightVariable SetSort.set)
    (hDepthFreshLeft :
      (SetSort.set, variableDepthId) ∉
        Term.freeSupport leftVariable)
    (hDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, variableDepthId) ∉
          Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_variable_code_condition_with_id
          (numₘ(cutoff)) (numₘ(entryDepth))
          leftVariable rightVariable variableDepthId) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (term_codeₘ(leftVariable) ∧ₘ
        (finite_sequence_condition leftVariable ∧ₘ
          (domₘ(leftVariable) ≐ₘ numₘ(1)))) := by
  let targetBody : SetFormula :=
    canonical_shifted_variable_target_condition
      (numₘ(cutoff)) (x#variableDepthId)
      rightVariable (x#(variableDepthId + 1))
  let outerBody : SetFormula :=
    (((x#variableDepthId ∈ₘ numₘ(entryDepth)) ∧ₘ
        (leftVariable ≐ₘ
          canonical_binder_variable_code_term
            (x#variableDepthId))) ∧ₘ
      (∃ₘ[SetSort.set, variableDepthId + 1], targetBody))
  have hTargetBody : Formula.Admissible targetBody := by
    simpa [targetBody] using
      canonical_shifted_variable_target_condition_admissible
        (numₘ(cutoff)) (x#variableDepthId)
        rightVariable (x#(variableDepthId + 1))
        (finite_numeral_term_admissible cutoff)
        (set_variable_admissible variableDepthId)
        hRightVariable
        (set_variable_admissible (variableDepthId + 1))
  have hExistsAdmissible :
      Formula.Admissible
        (canonical_shifted_variable_code_condition_with_id
          (numₘ(cutoff)) (numₘ(entryDepth))
          leftVariable rightVariable variableDepthId) :=
    canonical_shifted_variable_code_condition_with_id_admissible
      (numₘ(cutoff)) (numₘ(entryDepth))
      leftVariable rightVariable variableDepthId
      (finite_numeral_term_admissible cutoff)
      (finite_numeral_term_admissible entryDepth)
      hLeftVariable hRightVariable
  have hOuterBody : Formula.Admissible outerBody := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := (x#variableDepthId : SetTerm))
        SetSort.set hExistsAdmissible
        (set_variable_admissible variableDepthId)
    simpa [outerBody, targetBody,
      canonical_shifted_variable_code_condition_with_id,
      Formula.openAt_closeFreeAt] using hOpened
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, variableDepthId], outerBody := by
    simpa [outerBody, targetBody,
      canonical_shifted_variable_code_condition_with_id] using
      hCondition
  have hConclusion :
      Formula.Admissible
        (term_codeₘ(leftVariable) ∧ₘ
          (finite_sequence_condition leftVariable ∧ₘ
            (domₘ(leftVariable) ≐ₘ numₘ(1)))) :=
    Formula.Admissible.conj
      (is_term_code_formula_admissible hLeftVariable)
      (Formula.Admissible.conj
        (finite_sequence_condition_admissible
          leftVariable hLeftVariable)
        (Formula.Admissible.equal
          (domain_term_admissible
            leftVariable hLeftVariable)
          (finite_numeral_term_admissible 1)))
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := variableDepthId)
    (body := outerBody)
    (conclusion :=
      term_codeₘ(leftVariable) ∧ₘ
        (finite_sequence_condition leftVariable ∧ₘ
          (domₘ(leftVariable) ≐ₘ numₘ(1))))
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hDepthFreshContext
  · have hFiniteFresh :
        (SetSort.set, variableDepthId) ∉
          Formula.freeSupport
            (finite_sequence_condition leftVariable) := by
      simp only [finite_sequence_condition,
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList, List.append_nil]
      intro hMember
      rcases List.mem_append.mp hMember with
        hLeft | hRight
      · exact hDepthFreshLeft hLeft
      · exact hDepthFreshLeft hRight
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    intro hMember
    rcases List.mem_append.mp hMember with
      hLeft | hRest
    · exact hDepthFreshLeft hLeft
    · rcases List.mem_append.mp hRest with
        hFinite | hRest
      · exact hFiniteFresh hFinite
      · rcases List.mem_append.mp hRest with
          hLeft | hNumeral
        · exact hDepthFreshLeft hLeft
        · rw [finite_numeral_term_freeSupport] at hNumeral
          exact List.not_mem_nil hNumeral
  · exact hExists
  · let Δ : Context signature := outerBody :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory]
      (term_codeₘ(leftVariable) ∧ₘ
        (finite_sequence_condition leftVariable ∧ₘ
          (domₘ(leftVariable) ≐ₘ numₘ(1))))
    have hBody :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] outerBody :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hSourceData :=
      FirstOrder.Derives.conjElimLeft hBody
    have hSourceMember :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#variableDepthId) ∈ₘ numₘ(entryDepth) := by
      simpa [outerBody] using
        FirstOrder.Derives.conjElimLeft hSourceData
    have hLeftCode :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          leftVariable ≐ₘ
            canonical_binder_variable_code_term
              (x#variableDepthId) := by
      simpa [outerBody] using
        FirstOrder.Derives.conjElimRight hSourceData
    apply
      fs_zfc_support_raw_finite_numeral_member_elim_context
        entryDepth (x#variableDepthId)
        (term_codeₘ(leftVariable) ∧ₘ
          (finite_sequence_condition leftVariable ∧ₘ
            (domₘ(leftVariable) ≐ₘ numₘ(1))))
        (set_variable_admissible variableDepthId)
        hConclusion hSourceMember
    intro index hIndex
    let sourceEquality : SetFormula :=
      (x#variableDepthId) ≐ₘ numₘ(index)
    let Ε : Context signature := sourceEquality :: Δ
    change Ε ⊢ₘ[fs_zfc_support_raw_theory]
      (term_codeₘ(leftVariable) ∧ₘ
        (finite_sequence_condition leftVariable ∧ₘ
          (domₘ(leftVariable) ≐ₘ numₘ(1))))
    have hSourceEquality :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          (x#variableDepthId) ≐ₘ numₘ(index) := by
      simpa [Ε, sourceEquality] using
        (FirstOrder.Derives.assumption
          (T := fs_zfc_support_raw_theory)
          (Γ := Ε) (φ := sourceEquality) (by simp [Ε]))
    have hLeftCodeAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          leftVariable ≐ₘ
            canonical_binder_variable_code_term
              (x#variableDepthId) :=
      FirstOrder.Derives.context_weaken_cons hLeftCode
    have hDepthCode :=
      canonical_binder_variable_code_term_congr_of_equality
        (x#variableDepthId) (numₘ(index))
        (set_variable_admissible variableDepthId)
        (finite_numeral_term_admissible index)
        hSourceEquality
    have hKnownCode :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          leftVariable ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(index)) :=
      Metatheory.Derives.equality_trans
        hLeftCodeAt hDepthCode
    have hCanonicalMember :
        ⊢ₘ[GodelQuotation.godel_quotation_theory]
          canonical_binder_variable_code_term
            (numₘ(index)) ∈ₘ VarSymₘ :=
      canonical_binder_variable_code_numeral_mem index
    have hCanonicalMemberSet :
        ⊢ₘ[GodelQuotation.godel_quotation_theory]
          canonical_binder_variable_code_term
            (numₘ(index)) ∈ₘ TermCodeₘ :=
      gq_subset_member
        VarSymₘ TermCodeₘ
        (canonical_binder_variable_code_term (numₘ(index)))
        variable_symbol_set_term_admissible
        term_code_set_term_admissible
        (canonical_binder_variable_code_term_admissible
          (numₘ(index))
          (finite_numeral_term_admissible index))
        gq_variable_symbols_subset_term_codes
        hCanonicalMember
    have hCanonicalMemberSetAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_binder_variable_code_term
            (numₘ(index)) ∈ₘ TermCodeₘ :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Ε) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            hCanonicalMemberSet
    have hLeftMemberSet :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          leftVariable ∈ₘ TermCodeₘ :=
      FirstOrder.Derives.iffElimLeft
        (membership_left_iff_of_equality
          leftVariable
          (canonical_binder_variable_code_term (numₘ(index)))
          TermCodeₘ
          hLeftVariable
          (canonical_binder_variable_code_term_admissible
            (numₘ(index))
            (finite_numeral_term_admissible index))
          term_code_set_term_admissible
          hKnownCode)
        hCanonicalMemberSetAt
    have hDefinition :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          (term_codeₘ(leftVariable) ↔ₘ
            (leftVariable ∈ₘ TermCodeₘ)) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Ε) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            (gq_term_code_definition_instance
              leftVariable hLeftVariable)
    have hTermCode :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          term_codeₘ(leftVariable) :=
      FirstOrder.Derives.iffElimLeft
        hDefinition hLeftMemberSet
    have hCanonicalCode :
        Term.Admissible
          (canonical_binder_variable_code_term
            (numₘ(index))) SetSort.set :=
      canonical_binder_variable_code_term_admissible
        (numₘ(index))
        (finite_numeral_term_admissible index)
    have hCanonicalBoundary :
        ⊢ₘ[GodelQuotation.godel_quotation_theory]
          (finite_sequence_condition
              (canonical_binder_variable_code_term
                (numₘ(index))) ∧ₘ
            (domₘ(canonical_binder_variable_code_term
                (numₘ(index))) ≐ₘ numₘ(1))) := by
      simpa [canonical_binder_variable_code_term] using
        (gq_variable_code_finite_domain_one
          (Γ := [])
          (canonical_binder_name_term (numₘ(index)))
          (successor_term_admissible
            (numₘ(2) *ₘ numₘ(index))
            (natural_multiplication_term_admissible
              (numₘ(2)) (numₘ(index))
              (finite_numeral_term_admissible 2)
              (finite_numeral_term_admissible index)))
          (by
            intro term hTerm id hId
            rcases List.mem_singleton.mp hTerm with rfl
            have hClosed :
                Term.freeSupport
                    (variable_symbol_number_term
                      (canonical_binder_name_term
                        (numₘ(index)))) =
                  [] := by
              simp [Term.freeSupport,
                Term.freeSupportList,
                finite_numeral_term_freeSupport]
            rw [hClosed]
            exact List.not_mem_nil))
    have hCanonicalBoundaryAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          (finite_sequence_condition
              (canonical_binder_variable_code_term
                (numₘ(index))) ∧ₘ
            (domₘ(canonical_binder_variable_code_term
                (numₘ(index))) ≐ₘ numₘ(1))) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Ε) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            hCanonicalBoundary
    have hFinite :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          finite_sequence_condition leftVariable :=
      FirstOrder.Derives.iffElimLeft
        (finite_sequence_condition_iff_of_equality
          leftVariable
          (canonical_binder_variable_code_term
            (numₘ(index)))
          hLeftVariable hCanonicalCode hKnownCode)
        (FirstOrder.Derives.conjElimLeft
          hCanonicalBoundaryAt)
    have hDomain :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(leftVariable) ≐ₘ numₘ(1) :=
      Metatheory.Derives.equality_trans
        (domain_term_congr_of_equality
          leftVariable
          (canonical_binder_variable_code_term
            (numₘ(index)))
          hLeftVariable hCanonicalCode hKnownCode)
        (FirstOrder.Derives.conjElimRight
          hCanonicalBoundaryAt)
    exact FirstOrder.Derives.conjIntro
      hTermCode
      (FirstOrder.Derives.conjIntro
        hFinite hDomain)

/-! ## 规范 membership 原子的分量反演 -/

/--
已知规范 membership 整串等于一个括号三段构造，且左右分量均为长度一有限序列，
则两个分量分别等于源深度对应的规范 binder 变量码。
-/
theorem fs_zfc_support_raw_canonical_membership_parts_unique
    {Γ : Context signature}
    (leftDepth rightDepth : Nat)
    (leftFirst leftSecond : SetTerm)
    (hLeftFirst : Term.Admissible leftFirst SetSort.set)
    (hLeftSecond : Term.Admissible leftSecond SetSort.set)
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition leftFirst)
    (hFirstDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(leftFirst) ≐ₘ numₘ(1))
    (hSecondFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition leftSecond)
    (hSecondDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(leftSecond) ≐ₘ numₘ(1))
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .membership leftDepth rightDepth ≐ₘ
          membership_atomic_formula_code_term
            leftFirst leftSecond) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (leftFirst ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(leftDepth))) ∧ₘ
        (leftSecond ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(rightDepth))) := by
  let leftTokens : List Nat := [
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name leftDepth)]
  let rightTokens : List Nat := [
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name rightDepth)]
  let tokens : List Nat :=
    GodelQuotation.Numbered.membership_tokens
      leftTokens rightTokens
  have hCanonicalStandard :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .membership leftDepth rightDepth ≐ₘ
          standard_token_sequence tokens := by
    simpa [tokens, leftTokens, rightTokens,
      CanonicalProjectTrace.canonical_project_atom_code] using
      (membership_formula_string_eq_standard_token_sequence
        leftTokens rightTokens
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.bound_name leftDepth))
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.bound_name rightDepth))
        (by
          simpa [leftTokens] using
            GodelQuotation.named_variable_code_eq_standard_token_sequence
              (GodelQuotation.bound_name leftDepth))
        (by
          simpa [rightTokens] using
            GodelQuotation.named_variable_code_eq_standard_token_sequence
              (GodelQuotation.bound_name rightDepth)))
  have hCanonicalStandardAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .membership leftDepth rightDepth ≐ₘ
          standard_token_sequence tokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          hCanonicalStandard
  have hStandardSource :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          membership_atomic_formula_code_term
            leftFirst leftSecond :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        hCanonicalStandardAt)
      hSourceEquality
  have hMiddle :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        membership_symbol_code_term ≐ₘ
          standard_token_sequence
            [GodelQuotation.Numbered.membership_token] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          membership_symbol_code_eq_standard_token_sequence
  have hSlices :=
    gq_bracketed_three_part_parts_eq_standard_slices_of_theory
      (T := fs_zfc_support_raw_theory)
      (fun formula hFormula =>
        fs_zfc_support_raw_contains_godel_quotation
          hFormula)
      leftFirst membership_symbol_code_term leftSecond
      tokens GodelQuotation.Numbered.membership_token 1 1
      hFirstFinite hMiddle hSecondFinite
      hFirstDomain hSecondDomain hStandardSource
      (hFirstCheck :=
        Term.check_admissible_complete hLeftFirst)
      (hMiddleCheck :=
        Term.check_admissible_complete
          membership_symbol_code_term_admissible)
      (hLastCheck :=
        Term.check_admissible_complete hLeftSecond)
  have hFirstStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        leftFirst ≐ₘ
          standard_token_sequence leftTokens := by
    simpa [tokens, leftTokens, rightTokens,
      GodelQuotation.Numbered.membership_tokens] using
      FirstOrder.Derives.conjElimLeft hSlices
  have hSecondStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        leftSecond ≐ₘ
          standard_token_sequence rightTokens := by
    simpa [tokens, leftTokens, rightTokens,
      GodelQuotation.Numbered.membership_tokens] using
      FirstOrder.Derives.conjElimRight hSlices
  have hFirstCanonical :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(leftDepth)) ≐ₘ
          standard_token_sequence leftTokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <| by
          simpa [leftTokens] using
            canonical_binder_variable_code_numeral_eq_standard_token_sequence
              leftDepth
  have hSecondCanonical :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(rightDepth)) ≐ₘ
          standard_token_sequence rightTokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <| by
          simpa [rightTokens] using
            canonical_binder_variable_code_numeral_eq_standard_token_sequence
              rightDepth
  exact FirstOrder.Derives.conjIntro
    (Metatheory.Derives.equality_trans
      hFirstStandard
      (Metatheory.Derives.equality_symm hFirstCanonical))
    (Metatheory.Derives.equality_trans
      hSecondStandard
      (Metatheory.Derives.equality_symm hSecondCanonical))

/-! ## 规范 equality 原子的分量反演 -/

/--
在两个分量已经证明为项码时，等式公式码运算等于其括号化原始字符串。
该前提正是对象构造定义的合同。
-/
theorem fs_zfc_support_raw_equality_code_eq_raw_of_term_codes
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] term_codeₘ(left))
    (hRightCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] term_codeₘ(right)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      eq_codeₘ(left, right) ≐ₘ
        equality_atomic_formula_code_term left right := by
  let code : SetTerm := eq_codeₘ(left, right)
  have hCode : Term.Admissible code SetSort.set :=
    equality_formula_code_term_admissible
      left right hLeft hRight
  have hDefinition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        equality_formula_code_definition_instance
          left right code :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          gq_weaken_formula_constructor <|
            equality_formula_code_definition_instance_derives
              left right code hLeft hRight hCode
  have hContract :=
    FirstOrder.Derives.impElim hDefinition <|
      FirstOrder.Derives.conjIntro
        hLeftCode hRightCode
  have hReflexive :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ≐ₘ eq_codeₘ(left, right) := by
    simpa [code] using
      (FirstOrder.Derives.eq_refl_m
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ) (sort := SetSort.set) code)
  exact FirstOrder.Derives.iffElimRight
    (by
      simpa [code,
        equality_formula_code_definition_instance] using
        hContract)
    hReflexive

/--
已知规范 equality 码等于任意两个项码构成的等式码，则两个项码分别恢复为
源深度对应的规范 binder 变量码。
-/
theorem fs_zfc_support_raw_canonical_equality_parts_unique
    {Γ : Context signature}
    (leftDepth rightDepth : Nat)
    (leftFirst leftSecond : SetTerm)
    (hLeftFirst : Term.Admissible leftFirst SetSort.set)
    (hLeftSecond : Term.Admissible leftSecond SetSort.set)
    (hFirstTermCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        term_codeₘ(leftFirst))
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition leftFirst)
    (hFirstDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(leftFirst) ≐ₘ numₘ(1))
    (hSecondTermCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        term_codeₘ(leftSecond))
    (hSecondFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition leftSecond)
    (hSecondDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(leftSecond) ≐ₘ numₘ(1))
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .equality leftDepth rightDepth ≐ₘ
          eq_codeₘ(leftFirst, leftSecond)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (leftFirst ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(leftDepth))) ∧ₘ
        (leftSecond ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(rightDepth))) := by
  let leftTokens : List Nat := [
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name leftDepth)]
  let rightTokens : List Nat := [
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name rightDepth)]
  let tokens : List Nat :=
    GodelQuotation.Numbered.equality_tokens
      leftTokens rightTokens
  have hCanonicalStandard :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .equality leftDepth rightDepth ≐ₘ
          standard_token_sequence tokens := by
    simpa [tokens, leftTokens, rightTokens,
      CanonicalProjectTrace.canonical_project_atom_code] using
      (equality_formula_code_eq_standard_token_sequence
        leftTokens rightTokens
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.bound_name leftDepth))
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.bound_name rightDepth))
        (named_variable_code_is_term_code
          (GodelQuotation.bound_name leftDepth))
        (named_variable_code_is_term_code
          (GodelQuotation.bound_name rightDepth))
        (by
          simpa [leftTokens] using
            GodelQuotation.named_variable_code_eq_standard_token_sequence
              (GodelQuotation.bound_name leftDepth))
        (by
          simpa [rightTokens] using
            GodelQuotation.named_variable_code_eq_standard_token_sequence
              (GodelQuotation.bound_name rightDepth)))
  have hCanonicalStandardAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .equality leftDepth rightDepth ≐ₘ
          standard_token_sequence tokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          hCanonicalStandard
  have hSourceRaw :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .equality leftDepth rightDepth ≐ₘ
          equality_atomic_formula_code_term
            leftFirst leftSecond :=
    Metatheory.Derives.equality_trans
      hSourceEquality <|
        fs_zfc_support_raw_equality_code_eq_raw_of_term_codes
          leftFirst leftSecond hLeftFirst hLeftSecond
          hFirstTermCode hSecondTermCode
  have hStandardSource :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          equality_atomic_formula_code_term
            leftFirst leftSecond :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        hCanonicalStandardAt)
      hSourceRaw
  have hMiddle :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        equality_symbol_code_term ≐ₘ
          standard_token_sequence
            [GodelQuotation.Numbered.logical_token
              .equality] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          (logical_symbol_code_eq_standard_token_sequence
            .equality)
  have hSlices :=
    gq_bracketed_three_part_parts_eq_standard_slices_of_theory
      (T := fs_zfc_support_raw_theory)
      (fun formula hFormula =>
        fs_zfc_support_raw_contains_godel_quotation
          hFormula)
      leftFirst equality_symbol_code_term leftSecond
      tokens
      (GodelQuotation.Numbered.logical_token .equality)
      1 1
      hFirstFinite hMiddle hSecondFinite
      hFirstDomain hSecondDomain
      (by
        simpa [equality_atomic_formula_code_term] using
          hStandardSource)
      (hFirstCheck :=
        Term.check_admissible_complete hLeftFirst)
      (hMiddleCheck :=
        Term.check_admissible_complete
          (logical_symbol_code_term_admissible
            .equality))
      (hLastCheck :=
        Term.check_admissible_complete hLeftSecond)
  have hFirstStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        leftFirst ≐ₘ
          standard_token_sequence leftTokens := by
    simpa [tokens, leftTokens, rightTokens,
      GodelQuotation.Numbered.equality_tokens] using
      FirstOrder.Derives.conjElimLeft hSlices
  have hSecondStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        leftSecond ≐ₘ
          standard_token_sequence rightTokens := by
    simpa [tokens, leftTokens, rightTokens,
      GodelQuotation.Numbered.equality_tokens] using
      FirstOrder.Derives.conjElimRight hSlices
  have hFirstCanonical :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(leftDepth)) ≐ₘ
          standard_token_sequence leftTokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <| by
          simpa [leftTokens] using
            canonical_binder_variable_code_numeral_eq_standard_token_sequence
              leftDepth
  have hSecondCanonical :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(rightDepth)) ≐ₘ
          standard_token_sequence rightTokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <| by
          simpa [rightTokens] using
            canonical_binder_variable_code_numeral_eq_standard_token_sequence
              rightDepth
  exact FirstOrder.Derives.conjIntro
    (Metatheory.Derives.equality_trans
      hFirstStandard
      (Metatheory.Derives.equality_symm hFirstCanonical))
    (Metatheory.Derives.equality_trans
      hSecondStandard
      (Metatheory.Derives.equality_symm hSecondCanonical))

/-- 已展开的 equality 原子同步分支唯一决定目标规范原子码。 -/
theorem fs_zfc_support_raw_canonical_equality_shift_branch_unique
    {Γ : Context signature}
    (cutoff entryDepth leftDepth rightDepth : Nat)
    (rightCode : SetTerm)
    (leftFirst rightFirst leftSecond rightSecond : SetTerm)
    (firstDepthId secondDepthId : FreeVarId)
    (hLeftFirst : Term.Admissible leftFirst SetSort.set)
    (hRightFirst : Term.Admissible rightFirst SetSort.set)
    (hLeftSecond : Term.Admissible leftSecond SetSort.set)
    (hRightSecond : Term.Admissible rightSecond SetSort.set)
    (hFirstDepthFreshLeft :
      (SetSort.set, firstDepthId) ∉
        Term.freeSupport leftFirst)
    (hFirstDepthFreshRight :
      (SetSort.set, firstDepthId) ∉
        Term.freeSupport rightFirst)
    (hFirstTargetDepthFreshLeft :
      (SetSort.set, firstDepthId + 1) ∉
        Term.freeSupport leftFirst)
    (hFirstTargetDepthFreshRight :
      (SetSort.set, firstDepthId + 1) ∉
        Term.freeSupport rightFirst)
    (hSecondDepthFreshLeft :
      (SetSort.set, secondDepthId) ∉
        Term.freeSupport leftSecond)
    (hSecondDepthFreshRight :
      (SetSort.set, secondDepthId) ∉
        Term.freeSupport rightSecond)
    (hSecondTargetDepthFreshLeft :
      (SetSort.set, secondDepthId + 1) ∉
        Term.freeSupport leftSecond)
    (hSecondTargetDepthFreshRight :
      (SetSort.set, secondDepthId + 1) ∉
        Term.freeSupport rightSecond)
    (hFirstDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, firstDepthId) ∉
          Formula.freeSupport formula)
    (hFirstTargetDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, firstDepthId + 1) ∉
          Formula.freeSupport formula)
    (hSecondDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, secondDepthId) ∉
          Formula.freeSupport formula)
    (hSecondTargetDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, secondDepthId + 1) ∉
          Formula.freeSupport formula)
    (hFirstCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_variable_code_condition_with_id
          (numₘ(cutoff)) (numₘ(entryDepth))
          leftFirst rightFirst firstDepthId)
    (hSecondCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_variable_code_condition_with_id
          (numₘ(cutoff)) (numₘ(entryDepth))
          leftSecond rightSecond secondDepthId)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .equality leftDepth rightDepth ≐ₘ
          eq_codeₘ(leftFirst, leftSecond))
    (hTargetEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        rightCode ≐ₘ eq_codeₘ(rightFirst, rightSecond)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      rightCode ≐ₘ
        CanonicalProjectTrace.canonical_project_atom_code
          .equality
          (canonical_project_shift_depth cutoff leftDepth)
          (canonical_project_shift_depth cutoff rightDepth) := by
  have hFirstBoundary :=
    fs_zfc_support_raw_canonical_shifted_variable_left_boundary
      cutoff entryDepth leftFirst rightFirst firstDepthId
      hLeftFirst hRightFirst
      hFirstDepthFreshLeft hFirstDepthFreshContext
      hFirstCondition
  have hSecondBoundary :=
    fs_zfc_support_raw_canonical_shifted_variable_left_boundary
      cutoff entryDepth leftSecond rightSecond secondDepthId
      hLeftSecond hRightSecond
      hSecondDepthFreshLeft hSecondDepthFreshContext
      hSecondCondition
  have hSourceParts :=
    fs_zfc_support_raw_canonical_equality_parts_unique
      leftDepth rightDepth leftFirst leftSecond
      hLeftFirst hLeftSecond
      (FirstOrder.Derives.conjElimLeft hFirstBoundary)
      (FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight hFirstBoundary)
      (FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hFirstBoundary)
      (FirstOrder.Derives.conjElimLeft hSecondBoundary)
      (FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight hSecondBoundary)
      (FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hSecondBoundary)
      hSourceEquality
  have hTargetFirst :=
    fs_zfc_support_raw_canonical_shifted_variable_code_condition_unique
      cutoff entryDepth leftDepth
      leftFirst rightFirst firstDepthId
      hLeftFirst hRightFirst
      (FirstOrder.Derives.conjElimLeft hSourceParts)
      hFirstDepthFreshRight
      hFirstTargetDepthFreshLeft
      hFirstTargetDepthFreshRight
      hFirstDepthFreshContext
      hFirstTargetDepthFreshContext
      hFirstCondition
  have hTargetSecond :=
    fs_zfc_support_raw_canonical_shifted_variable_code_condition_unique
      cutoff entryDepth rightDepth
      leftSecond rightSecond secondDepthId
      hLeftSecond hRightSecond
      (FirstOrder.Derives.conjElimRight hSourceParts)
      hSecondDepthFreshRight
      hSecondTargetDepthFreshLeft
      hSecondTargetDepthFreshRight
      hSecondDepthFreshContext
      hSecondTargetDepthFreshContext
      hSecondCondition
  have hTargetConstructor :=
    canonical_equality_code_term_congr_of_equalities
      rightFirst
      (canonical_binder_variable_code_term
        (numₘ(canonical_project_shift_depth
          cutoff leftDepth)))
      rightSecond
      (canonical_binder_variable_code_term
        (numₘ(canonical_project_shift_depth
          cutoff rightDepth)))
      hRightFirst
      (canonical_binder_variable_code_term_admissible
        (numₘ(canonical_project_shift_depth
          cutoff leftDepth))
        (finite_numeral_term_admissible
          (canonical_project_shift_depth cutoff leftDepth)))
      hRightSecond
      (canonical_binder_variable_code_term_admissible
        (numₘ(canonical_project_shift_depth
          cutoff rightDepth))
        (finite_numeral_term_admissible
          (canonical_project_shift_depth cutoff rightDepth)))
      hTargetFirst hTargetSecond
  have hTargetLeftNamed :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(canonical_project_shift_depth
              cutoff leftDepth)) ≐ₘ
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name
              (canonical_project_shift_depth
                cutoff leftDepth)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          Metatheory.Derives.equality_symm <|
            canonical_binder_variable_code_numeral_derives
              (canonical_project_shift_depth
                cutoff leftDepth)
  have hTargetRightNamed :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(canonical_project_shift_depth
              cutoff rightDepth)) ≐ₘ
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name
              (canonical_project_shift_depth
                cutoff rightDepth)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          Metatheory.Derives.equality_symm <|
            canonical_binder_variable_code_numeral_derives
              (canonical_project_shift_depth
                cutoff rightDepth)
  have hTargetNamedConstructor :=
    canonical_equality_code_term_congr_of_equalities
      (canonical_binder_variable_code_term
        (numₘ(canonical_project_shift_depth
          cutoff leftDepth)))
      (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff leftDepth)))
      (canonical_binder_variable_code_term
        (numₘ(canonical_project_shift_depth
          cutoff rightDepth)))
      (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff rightDepth)))
      (canonical_binder_variable_code_term_admissible
        (numₘ(canonical_project_shift_depth
          cutoff leftDepth))
        (finite_numeral_term_admissible
          (canonical_project_shift_depth cutoff leftDepth)))
      (variable_code_term_admissible
        (numₘ(GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff leftDepth)))
        (finite_numeral_term_admissible
          (GodelQuotation.bound_name
            (canonical_project_shift_depth cutoff leftDepth))))
      (canonical_binder_variable_code_term_admissible
        (numₘ(canonical_project_shift_depth
          cutoff rightDepth))
        (finite_numeral_term_admissible
          (canonical_project_shift_depth cutoff rightDepth)))
      (variable_code_term_admissible
        (numₘ(GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff rightDepth)))
        (finite_numeral_term_admissible
          (GodelQuotation.bound_name
            (canonical_project_shift_depth cutoff rightDepth))))
      hTargetLeftNamed hTargetRightNamed
  exact Metatheory.Derives.equality_trans
    hTargetEquality <|
      Metatheory.Derives.equality_trans
        hTargetConstructor <| by
          simpa [
            CanonicalProjectTrace.canonical_project_atom_code] using
            hTargetNamedConstructor

/--
已展开的 membership 原子同步分支唯一决定目标规范原子码。

这里的显式新鲜性均来自四个外层变量见证与两个深度见证的存在消去；
定理本身只消费真实的捕获规避条件，不把它们提升为更强的闭项假设。
-/
theorem fs_zfc_support_raw_canonical_membership_shift_branch_unique
    {Γ : Context signature}
    (cutoff entryDepth leftDepth rightDepth : Nat)
    (rightCode : SetTerm)
    (leftFirst rightFirst leftSecond rightSecond : SetTerm)
    (firstDepthId secondDepthId : FreeVarId)
    (hLeftFirst : Term.Admissible leftFirst SetSort.set)
    (hRightFirst : Term.Admissible rightFirst SetSort.set)
    (hLeftSecond : Term.Admissible leftSecond SetSort.set)
    (hRightSecond : Term.Admissible rightSecond SetSort.set)
    (hFirstDepthFreshLeft :
      (SetSort.set, firstDepthId) ∉
        Term.freeSupport leftFirst)
    (hFirstDepthFreshRight :
      (SetSort.set, firstDepthId) ∉
        Term.freeSupport rightFirst)
    (hFirstTargetDepthFreshLeft :
      (SetSort.set, firstDepthId + 1) ∉
        Term.freeSupport leftFirst)
    (hFirstTargetDepthFreshRight :
      (SetSort.set, firstDepthId + 1) ∉
        Term.freeSupport rightFirst)
    (hSecondDepthFreshLeft :
      (SetSort.set, secondDepthId) ∉
        Term.freeSupport leftSecond)
    (hSecondDepthFreshRight :
      (SetSort.set, secondDepthId) ∉
        Term.freeSupport rightSecond)
    (hSecondTargetDepthFreshLeft :
      (SetSort.set, secondDepthId + 1) ∉
        Term.freeSupport leftSecond)
    (hSecondTargetDepthFreshRight :
      (SetSort.set, secondDepthId + 1) ∉
        Term.freeSupport rightSecond)
    (hFirstDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, firstDepthId) ∉
          Formula.freeSupport formula)
    (hFirstTargetDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, firstDepthId + 1) ∉
          Formula.freeSupport formula)
    (hSecondDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, secondDepthId) ∉
          Formula.freeSupport formula)
    (hSecondTargetDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, secondDepthId + 1) ∉
          Formula.freeSupport formula)
    (hFirstCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_variable_code_condition_with_id
          (numₘ(cutoff)) (numₘ(entryDepth))
          leftFirst rightFirst firstDepthId)
    (hSecondCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_variable_code_condition_with_id
          (numₘ(cutoff)) (numₘ(entryDepth))
          leftSecond rightSecond secondDepthId)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .membership leftDepth rightDepth ≐ₘ
          membership_atomic_formula_code_term
            leftFirst leftSecond)
    (hTargetEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        rightCode ≐ₘ
          membership_atomic_formula_code_term
            rightFirst rightSecond) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      rightCode ≐ₘ
        CanonicalProjectTrace.canonical_project_atom_code
          .membership
          (canonical_project_shift_depth cutoff leftDepth)
          (canonical_project_shift_depth cutoff rightDepth) := by
  have hFirstBoundary :=
    fs_zfc_support_raw_canonical_shifted_variable_left_boundary
      cutoff entryDepth leftFirst rightFirst firstDepthId
      hLeftFirst hRightFirst
      hFirstDepthFreshLeft hFirstDepthFreshContext
      hFirstCondition
  have hSecondBoundary :=
    fs_zfc_support_raw_canonical_shifted_variable_left_boundary
      cutoff entryDepth leftSecond rightSecond secondDepthId
      hLeftSecond hRightSecond
      hSecondDepthFreshLeft hSecondDepthFreshContext
      hSecondCondition
  have hSourceParts :=
    fs_zfc_support_raw_canonical_membership_parts_unique
      leftDepth rightDepth leftFirst leftSecond
      hLeftFirst hLeftSecond
      (FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight hFirstBoundary)
      (FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hFirstBoundary)
      (FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight hSecondBoundary)
      (FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hSecondBoundary)
      hSourceEquality
  have hTargetFirst :=
    fs_zfc_support_raw_canonical_shifted_variable_code_condition_unique
      cutoff entryDepth leftDepth
      leftFirst rightFirst firstDepthId
      hLeftFirst hRightFirst
      (FirstOrder.Derives.conjElimLeft hSourceParts)
      hFirstDepthFreshRight
      hFirstTargetDepthFreshLeft
      hFirstTargetDepthFreshRight
      hFirstDepthFreshContext
      hFirstTargetDepthFreshContext
      hFirstCondition
  have hTargetSecond :=
    fs_zfc_support_raw_canonical_shifted_variable_code_condition_unique
      cutoff entryDepth rightDepth
      leftSecond rightSecond secondDepthId
      hLeftSecond hRightSecond
      (FirstOrder.Derives.conjElimRight hSourceParts)
      hSecondDepthFreshRight
      hSecondTargetDepthFreshLeft
      hSecondTargetDepthFreshRight
      hSecondDepthFreshContext
      hSecondTargetDepthFreshContext
      hSecondCondition
  have hTargetConstructor :=
    canonical_membership_atomic_code_term_congr_of_equalities
      rightFirst
      (canonical_binder_variable_code_term
        (numₘ(canonical_project_shift_depth
          cutoff leftDepth)))
      rightSecond
      (canonical_binder_variable_code_term
        (numₘ(canonical_project_shift_depth
          cutoff rightDepth)))
      hRightFirst
      (canonical_binder_variable_code_term_admissible
        (numₘ(canonical_project_shift_depth
          cutoff leftDepth))
        (finite_numeral_term_admissible
          (canonical_project_shift_depth cutoff leftDepth)))
      hRightSecond
      (canonical_binder_variable_code_term_admissible
        (numₘ(canonical_project_shift_depth
          cutoff rightDepth))
        (finite_numeral_term_admissible
          (canonical_project_shift_depth cutoff rightDepth)))
      hTargetFirst hTargetSecond
  have hTargetLeftNamed :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(canonical_project_shift_depth
              cutoff leftDepth)) ≐ₘ
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name
              (canonical_project_shift_depth
                cutoff leftDepth)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          Metatheory.Derives.equality_symm <|
            canonical_binder_variable_code_numeral_derives
              (canonical_project_shift_depth
                cutoff leftDepth)
  have hTargetRightNamed :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(canonical_project_shift_depth
              cutoff rightDepth)) ≐ₘ
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name
              (canonical_project_shift_depth
                cutoff rightDepth)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          Metatheory.Derives.equality_symm <|
            canonical_binder_variable_code_numeral_derives
              (canonical_project_shift_depth
                cutoff rightDepth)
  have hTargetNamedConstructor :=
    canonical_membership_atomic_code_term_congr_of_equalities
      (canonical_binder_variable_code_term
        (numₘ(canonical_project_shift_depth
          cutoff leftDepth)))
      (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff leftDepth)))
      (canonical_binder_variable_code_term
        (numₘ(canonical_project_shift_depth
          cutoff rightDepth)))
      (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff rightDepth)))
      (canonical_binder_variable_code_term_admissible
        (numₘ(canonical_project_shift_depth
          cutoff leftDepth))
        (finite_numeral_term_admissible
          (canonical_project_shift_depth cutoff leftDepth)))
      (variable_code_term_admissible
        (numₘ(GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff leftDepth)))
        (finite_numeral_term_admissible
          (GodelQuotation.bound_name
            (canonical_project_shift_depth cutoff leftDepth))))
      (canonical_binder_variable_code_term_admissible
        (numₘ(canonical_project_shift_depth
          cutoff rightDepth))
        (finite_numeral_term_admissible
          (canonical_project_shift_depth cutoff rightDepth)))
      (variable_code_term_admissible
        (numₘ(GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff rightDepth)))
        (finite_numeral_term_admissible
          (GodelQuotation.bound_name
            (canonical_project_shift_depth cutoff rightDepth))))
      hTargetLeftNamed hTargetRightNamed
  exact Metatheory.Derives.equality_trans
    hTargetEquality <|
      Metatheory.Derives.equality_trans
        hTargetConstructor <| by
          simpa [
            CanonicalProjectTrace.canonical_project_atom_code] using
            hTargetNamedConstructor

/-! ## 规范 subset 原子的分量反演 -/

/--
已知规范 subset 码等于由两个长度一代码字符串构成的项目 subset 码，则两个分量
分别恢复为源深度对应的规范 binder 变量码。

`hReserved` 仅暴露标准有限函数图实现内部的三个编号；它不要求分量闭合。
-/
theorem fs_zfc_support_raw_canonical_subset_parts_unique
    {Γ : Context signature}
    (leftDepth rightDepth : Nat)
    (leftFirst leftSecond : SetTerm)
    (hLeftFirst : Term.Admissible leftFirst SetSort.set)
    (hLeftSecond : Term.Admissible leftSecond SetSort.set)
    (hReserved :
      ReservedIdsFresh [0, 1, 2]
        [leftFirst, leftSecond])
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition leftFirst)
    (hFirstDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(leftFirst) ≐ₘ numₘ(1))
    (hSecondFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition leftSecond)
    (hSecondDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(leftSecond) ≐ₘ numₘ(1))
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .subset leftDepth rightDepth ≐ₘ
          project_subset_atomic_code_term
            leftFirst leftSecond) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (leftFirst ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(leftDepth))) ∧ₘ
        (leftSecond ≐ₘ
          canonical_binder_variable_code_term
            (numₘ(rightDepth))) := by
  let leftTokens : List Nat := [
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name leftDepth)]
  let rightTokens : List Nat := [
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name rightDepth)]
  let pieces : List (List Nat) := [
    leftTokens, rightTokens]
  let tokens : List Nat :=
    GodelQuotation.Numbered.predicate_application_tokens
      1 RelationSymbol.subset.ctorIdx pieces
  let family : SetTerm :=
    GodelQuotation.Numbered.argument_sequence
      [leftFirst, leftSecond]
  let head : SetTerm :=
    coded_predicate_symbol_code_term
      (numₘ(1))
      (numₘ(RelationSymbol.subset.ctorIdx))
  have hLeftCanonicalBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.bound_name leftDepth)) := by
    exact canonical_quoted_binder_variable_code_boundary
      leftDepth
  have hRightCanonicalBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.bound_name rightDepth)) := by
    exact canonical_quoted_binder_variable_code_boundary
      rightDepth
  have hAligned :
      GodelQuotation.gq_code_token_aligned_list
        [GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name leftDepth),
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name rightDepth)]
        pieces := by
    apply GodelQuotation.gq_code_token_aligned_list.cons
    · exact ⟨hLeftCanonicalBoundary, by
        simpa [leftTokens] using
          GodelQuotation.named_variable_code_eq_standard_token_sequence
            (GodelQuotation.bound_name leftDepth)⟩
    apply GodelQuotation.gq_code_token_aligned_list.cons
    · exact ⟨hRightCanonicalBoundary, by
        simpa [rightTokens] using
          GodelQuotation.named_variable_code_eq_standard_token_sequence
            (GodelQuotation.bound_name rightDepth)⟩
    exact GodelQuotation.gq_code_token_aligned_list.nil
  have hCanonicalStandard :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .subset leftDepth rightDepth ≐ₘ
          standard_token_sequence tokens := by
    simpa [tokens, pieces,
      CanonicalProjectTrace.canonical_project_atom_code] using
      GodelQuotation.gq_predicate_application_code_eq_standard_token_sequence
        1 RelationSymbol.subset.ctorIdx hAligned
  have hCanonicalStandardAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .subset leftDepth rightDepth ≐ₘ
          standard_token_sequence tokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          hCanonicalStandard
  have hStandardSource :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          project_subset_atomic_code_term
            leftFirst leftSecond :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        hCanonicalStandardAt)
      hSourceEquality
  have hElements :
      ∀ term, term ∈ [leftFirst, leftSecond] →
        Term.Admissible term SetSort.set := by
    intro term hTerm
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hTerm
    rcases hTerm with rfl | rfl
    · exact hLeftFirst
    · exact hLeftSecond
  have hFreshZero :
      ∀ term, term ∈ [leftFirst, leftSecond] →
        (SetSort.set, 0) ∉
          Term.freeSupport term := by
    intro term hTerm
    exact hReserved term hTerm 0 (by simp)
  have hFreshOne :
      ∀ term, term ∈ [leftFirst, leftSecond] →
        (SetSort.set, 1) ∉
          Term.freeSupport term := by
    intro term hTerm
    exact hReserved term hTerm 1 (by simp)
  have hFreshTwo :
      ∀ term, term ∈ [leftFirst, leftSecond] →
        (SetSort.set, 2) ∉
          Term.freeSupport term := by
    intro term hTerm
    exact hReserved term hTerm 2 (by simp)
  have hElementFinite :
      ∀ term, term ∈ [leftFirst, leftSecond] →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          finite_sequence_condition term := by
    intro term hTerm
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hTerm
    rcases hTerm with rfl | rfl
    · exact hFirstFinite
    · exact hSecondFinite
  have hFamily :
      Term.Admissible family SetSort.set := by
    simpa [family,
      GodelQuotation.Numbered.argument_sequence] using
      GodelQuotation.seq_admissible_m 0 hElements
  have hFamilyCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_family_condition family := by
    simpa [family,
      GodelQuotation.Numbered.argument_sequence] using
      GodelQuotation.standard_sequence_family_condition_derives_of_theory_context
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_standard_sequence_semantics
            hFormula)
        (fun _ hFormula =>
          fs_zfc_support_raw_theory_sentence hFormula)
        hElements hFreshZero hFreshOne hFreshTwo
        hElementFinite
  have hFamilyDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(family) ≐ₘ numₘ(2) := by
    exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_standard_sequence_semantics
              hFormula) <| by
            simpa [family,
              GodelQuotation.Numbered.argument_sequence] using
              GodelQuotation.standard_sequence_domain_eq_numeral_length
                hElements hFreshZero hFreshOne
  have hFamilyFirstValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (family ·ₘ numₘ(0)) ≐ₘ leftFirst := by
    simpa [family,
      GodelQuotation.Numbered.argument_sequence] using
      GodelQuotation.standard_sequence_from_apply_getElem?_of_theory
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_standard_sequence_semantics
            hFormula)
        0 (elements := [leftFirst, leftSecond])
        (index := 0) (element := leftFirst)
        (by simp) hElements
        hFreshZero hFreshOne hFreshTwo hLeftFirst
  have hFamilySecondValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (family ·ₘ numₘ(1)) ≐ₘ leftSecond := by
    simpa [family,
      GodelQuotation.Numbered.argument_sequence] using
      GodelQuotation.standard_sequence_from_apply_getElem?_of_theory
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_standard_sequence_semantics
            hFormula)
        0 (elements := [leftFirst, leftSecond])
        (index := 1) (element := leftSecond)
        (by simp) hElements
        hFreshZero hFreshOne hFreshTwo hLeftSecond
  have hFamilyFirstDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(family ·ₘ numₘ(0)) ≐ₘ numₘ(1) :=
    Metatheory.Derives.equality_trans
      (domain_term_congr_of_equality
        (family ·ₘ numₘ(0)) leftFirst
        (function_application_term_admissible
          family (numₘ(0)) hFamily
          (finite_numeral_term_admissible 0))
        hLeftFirst hFamilyFirstValue)
      hFirstDomain
  have hFamilySecondDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(family ·ₘ numₘ(1)) ≐ₘ numₘ(1) :=
    Metatheory.Derives.equality_trans
      (domain_term_congr_of_equality
        (family ·ₘ numₘ(1)) leftSecond
        (function_application_term_admissible
          family (numₘ(1)) hFamily
          (finite_numeral_term_admissible 1))
        hLeftSecond hFamilySecondValue)
      hSecondDomain
  have hBodyFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition (flattenₘ(family)) := by
    exact FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            FirstOrder.Derives.theory_weaken
              (fun _ hFormula =>
                fs_zfc_support_raw_contains_standard_sequence_semantics
                  hFormula) <| by
                simpa using
                  GodelQuotation.finite_sequence_flatten_term_spec_derives
                    family hFamily)
        hFamilyCondition
  have hBodyDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(flattenₘ(family)) ≐ₘ numₘ(2) :=
    GodelQuotation.gq_flatten_pair_domain_eq_two_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation
          hFormula)
      family hFamilyCondition hFamilyDomain
      hFamilyFirstDomain hFamilySecondDomain
      (hFamilyCheck :=
        Term.check_admissible_complete hFamily)
  have hHeadEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        head ≐ₘ
          standard_token_sequence
            [GodelQuotation.Numbered.predicate_token
              1 RelationSymbol.subset.ctorIdx] := by
    exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <| by
          simpa [head] using
            GodelQuotation.coded_predicate_symbol_code_eq_standard_token_sequence
              1 RelationSymbol.subset.ctorIdx
  have hWholeAsHeaded :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          GodelQuotation.headed_application_code_term
            head (flattenₘ(family)) := by
    simpa [project_subset_atomic_code_term,
      predicate_application_code_term,
      GodelQuotation.headed_application_code_term,
      head, family] using hStandardSource
  have hBodyStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        flattenₘ(family) ≐ₘ
          standard_token_sequence
            ((tokens.drop 2).take 2) :=
    GodelQuotation.gq_headed_application_body_eq_standard_slice_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation
          hFormula)
      (GodelQuotation.Numbered.predicate_token
        1 RelationSymbol.subset.ctorIdx)
      head (flattenₘ(family)) tokens 2
      hHeadEquality hBodyFinite hBodyDomain
      hWholeAsHeaded
      (by
        simp [tokens, pieces, leftTokens, rightTokens,
          GodelQuotation.Numbered.predicate_application_tokens])
  let bodyTokens : List Nat :=
    (tokens.drop 2).take 2
  have hFlattenParts :=
    GodelQuotation.gq_flatten_pair_domain_and_parts_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation
          hFormula)
      family bodyTokens
      hFamilyCondition hFamilyDomain
      hFamilyFirstDomain hFamilySecondDomain
      (by
        simpa [bodyTokens] using
          Metatheory.Derives.equality_symm hBodyStandard)
      (by
        simp [bodyTokens, tokens, pieces,
          leftTokens, rightTokens,
          GodelQuotation.Numbered.predicate_application_tokens])
      (hFamilyCheck :=
        Term.check_admissible_complete hFamily)
  have hFirstSlice :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (family ·ₘ numₘ(0)) ≐ₘ
          standard_token_sequence leftTokens := by
    simpa [bodyTokens, tokens, pieces,
      leftTokens, rightTokens,
      GodelQuotation.Numbered.predicate_application_tokens] using
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight
          hFlattenParts
  have hSecondSlice :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (family ·ₘ numₘ(1)) ≐ₘ
          standard_token_sequence rightTokens := by
    simpa [bodyTokens, tokens, pieces,
      leftTokens, rightTokens,
      GodelQuotation.Numbered.predicate_application_tokens] using
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight
          hFlattenParts
  have hFirstStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        leftFirst ≐ₘ
          standard_token_sequence leftTokens :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        hFamilyFirstValue)
      hFirstSlice
  have hSecondStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        leftSecond ≐ₘ
          standard_token_sequence rightTokens :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        hFamilySecondValue)
      hSecondSlice
  have hFirstCanonical :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(leftDepth)) ≐ₘ
          standard_token_sequence leftTokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <| by
          simpa [leftTokens] using
            canonical_binder_variable_code_numeral_eq_standard_token_sequence
              leftDepth
  have hSecondCanonical :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            (numₘ(rightDepth)) ≐ₘ
          standard_token_sequence rightTokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <| by
          simpa [rightTokens] using
            canonical_binder_variable_code_numeral_eq_standard_token_sequence
              rightDepth
  exact FirstOrder.Derives.conjIntro
    (Metatheory.Derives.equality_trans
      hFirstStandard
      (Metatheory.Derives.equality_symm
        hFirstCanonical))
    (Metatheory.Derives.equality_trans
      hSecondStandard
      (Metatheory.Derives.equality_symm
        hSecondCanonical))

/-- 已展开的 subset 原子同步分支唯一决定目标规范原子码。 -/
theorem fs_zfc_support_raw_canonical_subset_shift_branch_unique
    {Γ : Context signature}
    (cutoff entryDepth leftDepth rightDepth : Nat)
    (rightCode : SetTerm)
    (leftFirst rightFirst leftSecond rightSecond : SetTerm)
    (firstDepthId secondDepthId : FreeVarId)
    (hLeftFirst : Term.Admissible leftFirst SetSort.set)
    (hRightFirst : Term.Admissible rightFirst SetSort.set)
    (hLeftSecond : Term.Admissible leftSecond SetSort.set)
    (hRightSecond : Term.Admissible rightSecond SetSort.set)
    (hReserved :
      ReservedIdsFresh [0, 1, 2]
        [leftFirst, leftSecond])
    (hFirstDepthFreshLeft :
      (SetSort.set, firstDepthId) ∉
        Term.freeSupport leftFirst)
    (hFirstDepthFreshRight :
      (SetSort.set, firstDepthId) ∉
        Term.freeSupport rightFirst)
    (hFirstTargetDepthFreshLeft :
      (SetSort.set, firstDepthId + 1) ∉
        Term.freeSupport leftFirst)
    (hFirstTargetDepthFreshRight :
      (SetSort.set, firstDepthId + 1) ∉
        Term.freeSupport rightFirst)
    (hSecondDepthFreshLeft :
      (SetSort.set, secondDepthId) ∉
        Term.freeSupport leftSecond)
    (hSecondDepthFreshRight :
      (SetSort.set, secondDepthId) ∉
        Term.freeSupport rightSecond)
    (hSecondTargetDepthFreshLeft :
      (SetSort.set, secondDepthId + 1) ∉
        Term.freeSupport leftSecond)
    (hSecondTargetDepthFreshRight :
      (SetSort.set, secondDepthId + 1) ∉
        Term.freeSupport rightSecond)
    (hFirstDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, firstDepthId) ∉
          Formula.freeSupport formula)
    (hFirstTargetDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, firstDepthId + 1) ∉
          Formula.freeSupport formula)
    (hSecondDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, secondDepthId) ∉
          Formula.freeSupport formula)
    (hSecondTargetDepthFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, secondDepthId + 1) ∉
          Formula.freeSupport formula)
    (hFirstCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_variable_code_condition_with_id
          (numₘ(cutoff)) (numₘ(entryDepth))
          leftFirst rightFirst firstDepthId)
    (hSecondCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_variable_code_condition_with_id
          (numₘ(cutoff)) (numₘ(entryDepth))
          leftSecond rightSecond secondDepthId)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .subset leftDepth rightDepth ≐ₘ
          project_subset_atomic_code_term
            leftFirst leftSecond)
    (hTargetEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        rightCode ≐ₘ
          project_subset_atomic_code_term
            rightFirst rightSecond) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      rightCode ≐ₘ
        CanonicalProjectTrace.canonical_project_atom_code
          .subset
          (canonical_project_shift_depth cutoff leftDepth)
          (canonical_project_shift_depth cutoff rightDepth) := by
  have hFirstBoundary :=
    fs_zfc_support_raw_canonical_shifted_variable_left_boundary
      cutoff entryDepth leftFirst rightFirst firstDepthId
      hLeftFirst hRightFirst
      hFirstDepthFreshLeft hFirstDepthFreshContext
      hFirstCondition
  have hSecondBoundary :=
    fs_zfc_support_raw_canonical_shifted_variable_left_boundary
      cutoff entryDepth leftSecond rightSecond secondDepthId
      hLeftSecond hRightSecond
      hSecondDepthFreshLeft hSecondDepthFreshContext
      hSecondCondition
  have hSourceParts :=
    fs_zfc_support_raw_canonical_subset_parts_unique
      leftDepth rightDepth leftFirst leftSecond
      hLeftFirst hLeftSecond hReserved
      (FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight hFirstBoundary)
      (FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hFirstBoundary)
      (FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight hSecondBoundary)
      (FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hSecondBoundary)
      hSourceEquality
  have hTargetFirst :=
    fs_zfc_support_raw_canonical_shifted_variable_code_condition_unique
      cutoff entryDepth leftDepth
      leftFirst rightFirst firstDepthId
      hLeftFirst hRightFirst
      (FirstOrder.Derives.conjElimLeft hSourceParts)
      hFirstDepthFreshRight
      hFirstTargetDepthFreshLeft
      hFirstTargetDepthFreshRight
      hFirstDepthFreshContext
      hFirstTargetDepthFreshContext
      hFirstCondition
  have hTargetSecond :=
    fs_zfc_support_raw_canonical_shifted_variable_code_condition_unique
      cutoff entryDepth rightDepth
      leftSecond rightSecond secondDepthId
      hLeftSecond hRightSecond
      (FirstOrder.Derives.conjElimRight hSourceParts)
      hSecondDepthFreshRight
      hSecondTargetDepthFreshLeft
      hSecondTargetDepthFreshRight
      hSecondDepthFreshContext
      hSecondTargetDepthFreshContext
      hSecondCondition
  have hTargetFirstNamed :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        rightFirst ≐ₘ
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name
              (canonical_project_shift_depth
                cutoff leftDepth)) :=
    Metatheory.Derives.equality_trans hTargetFirst <|
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            Metatheory.Derives.equality_symm <|
              canonical_binder_variable_code_numeral_derives
                (canonical_project_shift_depth
                  cutoff leftDepth)
  have hTargetSecondNamed :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        rightSecond ≐ₘ
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name
              (canonical_project_shift_depth
                cutoff rightDepth)) :=
    Metatheory.Derives.equality_trans hTargetSecond <|
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <|
            Metatheory.Derives.equality_symm <|
              canonical_binder_variable_code_numeral_derives
                (canonical_project_shift_depth
                  cutoff rightDepth)
  have hTargetConstructor :=
    canonical_project_subset_atomic_code_term_congr_of_equalities
      rightFirst
      (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff leftDepth)))
      rightSecond
      (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff rightDepth)))
      hRightFirst
      (variable_code_term_admissible
        (numₘ(GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff leftDepth)))
        (finite_numeral_term_admissible
          (GodelQuotation.bound_name
            (canonical_project_shift_depth cutoff leftDepth))))
      hRightSecond
      (variable_code_term_admissible
        (numₘ(GodelQuotation.bound_name
          (canonical_project_shift_depth cutoff rightDepth)))
        (finite_numeral_term_admissible
          (GodelQuotation.bound_name
            (canonical_project_shift_depth cutoff rightDepth))))
      hTargetFirstNamed hTargetSecondNamed
  exact Metatheory.Derives.equality_trans
    hTargetEquality <| by
      simpa [
        CanonicalProjectTrace.canonical_project_atom_code] using
        hTargetConstructor

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
