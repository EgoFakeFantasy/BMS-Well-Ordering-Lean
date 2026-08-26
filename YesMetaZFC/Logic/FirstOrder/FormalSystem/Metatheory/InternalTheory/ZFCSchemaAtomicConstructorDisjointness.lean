import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaAtomicShiftInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.AtomQuotation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.StandardOpening
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.ImplicationConstructionInversion

/-!
# ZFC schema 原子构造标签不交

本模块只比较规范原子码的固定 token。等式与隶属在第一分量之后比较中缀，
项目 subset 谓词应用则在零位比较谓词头；所有矛盾均归约为两个有限 numeral 不等。
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

/-- 长度一第一分量的等式原子在第二位具有 equality token。 -/
theorem fs_zfc_support_raw_equality_atomic_middle_point
    {Γ : Context signature}
    (first last : SetTerm)
    (hFirst : Term.Admissible first SetSort.set)
    (hLast : Term.Admissible last SetSort.set)
    (hFirstCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] term_codeₘ(first))
    (hLastCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] term_codeₘ(last))
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition first)
    (hFirstDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(first) ≐ₘ numₘ(1))
    (hLastFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition last) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      ((numₘ(2) ∈ₘ domₘ(eq_codeₘ(first, last))) ∧ₘ
        ((eq_codeₘ(first, last) ·ₘ numₘ(2)) ≐ₘ
          numₘ(GodelQuotation.Numbered.logical_token
            .equality))) := by
  have hRawPoint :=
    GodelQuotation.gq_bracketed_three_part_middle_point_of_first_domain_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      first equality_symbol_code_term last
      (GodelQuotation.Numbered.logical_token .equality) 1
      hFirstFinite hFirstDomain
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            (logical_symbol_code_eq_standard_token_sequence
              .equality))
      hLastFinite
      (hFirstCheck := Term.check_admissible_complete hFirst)
      (hLastCheck := Term.check_admissible_complete hLast)
  exact
    GodelQuotation.gq_point_inversion_of_equality_of_theory
      (eq_codeₘ(first, last))
      (equality_atomic_formula_code_term first last)
      (numₘ(2))
      (numₘ(GodelQuotation.Numbered.logical_token .equality))
      (fs_zfc_support_raw_equality_code_eq_raw_of_term_codes
        first last hFirst hLast hFirstCode hLastCode)
      hRawPoint
      (hLeft := Term.check_admissible_complete <|
        equality_formula_code_term_admissible
          first last hFirst hLast)
      (hRight := Term.check_admissible_complete <|
        binary_atomic_formula_code_term_admissible
          equality_symbol_code_term first last
          (logical_symbol_code_term_admissible .equality)
          hFirst hLast)

/-- 长度一第一分量的隶属原子在第二位具有 membership token。 -/
theorem fs_zfc_support_raw_membership_atomic_middle_point
    {Γ : Context signature}
    (first last : SetTerm)
    (hFirst : Term.Admissible first SetSort.set)
    (hLast : Term.Admissible last SetSort.set)
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition first)
    (hFirstDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(first) ≐ₘ numₘ(1))
    (hLastFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition last) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      ((numₘ(2) ∈ₘ
          domₘ(membership_atomic_formula_code_term first last)) ∧ₘ
        ((membership_atomic_formula_code_term first last ·ₘ
            numₘ(2)) ≐ₘ
          numₘ(GodelQuotation.Numbered.membership_token))) := by
  simpa [membership_atomic_formula_code_term] using
    GodelQuotation.gq_bracketed_three_part_middle_point_of_first_domain_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      first membership_symbol_code_term last
      GodelQuotation.Numbered.membership_token 1
      hFirstFinite hFirstDomain
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            membership_symbol_code_eq_standard_token_sequence)
      hLastFinite
      (hFirstCheck := Term.check_admissible_complete hFirst)
      (hLastCheck := Term.check_admissible_complete hLast)

/--
两个有限代码分量构成的项目 subset 谓词应用在零位具有固定谓词 token。
-/
theorem fs_zfc_support_raw_project_subset_atomic_head_point
    {Γ : Context signature}
    (first last : SetTerm)
    (hFirst : Term.Admissible first SetSort.set)
    (hLast : Term.Admissible last SetSort.set)
    (hReserved :
      ReservedIdsFresh [0, 1, 2] [first, last])
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition first)
    (hLastFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition last) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      ((numₘ(0) ∈ₘ
          domₘ(project_subset_atomic_code_term first last)) ∧ₘ
        ((project_subset_atomic_code_term first last ·ₘ
            numₘ(0)) ≐ₘ
          numₘ(GodelQuotation.Numbered.predicate_token
            1 RelationSymbol.subset.ctorIdx))) := by
  let elements : List SetTerm := [first, last]
  let family : SetTerm :=
    GodelQuotation.Numbered.argument_sequence elements
  let head : SetTerm :=
    coded_predicate_symbol_code_term
      (numₘ(1)) (numₘ(RelationSymbol.subset.ctorIdx))
  have hElements :
      ∀ term, term ∈ elements →
        Term.Admissible term SetSort.set := by
    intro term hTerm
    simp only [elements, List.mem_cons,
      List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl
    · exact hFirst
    · exact hLast
  have hFresh (id : FreeVarId) (hId : id ∈ [0, 1, 2]) :
      ∀ term, term ∈ elements →
        (SetSort.set, id) ∉ Term.freeSupport term := by
    intro term hTerm
    exact hReserved term (by simpa [elements] using hTerm) id hId
  have hElementFinite :
      ∀ term, term ∈ elements →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          finite_sequence_condition term := by
    intro term hTerm
    simp only [elements, List.mem_cons,
      List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl
    · exact hFirstFinite
    · exact hLastFinite
  have hFamily :
      Term.Admissible family SetSort.set := by
    simpa [family, elements,
      GodelQuotation.Numbered.argument_sequence] using
      GodelQuotation.seq_admissible_m 0 hElements
  have hFamilyCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_family_condition family := by
    simpa [family, elements,
      GodelQuotation.Numbered.argument_sequence] using
      GodelQuotation.standard_sequence_family_condition_derives_of_theory_context
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_standard_sequence_semantics
            hFormula)
        (fun _ hFormula =>
          fs_zfc_support_raw_theory_sentence hFormula)
        hElements
        (hFresh 0 (by simp))
        (hFresh 1 (by simp))
        (hFresh 2 (by simp))
        hElementFinite
  have hBodyFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition (flattenₘ(family)) :=
    FirstOrder.Derives.conjElimLeft <|
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
  have hHeadEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        head ≐ₘ
          standard_token_sequence
            [GodelQuotation.Numbered.predicate_token
              1 RelationSymbol.subset.ctorIdx] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <| by
          simpa [head] using
            GodelQuotation.coded_predicate_symbol_code_eq_standard_token_sequence
              1 RelationSymbol.subset.ctorIdx
  simpa [project_subset_atomic_code_term,
    predicate_application_code_term,
    GodelQuotation.headed_application_code_term,
    family, elements, head] using
      GodelQuotation.gq_headed_application_head_point_of_theory
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_godel_quotation hFormula)
        head (flattenₘ(family))
        (GodelQuotation.Numbered.predicate_token
          1 RelationSymbol.subset.ctorIdx)
        hHeadEquality hBodyFinite
        (hHead := Term.check_admissible_complete <|
          coded_predicate_symbol_code_term_admissible
            (numₘ(1)) (numₘ(RelationSymbol.subset.ctorIdx))
            (finite_numeral_term_admissible 1)
            (finite_numeral_term_admissible
              RelationSymbol.subset.ctorIdx))
        (hBody := Term.check_admissible_complete <|
          finite_sequence_flatten_term_admissible family hFamily)

theorem fs_zfc_support_raw_canonical_atom_standard_at
    {Γ : Context signature}
    (kind : CanonicalProjectAtomKind)
    (leftDepth rightDepth : Nat) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      CanonicalProjectTrace.canonical_project_atom_code
          kind leftDepth rightDepth ≐ₘ
        standard_token_sequence
          (CanonicalProjectTrace.canonical_project_atom_tokens
            kind leftDepth rightDepth) :=
  FirstOrder.Derives.context_weaken
    (Γ := []) (Δ := Γ) (by simp) <|
      fs_zfc_support_raw_derives_of_godel_quotation <|
        CanonicalProjectTrace.canonical_project_atom_code_eq_standard_token_sequence
          kind leftDepth rightDepth

/-- `FormulaCodeₘ` 成员在 ZFC raw 支持理论中仍给出有限序列条件。 -/
theorem fs_zfc_support_raw_formula_code_member_implies_finite_sequence
    {Γ : Context signature}
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      finite_sequence_condition code := by
  have hCodeString :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            (GodelQuotation.gq_formula_code_member_implies_code_string
              code hCode))
      hMember
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_standard_sequence
          (GodelQuotation.code_string_member_implies_finite_sequence_at
            code hCode))
    hCodeString

/-- 规范原子源码不可能满足蕴含构造分支。 -/
theorem fs_zfc_support_raw_canonical_atom_ne_implication_branch
    {Γ : Context signature}
    (kind : CanonicalProjectAtomKind)
    (leftDepth rightDepth : Nat)
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ∈ₘ FormulaCodeₘ)
    (hShape :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            kind leftDepth rightDepth ≐ₘ
          imp_codeₘ(left, right)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let tokens :=
    CanonicalProjectTrace.canonical_project_atom_tokens
      kind leftDepth rightDepth
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <| by
        simpa [tokens] using
          fs_zfc_support_raw_canonical_atom_standard_at
            (Γ := Γ) kind leftDepth rightDepth)
      hShape
  have hRoot :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ((numₘ(0) ∈ₘ
            domₘ(imp_codeₘ(left, right))) ∧ₘ
          ((imp_codeₘ(left, right) ·ₘ numₘ(0)) ≐ₘ
            numₘ(GodelQuotation.Numbered.logical_token
              .leftParenthesis))) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.theory_weaken
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_godel_quotation hFormula)
        (GodelQuotation.gq_implication_formula_opening_inversion
          (Γ := Γ) left right hLeft hRight))
      (FirstOrder.Derives.conjIntro
        hLeftMember hRightMember)
  have hLeftFinite :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      left hLeft hLeftMember
  have hRightFinite :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      right hRight hRightMember
  cases kind with
  | subset =>
      exact
        GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
          (T := fs_zfc_support_raw_theory)
          (Γ := Γ)
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          tokens (imp_codeₘ(left, right)) 0
          (GodelQuotation.Numbered.predicate_token
            1 RelationSymbol.subset.ctorIdx)
          (GodelQuotation.Numbered.logical_token
            .leftParenthesis)
          (by
            simp [tokens,
              CanonicalProjectTrace.canonical_project_atom_tokens,
              GodelQuotation.Numbered.predicate_application_tokens])
          (GodelQuotation.odd_token_ne_logical
            (GodelQuotation.predicate_token_odd
              1 RelationSymbol.subset.ctorIdx)
            .leftParenthesis)
          hStandard hRoot
          (hConstructor := Term.check_admissible_complete <|
            implication_formula_code_term_admissible
              left right hLeft hRight)
  | equality =>
      have hLeftOpening :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            GodelQuotation.formula_code_left_opening_condition
              left :=
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp) <|
              fs_zfc_support_raw_derives_of_godel_quotation
                (GodelQuotation.gq_formula_code_member_implies_opening
                  left hLeft))
          hLeftMember
      unfold GodelQuotation.formula_code_left_opening_condition at hLeftOpening
      apply FirstOrder.Derives.disjElim hLeftOpening
      · let Δ : Context signature :=
          (((numₘ(0) ∈ₘ domₘ(left)) ∧ₘ
            ((left ·ₘ numₘ(0)) ≐ₘ
              numₘ(GodelQuotation.Numbered.logical_token
                .leftParenthesis)))) :: Γ
        have hLeftPoint :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              ((numₘ(0) ∈ₘ domₘ(left)) ∧ₘ
                ((left ·ₘ numₘ(0)) ≐ₘ
                  numₘ(GodelQuotation.Numbered.logical_token
                    .leftParenthesis))) :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hShift :=
          GodelQuotation.gq_implication_formula_left_point_at_standard_offset_of_theory
            (T := fs_zfc_support_raw_theory)
            (Γ := Δ)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            left right 0
            (FirstOrder.Derives.context_weaken_cons hLeftFinite)
            (FirstOrder.Derives.context_weaken_cons hRightFinite)
            (FirstOrder.Derives.conjElimLeft hLeftPoint)
            (hLeft := Term.check_admissible_complete hLeft)
            (hRight := Term.check_admissible_complete hRight)
        have hWholePoint :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              ((numₘ(1) ∈ₘ
                  domₘ(imp_codeₘ(left, right))) ∧ₘ
                ((imp_codeₘ(left, right) ·ₘ numₘ(1)) ≐ₘ
                  numₘ(GodelQuotation.Numbered.logical_token
                    .leftParenthesis))) :=
          FirstOrder.Derives.conjIntro
            (FirstOrder.Derives.conjElimLeft hShift)
            (Metatheory.Derives.equality_trans
              (FirstOrder.Derives.conjElimRight hShift)
              (FirstOrder.Derives.conjElimRight hLeftPoint))
        exact
          GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
            (T := fs_zfc_support_raw_theory)
            (Γ := Δ)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            tokens (imp_codeₘ(left, right)) 1
            (GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name leftDepth))
            (GodelQuotation.Numbered.logical_token
              .leftParenthesis)
            (by
              simp [tokens,
                CanonicalProjectTrace.canonical_project_atom_tokens,
                GodelQuotation.Numbered.equality_tokens])
            ((GodelQuotation.logical_token_ne_variable_token
              .leftParenthesis
              (GodelQuotation.bound_name leftDepth)).symm)
            (FirstOrder.Derives.context_weaken_cons hStandard)
            hWholePoint
            (hConstructor := Term.check_admissible_complete <|
              implication_formula_code_term_admissible
                left right hLeft hRight)
      · let Δ : Context signature :=
          (((numₘ(1) ∈ₘ domₘ(left)) ∧ₘ
            ((left ·ₘ numₘ(1)) ≐ₘ
              numₘ(GodelQuotation.Numbered.logical_token
                .leftParenthesis)))) :: Γ
        have hLeftPoint :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              ((numₘ(1) ∈ₘ domₘ(left)) ∧ₘ
                ((left ·ₘ numₘ(1)) ≐ₘ
                  numₘ(GodelQuotation.Numbered.logical_token
                    .leftParenthesis))) :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hShift :=
          GodelQuotation.gq_implication_formula_left_point_at_standard_offset_of_theory
            (T := fs_zfc_support_raw_theory)
            (Γ := Δ)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            left right 1
            (FirstOrder.Derives.context_weaken_cons hLeftFinite)
            (FirstOrder.Derives.context_weaken_cons hRightFinite)
            (FirstOrder.Derives.conjElimLeft hLeftPoint)
            (hLeft := Term.check_admissible_complete hLeft)
            (hRight := Term.check_admissible_complete hRight)
        have hWholePoint :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              ((numₘ(2) ∈ₘ
                  domₘ(imp_codeₘ(left, right))) ∧ₘ
                ((imp_codeₘ(left, right) ·ₘ numₘ(2)) ≐ₘ
                  numₘ(GodelQuotation.Numbered.logical_token
                    .leftParenthesis))) :=
          FirstOrder.Derives.conjIntro
            (FirstOrder.Derives.conjElimLeft hShift)
            (Metatheory.Derives.equality_trans
              (FirstOrder.Derives.conjElimRight hShift)
              (FirstOrder.Derives.conjElimRight hLeftPoint))
        exact
          GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
            (T := fs_zfc_support_raw_theory)
            (Γ := Δ)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            tokens (imp_codeₘ(left, right)) 2
            (GodelQuotation.Numbered.logical_token .equality)
            (GodelQuotation.Numbered.logical_token
              .leftParenthesis)
            (by
              simp [tokens,
                CanonicalProjectTrace.canonical_project_atom_tokens,
                GodelQuotation.Numbered.equality_tokens])
            (by native_decide)
            (FirstOrder.Derives.context_weaken_cons hStandard)
            hWholePoint
            (hConstructor := Term.check_admissible_complete <|
              implication_formula_code_term_admissible
                left right hLeft hRight)
  | membership =>
      have hLeftOpening :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            GodelQuotation.formula_code_left_opening_condition
              left :=
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp) <|
              fs_zfc_support_raw_derives_of_godel_quotation
                (GodelQuotation.gq_formula_code_member_implies_opening
                  left hLeft))
          hLeftMember
      unfold GodelQuotation.formula_code_left_opening_condition at hLeftOpening
      apply FirstOrder.Derives.disjElim hLeftOpening
      · let Δ : Context signature :=
          (((numₘ(0) ∈ₘ domₘ(left)) ∧ₘ
            ((left ·ₘ numₘ(0)) ≐ₘ
              numₘ(GodelQuotation.Numbered.logical_token
                .leftParenthesis)))) :: Γ
        have hLeftPoint :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              ((numₘ(0) ∈ₘ domₘ(left)) ∧ₘ
                ((left ·ₘ numₘ(0)) ≐ₘ
                  numₘ(GodelQuotation.Numbered.logical_token
                    .leftParenthesis))) :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hShift :=
          GodelQuotation.gq_implication_formula_left_point_at_standard_offset_of_theory
            (T := fs_zfc_support_raw_theory)
            (Γ := Δ)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            left right 0
            (FirstOrder.Derives.context_weaken_cons hLeftFinite)
            (FirstOrder.Derives.context_weaken_cons hRightFinite)
            (FirstOrder.Derives.conjElimLeft hLeftPoint)
            (hLeft := Term.check_admissible_complete hLeft)
            (hRight := Term.check_admissible_complete hRight)
        have hWholePoint :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              ((numₘ(1) ∈ₘ
                  domₘ(imp_codeₘ(left, right))) ∧ₘ
                ((imp_codeₘ(left, right) ·ₘ numₘ(1)) ≐ₘ
                  numₘ(GodelQuotation.Numbered.logical_token
                    .leftParenthesis))) :=
          FirstOrder.Derives.conjIntro
            (FirstOrder.Derives.conjElimLeft hShift)
            (Metatheory.Derives.equality_trans
              (FirstOrder.Derives.conjElimRight hShift)
              (FirstOrder.Derives.conjElimRight hLeftPoint))
        exact
          GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
            (T := fs_zfc_support_raw_theory)
            (Γ := Δ)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            tokens (imp_codeₘ(left, right)) 1
            (GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name leftDepth))
            (GodelQuotation.Numbered.logical_token
              .leftParenthesis)
            (by
              simp [tokens,
                CanonicalProjectTrace.canonical_project_atom_tokens,
                GodelQuotation.Numbered.membership_tokens])
            ((GodelQuotation.logical_token_ne_variable_token
              .leftParenthesis
              (GodelQuotation.bound_name leftDepth)).symm)
            (FirstOrder.Derives.context_weaken_cons hStandard)
            hWholePoint
            (hConstructor := Term.check_admissible_complete <|
              implication_formula_code_term_admissible
                left right hLeft hRight)
      · let Δ : Context signature :=
          (((numₘ(1) ∈ₘ domₘ(left)) ∧ₘ
            ((left ·ₘ numₘ(1)) ≐ₘ
              numₘ(GodelQuotation.Numbered.logical_token
                .leftParenthesis)))) :: Γ
        have hLeftPoint :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              ((numₘ(1) ∈ₘ domₘ(left)) ∧ₘ
                ((left ·ₘ numₘ(1)) ≐ₘ
                  numₘ(GodelQuotation.Numbered.logical_token
                    .leftParenthesis))) :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hShift :=
          GodelQuotation.gq_implication_formula_left_point_at_standard_offset_of_theory
            (T := fs_zfc_support_raw_theory)
            (Γ := Δ)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            left right 1
            (FirstOrder.Derives.context_weaken_cons hLeftFinite)
            (FirstOrder.Derives.context_weaken_cons hRightFinite)
            (FirstOrder.Derives.conjElimLeft hLeftPoint)
            (hLeft := Term.check_admissible_complete hLeft)
            (hRight := Term.check_admissible_complete hRight)
        have hWholePoint :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              ((numₘ(2) ∈ₘ
                  domₘ(imp_codeₘ(left, right))) ∧ₘ
                ((imp_codeₘ(left, right) ·ₘ numₘ(2)) ≐ₘ
                  numₘ(GodelQuotation.Numbered.logical_token
                    .leftParenthesis))) :=
          FirstOrder.Derives.conjIntro
            (FirstOrder.Derives.conjElimLeft hShift)
            (Metatheory.Derives.equality_trans
              (FirstOrder.Derives.conjElimRight hShift)
              (FirstOrder.Derives.conjElimRight hLeftPoint))
        exact
          GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
            (T := fs_zfc_support_raw_theory)
            (Γ := Δ)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            tokens (imp_codeₘ(left, right)) 2
            GodelQuotation.Numbered.membership_token
            (GodelQuotation.Numbered.logical_token
              .leftParenthesis)
            (by
              simp [tokens,
                CanonicalProjectTrace.canonical_project_atom_tokens,
                GodelQuotation.Numbered.membership_tokens])
            (by native_decide)
            (FirstOrder.Derives.context_weaken_cons hStandard)
            hWholePoint
            (hConstructor := Term.check_admissible_complete <|
              implication_formula_code_term_admissible
                left right hLeft hRight)

/-- 规范原子源码不可能满足否定构造分支。 -/
theorem fs_zfc_support_raw_canonical_atom_ne_negation_branch
    {Γ : Context signature}
    (kind : CanonicalProjectAtomKind)
    (leftDepth rightDepth : Nat)
    (body : SetTerm)
    (hBody : Term.Admissible body SetSort.set)
    (hBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        body ∈ₘ FormulaCodeₘ)
    (hShape :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            kind leftDepth rightDepth ≐ₘ
          neg_codeₘ(body)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let tokens :=
    CanonicalProjectTrace.canonical_project_atom_tokens
      kind leftDepth rightDepth
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          neg_codeₘ(body) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <| by
        simpa [tokens] using
          fs_zfc_support_raw_canonical_atom_standard_at
            (Γ := Γ) kind leftDepth rightDepth)
      hShape
  have hOpening :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.theory_weaken
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_godel_quotation hFormula)
        (GodelQuotation.gq_negation_formula_opening_inversion
          (Γ := Γ) body hBody))
      hBodyMember
  cases kind with
  | equality =>
      exact
        GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
          (T := fs_zfc_support_raw_theory)
          (Γ := Γ)
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          tokens (neg_codeₘ(body)) 1
          (GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name leftDepth))
          (GodelQuotation.Numbered.logical_token .negation)
          (by
            simp [tokens,
              CanonicalProjectTrace.canonical_project_atom_tokens,
              GodelQuotation.Numbered.equality_tokens])
          ((GodelQuotation.logical_token_ne_variable_token
            .negation
            (GodelQuotation.bound_name leftDepth)).symm)
          hStandard
          (FirstOrder.Derives.conjElimRight hOpening)
          (hConstructor := Term.check_admissible_complete <|
            negation_formula_code_term_admissible body hBody)
  | membership =>
      exact
        GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
          (T := fs_zfc_support_raw_theory)
          (Γ := Γ)
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          tokens (neg_codeₘ(body)) 1
          (GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name leftDepth))
          (GodelQuotation.Numbered.logical_token .negation)
          (by
            simp [tokens,
              CanonicalProjectTrace.canonical_project_atom_tokens,
              GodelQuotation.Numbered.membership_tokens])
          ((GodelQuotation.logical_token_ne_variable_token
            .negation
            (GodelQuotation.bound_name leftDepth)).symm)
          hStandard
          (FirstOrder.Derives.conjElimRight hOpening)
          (hConstructor := Term.check_admissible_complete <|
            negation_formula_code_term_admissible body hBody)
  | subset =>
      exact
        GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
          (T := fs_zfc_support_raw_theory)
          (Γ := Γ)
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          tokens (neg_codeₘ(body)) 0
          (GodelQuotation.Numbered.predicate_token
            1 RelationSymbol.subset.ctorIdx)
          (GodelQuotation.Numbered.logical_token
            .leftParenthesis)
          (by
            simp [tokens,
              CanonicalProjectTrace.canonical_project_atom_tokens,
              GodelQuotation.Numbered.predicate_application_tokens])
          (GodelQuotation.odd_token_ne_logical
            (GodelQuotation.predicate_token_odd
              1 RelationSymbol.subset.ctorIdx)
            .leftParenthesis)
          hStandard
          (FirstOrder.Derives.conjElimLeft hOpening)
          (hConstructor := Term.check_admissible_complete <|
            negation_formula_code_term_admissible body hBody)

/-- 规范原子源码不可能满足全称构造分支。 -/
theorem fs_zfc_support_raw_canonical_atom_ne_universal_branch
    {Γ : Context signature}
    (kind : CanonicalProjectAtomKind)
    (leftDepth rightDepth : Nat)
    (boundVariable body : SetTerm)
    (hBoundVariable :
      Term.Admissible boundVariable SetSort.set)
    (hBody : Term.Admissible body SetSort.set)
    (hBoundVariableMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        boundVariable ∈ₘ VarSymₘ)
    (hBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        body ∈ₘ FormulaCodeₘ)
    (hShape :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            kind leftDepth rightDepth ≐ₘ
          forall_codeₘ(boundVariable, body)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let tokens :=
    CanonicalProjectTrace.canonical_project_atom_tokens
      kind leftDepth rightDepth
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(boundVariable, body) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <| by
        simpa [tokens] using
          fs_zfc_support_raw_canonical_atom_standard_at
            (Γ := Γ) kind leftDepth rightDepth)
      hShape
  have hBodyCodeString :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        body ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            (GodelQuotation.gq_formula_code_member_implies_code_string
              body hBody))
      hBodyMember
  have hOpening :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            (GodelQuotation.gq_universal_formula_opening_inversion
              boundVariable body
              (hBoundVariable :=
                Term.check_admissible_complete hBoundVariable)
              (hBody :=
                Term.check_admissible_complete hBody)))
      (FirstOrder.Derives.conjIntro
        hBoundVariableMember hBodyCodeString)
  cases kind with
  | equality =>
      exact
        GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
          (T := fs_zfc_support_raw_theory)
          (Γ := Γ)
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          tokens (forall_codeₘ(boundVariable, body)) 1
          (GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name leftDepth))
          (GodelQuotation.Numbered.logical_token .universal)
          (by
            simp [tokens,
              CanonicalProjectTrace.canonical_project_atom_tokens,
              GodelQuotation.Numbered.equality_tokens])
          ((GodelQuotation.logical_token_ne_variable_token
            .universal
            (GodelQuotation.bound_name leftDepth)).symm)
          hStandard
          (FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight hOpening)
          (hConstructor := Term.check_admissible_complete <|
            universal_formula_code_term_admissible
              boundVariable body hBoundVariable hBody)
  | membership =>
      exact
        GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
          (T := fs_zfc_support_raw_theory)
          (Γ := Γ)
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          tokens (forall_codeₘ(boundVariable, body)) 1
          (GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name leftDepth))
          (GodelQuotation.Numbered.logical_token .universal)
          (by
            simp [tokens,
              CanonicalProjectTrace.canonical_project_atom_tokens,
              GodelQuotation.Numbered.membership_tokens])
          ((GodelQuotation.logical_token_ne_variable_token
            .universal
            (GodelQuotation.bound_name leftDepth)).symm)
          hStandard
          (FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight hOpening)
          (hConstructor := Term.check_admissible_complete <|
            universal_formula_code_term_admissible
              boundVariable body hBoundVariable hBody)
  | subset =>
      exact
        GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
          (T := fs_zfc_support_raw_theory)
          (Γ := Γ)
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          tokens (forall_codeₘ(boundVariable, body)) 0
          (GodelQuotation.Numbered.predicate_token
            1 RelationSymbol.subset.ctorIdx)
          (GodelQuotation.Numbered.logical_token
            .leftParenthesis)
          (by
            simp [tokens,
              CanonicalProjectTrace.canonical_project_atom_tokens,
              GodelQuotation.Numbered.predicate_application_tokens])
          (GodelQuotation.odd_token_ne_logical
            (GodelQuotation.predicate_token_odd
              1 RelationSymbol.subset.ctorIdx)
            .leftParenthesis)
          hStandard
          (FirstOrder.Derives.conjElimLeft hOpening)
          (hConstructor := Term.check_admissible_complete <|
            universal_formula_code_term_admissible
              boundVariable body hBoundVariable hBody)

/-- 规范 equality 源码不可能满足 membership 构造分支。 -/
theorem fs_zfc_support_raw_canonical_equality_ne_membership_branch
    {Γ : Context signature}
    (leftDepth rightDepth : Nat)
    (first last : SetTerm)
    (hFirst : Term.Admissible first SetSort.set)
    (hLast : Term.Admissible last SetSort.set)
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition first)
    (hFirstDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(first) ≐ₘ numₘ(1))
    (hLastFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition last)
    (hShape :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .equality leftDepth rightDepth ≐ₘ
          membership_atomic_formula_code_term first last) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let tokens :=
    CanonicalProjectTrace.canonical_project_atom_tokens
      .equality leftDepth rightDepth
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          membership_atomic_formula_code_term first last :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <| by
        simpa [tokens] using
          fs_zfc_support_raw_canonical_atom_standard_at
            (Γ := Γ) .equality leftDepth rightDepth)
      hShape
  exact
    GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      tokens
      (membership_atomic_formula_code_term first last)
      2
      (GodelQuotation.Numbered.logical_token .equality)
      GodelQuotation.Numbered.membership_token
      (by simp [tokens,
        CanonicalProjectTrace.canonical_project_atom_tokens,
        GodelQuotation.Numbered.equality_tokens])
      (by native_decide)
      hStandard
      (fs_zfc_support_raw_membership_atomic_middle_point
        first last hFirst hLast
        hFirstFinite hFirstDomain hLastFinite)
      (hConstructor := Term.check_admissible_complete <|
        binary_atomic_formula_code_term_admissible
          membership_symbol_code_term first last
          membership_symbol_code_term_admissible
          hFirst hLast)

/-- 规范 membership 源码不可能满足 equality 构造分支。 -/
theorem fs_zfc_support_raw_canonical_membership_ne_equality_branch
    {Γ : Context signature}
    (leftDepth rightDepth : Nat)
    (first last : SetTerm)
    (hFirst : Term.Admissible first SetSort.set)
    (hLast : Term.Admissible last SetSort.set)
    (hFirstCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] term_codeₘ(first))
    (hLastCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] term_codeₘ(last))
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition first)
    (hFirstDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(first) ≐ₘ numₘ(1))
    (hLastFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition last)
    (hShape :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .membership leftDepth rightDepth ≐ₘ
          eq_codeₘ(first, last)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let tokens :=
    CanonicalProjectTrace.canonical_project_atom_tokens
      .membership leftDepth rightDepth
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          eq_codeₘ(first, last) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <| by
        simpa [tokens] using
          fs_zfc_support_raw_canonical_atom_standard_at
            (Γ := Γ) .membership leftDepth rightDepth)
      hShape
  exact
    GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      tokens (eq_codeₘ(first, last)) 2
      GodelQuotation.Numbered.membership_token
      (GodelQuotation.Numbered.logical_token .equality)
      (by simp [tokens,
        CanonicalProjectTrace.canonical_project_atom_tokens,
        GodelQuotation.Numbered.membership_tokens])
      (by native_decide)
      hStandard
      (fs_zfc_support_raw_equality_atomic_middle_point
        first last hFirst hLast hFirstCode hLastCode
        hFirstFinite hFirstDomain hLastFinite)
      (hConstructor := Term.check_admissible_complete <|
        equality_formula_code_term_admissible
          first last hFirst hLast)

/-- 规范 equality 源码不可能满足 subset 谓词应用分支。 -/
theorem fs_zfc_support_raw_canonical_equality_ne_subset_branch
    {Γ : Context signature}
    (leftDepth rightDepth : Nat)
    (first last : SetTerm)
    (hFirst : Term.Admissible first SetSort.set)
    (hLast : Term.Admissible last SetSort.set)
    (hReserved :
      ReservedIdsFresh [0, 1, 2] [first, last])
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition first)
    (hLastFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition last)
    (hShape :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .equality leftDepth rightDepth ≐ₘ
          project_subset_atomic_code_term first last) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let tokens :=
    CanonicalProjectTrace.canonical_project_atom_tokens
      .equality leftDepth rightDepth
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          project_subset_atomic_code_term first last :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <| by
        simpa [tokens] using
          fs_zfc_support_raw_canonical_atom_standard_at
            (Γ := Γ) .equality leftDepth rightDepth)
      hShape
  exact
    GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      tokens (project_subset_atomic_code_term first last) 0
      (GodelQuotation.Numbered.logical_token .leftParenthesis)
      (GodelQuotation.Numbered.predicate_token
        1 RelationSymbol.subset.ctorIdx)
      (by simp [tokens,
        CanonicalProjectTrace.canonical_project_atom_tokens,
        GodelQuotation.Numbered.equality_tokens])
      (by
        exact GodelQuotation.odd_token_ne_logical
          (GodelQuotation.predicate_token_odd
            1 RelationSymbol.subset.ctorIdx)
          .leftParenthesis |>.symm)
      hStandard
      (fs_zfc_support_raw_project_subset_atomic_head_point
        first last hFirst hLast hReserved
        hFirstFinite hLastFinite)
      (hConstructor := Term.check_admissible_complete <|
        canonical_project_subset_atomic_code_term_admissible
          first last hFirst hLast)

/-- 规范 membership 源码不可能满足 subset 谓词应用分支。 -/
theorem fs_zfc_support_raw_canonical_membership_ne_subset_branch
    {Γ : Context signature}
    (leftDepth rightDepth : Nat)
    (first last : SetTerm)
    (hFirst : Term.Admissible first SetSort.set)
    (hLast : Term.Admissible last SetSort.set)
    (hReserved :
      ReservedIdsFresh [0, 1, 2] [first, last])
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition first)
    (hLastFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition last)
    (hShape :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .membership leftDepth rightDepth ≐ₘ
          project_subset_atomic_code_term first last) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let tokens :=
    CanonicalProjectTrace.canonical_project_atom_tokens
      .membership leftDepth rightDepth
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          project_subset_atomic_code_term first last :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <| by
        simpa [tokens] using
          fs_zfc_support_raw_canonical_atom_standard_at
            (Γ := Γ) .membership leftDepth rightDepth)
      hShape
  exact
    GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      tokens (project_subset_atomic_code_term first last) 0
      (GodelQuotation.Numbered.logical_token .leftParenthesis)
      (GodelQuotation.Numbered.predicate_token
        1 RelationSymbol.subset.ctorIdx)
      (by simp [tokens,
        CanonicalProjectTrace.canonical_project_atom_tokens,
        GodelQuotation.Numbered.membership_tokens])
      (by
        exact GodelQuotation.odd_token_ne_logical
          (GodelQuotation.predicate_token_odd
            1 RelationSymbol.subset.ctorIdx)
          .leftParenthesis |>.symm)
      hStandard
      (fs_zfc_support_raw_project_subset_atomic_head_point
        first last hFirst hLast hReserved
        hFirstFinite hLastFinite)
      (hConstructor := Term.check_admissible_complete <|
        canonical_project_subset_atomic_code_term_admissible
          first last hFirst hLast)

/-- 规范 subset 源码不可能满足 equality 构造分支。 -/
theorem fs_zfc_support_raw_canonical_subset_ne_equality_branch
    {Γ : Context signature}
    (leftDepth rightDepth : Nat)
    (first last : SetTerm)
    (hFirst : Term.Admissible first SetSort.set)
    (hLast : Term.Admissible last SetSort.set)
    (hFirstCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] term_codeₘ(first))
    (hLastCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] term_codeₘ(last))
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition first)
    (hLastFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition last)
    (hShape :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .subset leftDepth rightDepth ≐ₘ
          eq_codeₘ(first, last)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let tokens :=
    CanonicalProjectTrace.canonical_project_atom_tokens
      .subset leftDepth rightDepth
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          eq_codeₘ(first, last) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <| by
        simpa [tokens] using
          fs_zfc_support_raw_canonical_atom_standard_at
            (Γ := Γ) .subset leftDepth rightDepth)
      hShape
  exact
    GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      tokens (eq_codeₘ(first, last)) 0
      (GodelQuotation.Numbered.predicate_token
        1 RelationSymbol.subset.ctorIdx)
      (GodelQuotation.Numbered.logical_token .leftParenthesis)
      (by simp [tokens,
        CanonicalProjectTrace.canonical_project_atom_tokens,
        GodelQuotation.Numbered.predicate_application_tokens])
      (GodelQuotation.odd_token_ne_logical
        (GodelQuotation.predicate_token_odd
          1 RelationSymbol.subset.ctorIdx)
        .leftParenthesis)
      hStandard
      (by
        have hMiddleFinite :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              finite_sequence_condition
                equality_symbol_code_term :=
          FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp) <|
              fs_zfc_support_raw_derives_of_godel_quotation <|
                GodelQuotation.gq_logical_symbol_code_finite_sequence
                  .equality
        have hRawPoint :=
          GodelQuotation.gq_bracketed_three_part_left_parenthesis_point_of_theory
            (T := fs_zfc_support_raw_theory)
            (Γ := Γ)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            first equality_symbol_code_term last
            hFirstFinite hMiddleFinite hLastFinite
            (hFirst := Term.check_admissible_complete hFirst)
            (hLast := Term.check_admissible_complete hLast)
        exact
          GodelQuotation.gq_point_inversion_of_equality_of_theory
            (eq_codeₘ(first, last))
            (equality_atomic_formula_code_term first last)
            (numₘ(0))
            (numₘ(GodelQuotation.Numbered.logical_token
              .leftParenthesis))
            (fs_zfc_support_raw_equality_code_eq_raw_of_term_codes
              first last hFirst hLast hFirstCode hLastCode)
            hRawPoint
            (hLeft := Term.check_admissible_complete <|
              equality_formula_code_term_admissible
                first last hFirst hLast)
            (hRight := Term.check_admissible_complete <|
              binary_atomic_formula_code_term_admissible
                equality_symbol_code_term first last
                (logical_symbol_code_term_admissible .equality)
                hFirst hLast))
      (hConstructor := Term.check_admissible_complete <|
        equality_formula_code_term_admissible
          first last hFirst hLast)

/-- 规范 subset 源码不可能满足 membership 构造分支。 -/
theorem fs_zfc_support_raw_canonical_subset_ne_membership_branch
    {Γ : Context signature}
    (leftDepth rightDepth : Nat)
    (first last : SetTerm)
    (hFirst : Term.Admissible first SetSort.set)
    (hLast : Term.Admissible last SetSort.set)
    (hFirstFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition first)
    (hLastFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition last)
    (hShape :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            .subset leftDepth rightDepth ≐ₘ
          membership_atomic_formula_code_term first last) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let tokens :=
    CanonicalProjectTrace.canonical_project_atom_tokens
      .subset leftDepth rightDepth
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          membership_atomic_formula_code_term first last :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <| by
        simpa [tokens] using
          fs_zfc_support_raw_canonical_atom_standard_at
            (Γ := Γ) .subset leftDepth rightDepth)
      hShape
  exact
    GodelQuotation.gq_standard_token_sequence_falsum_of_point_mismatch_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      tokens
      (membership_atomic_formula_code_term first last) 0
      (GodelQuotation.Numbered.predicate_token
        1 RelationSymbol.subset.ctorIdx)
      (GodelQuotation.Numbered.logical_token .leftParenthesis)
      (by simp [tokens,
        CanonicalProjectTrace.canonical_project_atom_tokens,
        GodelQuotation.Numbered.predicate_application_tokens])
      (GodelQuotation.odd_token_ne_logical
        (GodelQuotation.predicate_token_odd
          1 RelationSymbol.subset.ctorIdx)
        .leftParenthesis)
      hStandard
      (by
        have hMiddleFinite :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              finite_sequence_condition
                membership_symbol_code_term :=
          FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp) <|
              fs_zfc_support_raw_derives_of_godel_quotation <|
                GodelQuotation.gq_finite_sequence_of_eq_standard_token_sequence
                  membership_symbol_code_term
                  [GodelQuotation.Numbered.membership_token]
                  membership_symbol_code_eq_standard_token_sequence
        simpa [membership_atomic_formula_code_term] using
          GodelQuotation.gq_bracketed_three_part_left_parenthesis_point_of_theory
            (T := fs_zfc_support_raw_theory)
            (Γ := Γ)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            first membership_symbol_code_term last
            hFirstFinite hMiddleFinite hLastFinite
            (hFirst := Term.check_admissible_complete hFirst)
            (hLast := Term.check_admissible_complete hLast))
      (hConstructor := Term.check_admissible_complete <|
        binary_atomic_formula_code_term_admissible
          membership_symbol_code_term first last
          membership_symbol_code_term_admissible
          hFirst hLast)

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
