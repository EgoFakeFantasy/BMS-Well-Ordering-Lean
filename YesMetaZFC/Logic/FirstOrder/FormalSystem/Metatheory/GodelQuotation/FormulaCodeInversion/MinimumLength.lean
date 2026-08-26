import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TermCodeInversion.Opening

/-!
# 公式码的最小长度反演

本模块证明完整公式码的定义域同时包含 `0` 与 `1`。证明只反演五类语法构造：

* 二元原子的第二位来自非空左项；
* 蕴含的第二位来自非空左子公式；
* 谓词应用、否定与全称构造已有固定前两位证书。

全程只使用对象层有限序列、最小闭包与等式运输。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 公式码至少具有前两个位置。 -/
def formula_code_minimum_domain_condition
    (code : SetTerm) : SetFormula :=
  (numₘ(0) ∈ₘ domₘ(code)) ∧ₘ
    (numₘ(1) ∈ₘ domₘ(code))

theorem formula_code_minimum_domain_condition_admissible
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (formula_code_minimum_domain_condition code) := by
  unfold formula_code_minimum_domain_condition
  prove_admissible

theorem
    formula_code_minimum_domain_condition_fresh
    (code : SetTerm) (id : FreeVarId)
    (hFresh :
      (SetSort.set, id) ∉ Term.freeSupport code) :
    (SetSort.set, id) ∉
      Formula.freeSupport
        (formula_code_minimum_domain_condition code) := by
  simp only [formula_code_minimum_domain_condition,
    Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList,
    finite_numeral_term_freeSupport,
    List.nil_append, List.append_nil]
  intro hMember
  rcases List.mem_append.mp hMember with
    hMember | hMember <;> exact hFresh hMember

private theorem formula_code_zero_domain_fresh
    (code : SetTerm) (id : FreeVarId)
    (hFresh :
      (SetSort.set, id) ∉ Term.freeSupport code) :
    (SetSort.set, id) ∉
      Formula.freeSupport
        (numₘ(0) ∈ₘ domₘ(code)) := by
  simp [Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList,
    finite_numeral_term_freeSupport, hFresh]

private theorem gq_formula_minimum_length_theory_fresh
    (id : FreeVarId) :
    ∀ formula, godel_quotation_theory formula →
      (SetSort.set, id) ∉
        Formula.freeSupport formula := by
  intro formula hFormula
  rw [(godel_quotation_theory_sentence hFormula).2]
  exact List.not_mem_nil

/-- 构造码的前两个定义域成员沿代码等式运输到目标码。 -/
theorem gq_formula_minimum_domain_transport
    {Γ : Context signature}
    (code constructor : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hConstructor :
      Term.Admissible constructor SetSort.set)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ constructor)
    (hMinimum :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_minimum_domain_condition
          constructor) :
    Γ ⊢ₘ[godel_quotation_theory]
      formula_code_minimum_domain_condition code := by
  have hDomainEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ domₘ(constructor) :=
    domain_term_congr_of_equality
      code constructor hCode hConstructor hEquality
  unfold formula_code_minimum_domain_condition at *
  exact FirstOrder.Derives.conjIntro
    (FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(0)) (domₘ(code)) (domₘ(constructor))
        (finite_numeral_term_admissible 0)
        (domain_term_admissible code hCode)
        (domain_term_admissible constructor hConstructor)
        hDomainEquality)
      (FirstOrder.Derives.conjElimLeft hMinimum))
    (FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(1)) (domₘ(code)) (domₘ(constructor))
        (finite_numeral_term_admissible 1)
        (domain_term_admissible code hCode)
        (domain_term_admissible constructor hConstructor)
        hDomainEquality)
      (FirstOrder.Derives.conjElimRight hMinimum))

/-- 单个定义域成员沿代码等式运输。 -/
theorem gq_formula_domain_member_transport
    {Γ : Context signature}
    (code constructor index : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hConstructor :
      Term.Admissible constructor SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ constructor)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        index ∈ₘ domₘ(constructor)) :
    Γ ⊢ₘ[godel_quotation_theory]
      index ∈ₘ domₘ(code) := by
  have hDomainEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ domₘ(constructor) :=
    domain_term_congr_of_equality
      code constructor hCode hConstructor hEquality
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      index (domₘ(code)) (domₘ(constructor))
      hIndex
      (domain_term_admissible code hCode)
      (domain_term_admissible constructor hConstructor)
      hDomainEquality)
    hMember

/--
二元原子构造至少具有前两个位置。第二位由长度一左括号之后的左项零位平移得到。
-/
theorem gq_binary_atomic_formula_minimum_domain
    {Γ : Context signature}
    (relation left right : SetTerm)
    (hRelation :
      Term.Admissible relation SetSort.set)
    (hLeft :
      Term.Admissible left SetSort.set)
    (hRight :
      Term.Admissible right SetSort.set)
    (hRelationFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition relation)
    (hLeftFresh :
      ReservedIdsFresh
        [200, 201, 210, 211, 212, 213, 610]
        [left]) :
    Γ ⊢ₘ[godel_quotation_theory]
      (term_codeₘ(left) ∧ₘ term_codeₘ(right)) ⟶ₘ
        formula_code_minimum_domain_condition
          (binary_atomic_formula_code_term
            relation left right) := by
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  let prefixCode : SetTerm :=
    leftParenthesis ⌢ₘ left
  let precondition : SetFormula :=
    term_codeₘ(left) ∧ₘ term_codeₘ(right)
  let Δ : Context signature := precondition :: Γ
  have hPreconditionAdmissible :
      Formula.Admissible precondition := by
    dsimp only [precondition]
    prove_admissible
  nd_apply FirstOrder.Derives.impIntro
  have hPrecondition :
      Δ ⊢ₘ[godel_quotation_theory]
        precondition :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        hPreconditionAdmissible)
  have hLeftPredicate :
      Δ ⊢ₘ[godel_quotation_theory]
        term_codeₘ(left) :=
    FirstOrder.Derives.conjElimLeft hPrecondition
  have hLeftMember :
      Δ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ]) <|
          gq_term_code_definition_instance left hLeft)
      hLeftPredicate
  have hLeftZero :
      Δ ⊢ₘ[godel_quotation_theory]
        numₘ(0) ∈ₘ domₘ(left) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ]) <|
          gq_term_code_member_implies_zero_mem_domain_of_fresh
            left hLeft hLeftFresh)
      hLeftMember
  have hLeftFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    gq_term_code_implies_finite_sequence
      left hLeft hLeftPredicate
  have hRightFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right :=
    gq_term_code_implies_finite_sequence
      right hRight
      (FirstOrder.Derives.conjElimRight
        hPrecondition)
  have hRelationFiniteΔ :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition relation :=
    FirstOrder.Derives.context_weaken_cons
      hRelationFinite
  have hLeftParenthesisFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .leftParenthesis
  have hRightParenthesisFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .rightParenthesis
  have hLeftParenthesisDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Δ) .leftParenthesis
  have hPrefixPointRaw :=
    gq_concatenation_right_point_at_numeral_offset
      leftParenthesis left 1 0
      hLeftParenthesisFinite hLeftFinite
      hLeftParenthesisDomain hLeftZero
  have hPrefixPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1) ∈ₘ domₘ(prefixCode)) ∧ₘ
          ((prefixCode ·ₘ numₘ(1)) ≐ₘ
            (left ·ₘ numₘ(0)))) := by
    simpa [prefixCode] using hPrefixPointRaw
  have hPrefixFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        leftParenthesis left
        hLeftParenthesisFinite hLeftFinite
  have hOnePoint :=
    gq_four_part_left_point
      prefixCode relation right rightParenthesis
      (numₘ(1)) (left ·ₘ numₘ(0))
      hPrefixFinite hRelationFiniteΔ
      hRightFinite hRightParenthesisFinite
      (FirstOrder.Derives.conjElimLeft
        hPrefixPoint)
      (FirstOrder.Derives.conjElimRight
        hPrefixPoint)
  have hZeroPoint :=
    FirstOrder.Derives.impElim
      (gq_binary_atomic_formula_opening_inversion
        (Γ := Δ)
        relation left right
        hRelation hLeft hRight
        hRelationFiniteΔ)
      hPrecondition
  unfold formula_code_minimum_domain_condition
  simpa [prefixCode, leftParenthesis,
    rightParenthesis,
    binary_atomic_formula_code_term] using
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjElimLeft hZeroPoint)
      (FirstOrder.Derives.conjElimLeft hOnePoint)

/--
蕴含构造的第一位来自长度一左括号之后的左子公式零位。
-/
theorem gq_implication_formula_one_mem_domain
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hMembers :
      Γ ⊢ₘ[godel_quotation_theory]
        (left ∈ₘ FormulaCodeₘ) ∧ₘ
          (right ∈ₘ FormulaCodeₘ))
    (hLeftZero :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(0) ∈ₘ domₘ(left)) :
    Γ ⊢ₘ[godel_quotation_theory]
      numₘ(1) ∈ₘ
        domₘ(imp_codeₘ(left, right)) := by
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let implicationSymbol : SetTerm :=
    logical_symbol_code_term .implication
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  let prefixCode : SetTerm :=
    leftParenthesis ⌢ₘ left
  let rawCode : SetTerm :=
    ((prefixCode ⌢ₘ implicationSymbol) ⌢ₘ right) ⌢ₘ
      rightParenthesis
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    gq_formula_code_member_implies_finite_sequence
      left hLeft
      (FirstOrder.Derives.conjElimLeft hMembers)
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right :=
    gq_formula_code_member_implies_finite_sequence
      right hRight
      (FirstOrder.Derives.conjElimRight hMembers)
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hImplicationFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition implicationSymbol := by
    simpa [implicationSymbol] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .implication
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hLeftParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hPrefixPointRaw :=
    gq_concatenation_right_point_at_numeral_offset
      leftParenthesis left 1 0
      hLeftParenthesisFinite hLeftFinite
      hLeftParenthesisDomain hLeftZero
  have hPrefixPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1) ∈ₘ domₘ(prefixCode)) ∧ₘ
          ((prefixCode ·ₘ numₘ(1)) ≐ₘ
            (left ·ₘ numₘ(0)))) := by
    simpa [prefixCode] using hPrefixPointRaw
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        leftParenthesis left
        hLeftParenthesisFinite hLeftFinite
  have hOnePoint :=
    gq_four_part_left_point
      prefixCode implicationSymbol
      right rightParenthesis
      (numₘ(1)) (left ·ₘ numₘ(0))
      hPrefixFinite hImplicationFinite
      hRightFinite hRightParenthesisFinite
      (FirstOrder.Derives.conjElimLeft hPrefixPoint)
      (FirstOrder.Derives.conjElimRight hPrefixPoint)
  have hRawOne :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(1) ∈ₘ domₘ(rawCode) := by
    simpa [rawCode] using
      FirstOrder.Derives.conjElimLeft hOnePoint
  have hRawCode :
      Term.Admissible rawCode SetSort.set := by
    simpa [rawCode, prefixCode,
      leftParenthesis, implicationSymbol,
      rightParenthesis,
      implication_formula_string_term] using
      implication_formula_string_term_admissible
        left right hLeft hRight
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        imp_codeₘ(left, right) ≐ₘ rawCode := by
    have hDefinition :
        Γ ⊢ₘ[godel_quotation_theory]
          implication_formula_code_definition_instance
            left right (imp_codeₘ(left, right)) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_formula_constructor <|
            implication_formula_code_definition_instance_derives
              left right (imp_codeₘ(left, right))
              hLeft hRight
              (implication_formula_code_term_admissible
                left right hLeft hRight)
    have hReflexive :
        Γ ⊢ₘ[godel_quotation_theory]
          imp_codeₘ(left, right) ≐ₘ
            imp_codeₘ(left, right) :=
      FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (imp_codeₘ(left, right))
    simpa [rawCode, prefixCode,
      leftParenthesis, implicationSymbol,
      rightParenthesis,
      implication_formula_code_definition_instance,
      implication_formula_string_term] using
      FirstOrder.Derives.iffElimRight
        hDefinition hReflexive
  exact gq_formula_domain_member_transport
    (imp_codeₘ(left, right)) rawCode (numₘ(1))
    (implication_formula_code_term_admissible
      left right hLeft hRight)
    hRawCode (finite_numeral_term_admissible 1)
    hCodeRaw hRawOne

/--
二元原子定义条件至少产生两个位置。消去本征元与定义内部的 `233/234` 分离，防止
后续子项反演被保留编号捕获。
-/
private theorem
    gq_binary_atomic_formula_condition_implies_minimum_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [233, 234] [code]) :
    ⊢ₘ[godel_quotation_theory]
      binary_atomic_formula_code_condition code ⟶ₘ
        formula_code_minimum_domain_condition code := by
  let left : SetTerm := x#233
  let right : SetTerm := x#234
  let equalityShape : SetFormula :=
    code ≐ₘ
      equality_atomic_formula_code_term left right
  let membershipShape : SetFormula :=
    code ≐ₘ
      membership_atomic_formula_code_term left right
  let body : SetFormula :=
    ((term_codeₘ(left) ∧ₘ term_codeₘ(right)) ∧ₘ
      (equalityShape ∨ₘ membershipShape))
  let inner : SetFormula :=
    ∃ₘ[SetSort.set, 234], body
  have hLeft :
      Term.Admissible left SetSort.set := by
    simpa [left] using set_variable_admissible 233
  have hRight :
      Term.Admissible right SetSort.set := by
    simpa [right] using set_variable_admissible 234
  have hEqualityCode :
      Term.Admissible
        (equality_atomic_formula_code_term left right)
        SetSort.set :=
    binary_atomic_formula_code_term_admissible
      equality_symbol_code_term left right
      (logical_symbol_code_term_admissible .equality)
      hLeft hRight
  have hMembershipCode :
      Term.Admissible
        (membership_atomic_formula_code_term left right)
        SetSort.set :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term left right
      membership_symbol_code_term_admissible
      hLeft hRight
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body, equalityShape, membershipShape]
    prove_admissible
  have hLeftFresh :
      ReservedIdsFresh
        [200, 201, 210, 211, 212, 213, 610]
        [left] := by
    simpa [left] using
      reserved_ids_fresh_cons_variable
        233
        (by
          intro id hId
          simp only [List.mem_cons,
            List.not_mem_nil, or_false] at hId
          rcases hId with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              decide)
        (reserved_ids_fresh_nil
          [200, 201, 210, 211, 212, 213, 610])
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        body ⟶ₘ
          formula_code_minimum_domain_condition code := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [body]
    have hBody :
        Γ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hBodyAdmissible)
    have hTerms :
        Γ ⊢ₘ[godel_quotation_theory]
          term_codeₘ(left) ∧ₘ term_codeₘ(right) :=
      FirstOrder.Derives.conjElimLeft hBody
    have hShape :
        Γ ⊢ₘ[godel_quotation_theory]
          equalityShape ∨ₘ membershipShape :=
      FirstOrder.Derives.conjElimRight hBody
    apply FirstOrder.Derives.disjElim hShape
    · let Δ : Context signature := equalityShape :: Γ
      have hEquality :
          Δ ⊢ₘ[godel_quotation_theory]
            code ≐ₘ
              equality_atomic_formula_code_term
                left right := by
        simpa [equalityShape] using
          (FirstOrder.Derives.assumption
            (T := godel_quotation_theory)
            (Γ := Δ) (φ := equalityShape)
            (by simp [Δ]))
      have hMinimum :
          Δ ⊢ₘ[godel_quotation_theory]
            formula_code_minimum_domain_condition
              (equality_atomic_formula_code_term
                left right) :=
        FirstOrder.Derives.impElim
          (gq_binary_atomic_formula_minimum_domain
            (Γ := Δ)
            equality_symbol_code_term left right
            (logical_symbol_code_term_admissible .equality)
            hLeft hRight
            (gq_logical_symbol_code_finite_sequence
              (Γ := Δ) .equality)
            hLeftFresh)
          (FirstOrder.Derives.context_weaken_cons hTerms)
      exact gq_formula_minimum_domain_transport
        code
        (equality_atomic_formula_code_term left right)
        hCode hEqualityCode hEquality hMinimum
    · let Δ : Context signature := membershipShape :: Γ
      have hEquality :
          Δ ⊢ₘ[godel_quotation_theory]
            code ≐ₘ
              membership_atomic_formula_code_term
                left right := by
        simpa [membershipShape] using
          (FirstOrder.Derives.assumption
            (T := godel_quotation_theory)
            (Γ := Δ) (φ := membershipShape)
            (by simp [Δ]))
      have hRelationFinite :
          Δ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition
              membership_symbol_code_term :=
        gq_finite_sequence_of_eq_standard_token_sequence
          membership_symbol_code_term
          [Numbered.membership_token]
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ) (by simp [Δ])
            membership_symbol_code_eq_standard_token_sequence)
      have hMinimum :
          Δ ⊢ₘ[godel_quotation_theory]
            formula_code_minimum_domain_condition
              (membership_atomic_formula_code_term
                left right) :=
        FirstOrder.Derives.impElim
          (gq_binary_atomic_formula_minimum_domain
            (Γ := Δ)
            membership_symbol_code_term left right
            membership_symbol_code_term_admissible
            hLeft hRight hRelationFinite hLeftFresh)
          (FirstOrder.Derives.context_weaken_cons hTerms)
      exact gq_formula_minimum_domain_transport
        code
        (membership_atomic_formula_code_term left right)
        hCode hMembershipCode hEquality hMinimum
  have hConclusionFresh
      (id : FreeVarId)
      (hId : id ∈ [233, 234]) :
      (SetSort.set, id) ∉
        Formula.freeSupport
          (formula_code_minimum_domain_condition code) := by
    have hCodeFresh :
        (SetSort.set, id) ∉
          Term.freeSupport code :=
      hFresh code (by simp) id hId
    simp only [formula_code_minimum_domain_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      List.nil_append, List.append_nil]
    intro hMember
    rcases List.mem_append.mp hMember with
      hMember | hMember <;>
        exact hCodeFresh hMember
  have hAt234 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 234)
      (gq_formula_minimum_length_theory_fresh 234)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 234 (by simp))
      hPoint
  have hAt233 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 233)
      (gq_formula_minimum_length_theory_fresh 233)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 233 (by simp))
      hAt234
  simpa [binary_atomic_formula_code_condition,
    inner, body, equalityShape, membershipShape,
    left, right,
    Formula.closeFreeAt, Term.closeFreeAt,
    set_variable, set_bound_variable] using hAt233

/-- 一般谓词应用定义条件由固定的零位符号与第一位左括号给出最小长度。 -/
private theorem
    gq_predicate_application_condition_implies_minimum_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [230, 231, 232] [code]) :
    ⊢ₘ[godel_quotation_theory]
      predicate_application_code_condition code ⟶ₘ
        formula_code_minimum_domain_condition code := by
  let arity : SetTerm := x#230
  let symbolIndex : SetTerm := x#231
  let arguments : SetTerm := x#232
  let precondition : SetFormula :=
    (arity ∈ₘ ωₘ) ∧ₘ
      ((symbolIndex ∈ₘ ωₘ) ∧ₘ
        ((arguments ∈ₘ TermSeqₘ) ∧ₘ
          (domₘ(arguments) ≐ₘ Sₘ(arity))))
  let shape : SetFormula :=
    code ≐ₘ
      predicate_application_code_term
        arity symbolIndex arguments
  let body : SetFormula :=
    precondition ∧ₘ shape
  let inner₂ : SetFormula :=
    ∃ₘ[SetSort.set, 232], body
  let inner₁ : SetFormula :=
    ∃ₘ[SetSort.set, 231], inner₂
  have hArity :
      Term.Admissible arity SetSort.set := by
    simpa [arity] using set_variable_admissible 230
  have hIndex :
      Term.Admissible symbolIndex SetSort.set := by
    simpa [symbolIndex] using set_variable_admissible 231
  have hArguments :
      Term.Admissible arguments SetSort.set := by
    simpa [arguments] using set_variable_admissible 232
  have hConstructor :
      Term.Admissible
        (predicate_application_code_term
          arity symbolIndex arguments)
        SetSort.set :=
    predicate_application_code_term_admissible
      arity symbolIndex arguments
      hArity hIndex hArguments
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body, precondition, shape]
    prove_admissible
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        body ⟶ₘ
          formula_code_minimum_domain_condition code := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [body]
    have hBody :
        Γ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hBodyAdmissible)
    have hPrecondition :
        Γ ⊢ₘ[godel_quotation_theory]
          precondition :=
      FirstOrder.Derives.conjElimLeft hBody
    have hArgumentsMember :
        Γ ⊢ₘ[godel_quotation_theory]
          arguments ∈ₘ TermSeqₘ :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight
            hPrecondition
    have hEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ
            predicate_application_code_term
              arity symbolIndex arguments := by
      simpa [shape] using
        FirstOrder.Derives.conjElimRight hBody
    have hOpening :=
      FirstOrder.Derives.impElim
        (gq_predicate_application_formula_opening_inversion
          (Γ := Γ)
          arity symbolIndex arguments
          hArity hIndex hArguments
          (by
            simpa [arity, symbolIndex] using
              reserved_ids_fresh_cons_variable
                230
                (by
                  intro id hId
                  simp only [List.mem_cons,
                    List.not_mem_nil, or_false] at hId
                  rcases hId with rfl | rfl | rfl <;>
                    decide)
                (reserved_ids_fresh_cons_variable
                  231
                  (by
                    intro id hId
                    simp only [List.mem_cons,
                      List.not_mem_nil, or_false] at hId
                    rcases hId with rfl | rfl | rfl <;>
                      decide)
                  (reserved_ids_fresh_nil [0, 1, 2])))
          (by native_decide))
        hArgumentsMember
    have hMinimum :
        Γ ⊢ₘ[godel_quotation_theory]
          formula_code_minimum_domain_condition
            (predicate_application_code_term
              arity symbolIndex arguments) := by
      unfold formula_code_minimum_domain_condition
      exact FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimLeft hOpening)
        (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hOpening)
    exact gq_formula_minimum_domain_transport
      code
      (predicate_application_code_term
        arity symbolIndex arguments)
      hCode hConstructor hEquality hMinimum
  have hConclusionFresh
      (id : FreeVarId)
      (hId : id ∈ [230, 231, 232]) :
      (SetSort.set, id) ∉
        Formula.freeSupport
          (formula_code_minimum_domain_condition code) := by
    have hCodeFresh :
        (SetSort.set, id) ∉
          Term.freeSupport code :=
      hFresh code (by simp) id hId
    simp only [formula_code_minimum_domain_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      List.nil_append, List.append_nil]
    intro hMember
    rcases List.mem_append.mp hMember with
      hMember | hMember <;>
        exact hCodeFresh hMember
  have hAt232 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 232)
      (gq_formula_minimum_length_theory_fresh 232)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 232 (by simp))
      hPoint
  have hAt231 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 231)
      (gq_formula_minimum_length_theory_fresh 231)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 231 (by simp))
      hAt232
  have hAt230 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 230)
      (gq_formula_minimum_length_theory_fresh 230)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 230 (by simp))
      hAt231
  simpa [predicate_application_code_condition,
    inner₁, inner₂, body, precondition, shape,
    arity, symbolIndex, arguments,
    Formula.closeFreeAt, Term.closeFreeAt,
    set_variable, set_bound_variable] using hAt230

/-- 原子公式条件的两个构造分支统一给出前两个定义域位置。 -/
private theorem
    gq_atomic_formula_condition_implies_minimum_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234] [code]) :
    ⊢ₘ[godel_quotation_theory]
      atomic_formula_code_condition code ⟶ₘ
        formula_code_minimum_domain_condition code := by
  have hConditionAdmissible :
      Formula.Admissible
        (atomic_formula_code_condition code) := by
    prove_admissible
  have hBinaryFresh :
      ReservedIdsFresh [233, 234] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with rfl | rfl <;> simp
  have hPredicateFresh :
      ReservedIdsFresh [230, 231, 232] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with rfl | rfl | rfl <;> simp
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [atomic_formula_code_condition code]
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        atomic_formula_code_condition code :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hConditionAdmissible)
  unfold atomic_formula_code_condition at hCondition
  apply FirstOrder.Derives.disjElim hCondition
  · exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := [])
        (Δ := binary_atomic_formula_code_condition code :: Γ)
        (by simp)
        (gq_binary_atomic_formula_condition_implies_minimum_domain
          code hCode hBinaryFresh))
      (FirstOrder.Derives.assumption (by simp))
  · exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := [])
        (Δ := predicate_application_code_condition code :: Γ)
        (by simp)
        (gq_predicate_application_condition_implies_minimum_domain
          code hCode hPredicateFresh))
      (FirstOrder.Derives.assumption (by simp))

/-- 原子公式集合成员至少具有前两个位置。 -/
theorem
    gq_atomic_formula_member_implies_minimum_domain_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234] [code]) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ AtomicCodeₘ) ⟶ₘ
        formula_code_minimum_domain_condition code := by
  have hMemberAdmissible :
      Formula.Admissible
        (code ∈ₘ AtomicCodeₘ) :=
    membership_formula_admissible
      hCode atomic_formula_code_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [code ∈ₘ AtomicCodeₘ]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ AtomicCodeₘ :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMemberAdmissible)
  have hAtomic :
      Γ ⊢ₘ[godel_quotation_theory]
        atomic_formula_codeₘ(code) :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_atomic_formula_code_set_definition_instance
            code hCode)
      hMember
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        atomic_formula_code_condition code :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_atomic_formula_code_definition_instance
            code hCode hFresh)
      hAtomic
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        gq_atomic_formula_condition_implies_minimum_domain
          code hCode hFresh)
    hCondition

/-- 闭原子公式码上的最小长度是精确新鲜度接口的直接推论。 -/
private theorem
    gq_atomic_formula_member_implies_minimum_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hClosed : Term.freeSupport code = []) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ AtomicCodeₘ) ⟶ₘ
        formula_code_minimum_domain_condition code :=
  gq_atomic_formula_member_implies_minimum_domain_of_fresh
    code hCode <|
      reserved_ids_fresh_cons_closed hClosed <|
        reserved_ids_fresh_nil
          [230, 231, 232, 233, 234]

/-- 否定生成分支的固定左括号与否定符号给出前两个位置。 -/
theorem
    gq_negation_generation_implies_minimum_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      (SetSort.set, 306) ∉
        Term.freeSupport code) :
    ⊢ₘ[godel_quotation_theory]
      (∃ₘ[SetSort.set, 306],
        ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
          (code ≐ₘ neg_codeₘ(x#306)))) ⟶ₘ
        formula_code_minimum_domain_condition code := by
  let source : SetTerm := x#306
  let shape : SetFormula :=
    code ≐ₘ neg_codeₘ(source)
  let body : SetFormula :=
    (source ∈ₘ FormulaCodeₘ) ∧ₘ shape
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 306], body
  have hSource :
      Term.Admissible source SetSort.set := by
    simpa [source] using set_variable_admissible 306
  have hConstructor :
      Term.Admissible (neg_codeₘ(source)) SetSort.set :=
    negation_formula_code_term_admissible
      source hSource
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body, shape]
    prove_admissible
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        body ⟶ₘ
          formula_code_minimum_domain_condition code := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [body]
    have hBody :
        Γ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hBodyAdmissible)
    have hMember :
        Γ ⊢ₘ[godel_quotation_theory]
          source ∈ₘ FormulaCodeₘ :=
      FirstOrder.Derives.conjElimLeft hBody
    have hEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ neg_codeₘ(source) := by
      simpa [shape] using
        FirstOrder.Derives.conjElimRight hBody
    have hOpening :=
      FirstOrder.Derives.impElim
        (gq_negation_formula_opening_inversion
          (Γ := Γ) source hSource)
        hMember
    have hMinimum :
        Γ ⊢ₘ[godel_quotation_theory]
          formula_code_minimum_domain_condition
            (neg_codeₘ(source)) := by
      unfold formula_code_minimum_domain_condition
      exact FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimLeft hOpening)
        (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hOpening)
    exact gq_formula_minimum_domain_transport
      code (neg_codeₘ(source))
      hCode hConstructor hEquality hMinimum
  change ⊢ₘ[godel_quotation_theory]
    condition ⟶ₘ
      formula_code_minimum_domain_condition code
  exact Metatheory.Derives.exists_imp_of_imp
    (T := godel_quotation_theory)
    (Γ := [])
    (sort := SetSort.set)
    (eigen := 306)
    (gq_formula_minimum_length_theory_fresh 306)
    (by
      intro formula hFormula
      cases hFormula)
    (formula_code_minimum_domain_condition_fresh
      code 306 hFresh)
    hPoint

/-- 蕴含生成分支无条件给出第零位左括号。 -/
theorem
    gq_implication_generation_implies_zero_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [307, 308] [code]) :
    ⊢ₘ[godel_quotation_theory]
      (∃ₘ[SetSort.set, 307],
        ∃ₘ[SetSort.set, 308],
          (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
            (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (code ≐ₘ imp_codeₘ(x#307, x#308)))) ⟶ₘ
        (numₘ(0) ∈ₘ domₘ(code)) := by
  let left : SetTerm := x#307
  let right : SetTerm := x#308
  let shape : SetFormula :=
    code ≐ₘ imp_codeₘ(left, right)
  let body : SetFormula :=
    ((left ∈ₘ FormulaCodeₘ) ∧ₘ
      (right ∈ₘ FormulaCodeₘ)) ∧ₘ shape
  let inner : SetFormula :=
    ∃ₘ[SetSort.set, 308], body
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 307], inner
  have hLeft :
      Term.Admissible left SetSort.set := by
    simpa [left] using set_variable_admissible 307
  have hRight :
      Term.Admissible right SetSort.set := by
    simpa [right] using set_variable_admissible 308
  have hConstructor :
      Term.Admissible
        (imp_codeₘ(left, right)) SetSort.set :=
    implication_formula_code_term_admissible
      left right hLeft hRight
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body, shape]
    prove_admissible
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        body ⟶ₘ (numₘ(0) ∈ₘ domₘ(code)) := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [body]
    have hBody :
        Γ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hBodyAdmissible)
    have hMembers :
        Γ ⊢ₘ[godel_quotation_theory]
          (left ∈ₘ FormulaCodeₘ) ∧ₘ
            (right ∈ₘ FormulaCodeₘ) :=
      FirstOrder.Derives.conjElimLeft hBody
    have hEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ imp_codeₘ(left, right) := by
      simpa [shape] using
        FirstOrder.Derives.conjElimRight hBody
    have hOpening :=
      FirstOrder.Derives.impElim
        (gq_implication_formula_opening_inversion
          (Γ := Γ) left right hLeft hRight)
        hMembers
    exact gq_formula_domain_member_transport
      code (imp_codeₘ(left, right)) (numₘ(0))
      hCode hConstructor
      (finite_numeral_term_admissible 0)
      hEquality
      (FirstOrder.Derives.conjElimLeft hOpening)
  change ⊢ₘ[godel_quotation_theory]
    condition ⟶ₘ (numₘ(0) ∈ₘ domₘ(code))
  have hAt308 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 308)
      (gq_formula_minimum_length_theory_fresh 308)
      (by
        intro formula hFormula
        cases hFormula)
      (formula_code_zero_domain_fresh
        code 308
        (hFresh code (by simp) 308 (by simp)))
      hPoint
  exact Metatheory.Derives.exists_imp_of_imp
    (T := godel_quotation_theory)
    (Γ := [])
    (sort := SetSort.set)
    (eigen := 307)
    (gq_formula_minimum_length_theory_fresh 307)
    (by
      intro formula hFormula
      cases hFormula)
    (formula_code_zero_domain_fresh
      code 307
      (hFresh code (by simp) 307 (by simp)))
    hAt308

/-- 全称生成分支的固定左括号与量词符号给出前两个位置。 -/
theorem
    gq_universal_generation_implies_minimum_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [309, 310] [code]) :
    ⊢ₘ[godel_quotation_theory]
      (∃ₘ[SetSort.set, 309],
        ∃ₘ[SetSort.set, 310],
          (((x#309 ∈ₘ VarSymₘ) ∧ₘ
            (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (code ≐ₘ
              forall_codeₘ(x#309, x#310)))) ⟶ₘ
        formula_code_minimum_domain_condition code := by
  let boundVariable : SetTerm := x#309
  let bodyCode : SetTerm := x#310
  let shape : SetFormula :=
    code ≐ₘ forall_codeₘ(boundVariable, bodyCode)
  let body : SetFormula :=
    ((boundVariable ∈ₘ VarSymₘ) ∧ₘ
      (bodyCode ∈ₘ FormulaCodeₘ)) ∧ₘ shape
  let inner : SetFormula :=
    ∃ₘ[SetSort.set, 310], body
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 309], inner
  have hVariable :
      Term.Admissible boundVariable SetSort.set := by
    simpa [boundVariable] using
      set_variable_admissible 309
  have hBodyCode :
      Term.Admissible bodyCode SetSort.set := by
    simpa [bodyCode] using
      set_variable_admissible 310
  have hConstructor :
      Term.Admissible
        (forall_codeₘ(boundVariable, bodyCode))
        SetSort.set :=
    universal_formula_code_term_admissible
      boundVariable bodyCode hVariable hBodyCode
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body, shape]
    prove_admissible
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        body ⟶ₘ
          formula_code_minimum_domain_condition code := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [body]
    have hBody :
        Γ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hBodyAdmissible)
    have hMembers :
        Γ ⊢ₘ[godel_quotation_theory]
          (boundVariable ∈ₘ VarSymₘ) ∧ₘ
            (bodyCode ∈ₘ FormulaCodeₘ) :=
      FirstOrder.Derives.conjElimLeft hBody
    have hVariableMember :=
      FirstOrder.Derives.conjElimLeft hMembers
    have hBodyMember :=
      FirstOrder.Derives.conjElimRight hMembers
    have hBodyCodeString :
        Γ ⊢ₘ[godel_quotation_theory]
          bodyCode ∈ₘ CodeStrₘ :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp [Γ]) <|
            gq_formula_code_member_implies_code_string
              bodyCode hBodyCode)
        hBodyMember
    have hEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ
            forall_codeₘ(boundVariable, bodyCode) := by
      simpa [shape] using
        FirstOrder.Derives.conjElimRight hBody
    have hOpening :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp [Γ]) <|
            gq_universal_formula_opening_inversion
              boundVariable bodyCode)
        (FirstOrder.Derives.conjIntro
          hVariableMember hBodyCodeString)
    have hMinimum :
        Γ ⊢ₘ[godel_quotation_theory]
          formula_code_minimum_domain_condition
            (forall_codeₘ(boundVariable, bodyCode)) := by
      unfold formula_code_minimum_domain_condition
      exact FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimLeft hOpening)
        (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight hOpening)
    exact gq_formula_minimum_domain_transport
      code
      (forall_codeₘ(boundVariable, bodyCode))
      hCode hConstructor hEquality hMinimum
  change ⊢ₘ[godel_quotation_theory]
    condition ⟶ₘ
      formula_code_minimum_domain_condition code
  have hAt310 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 310)
      (gq_formula_minimum_length_theory_fresh 310)
      (by
        intro formula hFormula
        cases hFormula)
      (formula_code_minimum_domain_condition_fresh
        code 310
        (hFresh code (by simp) 310 (by simp)))
      hPoint
  exact Metatheory.Derives.exists_imp_of_imp
    (T := godel_quotation_theory)
    (Γ := [])
    (sort := SetSort.set)
    (eigen := 309)
    (gq_formula_minimum_length_theory_fresh 309)
    (by
      intro formula hFormula
      cases hFormula)
    (formula_code_minimum_domain_condition_fresh
      code 309
      (hFresh code (by simp) 309 (by simp)))
    hAt310

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
