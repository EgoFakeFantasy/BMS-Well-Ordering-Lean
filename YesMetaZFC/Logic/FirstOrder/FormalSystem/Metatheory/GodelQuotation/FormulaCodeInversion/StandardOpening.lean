import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion

/-!
# 标准公式码的根开头反演

本模块把一步公式生成反演压缩为 parser 可直接消费的根开头条件：

* 等式、隶属、否定、蕴含和全称公式在第零位具有左括号；
* 一般谓词应用在第一位具有左括号。

随后标准 token 行只要两个位置都不是左括号，就能得到 `FormulaCodeₘ` 的闭否定。
整个证明只比较有限序列位置。
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

/--
公式码的根开头条件：第零位是左括号，或第一位是左括号。

第二个析取精确对应一般谓词应用；其余四类构造均落在第一个析取。
-/
def formula_code_left_opening_condition
    (code : SetTerm) : SetFormula :=
  ((numₘ(0) ∈ₘ domₘ(code)) ∧ₘ
      ((code ·ₘ numₘ(0)) ≐ₘ
        numₘ(Numbered.logical_token
          .leftParenthesis))) ∨ₘ
    ((numₘ(1) ∈ₘ domₘ(code)) ∧ₘ
      ((code ·ₘ numₘ(1)) ≐ₘ
        numₘ(Numbered.logical_token
          .leftParenthesis)))

theorem formula_code_left_opening_condition_admissible
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (formula_code_left_opening_condition code) := by
  unfold formula_code_left_opening_condition
  prove_admissible

private theorem formula_code_left_opening_condition_fresh
    (code : SetTerm) (id : FreeVarId)
    (hFresh :
      (SetSort.set, id) ∉ Term.freeSupport code) :
    (SetSort.set, id) ∉
      Formula.freeSupport
        (formula_code_left_opening_condition code) := by
  simp only [formula_code_left_opening_condition,
    Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList,
    finite_numeral_term_freeSupport,
    List.nil_append, List.append_nil]
  intro hMember
  rcases List.mem_append.mp hMember with
    hMember | hMember
  · rcases List.mem_append.mp hMember with
      hMember | hMember <;> exact hFresh hMember
  · rcases List.mem_append.mp hMember with
      hMember | hMember <;> exact hFresh hMember

private theorem gq_standard_opening_theory_fresh
    (id : FreeVarId) :
    ∀ formula, godel_quotation_theory formula →
      (SetSort.set, id) ∉
        Formula.freeSupport formula := by
  intro formula hFormula
  rw [(godel_quotation_theory_sentence hFormula).2]
  exact List.not_mem_nil

/-- 构造码的第零位开头沿代码等式运输到目标代码。 -/
private theorem gq_formula_left_opening_of_zero
    {Γ : Context signature}
    (code constructor : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ constructor)
    (hConstructorPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(constructor)) ∧ₘ
          ((constructor ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis)))) :
    Γ ⊢ₘ[godel_quotation_theory]
      formula_code_left_opening_condition code := by
  have hConstructor :
      Term.Admissible constructor SetSort.set := by
    rcases hEquality.admissible with
      ⟨hWellFormed, hScoped⟩
    cases hWellFormed with
    | equal hLeft hRight =>
        cases hScoped with
        | equal hLeftScoped hRightScoped =>
            exact ⟨hRight, hRightScoped⟩
  have hPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(code)) ∧ₘ
          ((code ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) :=
    gq_point_inversion_of_equality
      code constructor
      (numₘ(0))
      (numₘ(Numbered.logical_token
        .leftParenthesis))
      hEquality hConstructorPoint
      (hLeft :=
        Term.check_certificate_of_admissible hCode)
      (hRight :=
        Term.check_certificate_of_admissible hConstructor)
  have hOpening :=
    formula_code_left_opening_condition_admissible
      code hCode
  unfold formula_code_left_opening_condition
  exact FirstOrder.Derives.disjIntroLeft
    hPoint
    (hRightCheck :=
      Formula.check_certificate_of_admissible
        (Formula.Admissible.disj_right hOpening))

/-- 构造码的第一位开头沿代码等式运输到目标代码。 -/
private theorem gq_formula_left_opening_of_one
    {Γ : Context signature}
    (code constructor : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ constructor)
    (hConstructorPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1) ∈ₘ domₘ(constructor)) ∧ₘ
          ((constructor ·ₘ numₘ(1)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis)))) :
    Γ ⊢ₘ[godel_quotation_theory]
      formula_code_left_opening_condition code := by
  have hConstructor :
      Term.Admissible constructor SetSort.set := by
    rcases hEquality.admissible with
      ⟨hWellFormed, hScoped⟩
    cases hWellFormed with
    | equal hLeft hRight =>
        cases hScoped with
        | equal hLeftScoped hRightScoped =>
            exact ⟨hRight, hRightScoped⟩
  have hPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1) ∈ₘ domₘ(code)) ∧ₘ
          ((code ·ₘ numₘ(1)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) :=
    gq_point_inversion_of_equality
      code constructor
      (numₘ(1))
      (numₘ(Numbered.logical_token
        .leftParenthesis))
      hEquality hConstructorPoint
      (hLeft :=
        Term.check_certificate_of_admissible hCode)
      (hRight :=
        Term.check_certificate_of_admissible hConstructor)
  have hOpening :=
    formula_code_left_opening_condition_admissible
      code hCode
  unfold formula_code_left_opening_condition
  exact FirstOrder.Derives.disjIntroRight
    hPoint
    (hLeftCheck :=
      Formula.check_certificate_of_admissible
        (Formula.Admissible.disj_left hOpening))

/--
二元原子条件必给出第零位左括号。两个项见证只在对象层作存在消去。
-/
private theorem
    gq_binary_atomic_formula_condition_implies_opening
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [233, 234] [code]) :
    Derives godel_quotation_theory [] (
      binary_atomic_formula_code_condition code ⟶ₘ
        formula_code_left_opening_condition code) := by
  have hConditionAdmissible :
      Formula.Admissible
        (binary_atomic_formula_code_condition code) := by
    prove_admissible
  have hOpeningAdmissible :=
    formula_code_left_opening_condition_admissible
      code hCode
  have hOpeningFresh :
      ∀ id, id ∈ [233, 234] →
        (SetSort.set, id) ∉
          Formula.freeSupport
            (formula_code_left_opening_condition code) := by
    intro id hId
    exact formula_code_left_opening_condition_fresh
      code id (hFresh code (by simp) id hId)
  nd_apply FirstOrder.Derives.impIntro
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
  have hLeftAdmissible :
      Term.Admissible left SetSort.set := by
    simpa [left] using set_variable_admissible 233
  have hRightAdmissible :
      Term.Admissible right SetSort.set := by
    simpa [right] using set_variable_admissible 234
  have hEqualityCodeAdmissible :
      Term.Admissible
        (equality_atomic_formula_code_term left right)
        SetSort.set :=
    binary_atomic_formula_code_term_admissible
      equality_symbol_code_term left right
      (logical_symbol_code_term_admissible .equality)
      hLeftAdmissible hRightAdmissible
  have hMembershipCodeAdmissible :
      Term.Admissible
        (membership_atomic_formula_code_term left right)
        SetSort.set :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term left right
      membership_symbol_code_term_admissible
      hLeftAdmissible hRightAdmissible
  have hEqualityShapeAdmissible :
      Formula.Admissible equalityShape := by
    dsimp [equalityShape]
    exact Formula.Admissible.equal
      hCode hEqualityCodeAdmissible
  have hMembershipShapeAdmissible :
      Formula.Admissible membershipShape := by
    dsimp [membershipShape]
    exact Formula.Admissible.equal
      hCode hMembershipCodeAdmissible
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body]
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (is_term_code_formula_admissible
          hLeftAdmissible)
        (is_term_code_formula_admissible
          hRightAdmissible))
      (Formula.Admissible.disj
        hEqualityShapeAdmissible
        hMembershipShapeAdmissible)
  have hInnerAdmissible :
      Formula.Admissible inner := by
    dsimp [inner]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 234 hBodyAdmissible
  let Γ : Context signature :=
    [binary_atomic_formula_code_condition code]
  change
    Γ ⊢ₘ[godel_quotation_theory]
      formula_code_left_opening_condition code
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        binary_atomic_formula_code_condition code :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 233], inner := by
    simpa [binary_atomic_formula_code_condition,
      inner, body, equalityShape, membershipShape,
      left, right] using hCondition
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 233)
    (body := inner)
    (conclusion :=
      formula_code_left_opening_condition code)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hInnerAdmissible)
  · exact gq_standard_opening_theory_fresh 233
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [binary_atomic_formula_code_condition,
      inner, body, equalityShape, membershipShape,
      left, right] using
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set 233 0 inner
  · exact hOpeningFresh 233 (by simp)
  · exact hExists
  · let Δ : Context signature := inner :: Γ
    change
      Δ ⊢ₘ[godel_quotation_theory]
        formula_code_left_opening_condition code
    have hInner :
        Δ ⊢ₘ[godel_quotation_theory] inner :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 234)
      (body := body)
      (conclusion :=
        formula_code_left_opening_condition code)
      (hBodyCheck :=
        Formula.check_admissible_complete
          hBodyAdmissible)
    · exact gq_standard_opening_theory_fresh 234
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · simpa [inner, Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 234 0 body
      · rcases List.mem_singleton.mp hFormula with rfl
        have hInnerFresh :
            (SetSort.set, 234) ∉
              Formula.freeSupport inner := by
          simpa [inner, Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 234 0 body
        simpa [binary_atomic_formula_code_condition,
          inner, body, equalityShape, membershipShape,
          left, right] using
            Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
              (SetSort.set, 234)
              SetSort.set 233 0 inner hInnerFresh
    · exact hOpeningFresh 234 (by simp)
    · exact hInner
    · let Ε : Context signature := body :: Δ
      have hBody :
          Ε ⊢ₘ[godel_quotation_theory] body :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete
            hBodyAdmissible)
      dsimp only [body] at hBody
      have hTerms :
          Ε ⊢ₘ[godel_quotation_theory]
            term_codeₘ(left) ∧ₘ
              term_codeₘ(right) :=
        FirstOrder.Derives.conjElimLeft hBody
      have hShape :
          Ε ⊢ₘ[godel_quotation_theory]
            equalityShape ∨ₘ membershipShape :=
        FirstOrder.Derives.conjElimRight hBody
      apply FirstOrder.Derives.disjElim hShape
      · have hEqualityShape :
            equalityShape :: Ε
              ⊢ₘ[godel_quotation_theory]
                equalityShape :=
          FirstOrder.Derives.assumption
            (by simp)
        have hEquality :
            equalityShape :: Ε
              ⊢ₘ[godel_quotation_theory]
                code ≐ₘ
                  equality_atomic_formula_code_term
                    left right := by
          simpa [equalityShape] using hEqualityShape
        have hPoint :=
          FirstOrder.Derives.impElim
            (gq_equality_formula_opening_inversion
              (Γ := equalityShape :: Ε)
              left right
              (by simpa [left] using
                set_variable_admissible 233)
              (by simpa [right] using
                set_variable_admissible 234))
            (FirstOrder.Derives.context_weaken_cons
              hTerms)
        exact gq_formula_left_opening_of_zero
          code
          (equality_atomic_formula_code_term
            left right)
          hCode hEquality
          hPoint
      · have hMembershipShape :
            membershipShape :: Ε
              ⊢ₘ[godel_quotation_theory]
                membershipShape :=
          FirstOrder.Derives.assumption
            (by simp)
        have hEquality :
            membershipShape :: Ε
              ⊢ₘ[godel_quotation_theory]
                code ≐ₘ
                  membership_atomic_formula_code_term
                    left right := by
          simpa [membershipShape] using
            hMembershipShape
        have hPoint :=
          FirstOrder.Derives.impElim
            (gq_membership_formula_opening_inversion
              (Γ := membershipShape :: Ε)
              left right
              (by simpa [left] using
                set_variable_admissible 233)
              (by simpa [right] using
                set_variable_admissible 234))
            (FirstOrder.Derives.context_weaken_cons
              hTerms)
        exact gq_formula_left_opening_of_zero
          code
          (membership_atomic_formula_code_term
            left right)
          hCode hEquality
          hPoint

/--
一般谓词应用条件必给出第一位左括号。算术编号与长度等式只负责保持原生成条件；
开头反演本身精确使用参数列属于 `TermSeqₘ`。
-/
theorem
    gq_predicate_application_condition_implies_opening
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [230, 231, 232] [code]) :
    Derives godel_quotation_theory [] (
      predicate_application_code_condition code ⟶ₘ
        formula_code_left_opening_condition code) := by
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
  let body : SetFormula := precondition ∧ₘ shape
  let inner₂ : SetFormula :=
    ∃ₘ[SetSort.set, 232], body
  let inner₁ : SetFormula :=
    ∃ₘ[SetSort.set, 231], inner₂
  have hArityAdmissible :
      Term.Admissible arity SetSort.set := by
    simpa [arity] using set_variable_admissible 230
  have hIndexAdmissible :
      Term.Admissible symbolIndex SetSort.set := by
    simpa [symbolIndex] using set_variable_admissible 231
  have hArgumentsAdmissible :
      Term.Admissible arguments SetSort.set := by
    simpa [arguments] using set_variable_admissible 232
  have hConstructorAdmissible :
      Term.Admissible
        (predicate_application_code_term
          arity symbolIndex arguments)
        SetSort.set :=
    predicate_application_code_term_admissible
      arity symbolIndex arguments
      hArityAdmissible hIndexAdmissible
      hArgumentsAdmissible
  have hPreconditionAdmissible :
      Formula.Admissible precondition := by
    dsimp only [precondition]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        hArityAdmissible omega_term_admissible)
      (Formula.Admissible.conj
        (membership_formula_admissible
          hIndexAdmissible omega_term_admissible)
        (Formula.Admissible.conj
          (membership_formula_admissible
            hArgumentsAdmissible
            term_sequence_set_term_admissible)
          (Formula.Admissible.equal
            (domain_term_admissible
              arguments hArgumentsAdmissible)
            (successor_term_admissible
              arity hArityAdmissible))))
  have hShapeAdmissible :
      Formula.Admissible shape := by
    dsimp only [shape]
    exact Formula.Admissible.equal
      hCode hConstructorAdmissible
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body]
    exact Formula.Admissible.conj
      hPreconditionAdmissible hShapeAdmissible
  have hInner₂Admissible :
      Formula.Admissible inner₂ := by
    dsimp only [inner₂]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 232 hBodyAdmissible
  have hInner₁Admissible :
      Formula.Admissible inner₁ := by
    dsimp only [inner₁]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 231 hInner₂Admissible
  have hConditionAdmissible :
      Formula.Admissible
        (predicate_application_code_condition code) := by
    simpa [predicate_application_code_condition,
      inner₁, inner₂, body, precondition, shape,
      arity, symbolIndex, arguments] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set 230 hInner₁Admissible
  have hOpeningFresh :
      ∀ id, id ∈ [230, 231, 232] →
        (SetSort.set, id) ∉
          Formula.freeSupport
            (formula_code_left_opening_condition code) := by
    intro id hId
    exact formula_code_left_opening_condition_fresh
      code id (hFresh code (by simp) id hId)
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [predicate_application_code_condition code]
  change
    Γ ⊢ₘ[godel_quotation_theory]
      formula_code_left_opening_condition code
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        predicate_application_code_condition code :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hConditionAdmissible)
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 230], inner₁ := by
    simpa [predicate_application_code_condition,
      inner₁, inner₂, body, precondition, shape,
      arity, symbolIndex, arguments] using hCondition
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 230)
    (body := inner₁)
    (conclusion :=
      formula_code_left_opening_condition code)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hInner₁Admissible)
  · exact gq_standard_opening_theory_fresh 230
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [predicate_application_code_condition,
      inner₁, inner₂, body, precondition, shape,
      arity, symbolIndex, arguments] using
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set 230 0 inner₁
  · exact hOpeningFresh 230 (by simp)
  · exact hExists
  · let Δ : Context signature := inner₁ :: Γ
    have hInner₁ :
        Δ ⊢ₘ[godel_quotation_theory] inner₁ :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete
          hInner₁Admissible)
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 231)
      (body := inner₂)
      (conclusion :=
        formula_code_left_opening_condition code)
      (hBodyCheck :=
        Formula.check_admissible_complete
          hInner₂Admissible)
    · exact gq_standard_opening_theory_fresh 231
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · simpa [inner₁, Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 231 0 inner₂
      · rcases List.mem_singleton.mp hFormula with rfl
        have hInner₁Fresh :
            (SetSort.set, 231) ∉
              Formula.freeSupport inner₁ := by
          simpa [inner₁, Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 231 0 inner₂
        simpa [predicate_application_code_condition,
          inner₁, inner₂, body, precondition, shape,
          arity, symbolIndex, arguments] using
            Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
              (SetSort.set, 231)
              SetSort.set 230 0 inner₁ hInner₁Fresh
    · exact hOpeningFresh 231 (by simp)
    · exact hInner₁
    · let Ε : Context signature := inner₂ :: Δ
      have hInner₂ :
          Ε ⊢ₘ[godel_quotation_theory] inner₂ :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete
            hInner₂Admissible)
      apply FirstOrder.Derives.exists_elim
        (T := godel_quotation_theory)
        (Γ := Ε)
        (sort := SetSort.set)
        (eigen := 232)
        (body := body)
        (conclusion :=
          formula_code_left_opening_condition code)
        (hBodyCheck :=
          Formula.check_admissible_complete
            hBodyAdmissible)
      · exact gq_standard_opening_theory_fresh 232
      · intro formula hFormula
        rcases List.mem_cons.mp hFormula with
          rfl | hFormula
        · simpa [inner₂, Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 232 0 body
        · rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · have hInner₂Fresh :
                (SetSort.set, 232) ∉
                  Formula.freeSupport inner₂ := by
              simpa [inner₂, Formula.freeSupport] using
                Formula.not_mem_freeSupport_closeFreeAt
                  SetSort.set 232 0 body
            simpa [inner₁] using
              Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
                (SetSort.set, 232)
                SetSort.set 231 0 inner₂ hInner₂Fresh
          · rcases List.mem_singleton.mp hFormula with rfl
            have hInner₂Fresh :
                (SetSort.set, 232) ∉
                  Formula.freeSupport inner₂ := by
              simpa [inner₂, Formula.freeSupport] using
                Formula.not_mem_freeSupport_closeFreeAt
                  SetSort.set 232 0 body
            have hInner₁Fresh :
                (SetSort.set, 232) ∉
                  Formula.freeSupport inner₁ := by
              simpa [inner₁] using
                Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
                  (SetSort.set, 232)
                  SetSort.set 231 0 inner₂ hInner₂Fresh
            simpa [predicate_application_code_condition,
              inner₁, inner₂, body, precondition, shape,
              arity, symbolIndex, arguments] using
                Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
                  (SetSort.set, 232)
                  SetSort.set 230 0 inner₁ hInner₁Fresh
      · exact hOpeningFresh 232 (by simp)
      · exact hInner₂
      · let Ζ : Context signature := body :: Ε
        have hBody :
            Ζ ⊢ₘ[godel_quotation_theory] body :=
          FirstOrder.Derives.assumption
            (by simp [Ζ])
            (Formula.check_admissible_complete
              hBodyAdmissible)
        dsimp only [body] at hBody
        have hPrecondition :
            Ζ ⊢ₘ[godel_quotation_theory]
              precondition :=
          FirstOrder.Derives.conjElimLeft hBody
        have hEquality :
            Ζ ⊢ₘ[godel_quotation_theory]
              code ≐ₘ
                predicate_application_code_term
                  arity symbolIndex arguments := by
          simpa [shape] using
            FirstOrder.Derives.conjElimRight hBody
        dsimp only [precondition] at hPrecondition
        have hArgumentsMember :
            Ζ ⊢ₘ[godel_quotation_theory]
              arguments ∈ₘ TermSeqₘ :=
          FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight <|
              FirstOrder.Derives.conjElimRight
                hPrecondition
        have hOpening :=
          FirstOrder.Derives.impElim
            (gq_predicate_application_formula_opening_inversion
              (Γ := Ζ)
              arity symbolIndex arguments
              hArityAdmissible hIndexAdmissible
              hArgumentsAdmissible
              (by
                simpa [arity, symbolIndex] using
                  reserved_ids_fresh_cons_variable
                    230 (by
                      intro id hId
                      simp only [List.mem_cons,
                        List.not_mem_nil, or_false] at hId
                      rcases hId with rfl | rfl | rfl <;>
                        decide)
                    (reserved_ids_fresh_cons_variable
                      231 (by
                        intro id hId
                        simp only [List.mem_cons,
                          List.not_mem_nil, or_false] at hId
                        rcases hId with rfl | rfl | rfl <;>
                          decide)
                      (reserved_ids_fresh_nil [0, 1, 2])))
              (by native_decide))
            hArgumentsMember
        exact gq_formula_left_opening_of_one
          code
          (predicate_application_code_term
            arity symbolIndex arguments)
          hCode hEquality
          (FirstOrder.Derives.conjElimRight hOpening)

/-- 原子公式定义的两个构造分支统一导出根开头条件。 -/
private theorem
    gq_atomic_formula_condition_implies_opening
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234] [code]) :
    Derives godel_quotation_theory [] (
      atomic_formula_code_condition code ⟶ₘ
        formula_code_left_opening_condition code) := by
  have hDefinition :=
    gq_atomic_formula_code_definition_instance
      code hCode hFresh
  have hConditionAdmissible :
      Formula.Admissible
        (atomic_formula_code_condition code) :=
    Formula.Admissible.iff_right
      hDefinition.admissible
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
        (Δ :=
          binary_atomic_formula_code_condition code ::
            Γ)
        (by simp)
        (gq_binary_atomic_formula_condition_implies_opening
          code hCode <| by
            intro term hTerm id hId
            apply hFresh term hTerm id
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at hId ⊢
            rcases hId with rfl | rfl <;> simp))
      (FirstOrder.Derives.assumption (by simp))
  · exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := [])
        (Δ :=
          predicate_application_code_condition code ::
            Γ)
        (by simp)
        (gq_predicate_application_condition_implies_opening
          code hCode <| by
            intro term hTerm id hId
            apply hFresh term hTerm id
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at hId ⊢
            rcases hId with rfl | rfl | rfl <;> simp))
      (FirstOrder.Derives.assumption (by simp))

/-- 原子公式集合成员经两个对象层定义实例导出根开头条件。 -/
private theorem
    gq_atomic_formula_member_implies_opening
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234] [code]) :
    Derives godel_quotation_theory [] (
      (code ∈ₘ AtomicCodeₘ) ⟶ₘ
        formula_code_left_opening_condition code) := by
  have hMemberAdmissible :
      Formula.Admissible
        (code ∈ₘ AtomicCodeₘ) :=
    membership_formula_admissible
      hCode atomic_formula_code_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [code ∈ₘ AtomicCodeₘ]
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
        (Γ := []) (Δ := Γ) (by simp)
        (gq_atomic_formula_code_set_definition_instance
          code hCode))
      hMember
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        atomic_formula_code_condition code :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_atomic_formula_code_definition_instance
          code hCode hFresh))
      hAtomic
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (gq_atomic_formula_condition_implies_opening
        code hCode hFresh))
    hCondition

/-- 否定生成分支消去其唯一子公式见证，并运输第零位左括号。 -/
private theorem
    gq_negation_generation_implies_opening
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [306] [code]) :
    Derives godel_quotation_theory [] (
      (∃ₘ[SetSort.set, 306],
        ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
          (code ≐ₘ neg_codeₘ(x#306)))) ⟶ₘ
        formula_code_left_opening_condition code) := by
  let source : SetTerm := x#306
  let shape : SetFormula :=
    code ≐ₘ neg_codeₘ(source)
  let body : SetFormula :=
    (source ∈ₘ FormulaCodeₘ) ∧ₘ shape
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 306], body
  have hSourceAdmissible :
      Term.Admissible source SetSort.set := by
    simpa [source] using set_variable_admissible 306
  have hConstructorAdmissible :
      Term.Admissible
        (neg_codeₘ(source)) SetSort.set :=
    negation_formula_code_term_admissible
      source hSourceAdmissible
  have hShapeAdmissible :
      Formula.Admissible shape := by
    dsimp only [shape]
    exact Formula.Admissible.equal
      hCode hConstructorAdmissible
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        hSourceAdmissible
        formula_code_set_term_admissible)
      hShapeAdmissible
  have hConditionAdmissible :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 306 hBodyAdmissible
  have hOpeningFresh :
      (SetSort.set, 306) ∉
        Formula.freeSupport
          (formula_code_left_opening_condition code) :=
    formula_code_left_opening_condition_fresh
      code 306 (hFresh code (by simp) 306 (by simp))
  change Derives godel_quotation_theory [] (
    condition ⟶ₘ
      formula_code_left_opening_condition code)
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hConditionAdmissible)
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 306)
    (body := body)
    (conclusion :=
      formula_code_left_opening_condition code)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hBodyAdmissible)
  · exact gq_standard_opening_theory_fresh 306
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [condition, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set 306 0 body
  · exact hOpeningFresh
  · exact hCondition
  · let Δ : Context signature := body :: Γ
    have hBody :
        Δ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete
          hBodyAdmissible)
    dsimp only [body] at hBody
    have hMember :
        Δ ⊢ₘ[godel_quotation_theory]
          source ∈ₘ FormulaCodeₘ :=
      FirstOrder.Derives.conjElimLeft hBody
    have hEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ neg_codeₘ(source) := by
      simpa [shape] using
        FirstOrder.Derives.conjElimRight hBody
    have hOpening :=
      FirstOrder.Derives.impElim
        (gq_negation_formula_opening_inversion
          (Γ := Δ) source hSourceAdmissible)
        hMember
    exact gq_formula_left_opening_of_zero
      code (neg_codeₘ(source))
      hCode hEquality
      (FirstOrder.Derives.conjElimLeft hOpening)

/-- 蕴含生成分支消去两个子公式见证，并运输第零位左括号。 -/
private theorem
    gq_implication_generation_implies_opening
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [307, 308] [code]) :
    Derives godel_quotation_theory [] (
      (∃ₘ[SetSort.set, 307],
        ∃ₘ[SetSort.set, 308],
          (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
            (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (code ≐ₘ imp_codeₘ(x#307, x#308)))) ⟶ₘ
        formula_code_left_opening_condition code) := by
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
  have hLeftAdmissible :
      Term.Admissible left SetSort.set := by
    simpa [left] using set_variable_admissible 307
  have hRightAdmissible :
      Term.Admissible right SetSort.set := by
    simpa [right] using set_variable_admissible 308
  have hConstructorAdmissible :
      Term.Admissible
        (imp_codeₘ(left, right)) SetSort.set :=
    implication_formula_code_term_admissible
      left right hLeftAdmissible hRightAdmissible
  have hShapeAdmissible :
      Formula.Admissible shape := by
    dsimp only [shape]
    exact Formula.Admissible.equal
      hCode hConstructorAdmissible
  have hMembersAdmissible :
      Formula.Admissible
        ((left ∈ₘ FormulaCodeₘ) ∧ₘ
          (right ∈ₘ FormulaCodeₘ)) :=
    Formula.Admissible.conj
      (membership_formula_admissible
        hLeftAdmissible
        formula_code_set_term_admissible)
      (membership_formula_admissible
        hRightAdmissible
        formula_code_set_term_admissible)
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body]
    exact Formula.Admissible.conj
      hMembersAdmissible hShapeAdmissible
  have hInnerAdmissible :
      Formula.Admissible inner := by
    dsimp only [inner]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 308 hBodyAdmissible
  have hConditionAdmissible :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 307 hInnerAdmissible
  have hOpeningFresh :
      ∀ id, id ∈ [307, 308] →
        (SetSort.set, id) ∉
          Formula.freeSupport
            (formula_code_left_opening_condition code) := by
    intro id hId
    exact formula_code_left_opening_condition_fresh
      code id (hFresh code (by simp) id hId)
  change Derives godel_quotation_theory [] (
    condition ⟶ₘ
      formula_code_left_opening_condition code)
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hConditionAdmissible)
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 307)
    (body := inner)
    (conclusion :=
      formula_code_left_opening_condition code)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hInnerAdmissible)
  · exact gq_standard_opening_theory_fresh 307
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [condition, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set 307 0 inner
  · exact hOpeningFresh 307 (by simp)
  · exact hCondition
  · let Δ : Context signature := inner :: Γ
    have hInner :
        Δ ⊢ₘ[godel_quotation_theory] inner :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete
          hInnerAdmissible)
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 308)
      (body := body)
      (conclusion :=
        formula_code_left_opening_condition code)
      (hBodyCheck :=
        Formula.check_admissible_complete
          hBodyAdmissible)
    · exact gq_standard_opening_theory_fresh 308
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · simpa [inner, Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 308 0 body
      · rcases List.mem_singleton.mp hFormula with rfl
        have hInnerFresh :
            (SetSort.set, 308) ∉
              Formula.freeSupport inner := by
          simpa [inner, Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 308 0 body
        simpa [condition] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, 308)
            SetSort.set 307 0 inner hInnerFresh
    · exact hOpeningFresh 308 (by simp)
    · exact hInner
    · let Ε : Context signature := body :: Δ
      have hBody :
          Ε ⊢ₘ[godel_quotation_theory] body :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete
            hBodyAdmissible)
      dsimp only [body] at hBody
      have hMembers :
          Ε ⊢ₘ[godel_quotation_theory]
            (left ∈ₘ FormulaCodeₘ) ∧ₘ
              (right ∈ₘ FormulaCodeₘ) :=
        FirstOrder.Derives.conjElimLeft hBody
      have hEquality :
          Ε ⊢ₘ[godel_quotation_theory]
            code ≐ₘ imp_codeₘ(left, right) := by
        simpa [shape] using
          FirstOrder.Derives.conjElimRight hBody
      have hOpening :=
        FirstOrder.Derives.impElim
          (gq_implication_formula_opening_inversion
            (Γ := Ε) left right
            hLeftAdmissible hRightAdmissible)
          hMembers
      exact gq_formula_left_opening_of_zero
        code (imp_codeₘ(left, right))
        hCode hEquality hOpening

/-- 全称生成分支消去绑定变量与正文见证，并运输第零位左括号。 -/
private theorem
    gq_universal_generation_implies_opening
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [309, 310] [code]) :
    Derives godel_quotation_theory [] (
      (∃ₘ[SetSort.set, 309],
        ∃ₘ[SetSort.set, 310],
          (((x#309 ∈ₘ VarSymₘ) ∧ₘ
            (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (code ≐ₘ
              forall_codeₘ(x#309, x#310)))) ⟶ₘ
        formula_code_left_opening_condition code) := by
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
  have hVariableAdmissible :
      Term.Admissible boundVariable SetSort.set := by
    simpa [boundVariable] using set_variable_admissible 309
  have hBodyCodeAdmissible :
      Term.Admissible bodyCode SetSort.set := by
    simpa [bodyCode] using set_variable_admissible 310
  have hConstructorAdmissible :
      Term.Admissible
        (forall_codeₘ(boundVariable, bodyCode))
        SetSort.set :=
    universal_formula_code_term_admissible
      boundVariable bodyCode
      hVariableAdmissible hBodyCodeAdmissible
  have hShapeAdmissible :
      Formula.Admissible shape := by
    dsimp only [shape]
    exact Formula.Admissible.equal
      hCode hConstructorAdmissible
  have hMembersAdmissible :
      Formula.Admissible
        ((boundVariable ∈ₘ VarSymₘ) ∧ₘ
          (bodyCode ∈ₘ FormulaCodeₘ)) :=
    Formula.Admissible.conj
      (membership_formula_admissible
        hVariableAdmissible
        variable_symbol_set_term_admissible)
      (membership_formula_admissible
        hBodyCodeAdmissible
        formula_code_set_term_admissible)
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body]
    exact Formula.Admissible.conj
      hMembersAdmissible hShapeAdmissible
  have hInnerAdmissible :
      Formula.Admissible inner := by
    dsimp only [inner]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 310 hBodyAdmissible
  have hConditionAdmissible :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 309 hInnerAdmissible
  have hOpeningFresh :
      ∀ id, id ∈ [309, 310] →
        (SetSort.set, id) ∉
          Formula.freeSupport
            (formula_code_left_opening_condition code) := by
    intro id hId
    exact formula_code_left_opening_condition_fresh
      code id (hFresh code (by simp) id hId)
  change Derives godel_quotation_theory [] (
    condition ⟶ₘ
      formula_code_left_opening_condition code)
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hConditionAdmissible)
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 309)
    (body := inner)
    (conclusion :=
      formula_code_left_opening_condition code)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hInnerAdmissible)
  · exact gq_standard_opening_theory_fresh 309
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [condition, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set 309 0 inner
  · exact hOpeningFresh 309 (by simp)
  · exact hCondition
  · let Δ : Context signature := inner :: Γ
    have hInner :
        Δ ⊢ₘ[godel_quotation_theory] inner :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete
          hInnerAdmissible)
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 310)
      (body := body)
      (conclusion :=
        formula_code_left_opening_condition code)
      (hBodyCheck :=
        Formula.check_admissible_complete
          hBodyAdmissible)
    · exact gq_standard_opening_theory_fresh 310
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · simpa [inner, Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 310 0 body
      · rcases List.mem_singleton.mp hFormula with rfl
        have hInnerFresh :
            (SetSort.set, 310) ∉
              Formula.freeSupport inner := by
          simpa [inner, Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 310 0 body
        simpa [condition] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, 310)
            SetSort.set 309 0 inner hInnerFresh
    · exact hOpeningFresh 310 (by simp)
    · exact hInner
    · let Ε : Context signature := body :: Δ
      have hBody :
          Ε ⊢ₘ[godel_quotation_theory] body :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete
            hBodyAdmissible)
      dsimp only [body] at hBody
      have hMembers :
          Ε ⊢ₘ[godel_quotation_theory]
            (boundVariable ∈ₘ VarSymₘ) ∧ₘ
              (bodyCode ∈ₘ FormulaCodeₘ) :=
        FirstOrder.Derives.conjElimLeft hBody
      have hVariableMember :
          Ε ⊢ₘ[godel_quotation_theory]
            boundVariable ∈ₘ VarSymₘ :=
        FirstOrder.Derives.conjElimLeft hMembers
      have hBodyMember :
          Ε ⊢ₘ[godel_quotation_theory]
            bodyCode ∈ₘ FormulaCodeₘ :=
        FirstOrder.Derives.conjElimRight hMembers
      have hEquality :
          Ε ⊢ₘ[godel_quotation_theory]
            code ≐ₘ
              forall_codeₘ(boundVariable, bodyCode) := by
        simpa [shape] using
          FirstOrder.Derives.conjElimRight hBody
      have hBodyCodeString :
          Ε ⊢ₘ[godel_quotation_theory]
            bodyCode ∈ₘ CodeStrₘ :=
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ε) (by simp)
            (gq_formula_code_member_implies_code_string
              bodyCode hBodyCodeAdmissible))
          hBodyMember
      have hOpening :=
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ε) (by simp)
            (gq_universal_formula_opening_inversion
              boundVariable bodyCode))
          (FirstOrder.Derives.conjIntro
            hVariableMember hBodyCodeString)
      exact gq_formula_left_opening_of_zero
        code (forall_codeₘ(boundVariable, bodyCode))
        hCode hEquality
        (FirstOrder.Derives.conjElimLeft hOpening)

/--
一步公式生成的四个构造分支统一导出根开头条件。

该接口只消费生成反演本身，不增加额外归纳前提。
-/
theorem gq_formula_code_generation_implies_opening_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310] [code]) :
    Derives godel_quotation_theory [] (
      formula_code_generation_condition FormulaCodeₘ code ⟶ₘ
        formula_code_left_opening_condition code) := by
  let atomic : SetFormula :=
    code ∈ₘ AtomicCodeₘ
  let negation : SetFormula :=
    ∃ₘ[SetSort.set, 306],
      ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
        (code ≐ₘ neg_codeₘ(x#306)))
  let implication : SetFormula :=
    ∃ₘ[SetSort.set, 307],
      ∃ₘ[SetSort.set, 308],
        (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
          (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
          (code ≐ₘ imp_codeₘ(x#307, x#308)))
  let universal : SetFormula :=
    ∃ₘ[SetSort.set, 309],
      ∃ₘ[SetSort.set, 310],
        (((x#309 ∈ₘ VarSymₘ) ∧ₘ
          (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
          (code ≐ₘ forall_codeₘ(x#309, x#310)))
  let rest : SetFormula := implication ∨ₘ universal
  let tail : SetFormula := negation ∨ₘ rest
  have hGenerationAdmissible :
      Formula.Admissible
        (formula_code_generation_condition
          FormulaCodeₘ code) :=
    by
      unfold formula_code_generation_condition
      prove_admissible
  have hAtomicFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hId ⊢
    rcases hId with
      rfl | rfl | rfl | rfl | rfl <;> simp
  have hNegationFresh :
      ReservedIdsFresh [306] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hId ⊢
    rcases hId with rfl
    simp
  have hImplicationFresh :
      ReservedIdsFresh [307, 308] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hId ⊢
    rcases hId with rfl | rfl <;> simp
  have hUniversalFresh :
      ReservedIdsFresh [309, 310] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hId ⊢
    rcases hId with rfl | rfl <;> simp
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [formula_code_generation_condition
      FormulaCodeₘ code]
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition
          FormulaCodeₘ code :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hGenerationAdmissible)
  have hShape :
      Γ ⊢ₘ[godel_quotation_theory]
        atomic ∨ₘ tail := by
    simpa [formula_code_generation_condition,
      atomic, tail, rest, negation,
      implication, universal] using hGeneration
  apply FirstOrder.Derives.disjElim hShape
  · let Δ : Context signature := atomic :: Γ
    change
      Δ ⊢ₘ[godel_quotation_theory]
        formula_code_left_opening_condition code
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ, atomic])
      (gq_atomic_formula_member_implies_opening
          code hCode hAtomicFresh))
      (FirstOrder.Derives.assumption
        (by simp [Δ, atomic]))
  · let Δ : Context signature := tail :: Γ
    change
      Δ ⊢ₘ[godel_quotation_theory]
        formula_code_left_opening_condition code
    have hTail :
        Δ ⊢ₘ[godel_quotation_theory] tail :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    apply FirstOrder.Derives.disjElim hTail
    · let Ε : Context signature := negation :: Δ
      change
        Ε ⊢ₘ[godel_quotation_theory]
          formula_code_left_opening_condition code
      exact FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp [Ε, negation])
          (gq_negation_generation_implies_opening
            code hCode hNegationFresh))
        (FirstOrder.Derives.assumption
          (by simp [Ε, negation]))
    · let Ε : Context signature := rest :: Δ
      change
        Ε ⊢ₘ[godel_quotation_theory]
          formula_code_left_opening_condition code
      have hRest :
          Ε ⊢ₘ[godel_quotation_theory] rest :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
      apply FirstOrder.Derives.disjElim hRest
      · let Ζ : Context signature := implication :: Ε
        change
          Ζ ⊢ₘ[godel_quotation_theory]
            formula_code_left_opening_condition code
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ζ)
            (by simp [Ζ, implication])
            (gq_implication_generation_implies_opening
              code hCode hImplicationFresh))
          (FirstOrder.Derives.assumption
            (by simp [Ζ, implication]))
      · let Ζ : Context signature := universal :: Ε
        change
          Ζ ⊢ₘ[godel_quotation_theory]
            formula_code_left_opening_condition code
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ζ)
            (by simp [Ζ, universal])
            (gq_universal_generation_implies_opening
              code hCode hUniversalFresh))
          (FirstOrder.Derives.assumption
            (by simp [Ζ, universal]))

/-- 完整公式码成员经最小闭包生成反演导出根开头条件。 -/
theorem gq_formula_code_member_implies_opening_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310, 600] [code]) :
    Derives godel_quotation_theory [] (
      (code ∈ₘ FormulaCodeₘ) ⟶ₘ
        formula_code_left_opening_condition code) := by
  have hMemberAdmissible :
      Formula.Admissible
        (code ∈ₘ FormulaCodeₘ) :=
    membership_formula_admissible
      hCode formula_code_set_term_admissible
  have hGenerationFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310, 600] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hId ⊢
    rcases hId with
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hOpeningFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hId ⊢
    rcases hId with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> simp
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [code ∈ₘ FormulaCodeₘ]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMemberAdmissible)
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition
          FormulaCodeₘ code :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_formula_code_member_implies_generation_of_fresh
          code hCode hGenerationFresh))
      hMember
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ])
      (gq_formula_code_generation_implies_opening_of_fresh
        code hCode hOpeningFresh))
    hGeneration

/-- 对象层全称化后的公式码根开头定理。 -/
theorem gq_formula_code_opening_universal :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 700],
        ((x#700 ∈ₘ FormulaCodeₘ) ⟶ₘ
          formula_code_left_opening_condition
            (x#700)) := by
  let code : SetTerm := x#700
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using set_variable_admissible 700
  have hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310, 600]
        [code] := by
    simpa [code] using
      reserved_ids_fresh_cons_variable
        700
        (by
          intro id hId
          simp only [List.mem_cons,
            List.not_mem_nil, or_false] at hId
          rcases hId with
            rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl <;>
              decide)
        (reserved_ids_fresh_nil
          [230, 231, 232, 233, 234,
            306, 307, 308, 309, 310, 600])
  have hPoint :=
    gq_formula_code_member_implies_opening_of_fresh
      code hCode hFresh
  simpa [code] using
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := []) (sort := SetSort.set)
      (eigen := 700)
      (gq_standard_opening_theory_fresh 700)
      (by
        intro formula hFormula
        cases hFormula)
      hPoint

/-- 任意 admissible 完整公式码都满足根开头条件。 -/
theorem gq_formula_code_member_implies_opening
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ FormulaCodeₘ) ⟶ₘ
        formula_code_left_opening_condition code := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := code)
      gq_formula_code_opening_universal
  have hZeroFixed :
      Term.substituteFree SetSort.set 700 code
          (numₘ(0)) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 700 code (numₘ(0)) <| by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil
  have hOneFixed :
      Term.substituteFree SetSort.set 700 code
          (numₘ(1)) =
        numₘ(1) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 700 code (numₘ(1)) <| by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil
  have hLeftParenthesisFixed :
      Term.substituteFree SetSort.set 700 code
          (numₘ(Numbered.logical_token
            .leftParenthesis)) =
        numₘ(Numbered.logical_token
          .leftParenthesis) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 700 code
        (numₘ(Numbered.logical_token
          .leftParenthesis)) <| by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil
  simpa [formula_code_left_opening_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hZeroFixed, hOneFixed,
    hLeftParenthesisFixed] using hAt

/--
标准 token 行的两个根开头位置都不是左括号时，任意已推出的根开头条件导致矛盾。
-/
theorem gq_standard_token_sequence_falsum_of_no_left_opening
    {Γ : Context signature}
    (tokens : List Nat)
    (hZero :
      tokens[0]? ≠
        some (Numbered.logical_token
          .leftParenthesis))
    (hOne :
      tokens[1]? ≠
        some (Numbered.logical_token
          .leftParenthesis))
    (hOpening :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_left_opening_condition
          (standard_token_sequence tokens)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  unfold formula_code_left_opening_condition at hOpening
  apply FirstOrder.Derives.disjElim hOpening
  · exact
      gq_standard_token_sequence_falsum_of_point_not_expected
        tokens
        (standard_token_sequence tokens)
        0
        (Numbered.logical_token .leftParenthesis)
        hZero
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (standard_token_sequence tokens))
        (FirstOrder.Derives.assumption (by simp))
  · exact
      gq_standard_token_sequence_falsum_of_point_not_expected
        tokens
        (standard_token_sequence tokens)
        1
        (Numbered.logical_token .leftParenthesis)
        hOne
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (standard_token_sequence tokens))
        (FirstOrder.Derives.assumption (by simp))

/--
标准 token 行的第零、第一位均不可能是左括号时，该行不是完整公式码。

结论是对象层闭否定，后续 parser/证明行拒绝只需提供两个可计算的宿主索引事实。
-/
theorem
    gq_standard_token_sequence_formula_code_not_of_no_left_opening
    (tokens : List Nat)
    (hZero :
      tokens[0]? ≠
        some (Numbered.logical_token
          .leftParenthesis))
    (hOne :
      tokens[1]? ≠
        some (Numbered.logical_token
          .leftParenthesis)) :
    Derives godel_quotation_theory [] (
      ¬ₘ (standard_token_sequence tokens ∈ₘ
        FormulaCodeₘ)) := by
  let code : SetTerm :=
    standard_token_sequence tokens
  let membership : SetFormula :=
    code ∈ₘ FormulaCodeₘ
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    dsimp only [membership]
    exact membership_formula_admissible
      hCode formula_code_set_term_admissible
  change Derives godel_quotation_theory [] (
    ¬ₘ membership)
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hMembershipAdmissible)
  let Γ : Context signature := [membership]
  change
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory] membership :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMembershipAdmissible)
  have hOpening :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_left_opening_condition code :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_formula_code_member_implies_opening
          code hCode))
      hMember
  simpa [code] using
    gq_standard_token_sequence_falsum_of_no_left_opening
      tokens hZero hOne hOpening

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
