import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstructionInversion

/-!
# Gödel quotation 的蕴含构造反演

本模块先提供蕴含左正文的定义域下降。右正文需要在左长度已经被有限
numeral 消去后再使用，因此不把更强的全局加法反演前提传播到这里。
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
蕴含左正文的定义域严格落入整个蕴含代码的定义域。

左侧只跨过一个固定左括号，故对象层只需使用
`num(1) + dom(left) = S(dom(left))`；随后通过有限序列拼接的左段
投影把该成员关系提升到完整构造代码。
-/
theorem gq_implication_left_domain_mem_code_domain
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(left) ∈ₘ
        domₘ(imp_codeₘ(left, right)) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let implicationSymbol :=
    logical_symbol_code_term .implication
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let leftStage := leftParenthesis ⌢ₘ left
  let prefixCode := leftStage ⌢ₘ implicationSymbol
  let bodyStage := prefixCode ⌢ₘ right
  let rawCode := bodyStage ⌢ₘ rightParenthesis
  let code := imp_codeₘ(left, right)
  let leftDomain := domₘ(left)
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hImplicationSymbol :
      Term.CheckCertificate implicationSymbol SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hLeftStage :
      Term.CheckCertificate leftStage SetSort.set := by
    prove_term_check
  have hPrefix :
      Term.CheckCertificate prefixCode SetSort.set := by
    prove_term_check
  have hBodyStage :
      Term.CheckCertificate bodyStage SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hLeftDomainCheck :
      Term.CheckCertificate leftDomain SetSort.set := by
    prove_term_check
  have hLeftOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        leftDomain ∈ₘ ωₘ := by
    simpa [leftDomain, finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hLeftFinite
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hLeftStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftStage := by
    simpa [leftStage] using
      gq_concatenation_finite
        leftParenthesis left
        hLeftParenthesisFinite hLeftFinite
        (hLeft := hLeftParenthesis) (hRight := hLeft)
  have hLeftStageDomainRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftStage) ≐ₘ
          (domₘ(leftParenthesis) +ₘ leftDomain) := by
    simpa [leftStage, leftDomain] using
      gq_concatenation_domain_eq_sum_of_theory
        (fun _ hAxiom => hAxiom)
        leftParenthesis left
        hLeftParenthesisFinite hLeftFinite
        (hLeft := hLeftParenthesis) (hRight := hLeft)
  have hLeftStageDomainCongruence :
      Γ ⊢ₘ[godel_quotation_theory]
        (domₘ(leftParenthesis) +ₘ leftDomain) ≐ₘ
          (numₘ(1) +ₘ leftDomain) :=
    natural_addition_term_congr_of_equalities
      (domₘ(leftParenthesis)) (numₘ(1))
      leftDomain leftDomain
      (domain_term_admissible
        leftParenthesis hLeftParenthesis.admissible)
      (finite_numeral_term_admissible 1)
      hLeftDomainCheck.admissible hLeftDomainCheck.admissible
      hLeftParenthesisDomain
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) leftDomain)
  have hLeftStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftStage) ≐ₘ
          (numₘ(1) +ₘ leftDomain) :=
    Metatheory.Derives.equality_trans
      hLeftStageDomainRaw hLeftStageDomainCongruence
  have hOneAddition :
      Γ ⊢ₘ[godel_quotation_theory]
        (numₘ(1) +ₘ leftDomain) ≐ₘ
          Sₘ(leftDomain) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            standard_sequence_one_addition_eq_successor
              leftDomain hLeftDomainCheck.admissible)
      hLeftOmega
  have hLeftInSuccessor :
      Γ ⊢ₘ[godel_quotation_theory]
        leftDomain ∈ₘ Sₘ(leftDomain) :=
    FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
          standard_sequence_weaken_successor <|
            mem_successor_self
              leftDomain hLeftDomainCheck.admissible
  have hLeftInStage :
      Γ ⊢ₘ[godel_quotation_theory]
        leftDomain ∈ₘ domₘ(leftStage) := by
    apply FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        leftDomain
        (domₘ(leftStage))
        (numₘ(1) +ₘ leftDomain)
        hLeftDomainCheck.admissible
        (domain_term_admissible
          leftStage hLeftStage.admissible)
        (natural_addition_term_admissible
          (numₘ(1)) leftDomain
          (finite_numeral_term_admissible 1)
          hLeftDomainCheck.admissible)
        hLeftStageDomain)
    apply FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        leftDomain
        (numₘ(1) +ₘ leftDomain)
        (Sₘ(leftDomain))
        hLeftDomainCheck.admissible
        (natural_addition_term_admissible
          (numₘ(1)) leftDomain
          (finite_numeral_term_admissible 1)
          hLeftDomainCheck.admissible)
        (successor_term_admissible
          leftDomain hLeftDomainCheck.admissible)
        hOneAddition)
      hLeftInSuccessor
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    have hImplicationFinite :
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition implicationSymbol := by
      simpa [implicationSymbol] using
        gq_logical_symbol_code_finite_sequence
          (Γ := Γ) .implication
    simpa [prefixCode] using
      gq_concatenation_finite
        leftStage implicationSymbol
        hLeftStageFinite
        hImplicationFinite
        (hLeft := hLeftStage) (hRight := hImplicationSymbol)
  have hLeftInPrefix :
      Γ ⊢ₘ[godel_quotation_theory]
        leftDomain ∈ₘ domₘ(prefixCode) :=
    by
      have hImplicationFinite :
          Γ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition implicationSymbol := by
        simpa [implicationSymbol] using
          gq_logical_symbol_code_finite_sequence
            (Γ := Γ) .implication
      exact
        gq_concatenation_left_domain_member
          leftStage implicationSymbol leftDomain
          hLeftStageFinite hImplicationFinite hLeftInStage
          (hLeft := hLeftStage) (hRight := hImplicationSymbol)
  have hBodyStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition bodyStage := by
    simpa [bodyStage] using
      gq_concatenation_finite
        prefixCode right hPrefixFinite hRightFinite
        (hLeft := hPrefix) (hRight := hRight)
  have hLeftInBodyStage :
      Γ ⊢ₘ[godel_quotation_theory]
        leftDomain ∈ₘ domₘ(bodyStage) :=
    gq_concatenation_left_domain_member
      prefixCode right leftDomain
      hPrefixFinite hRightFinite hLeftInPrefix
      (hLeft := hPrefix) (hRight := hRight)
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hLeftInRawCode :
      Γ ⊢ₘ[godel_quotation_theory]
        leftDomain ∈ₘ domₘ(rawCode) :=
    gq_concatenation_left_domain_member
      bodyStage rightParenthesis leftDomain
      hBodyStageFinite hRightParenthesisFinite
      hLeftInBodyStage
      (hLeft := hBodyStage) (hRight := hRightParenthesis)
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    have hCodeString :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ
            implication_formula_string_term left right :=
      gq_implication_formula_code_eq_string_of_context
        left right (hLeft := hLeft) (hRight := hRight)
    simpa [code, rawCode, bodyStage, prefixCode,
      leftStage, leftParenthesis, implicationSymbol,
      rightParenthesis, implication_formula_string_term] using
      hCodeString
  have hCodeRawDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ domₘ(rawCode) :=
    domain_term_congr_of_equality
      code rawCode hCode.admissible hRawCode.admissible
      hCodeRaw
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      leftDomain
      (domₘ(code)) (domₘ(rawCode))
      hLeftDomainCheck.admissible
      (domain_term_admissible code hCode.admissible)
      (domain_term_admissible rawCode hRawCode.admissible)
      hCodeRawDomain)
    hLeftInRawCode

/-!
蕴含左正文的逐点值在整个构造中只平移一个左括号位置。该接口不要求整行已经
按宿主列表切分，供后续从任意标准整串恢复左正文切片。
-/
theorem gq_implication_formula_left_point_at_standard_offset
    {Γ : Context signature}
    (left right : SetTerm) (index : Nat)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(left))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((numₘ(1 + index) ∈ₘ
          domₘ(imp_codeₘ(left, right))) ∧ₘ
        ((imp_codeₘ(left, right) ·ₘ numₘ(1 + index)) ≐ₘ
          (left ·ₘ numₘ(index)))) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let implicationSymbol :=
    logical_symbol_code_term .implication
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let prefixCode :=
    (leftParenthesis ⌢ₘ left) ⌢ₘ implicationSymbol
  let bodyStage := prefixCode ⌢ₘ right
  let rawCode := bodyStage ⌢ₘ rightParenthesis
  let code := imp_codeₘ(left, right)
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hImplicationSymbol :
      Term.CheckCertificate implicationSymbol SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hPrefix :
      Term.CheckCertificate prefixCode SetSort.set := by
    prove_term_check
  have hBodyStage :
      Term.CheckCertificate bodyStage SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hLeftParenthesisEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ
          standard_token_sequence
            [Numbered.logical_token .leftParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [leftParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis
  have hImplicationFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition implicationSymbol := by
    simpa [implicationSymbol] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .implication
  have hPrefixPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1 + index) ∈ₘ domₘ(prefixCode)) ∧ₘ
          ((prefixCode ·ₘ numₘ(1 + index)) ≐ₘ
            (left ·ₘ numₘ(index)))) := by
    simpa [prefixCode] using
      gq_concatenation_middle_point_at_standard_offset
        leftParenthesis left implicationSymbol
        [Numbered.logical_token .leftParenthesis]
        index hLeftParenthesisEquality
        hLeftFinite hImplicationFinite hLeftIndex
        (hPrefix := hLeftParenthesis)
        (hBody := hLeft)
        (hSuffix := hImplicationSymbol)
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis :=
    gq_finite_sequence_of_eq_standard_token_sequence
      leftParenthesis
      [Numbered.logical_token .leftParenthesis]
      hLeftParenthesisEquality
      (hCode := hLeftParenthesis)
  have hLeftStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          (leftParenthesis ⌢ₘ left) :=
    gq_concatenation_finite
      leftParenthesis left
      hLeftParenthesisFinite hLeftFinite
      (hLeft := hLeftParenthesis)
      (hRight := hLeft)
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        (leftParenthesis ⌢ₘ left)
        implicationSymbol
        hLeftStageFinite hImplicationFinite
        (hLeft := by prove_term_check)
        (hRight := hImplicationSymbol)
  have hBodyStagePoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1 + index) ∈ₘ domₘ(bodyStage)) ∧ₘ
          ((bodyStage ·ₘ numₘ(1 + index)) ≐ₘ
            (left ·ₘ numₘ(index)))) := by
    simpa [bodyStage] using
      gq_concatenation_left_point
        prefixCode right
        (numₘ(1 + index))
        (left ·ₘ numₘ(index))
        hPrefixFinite hRightFinite
        (FirstOrder.Derives.conjElimLeft hPrefixPoint)
        (FirstOrder.Derives.conjElimRight hPrefixPoint)
        (hLeft := hPrefix)
        (hRight := hRight)
  have hBodyStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition bodyStage := by
    simpa [bodyStage] using
      gq_concatenation_finite
        prefixCode right
        hPrefixFinite hRightFinite
        (hLeft := hPrefix)
        (hRight := hRight)
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRawPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1 + index) ∈ₘ domₘ(rawCode)) ∧ₘ
          ((rawCode ·ₘ numₘ(1 + index)) ≐ₘ
            (left ·ₘ numₘ(index)))) := by
    simpa [rawCode] using
      gq_concatenation_left_point
        bodyStage rightParenthesis
        (numₘ(1 + index))
        (left ·ₘ numₘ(index))
        hBodyStageFinite hRightParenthesisFinite
        (FirstOrder.Derives.conjElimLeft hBodyStagePoint)
        (FirstOrder.Derives.conjElimRight hBodyStagePoint)
        (hLeft := hBodyStage)
        (hRight := hRightParenthesis)
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    simpa [code, rawCode, bodyStage, prefixCode,
      leftParenthesis, implicationSymbol,
      rightParenthesis,
      implication_formula_string_term] using
      gq_implication_formula_code_eq_string_of_context
        (Γ := Γ) left right
        (hLeft := hLeft) (hRight := hRight)
  simpa [code] using
    gq_point_inversion_of_equality
      code rawCode
      (numₘ(1 + index))
      (left ·ₘ numₘ(index))
      hCodeRaw hRawPoint
      (hLeft := hCode)
      (hRight := hRawCode)

/--
任意 Gödel quotation 理论扩张中的蕴含左正文逐点平移。

该接口把三个对象前提放入临时上下文后 checked replay，避免上层实例重复展开
五段拼接。
-/
theorem gq_implication_formula_left_point_at_standard_offset_of_theory
    {T : SetTheory} {Γ : Context signature}
    (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (left right : SetTerm) (index : Nat)
    (hLeftFinite :
      Γ ⊢ₘ[T] finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[T] finite_sequence_condition right)
    (hLeftIndex :
      Γ ⊢ₘ[T] numₘ(index) ∈ₘ domₘ(left))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T]
      ((numₘ(1 + index) ∈ₘ
          domₘ(imp_codeₘ(left, right))) ∧ₘ
        ((imp_codeₘ(left, right) ·ₘ numₘ(1 + index)) ≐ₘ
          (left ·ₘ numₘ(index)))) := by
  let Δ : Context signature :=
    finite_sequence_condition left ::
      finite_sequence_condition right ::
        (numₘ(index) ∈ₘ domₘ(left)) :: []
  have hLeftFiniteAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hRightFiniteAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hLeftIndexAt :
      Δ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(left) :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hPoint :=
    gq_implication_formula_left_point_at_standard_offset
      left right index
      hLeftFiniteAt hRightFiniteAt hLeftIndexAt
      (hLeft := hLeft) (hRight := hRight)
  apply FirstOrder.Derives.multi_cut
    (T := T) (Γ := Γ) (premises := Δ)
  · intro formula hFormula
    simp [Δ] at hFormula
    rcases hFormula with rfl | rfl | rfl
    · exact hLeftFinite
    · exact hRightFinite
    · exact hLeftIndex
  · exact
      (FirstOrder.Derives.theory_weaken
        hTheory hPoint).context_weaken_append

/--
任意标准整串等于对象蕴含代码时，已知左正文长度即可恢复整串中紧随首括号的
左正文切片。
-/
theorem gq_implication_left_eq_standard_token_slice_of_domain
    {Γ : Context signature}
    (left right : SetTerm) (tokens : List Nat)
    (leftLength : Nat)
    (hLeftLength : leftLength < tokens.length)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      left ≐ₘ
        standard_token_sequence
          ((tokens.drop 1).take leftLength) := by
  let leftTokens :=
    (tokens.drop 1).take leftLength
  have hLeftTokensLength :
      leftTokens.length = leftLength := by
    simp only [leftTokens, List.length_take,
      List.length_drop]
    omega
  have hLeftFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula left := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hLeftFinite
  have hLeftDomain' :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftTokens.length) := by
    simpa [hLeftTokensLength] using hLeftDomain
  apply
    gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := godel_quotation_theory)
      (Γ := Γ)
      (fun _ hAxiom => Or.inl hAxiom)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      left leftTokens hLeftFunction hLeftDomain'
      (hSource := hLeft)
  intro index token hGet
  have hIndex :
      index < leftTokens.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hIndexNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ numₘ(leftTokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index leftTokens.length hIndex
  have hIndexLeft :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(left) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(left))
        (numₘ(leftTokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible left hLeft.admissible)
        (finite_numeral_term_admissible
          leftTokens.length)
        hLeftDomain')
      hIndexNumeral
  have hSliceIndex :
      index < leftLength := by
    simpa [hLeftTokensLength] using hIndex
  have hDropGet :
      (tokens.drop 1)[index]? = some token := by
    rw [List.getElem?_take_of_lt hSliceIndex] at hGet
    simpa [leftTokens] using hGet
  have hTokenGet :
      tokens[1 + index]? = some token := by
    simpa [Nat.add_comm] using hDropGet
  have hBodyPoint :=
    gq_implication_formula_left_point_at_standard_offset
      left right index
      hLeftFinite hRightFinite hIndexLeft
      (hLeft := hLeft) (hRight := hRight)
  have hCodePoint :=
    gq_standard_token_sequence_point_inversion
      (imp_codeₘ(left, right)) tokens
      (Metatheory.Derives.equality_symm hEquality)
      hTokenGet
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight
        hBodyPoint)
    (FirstOrder.Derives.conjElimRight
      hCodePoint)

/-!
蕴含右正文只需在左长度恢复后即可严格下降。固定左括号与蕴含符号使右正文
前缀长度为 `leftLength + 2`；右正文自身长度保持开放，不传播额外 numeral
等式。
-/
theorem gq_implication_right_domain_mem_code_domain
    {Γ : Context signature}
    (left right : SetTerm)
    (leftLength : Nat)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(right) ∈ₘ
        domₘ(imp_codeₘ(left, right)) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let implicationSymbol :=
    logical_symbol_code_term .implication
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let leftStage := leftParenthesis ⌢ₘ left
  let prefixCode := leftStage ⌢ₘ implicationSymbol
  let bodyStage := prefixCode ⌢ₘ right
  let rawCode := bodyStage ⌢ₘ rightParenthesis
  let code := imp_codeₘ(left, right)
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hImplicationSymbol :
      Term.CheckCertificate implicationSymbol SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hLeftStage :
      Term.CheckCertificate leftStage SetSort.set := by
    prove_term_check
  have hPrefix :
      Term.CheckCertificate prefixCode SetSort.set := by
    prove_term_check
  have hBodyStage :
      Term.CheckCertificate bodyStage SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hImplicationFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition implicationSymbol := by
    simpa [implicationSymbol] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .implication
  have hImplicationDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(implicationSymbol) ≐ₘ numₘ(1) := by
    simpa [implicationSymbol] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .implication
  have hLeftStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftStage := by
    simpa [leftStage] using
      gq_concatenation_finite
        leftParenthesis left
        hLeftParenthesisFinite hLeftFinite
        (hLeft := hLeftParenthesis) (hRight := hLeft)
  have hLeftStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftStage) ≐ₘ
          numₘ(leftLength + 1) := by
    simpa [leftStage, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        leftParenthesis left 1 leftLength
        hLeftParenthesisFinite hLeftFinite
        hLeftParenthesisDomain hLeftDomain
        (hLeft := hLeftParenthesis) (hRight := hLeft)
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        leftStage implicationSymbol
        hLeftStageFinite hImplicationFinite
        (hLeft := hLeftStage)
        (hRight := hImplicationSymbol)
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ
          numₘ((leftLength + 1) + 1) := by
    simpa [prefixCode, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        leftStage implicationSymbol
        (leftLength + 1) 1
        hLeftStageFinite hImplicationFinite
        hLeftStageDomain hImplicationDomain
        (hLeft := hLeftStage)
        (hRight := hImplicationSymbol)
  have hRightInBodyStage :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ∈ₘ domₘ(bodyStage) := by
    simpa [bodyStage] using
      gq_concatenation_right_domain_member_of_positive_left_length
        prefixCode right (leftLength + 1)
        hPrefixFinite hRightFinite hPrefixDomain
        (hLeft := hPrefix) (hRight := hRight)
  have hBodyStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition bodyStage := by
    simpa [bodyStage] using
      gq_concatenation_finite
        prefixCode right hPrefixFinite hRightFinite
        (hLeft := hPrefix) (hRight := hRight)
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRightInRawCode :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ∈ₘ domₘ(rawCode) := by
    simpa [rawCode] using
      gq_concatenation_left_domain_member
        bodyStage rightParenthesis
        (domₘ(right))
        hBodyStageFinite hRightParenthesisFinite
        hRightInBodyStage
        (hLeft := hBodyStage)
        (hRight := hRightParenthesis)
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    have hCodeString :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ
            implication_formula_string_term left right :=
      gq_implication_formula_code_eq_string_of_context
        left right (hLeft := hLeft) (hRight := hRight)
    simpa [code, rawCode, bodyStage, prefixCode,
      leftStage, leftParenthesis, implicationSymbol,
      rightParenthesis, implication_formula_string_term] using
      hCodeString
  have hCodeRawDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ domₘ(rawCode) :=
    domain_term_congr_of_equality
      code rawCode hCode.admissible hRawCode.admissible
      hCodeRaw
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      (domₘ(right))
      (domₘ(code)) (domₘ(rawCode))
      (domain_term_admissible right hRight.admissible)
      (domain_term_admissible code hCode.admissible)
      (domain_term_admissible rawCode hRawCode.admissible)
      hCodeRawDomain)
    hRightInRawCode

/-!
左正文已经恢复为标准切片时，右正文逐点值平移到左括号、左正文与蕴含符号
组成的规范前缀之后。
-/
theorem gq_implication_formula_right_point_at_standard_offset
    {Γ : Context signature}
    (left right : SetTerm) (leftTokens : List Nat)
    (index : Nat)
    (hLeftEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        left ≐ₘ standard_token_sequence leftTokens)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hRightIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(right))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((numₘ(leftTokens.length + 2 + index) ∈ₘ
          domₘ(imp_codeₘ(left, right))) ∧ₘ
        ((imp_codeₘ(left, right) ·ₘ
            numₘ(leftTokens.length + 2 + index)) ≐ₘ
          (right ·ₘ numₘ(index)))) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let implicationSymbol :=
    logical_symbol_code_term .implication
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let leftStage := leftParenthesis ⌢ₘ left
  let prefixCode := leftStage ⌢ₘ implicationSymbol
  let rawCode := (prefixCode ⌢ₘ right) ⌢ₘ rightParenthesis
  let code := imp_codeₘ(left, right)
  let prefixTokens :=
    [Numbered.logical_token .leftParenthesis] ++
      leftTokens ++
        [Numbered.logical_token .implication]
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hImplicationSymbol :
      Term.CheckCertificate implicationSymbol SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hLeftStage :
      Term.CheckCertificate leftStage SetSort.set := by
    prove_term_check
  have hPrefix :
      Term.CheckCertificate prefixCode SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hLeftParenthesisEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ
          standard_token_sequence
            [Numbered.logical_token .leftParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [leftParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis
  have hImplicationEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        implicationSymbol ≐ₘ
          standard_token_sequence
            [Numbered.logical_token .implication] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [implicationSymbol] using
          logical_symbol_code_eq_standard_token_sequence
            .implication
  have hLeftStageEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftStage ≐ₘ
          standard_token_sequence
            ([Numbered.logical_token .leftParenthesis] ++
              leftTokens) := by
    simpa [leftStage] using
      gq_concatenation_eq_standard_token_sequence
        [Numbered.logical_token .leftParenthesis]
        leftTokens leftParenthesis left
        hLeftParenthesisEquality hLeftEquality
        (hLeftCode := hLeftParenthesis)
        (hRightCode := hLeft)
  have hPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence prefixTokens := by
    simpa [prefixCode, prefixTokens,
      List.append_assoc] using
      gq_concatenation_eq_standard_token_sequence
        ([Numbered.logical_token .leftParenthesis] ++
          leftTokens)
        [Numbered.logical_token .implication]
        leftStage implicationSymbol
        hLeftStageEquality hImplicationEquality
        (hLeftCode := hLeftStage)
        (hRightCode := hImplicationSymbol)
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRawPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(prefixTokens.length + index) ∈ₘ
            domₘ(rawCode)) ∧ₘ
          ((rawCode ·ₘ numₘ(prefixTokens.length + index)) ≐ₘ
            (right ·ₘ numₘ(index)))) := by
    simpa [rawCode] using
      gq_concatenation_middle_point_at_standard_offset
        prefixCode right rightParenthesis
        prefixTokens index hPrefixEquality
        hRightFinite hRightParenthesisFinite hRightIndex
        (hPrefix := hPrefix)
        (hBody := hRight)
        (hSuffix := hRightParenthesis)
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    simpa [code, rawCode, prefixCode, leftStage,
      leftParenthesis, implicationSymbol,
      rightParenthesis,
      implication_formula_string_term] using
      gq_implication_formula_code_eq_string_of_context
        (Γ := Γ) left right
        (hLeft := hLeft) (hRight := hRight)
  have hCodePoint :=
    gq_point_inversion_of_equality
      code rawCode
      (numₘ(prefixTokens.length + index))
      (right ·ₘ numₘ(index))
      hCodeRaw hRawPoint
      (hLeft := hCode)
      (hRight := hRawCode)
  simpa [code, prefixTokens, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hCodePoint

/--
任意标准整串等于对象蕴含代码时，已知左右正文长度即可恢复右正文切片。总长度
不匹配的分支由对象层长度矛盾直接消去。
-/
theorem gq_implication_right_eq_standard_token_slice_of_domains
    {Γ : Context signature}
    (left right : SetTerm) (tokens : List Nat)
    (leftLength rightLength : Nat)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength))
    (hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      right ≐ₘ
        standard_token_sequence
          ((tokens.drop (leftLength + 2)).take rightLength) := by
  let leftTokens :=
    (tokens.drop 1).take leftLength
  let rightTokens :=
    (tokens.drop (leftLength + 2)).take rightLength
  by_cases hLength :
      tokens.length = leftLength + rightLength + 3
  · have hLeftLength :
        leftLength < tokens.length := by
      omega
    have hLeftTokensLength :
        leftTokens.length = leftLength := by
      simp only [leftTokens, List.length_take,
        List.length_drop]
      omega
    have hRightTokensLength :
        rightTokens.length = rightLength := by
      simp only [rightTokens, List.length_take,
        List.length_drop]
      omega
    have hLeftEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          left ≐ₘ standard_token_sequence leftTokens := by
      simpa [leftTokens] using
        gq_implication_left_eq_standard_token_slice_of_domain
          left right tokens leftLength hLeftLength
          hLeftFinite hRightFinite hLeftDomain hEquality
          (hLeft := hLeft) (hRight := hRight)
    have hRightFunction :
        Γ ⊢ₘ[godel_quotation_theory]
          is_function_formula right := by
      simpa [finite_sequence_condition] using
        FirstOrder.Derives.conjElimLeft hRightFinite
    have hRightDomain' :
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(right) ≐ₘ numₘ(rightTokens.length) := by
      simpa [hRightTokensLength] using hRightDomain
    apply
      gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
        (T := godel_quotation_theory)
        (Γ := Γ)
        (fun _ hAxiom => Or.inl hAxiom)
        (fun _ hFormula =>
          godel_quotation_theory_sentence hFormula)
        right rightTokens hRightFunction hRightDomain'
        (hSource := hRight)
    intro index token hGet
    have hIndex :
        index < rightTokens.length :=
      (List.getElem?_eq_some_iff.mp hGet).1
    have hIndexNumeral :
        Γ ⊢ₘ[godel_quotation_theory]
          numₘ(index) ∈ₘ numₘ(rightTokens.length) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_of_lt
              index rightTokens.length hIndex
    have hIndexRight :
        Γ ⊢ₘ[godel_quotation_theory]
          numₘ(index) ∈ₘ domₘ(right) :=
      FirstOrder.Derives.iffElimLeft
        (membership_right_iff_of_equality
          (numₘ(index))
          (domₘ(right))
          (numₘ(rightTokens.length))
          (finite_numeral_term_admissible index)
          (domain_term_admissible right hRight.admissible)
          (finite_numeral_term_admissible
            rightTokens.length)
          hRightDomain')
        hIndexNumeral
    have hSliceIndex :
        index < rightLength := by
      simpa [hRightTokensLength] using hIndex
    have hDropGet :
        (tokens.drop (leftLength + 2))[index]? =
          some token := by
      rw [List.getElem?_take_of_lt hSliceIndex] at hGet
      simpa [rightTokens] using hGet
    have hTokenGet :
        tokens[leftLength + 2 + index]? = some token := by
      simpa using hDropGet
    have hBodyPoint :=
      gq_implication_formula_right_point_at_standard_offset
        left right leftTokens index
        hLeftEquality hRightFinite hIndexRight
        (hLeft := hLeft) (hRight := hRight)
    have hCodePoint :=
      gq_standard_token_sequence_point_inversion
        (imp_codeₘ(left, right)) tokens
        (Metatheory.Derives.equality_symm hEquality)
        hTokenGet
    have hBodyPoint' :
        Γ ⊢ₘ[godel_quotation_theory]
          ((numₘ(leftLength + 2 + index) ∈ₘ
              domₘ(imp_codeₘ(left, right))) ∧ₘ
            ((imp_codeₘ(left, right) ·ₘ
                numₘ(leftLength + 2 + index)) ≐ₘ
              (right ·ₘ numₘ(index)))) := by
      simpa [hLeftTokensLength] using hBodyPoint
    exact Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <|
        FirstOrder.Derives.conjElimRight hBodyPoint')
      (FirstOrder.Derives.conjElimRight hCodePoint)
  · have hCodeString :
        Γ ⊢ₘ[godel_quotation_theory]
          imp_codeₘ(left, right) ≐ₘ
            implication_formula_string_term left right :=
      gq_implication_formula_code_eq_string_of_context
        (Γ := Γ) left right
        (hLeft := hLeft) (hRight := hRight)
    have hStringEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          standard_token_sequence tokens ≐ₘ
            implication_formula_string_term left right :=
      Metatheory.Derives.equality_trans
        hEquality hCodeString
    exact FirstOrder.Derives.falsumElim <|
      gq_implication_standard_code_falsum_of_length_ne
        left right tokens leftLength rightLength
        hLeftFinite hRightFinite
        hLeftDomain hRightDomain
        hStringEquality hLength
        (hLeft := hLeft) (hRight := hRight)

/--
已知左右正文定义域长度时，任意标准整串同时恢复两个正文切片。总长度错误时，
结论由对象层矛盾给出；总长度正确时，两段分别按固定偏移反演。
-/
theorem gq_implication_bodies_eq_standard_token_slices_of_domains
    {Γ : Context signature}
    (left right : SetTerm) (tokens : List Nat)
    (leftLength rightLength : Nat)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength))
    (hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      (left ≐ₘ
          standard_token_sequence
            ((tokens.drop 1).take leftLength)) ∧ₘ
        (right ≐ₘ
          standard_token_sequence
            ((tokens.drop (leftLength + 2)).take rightLength)) := by
  by_cases hLength :
      tokens.length = leftLength + rightLength + 3
  · have hLeftLength :
        leftLength < tokens.length := by
      omega
    exact FirstOrder.Derives.conjIntro
      (gq_implication_left_eq_standard_token_slice_of_domain
        left right tokens leftLength hLeftLength
        hLeftFinite hRightFinite hLeftDomain hEquality
        (hLeft := hLeft) (hRight := hRight))
      (gq_implication_right_eq_standard_token_slice_of_domains
        left right tokens leftLength rightLength
        hLeftFinite hRightFinite
        hLeftDomain hRightDomain hEquality
        (hLeft := hLeft) (hRight := hRight))
  · have hCodeString :
        Γ ⊢ₘ[godel_quotation_theory]
          imp_codeₘ(left, right) ≐ₘ
            implication_formula_string_term left right :=
      gq_implication_formula_code_eq_string_of_context
        (Γ := Γ) left right
        (hLeft := hLeft) (hRight := hRight)
    have hStringEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          standard_token_sequence tokens ≐ₘ
            implication_formula_string_term left right :=
      Metatheory.Derives.equality_trans
        hEquality hCodeString
    exact FirstOrder.Derives.falsumElim <|
      gq_implication_standard_code_falsum_of_length_ne
        left right tokens leftLength rightLength
        hLeftFinite hRightFinite
        hLeftDomain hRightDomain
        hStringEquality hLength
        (hLeft := hLeft) (hRight := hRight)

/--
任意整串不等于由其两段长度重建出的规范蕴含串时，对象构造等式推出矛盾。
该结论是 parser 强归纳中排除错误分割的公共入口。
-/
theorem gq_implication_standard_code_falsum_of_not_slice_shape
    {Γ : Context signature}
    (left right : SetTerm) (tokens : List Nat)
    (leftLength rightLength : Nat)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength))
    (hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right))
    (hShape :
      tokens ≠
        Numbered.implication_tokens
          ((tokens.drop 1).take leftLength)
          ((tokens.drop (leftLength + 2)).take rightLength))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let leftTokens :=
    (tokens.drop 1).take leftLength
  let rightTokens :=
    (tokens.drop (leftLength + 2)).take rightLength
  have hBodies :=
    gq_implication_bodies_eq_standard_token_slices_of_domains
      left right tokens leftLength rightLength
      hLeftFinite hRightFinite
      hLeftDomain hRightDomain hEquality
      (hLeft := hLeft) (hRight := hRight)
  have hCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        imp_codeₘ(left, right) ≐ₘ
          implication_formula_string_term left right :=
    gq_implication_formula_code_eq_string_of_context
      (Γ := Γ) left right
      (hLeft := hLeft) (hRight := hRight)
  have hStringStandard :
      Γ ⊢ₘ[godel_quotation_theory]
        implication_formula_string_term left right ≐ₘ
          standard_token_sequence
            (Numbered.implication_tokens
              leftTokens rightTokens) :=
    gq_implication_formula_string_eq_standard_token_sequence_of_context
      leftTokens rightTokens left right
      (FirstOrder.Derives.conjElimLeft hBodies)
      (FirstOrder.Derives.conjElimRight hBodies)
      (hLeftCode := hLeft) (hRightCode := hRight)
  have hStandardEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          standard_token_sequence
            (Numbered.implication_tokens
              leftTokens rightTokens) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_trans
        hEquality hCodeString)
      hStringStandard
  have hNotEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        ¬ₘ (standard_token_sequence tokens ≐ₘ
          standard_token_sequence
            (Numbered.implication_tokens
              leftTokens rightTokens)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_token_sequence_ne <| by
            simpa [leftTokens, rightTokens] using hShape
  exact FirstOrder.Derives.negElim
    hStandardEquality hNotEquality

/-!
蕴含右正文的标准序列等式只需左正文长度。右正文长度由其定义域属于
完整构造码的对象层证书逐个消去；错误长度分支直接在对象层闭合。
-/
theorem gq_implication_right_eq_standard_token_sequence_of_left_domain
    {Γ : Context signature}
    (left right : SetTerm)
    (leftTokens rightTokens : List Nat)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftTokens.length))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.implication_tokens
              leftTokens rightTokens) ≐ₘ
          implication_formula_string_term left right)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      right ≐ₘ standard_token_sequence rightTokens := by
  let code : SetTerm := imp_codeₘ(left, right)
  let tokens : List Nat :=
    Numbered.implication_tokens leftTokens rightTokens
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ implication_formula_string_term left right := by
    simpa [code] using
      gq_implication_formula_code_eq_string_of_context
        left right (hLeft := hLeft) (hRight := hRight)
  have hEqualityCode :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ code :=
    Metatheory.Derives.equality_trans
      hEquality
      (Metatheory.Derives.equality_symm hCodeString)
  have hRightMember :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ∈ₘ domₘ(code) := by
    simpa [code] using
      gq_implication_right_domain_mem_code_domain
        left right leftTokens.length
        hLeftFinite hRightFinite hLeftDomain
        (hLeft := hLeft) (hRight := hRight)
  have hCodeDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(tokens.length) := by
    simpa [code] using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        code tokens
        (Metatheory.Derives.equality_symm hEqualityCode)
        (hCode := hCode)
  apply
    gq_domain_length_elim_of_member_of_standard_equality
      (child := right)
      (parent := code)
      tokens
      (right ≐ₘ standard_token_sequence rightTokens)
      hRightMember
      (by simpa [code, tokens] using hEqualityCode)
  intro rightLength hRightLength
  let candidate : SetFormula :=
    domₘ(right) ≐ₘ numₘ(rightLength)
  let Δ : Context signature :=
    candidate :: Γ
  have hRightDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightLength) :=
    FirstOrder.Derives.assumption
      (by simp [candidate, Δ])
  have hLeftFinite' :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ)
      (by
        intro formula hFormula
        exact List.mem_cons_of_mem candidate hFormula)
      hLeftFinite
  have hRightFinite' :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ)
      (by
        intro formula hFormula
        exact List.mem_cons_of_mem candidate hFormula)
      hRightFinite
  have hLeftDomain' :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftTokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ)
      (by
        intro formula hFormula
        exact List.mem_cons_of_mem candidate hFormula)
      hLeftDomain
  have hCandidateDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ
          numₘ(leftTokens.length + rightLength + 3) := by
    simpa [code, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      gq_implication_formula_domain_eq_numeral_lengths
        left right leftTokens.length rightLength
        hLeftFinite' hRightFinite'
        hLeftDomain' hRightDomain
        (hLeft := hLeft) (hRight := hRight)
  have hCodeDomain' :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(tokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ)
      (by
        intro formula hFormula
        exact List.mem_cons_of_mem candidate hFormula)
      hCodeDomain
  have hNumeralEquality :
      Δ ⊢ₘ[godel_quotation_theory]
        numₘ(tokens.length) ≐ₘ
          numₘ(leftTokens.length + rightLength + 3) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hCodeDomain')
      hCandidateDomain
  have hEqualityString :
      Δ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.implication_tokens
              leftTokens rightTokens) ≐ₘ
          implication_formula_string_term left right :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ)
      (by
        intro formula hFormula
        exact List.mem_cons_of_mem candidate hFormula)
      hEquality
  by_cases hCorrect : rightLength = rightTokens.length
  · have hRightDomain' :
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(right) ≐ₘ numₘ(rightTokens.length) := by
      simpa [candidate, Δ, hCorrect] using hRightDomain
    simpa [code] using
      gq_implication_right_eq_standard_token_sequence_of_domains
        left right leftTokens rightTokens
        hLeftFinite' hRightFinite'
        hLeftDomain' hRightDomain' hEqualityString
        (hLeft := hLeft) (hRight := hRight)
  · have hDifferent :
        tokens.length ≠
          leftTokens.length + rightLength + 3 := by
      intro hNumeralLength
      apply hCorrect
      simp [tokens, Numbered.implication_tokens] at hNumeralLength
      omega
    have hNotEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          ¬ₘ (numₘ(tokens.length) ≐ₘ
            numₘ(leftTokens.length + rightLength + 3)) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_ne hDifferent
    exact FirstOrder.Derives.falsumElim <|
      FirstOrder.Derives.negElim
        hNumeralEquality hNotEquality

/-! 左长度已固定时，蕴含两正文的联合反演只传播最弱的长度接口。 -/
theorem gq_implication_bodies_eq_standard_token_sequences_of_left_domain
    {Γ : Context signature}
    (left right : SetTerm)
    (leftTokens rightTokens : List Nat)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftTokens.length))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.implication_tokens
              leftTokens rightTokens) ≐ₘ
          implication_formula_string_term left right)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      (left ≐ₘ standard_token_sequence leftTokens) ∧ₘ
        (right ≐ₘ standard_token_sequence rightTokens) :=
  FirstOrder.Derives.conjIntro
    (gq_implication_left_eq_standard_token_sequence_of_domain
      left right leftTokens rightTokens
      hLeftFinite hRightFinite hLeftDomain hEquality
      (hLeft := hLeft) (hRight := hRight))
    (gq_implication_right_eq_standard_token_sequence_of_left_domain
      left right leftTokens rightTokens
      hLeftFinite hRightFinite hLeftDomain hEquality
      (hLeft := hLeft) (hRight := hRight))

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
