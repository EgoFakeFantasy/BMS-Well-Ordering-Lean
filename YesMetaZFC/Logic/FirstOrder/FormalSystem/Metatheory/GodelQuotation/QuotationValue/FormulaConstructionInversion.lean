import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstruction

/-!
# Gödel quotation 的公式构造反演

本模块从一个已知标准 token 串与对象公式构造代码的等式，反向恢复各递归子代码。
证明只使用有限序列、对象自然数的固定有限计算与 numeral 有限分类。
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
否定正文的定义域严格落在整个否定代码的定义域内。

正文长度只需是对象自然数；证明把固定双 token 前缀计算为两次后继，再沿末尾
右括号的拼接提升成员关系，不预先假定正文长度是任何外部 numeral。
-/
theorem gq_negation_body_domain_mem_code_domain
    {Γ : Context signature} (body : SetTerm)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(body) ∈ₘ domₘ(neg_codeₘ(body)) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let negationSymbol :=
    logical_symbol_code_term .negation
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let prefixCode := leftParenthesis ⌢ₘ negationSymbol
  let stage := prefixCode ⌢ₘ body
  let rawCode := stage ⌢ₘ rightParenthesis
  let code := neg_codeₘ(body)
  let bodyDomain := domₘ(body)
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hNegationSymbol :
      Term.CheckCertificate negationSymbol SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hPrefix :
      Term.CheckCertificate prefixCode SetSort.set := by
    prove_term_check
  have hStage :
      Term.CheckCertificate stage SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hBodyDomain :
      Term.CheckCertificate bodyDomain SetSort.set := by
    prove_term_check
  have hBodyOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyDomain ∈ₘ ωₘ := by
    simpa [bodyDomain, finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hBodyFinite
  have hPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence
            [logical_token .leftParenthesis,
              logical_token .negation] := by
    simpa [prefixCode] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis]
        [logical_token .negation]
        leftParenthesis negationSymbol
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <| by
            simpa [leftParenthesis] using
              logical_symbol_code_eq_standard_token_sequence
                .leftParenthesis)
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <| by
            simpa [negationSymbol] using
              logical_symbol_code_eq_standard_token_sequence
                .negation)
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode :=
    gq_finite_sequence_of_eq_standard_token_sequence
      prefixCode
      [logical_token .leftParenthesis,
        logical_token .negation]
      hPrefixEquality
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ numₘ(2) := by
    simpa using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        prefixCode
        [logical_token .leftParenthesis,
          logical_token .negation]
        hPrefixEquality
  have hStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition stage := by
    simpa [stage] using
      gq_concatenation_finite
        prefixCode body hPrefixFinite hBodyFinite
  have hStageDomainRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(stage) ≐ₘ
          (domₘ(prefixCode) +ₘ bodyDomain) := by
    simpa [stage, bodyDomain] using
      gq_concatenation_domain_eq_sum_of_theory
        (fun _ hAxiom => hAxiom)
        prefixCode body hPrefixFinite hBodyFinite
  have hStageDomainCongruence :
      Γ ⊢ₘ[godel_quotation_theory]
        (domₘ(prefixCode) +ₘ bodyDomain) ≐ₘ
          (numₘ(2) +ₘ bodyDomain) :=
    natural_addition_term_congr_of_equalities
      (domₘ(prefixCode)) (numₘ(2))
      bodyDomain bodyDomain
      (domain_term_admissible prefixCode hPrefix.admissible)
      (finite_numeral_term_admissible 2)
      hBodyDomain.admissible hBodyDomain.admissible
      hPrefixDomain
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) bodyDomain)
  have hStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(stage) ≐ₘ
          (numₘ(2) +ₘ bodyDomain) :=
    Metatheory.Derives.equality_trans
      hStageDomainRaw hStageDomainCongruence
  have hOneAddition :
      Γ ⊢ₘ[godel_quotation_theory]
        (numₘ(1) +ₘ bodyDomain) ≐ₘ
          Sₘ(bodyDomain) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            standard_sequence_one_addition_eq_successor
              bodyDomain hBodyDomain.admissible)
      hBodyOmega
  have hBodyInSuccessor :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyDomain ∈ₘ Sₘ(bodyDomain) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_weaken_successor <|
            mem_successor_self
              bodyDomain hBodyDomain.admissible
  have hBodyInOneAddition :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyDomain ∈ₘ
          (numₘ(1) +ₘ bodyDomain) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        bodyDomain
        (numₘ(1) +ₘ bodyDomain)
        (Sₘ(bodyDomain))
        hBodyDomain.admissible
        (natural_addition_term_admissible
          (numₘ(1)) bodyDomain
          (finite_numeral_term_admissible 1)
          hBodyDomain.admissible)
        (successor_term_admissible
          bodyDomain hBodyDomain.admissible)
        hOneAddition)
      hBodyInSuccessor
  have hBodyInSuccessorOneAddition :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyDomain ∈ₘ
          Sₘ(numₘ(1) +ₘ bodyDomain) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            standard_sequence_weaken_successor <|
              mem_successor_of_mem
                (numₘ(1) +ₘ bodyDomain)
                bodyDomain
                (natural_addition_term_admissible
                  (numₘ(1)) bodyDomain
                  (finite_numeral_term_admissible 1)
                  hBodyDomain.admissible)
                hBodyDomain.admissible)
      hBodyInOneAddition
  have hTwoAddition :
      Γ ⊢ₘ[godel_quotation_theory]
        (numₘ(2) +ₘ bodyDomain) ≐ₘ
          Sₘ(numₘ(1) +ₘ bodyDomain) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            standard_sequence_two_addition_eq_successor_one
              bodyDomain hBodyDomain.admissible)
      hBodyOmega
  have hBodyInTwoAddition :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyDomain ∈ₘ
          (numₘ(2) +ₘ bodyDomain) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        bodyDomain
        (numₘ(2) +ₘ bodyDomain)
        (Sₘ(numₘ(1) +ₘ bodyDomain))
        hBodyDomain.admissible
        (natural_addition_term_admissible
          (numₘ(2)) bodyDomain
          (finite_numeral_term_admissible 2)
          hBodyDomain.admissible)
        (successor_term_admissible
          (numₘ(1) +ₘ bodyDomain)
          (natural_addition_term_admissible
            (numₘ(1)) bodyDomain
            (finite_numeral_term_admissible 1)
            hBodyDomain.admissible))
        hTwoAddition)
      hBodyInSuccessorOneAddition
  have hBodyInStage :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyDomain ∈ₘ domₘ(stage) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        bodyDomain
        (domₘ(stage))
        (numₘ(2) +ₘ bodyDomain)
        hBodyDomain.admissible
        (domain_term_admissible stage hStage.admissible)
        (natural_addition_term_admissible
          (numₘ(2)) bodyDomain
          (finite_numeral_term_admissible 2)
          hBodyDomain.admissible)
        hStageDomain)
      hBodyInTwoAddition
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hBodyInRawCode :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyDomain ∈ₘ domₘ(rawCode) := by
    simpa [rawCode] using
      gq_concatenation_left_domain_member
        stage rightParenthesis bodyDomain
        hStageFinite hRightParenthesisFinite
        hBodyInStage
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    have hDefinition :
        Γ ⊢ₘ[godel_quotation_theory]
          negation_formula_code_definition_instance
            body code :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_formula_constructor <|
            negation_formula_code_definition_instance_derives
              body code hBody.admissible hCode.admissible
    have hReflexive :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ neg_codeₘ(body) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <| by
          simpa [code] using
            FirstOrder.Derives.eq_refl_m code
    simpa [code, rawCode, stage, prefixCode,
      leftParenthesis, negationSymbol,
      rightParenthesis,
      negation_formula_code_definition_instance,
      negation_formula_string_term] using
        FirstOrder.Derives.iffElimRight
          hDefinition hReflexive
  have hCodeRawDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ domₘ(rawCode) :=
    domain_term_congr_of_equality
      code rawCode hCode.admissible hRawCode.admissible
      hCodeRaw
  simpa [code, bodyDomain] using
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        bodyDomain
        (domₘ(code)) (domₘ(rawCode))
        hBodyDomain.admissible
        (domain_term_admissible code hCode.admissible)
        (domain_term_admissible rawCode hRawCode.admissible)
        hCodeRawDomain)
      hBodyInRawCode

/--
任意标准 token 串等于对象否定构造代码时，正文定义域必须恰为总长度减去三个
固定 token。

先由正文定义域属于整个构造代码得到有限上界，再枚举该具体 numeral 内的候选
长度。唯一不矛盾的候选满足 `bodyLength + 3 = tokens.length`。
-/
theorem gq_negation_body_domain_eq_of_standard_code_equality
    {Γ : Context signature}
    (body : SetTerm) (tokens : List Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          neg_codeₘ(body))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(body) ≐ₘ numₘ(tokens.length - 3) := by
  let code := neg_codeₘ(body)
  let bodyDomain := domₘ(body)
  let bound := tokens.length
  let conclusion : SetFormula :=
    bodyDomain ≐ₘ numₘ(tokens.length - 3)
  let condition : SetFormula :=
    stdseq_numeral_member_condition
      bound bodyDomain
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hBodyDomain :
      Term.CheckCertificate bodyDomain SetSort.set := by
    prove_term_check
  have hCodeDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(bound) := by
    simpa [code, bound] using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        code tokens
        (Metatheory.Derives.equality_symm hEquality)
  have hBodyDomainMember :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyDomain ∈ₘ domₘ(code) := by
    simpa [code, bodyDomain] using
      gq_negation_body_domain_mem_code_domain
        body hBodyFinite
  have hBodyDomainBound :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyDomain ∈ₘ numₘ(bound) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        bodyDomain
        (domₘ(code)) (numₘ(bound))
        hBodyDomain.admissible
        (domain_term_admissible code hCode.admissible)
        (finite_numeral_term_admissible bound)
        hCodeDomain)
      hBodyDomainMember
  have hNumeralIff :
      Γ ⊢ₘ[godel_quotation_theory]
        (bodyDomain ∈ₘ numₘ(bound)) ↔ₘ
          condition :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <| by
          simpa [condition] using
            stdseq_numeral_member_iff
              bound bodyDomain hBodyDomain.admissible
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        condition :=
    FirstOrder.Derives.iffElimRight
      hNumeralIff hBodyDomainBound
  have hCases :
      condition :: Γ ⊢ₘ[godel_quotation_theory]
        conclusion := by
    apply stdseq_numeral_member_condition_elim_context
      bound bodyDomain conclusion
    intro index hIndex
    let equality : SetFormula :=
      bodyDomain ≐ₘ numₘ(index)
    let Δ : Context signature := equality :: Γ
    have hCandidate :
        Δ ⊢ₘ[godel_quotation_theory]
          bodyDomain ≐ₘ numₘ(index) := by
      simpa [Δ, equality] using
        (FirstOrder.Derives.assumption
          (T := godel_quotation_theory)
          (Γ := Δ) (φ := equality)
          (by simp [Δ]))
    by_cases hCorrect :
        index + 3 = bound
    · have hIndex :
          index = tokens.length - 3 := by
        simp only [bound] at hCorrect
        omega
      simpa [Δ, equality, conclusion, hIndex] using
        hCandidate
    · have hBodyFinite' :
          Δ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition body :=
        FirstOrder.Derives.context_weaken
          (Γ := Γ) (Δ := Δ)
          (by
            intro formula hFormula
            simpa [Δ] using
              List.mem_cons_of_mem equality hFormula)
          hBodyFinite
      have hCandidateDomain :
          Δ ⊢ₘ[godel_quotation_theory]
            domₘ(code) ≐ₘ
              numₘ(index + 3) := by
        simpa [code, bodyDomain] using
          gq_negation_formula_domain_eq_numeral_length
            body index hBodyFinite' hCandidate
      have hActualDomain :
          Δ ⊢ₘ[godel_quotation_theory]
            domₘ(code) ≐ₘ numₘ(bound) :=
        FirstOrder.Derives.context_weaken
          (Γ := Γ) (Δ := Δ)
          (by
            intro formula hFormula
            simpa [Δ] using
              List.mem_cons_of_mem equality hFormula)
          hCodeDomain
      have hNumeralEquality :
          Δ ⊢ₘ[godel_quotation_theory]
            numₘ(index + 3) ≐ₘ numₘ(bound) :=
        Metatheory.Derives.equality_trans
          (Metatheory.Derives.equality_symm
            hCandidateDomain)
          hActualDomain
      have hDifferent :
          index + 3 ≠ bound := by
        exact hCorrect
      have hNotEquality :
          Δ ⊢ₘ[godel_quotation_theory]
            ¬ₘ (numₘ(index + 3) ≐ₘ numₘ(bound)) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) <|
            gq_weaken_standard_sequence <|
              standard_sequence_finite_numeral_ne
                hDifferent
      exact FirstOrder.Derives.falsumElim <|
        FirstOrder.Derives.negElim
          hNumeralEquality hNotEquality
  simpa [condition, conclusion] using
    FirstOrder.Derives.cut hCondition hCases

/--
标准否定 token 串的专用长度反演；固定三 token 外壳化简后直接恢复正文长度。
-/
theorem gq_negation_body_domain_eq_of_standard_equality
    {Γ : Context signature}
    (body : SetTerm) (bodyTokens : List Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (negation_tokens bodyTokens) ≐ₘ
          neg_codeₘ(body))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(body) ≐ₘ numₘ(bodyTokens.length) := by
  simpa [Numbered.negation_tokens] using
    gq_negation_body_domain_eq_of_standard_code_equality
      body (negation_tokens bodyTokens)
      hBodyFinite hEquality

/--
任意标准整串等于对象否定代码时，正文等于去掉双 token 前缀与末 token 后得到的
标准中段。若整串长度不足三，前一条长度反演已在对象层排除该情形。
-/
theorem gq_negation_body_eq_standard_token_slice
    {Γ : Context signature}
    (body : SetTerm) (tokens : List Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          neg_codeₘ(body))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      body ≐ₘ
        standard_token_sequence
          ((tokens.drop 2).take (tokens.length - 3)) := by
  let bodyTokens :=
    (tokens.drop 2).take (tokens.length - 3)
  have hBodyTokensLength :
      bodyTokens.length = tokens.length - 3 := by
    simp only [bodyTokens, List.length_take,
      List.length_drop]
    omega
  have hBodyFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula body := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hBodyFinite
  have hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyTokens.length) := by
    simpa [hBodyTokensLength] using
      gq_negation_body_domain_eq_of_standard_code_equality
        body tokens hBodyFinite hEquality
  apply
    gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := godel_quotation_theory)
      (Γ := Γ)
      (fun _ hAxiom => Or.inl hAxiom)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      body bodyTokens hBodyFunction hBodyDomain
  intro index token hGet
  have hIndex :
      index < bodyTokens.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hIndexNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ
          numₘ(bodyTokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index bodyTokens.length hIndex
  have hIndexBody :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(body) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(body))
        (numₘ(bodyTokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible body hBody.admissible)
        (finite_numeral_term_admissible
          bodyTokens.length)
        hBodyDomain)
      hIndexNumeral
  have hBodyPoint :=
    gq_negation_formula_body_point_at_standard_offset
      body index hBodyFinite hIndexBody
  have hSliceIndex :
      index < tokens.length - 3 := by
    simpa [hBodyTokensLength] using hIndex
  have hDropGet :
      (tokens.drop 2)[index]? = some token := by
    rw [List.getElem?_take_of_lt hSliceIndex] at hGet
    simpa [bodyTokens] using hGet
  have hTokenGet :
      tokens[2 + index]? = some token := by
    simpa using hDropGet
  have hCodePoint :=
    gq_standard_token_sequence_point_inversion
      (neg_codeₘ(body)) tokens
      (Metatheory.Derives.equality_symm hEquality)
      hTokenGet
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight
        hBodyPoint)
    (FirstOrder.Derives.conjElimRight
      hCodePoint)

/--
标准整串与对象否定代码相等，但整串不等于由其中段重建出的规范否定串时，
对象层推出矛盾。该接口把正文反演与标准序列外部列表互异性组合成 parser
否定分支可直接消费的拒绝结论。
-/
theorem gq_negation_standard_code_falsum_of_not_slice_shape
    {Γ : Context signature}
    (body : SetTerm) (tokens : List Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          neg_codeₘ(body))
    (hShape :
      tokens ≠
        negation_tokens
          ((tokens.drop 2).take
            (tokens.length - 3)))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let bodyTokens :=
    (tokens.drop 2).take (tokens.length - 3)
  have hBodyEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        body ≐ₘ standard_token_sequence bodyTokens := by
    simpa [bodyTokens] using
      gq_negation_body_eq_standard_token_slice
        body tokens hBodyFinite hEquality
  have hCodeEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        neg_codeₘ(body) ≐ₘ
          standard_token_sequence
            (negation_tokens bodyTokens) :=
    gq_negation_formula_code_eq_standard_token_sequence_of_context
      bodyTokens body hBodyEquality
  have hStandardEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          standard_token_sequence
            (negation_tokens bodyTokens) :=
    Metatheory.Derives.equality_trans
      hEquality hCodeEquality
  have hNotEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        ¬ₘ (standard_token_sequence tokens ≐ₘ
          standard_token_sequence
            (negation_tokens bodyTokens)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_token_sequence_ne <| by
            simpa [bodyTokens] using hShape
  exact FirstOrder.Derives.negElim
    hStandardEquality hNotEquality

/--
标准否定 token 串等于对象否定构造代码时，正文代码就是对应的标准正文串。
长度由上一条有限分类定理恢复，逐点值则由否定构造的固定偏移 `2` 反演。
-/
theorem gq_negation_body_eq_standard_token_sequence
    {Γ : Context signature}
    (body : SetTerm) (bodyTokens : List Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (negation_tokens bodyTokens) ≐ₘ
          neg_codeₘ(body))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      body ≐ₘ standard_token_sequence bodyTokens := by
  have hBodyFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula body := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hBodyFinite
  have hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyTokens.length) :=
    gq_negation_body_domain_eq_of_standard_equality
      body bodyTokens hBodyFinite hEquality
  apply
    gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := godel_quotation_theory)
      (Γ := Γ)
      (fun _ hAxiom => Or.inl hAxiom)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      body bodyTokens hBodyFunction hBodyDomain
  intro index token hGet
  have hIndex :
      index < bodyTokens.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hIndexNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ
          numₘ(bodyTokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index bodyTokens.length hIndex
  have hIndexBody :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(body) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(body))
        (numₘ(bodyTokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible body hBody.admissible)
        (finite_numeral_term_admissible
          bodyTokens.length)
        hBodyDomain)
      hIndexNumeral
  have hBodyPoint :=
    gq_negation_formula_body_point_at_standard_offset
      body index hBodyFinite hIndexBody
  have hBodySuffixGet :
      (bodyTokens ++
          [logical_token .rightParenthesis])[index]? =
        some token := by
    rw [List.getElem?_append_left hIndex]
    exact hGet
  have hNegationGet :
      (negation_tokens bodyTokens)[2 + index]? =
        some token := by
    have hRaw :
        ([logical_token .leftParenthesis,
            logical_token .negation] ++
          (bodyTokens ++
            [logical_token .rightParenthesis]))[2 + index]? =
          some token := by
      rw [List.getElem?_append_right]
      · simpa using hBodySuffixGet
      · simp
    simpa [Numbered.negation_tokens,
      List.append_assoc] using hRaw
  have hCodePoint :=
    gq_standard_token_sequence_point_inversion
      (neg_codeₘ(body))
      (negation_tokens bodyTokens)
      (Metatheory.Derives.equality_symm hEquality)
      hNegationGet
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight
        hBodyPoint)
      (FirstOrder.Derives.conjElimRight
        hCodePoint)

/-- 蕴含公式的左正文可由已知长度和标准整串等式反演。 -/
theorem gq_implication_left_eq_standard_token_sequence_of_domain
    {Γ : Context signature}
    (left right : SetTerm) (leftTokens rightTokens : List Nat)
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
            (implication_tokens leftTokens rightTokens) ≐ₘ
          implication_formula_string_term left right)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      left ≐ₘ standard_token_sequence leftTokens := by
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
  let leftStageTokens :=
    [logical_token .leftParenthesis] ++ leftTokens
  let prefixTokens := leftStageTokens ++
    [logical_token .implication]
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
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hImplicationSymbolFinite :
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
  have hImplicationSymbolDomain :
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
        domₘ(leftStage) ≐ₘ numₘ(leftStageTokens.length) := by
    simpa [leftStageTokens, leftStage, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        leftParenthesis left 1 leftTokens.length
        hLeftParenthesisFinite hLeftFinite
        hLeftParenthesisDomain hLeftDomain
        (hLeft := hLeftParenthesis) (hRight := hLeft)
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        leftStage implicationSymbol
        hLeftStageFinite hImplicationSymbolFinite
        (hLeft := hLeftStage) (hRight := hImplicationSymbol)
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ numₘ(prefixTokens.length) := by
    simpa [prefixTokens, leftStageTokens, prefixCode,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        leftStage implicationSymbol
        leftStageTokens.length 1
        hLeftStageFinite hImplicationSymbolFinite
        hLeftStageDomain hImplicationSymbolDomain
        (hLeft := hLeftStage) (hRight := hImplicationSymbol)
  have hBodyStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition bodyStage := by
    simpa [bodyStage] using
      gq_concatenation_finite
        prefixCode right
        hPrefixFinite hRightFinite
        (hLeft := hPrefix) (hRight := hRight)
  have hRawCodeFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rawCode := by
    simpa [rawCode] using
      gq_concatenation_finite
        bodyStage rightParenthesis
        hBodyStageFinite hRightParenthesisFinite
        (hLeft := by prove_term_check)
        (hRight := hRightParenthesis)
  have hPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ standard_token_sequence prefixTokens := by
    have hPrefixFunction :
        Γ ⊢ₘ[godel_quotation_theory]
          is_function_formula prefixCode := by
      simpa [finite_sequence_condition] using
        FirstOrder.Derives.conjElimLeft hPrefixFinite
    apply
      gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
        (T := godel_quotation_theory)
        (Γ := Γ)
        (fun _ hAxiom => Or.inl hAxiom)
        (fun _ hFormula =>
          godel_quotation_theory_sentence hFormula)
        prefixCode prefixTokens hPrefixFunction hPrefixDomain
    intro index token hGet
    have hIndex :
        index < prefixTokens.length :=
      (List.getElem?_eq_some_iff.mp hGet).1
    have hIndexInNumeral :
        Γ ⊢ₘ[godel_quotation_theory]
          numₘ(index) ∈ₘ numₘ(prefixTokens.length) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index prefixTokens.length hIndex
    have hIndexInPrefix :
        Γ ⊢ₘ[godel_quotation_theory]
          numₘ(index) ∈ₘ domₘ(prefixCode) :=
      FirstOrder.Derives.iffElimLeft
        (membership_right_iff_of_equality
          (numₘ(index))
          (domₘ(prefixCode))
          (numₘ(prefixTokens.length))
          (finite_numeral_term_admissible index)
          (domain_term_admissible prefixCode hPrefix.admissible)
          (finite_numeral_term_admissible prefixTokens.length)
          hPrefixDomain)
        hIndexInNumeral
    have hRawGet :
        (implication_tokens leftTokens rightTokens)[index]? =
          some token := by
      have hPrefixGet :
          ([logical_token .leftParenthesis] ++ leftTokens ++
              [logical_token .implication])[index]? =
            some token := by
        simpa [prefixTokens, leftStageTokens,
          List.append_assoc] using hGet
      rw [show implication_tokens leftTokens rightTokens =
          ([logical_token .leftParenthesis] ++ leftTokens ++
            [logical_token .implication]) ++
              (rightTokens ++ [logical_token .rightParenthesis]) by
        simp [Numbered.implication_tokens, List.append_assoc]]
      rw [List.getElem?_append_left hIndex]
      exact hPrefixGet
    have hRawPoint :
        Γ ⊢ₘ[godel_quotation_theory]
          ((numₘ(index) ∈ₘ domₘ(rawCode)) ∧ₘ
            ((rawCode ·ₘ numₘ(index)) ≐ₘ
              numₘ(token))) := by
      simpa [rawCode, bodyStage, prefixCode,
        leftStage, implication_formula_string_term,
        Numbered.implication_tokens] using
        gq_standard_token_sequence_point_inversion
          rawCode
          (implication_tokens leftTokens rightTokens)
          (Metatheory.Derives.equality_symm <| by
            simpa [rawCode, bodyStage, prefixCode,
              leftStage, implication_formula_string_term] using
              hEquality)
          hRawGet
    have hBodyPoint :
        Γ ⊢ₘ[godel_quotation_theory]
          ((numₘ(index) ∈ₘ domₘ(bodyStage)) ∧ₘ
            ((bodyStage ·ₘ numₘ(index)) ≐ₘ
              (prefixCode ·ₘ numₘ(index)))) := by
      simpa [bodyStage] using
        gq_concatenation_left_point
          prefixCode right
          (numₘ(index))
          (prefixCode ·ₘ numₘ(index))
          hPrefixFinite hRightFinite hIndexInPrefix
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set)
            (prefixCode ·ₘ numₘ(index)))
          (hLeft := hPrefix) (hRight := hRight)
    have hRawPointFromBody :
        Γ ⊢ₘ[godel_quotation_theory]
          ((numₘ(index) ∈ₘ domₘ(rawCode)) ∧ₘ
            ((rawCode ·ₘ numₘ(index)) ≐ₘ
              (bodyStage ·ₘ numₘ(index)))) := by
      simpa [rawCode] using
        gq_concatenation_left_point
          bodyStage rightParenthesis
          (numₘ(index))
          (bodyStage ·ₘ numₘ(index))
          hBodyStageFinite hRightParenthesisFinite
          (FirstOrder.Derives.conjElimLeft hBodyPoint)
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set)
            (bodyStage ·ₘ numₘ(index)))
          (hLeft := by prove_term_check)
          (hRight := hRightParenthesis)
    have hBodyValue :
        Γ ⊢ₘ[godel_quotation_theory]
          (bodyStage ·ₘ numₘ(index)) ≐ₘ numₘ(token) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm <|
          FirstOrder.Derives.conjElimRight hRawPointFromBody)
        (FirstOrder.Derives.conjElimRight hRawPoint)
    exact Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <|
        FirstOrder.Derives.conjElimRight hBodyPoint)
      hBodyValue
  have hLeftStageImplicationEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (leftStageTokens ++ [logical_token .implication]) ≐ₘ
          (leftStage ⌢ₘ implicationSymbol) := by
    simpa [prefixTokens, prefixCode] using
      Metatheory.Derives.equality_symm hPrefixEquality
  have hLeftStageEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftStage ≐ₘ standard_token_sequence leftStageTokens :=
    gq_concatenation_left_inversion_of_standard_equality
      leftStage implicationSymbol
      leftStageTokens [logical_token .implication]
      hLeftStageFinite hImplicationSymbolFinite
      hLeftStageDomain hLeftStageImplicationEquality
      (hLeft := hLeftStage) (hRight := hImplicationSymbol)
  have hLeftParenthesisEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            ([logical_token .leftParenthesis] ++ leftTokens) ≐ₘ
          (leftParenthesis ⌢ₘ left) := by
    simpa [leftStage, leftStageTokens] using
      Metatheory.Derives.equality_symm hLeftStageEquality
  exact
    gq_concatenation_right_inversion_of_standard_equality
      leftParenthesis left
      [logical_token .leftParenthesis] leftTokens
      hLeftParenthesisFinite hLeftFinite
      hLeftParenthesisDomain hLeftDomain
      hLeftParenthesisEquality
      (hLeft := hLeftParenthesis) (hRight := hLeft)

/--
蕴含公式的右正文可由左右已知长度和标准整串等式反演。

证明先按末尾右括号剥离整串，再从“固定前缀与右正文”的拼接中恢复右段；
不对正文公式本身增加任何规范命名条件。
-/
theorem gq_implication_right_eq_standard_token_sequence_of_domains
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
    (hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightTokens.length))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (implication_tokens leftTokens rightTokens) ≐ₘ
          implication_formula_string_term left right)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      right ≐ₘ standard_token_sequence rightTokens := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let implicationSymbol :=
    logical_symbol_code_term .implication
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let leftStage := leftParenthesis ⌢ₘ left
  let prefixCode := leftStage ⌢ₘ implicationSymbol
  let bodyStage := prefixCode ⌢ₘ right
  let leftStageTokens :=
    [logical_token .leftParenthesis] ++ leftTokens
  let prefixTokens :=
    leftStageTokens ++ [logical_token .implication]
  let bodyTokens := prefixTokens ++ rightTokens
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
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hImplicationSymbolFinite :
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
  have hImplicationSymbolDomain :
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
        domₘ(leftStage) ≐ₘ numₘ(leftStageTokens.length) := by
    simpa [leftStageTokens, leftStage,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        leftParenthesis left 1 leftTokens.length
        hLeftParenthesisFinite hLeftFinite
        hLeftParenthesisDomain hLeftDomain
        (hLeft := hLeftParenthesis) (hRight := hLeft)
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        leftStage implicationSymbol
        hLeftStageFinite hImplicationSymbolFinite
        (hLeft := hLeftStage) (hRight := hImplicationSymbol)
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ numₘ(prefixTokens.length) := by
    simpa [prefixTokens, leftStageTokens, prefixCode,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        leftStage implicationSymbol
        leftStageTokens.length 1
        hLeftStageFinite hImplicationSymbolFinite
        hLeftStageDomain hImplicationSymbolDomain
        (hLeft := hLeftStage) (hRight := hImplicationSymbol)
  have hBodyStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition bodyStage := by
    simpa [bodyStage] using
      gq_concatenation_finite
        prefixCode right
        hPrefixFinite hRightFinite
        (hLeft := hPrefix) (hRight := hRight)
  have hBodyStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(bodyStage) ≐ₘ numₘ(bodyTokens.length) := by
    simpa [bodyTokens, prefixTokens, leftStageTokens,
      bodyStage, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        prefixCode right
        prefixTokens.length rightTokens.length
        hPrefixFinite hRightFinite
        hPrefixDomain hRightDomain
        (hLeft := hPrefix) (hRight := hRight)
  have hWholeEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (bodyTokens ++
              [logical_token .rightParenthesis]) ≐ₘ
          (bodyStage ⌢ₘ rightParenthesis) := by
    simpa [bodyTokens, prefixTokens, leftStageTokens,
      bodyStage, prefixCode, leftStage,
      implication_formula_string_term,
      Numbered.implication_tokens,
      List.append_assoc] using hEquality
  have hBodyEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyStage ≐ₘ standard_token_sequence bodyTokens :=
    gq_concatenation_left_inversion_of_standard_equality
      bodyStage rightParenthesis
      bodyTokens [logical_token .rightParenthesis]
      hBodyStageFinite hRightParenthesisFinite
      hBodyStageDomain hWholeEquality
      (hLeft := hBodyStage)
      (hRight := hRightParenthesis)
  have hPrefixRightEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (prefixTokens ++ rightTokens) ≐ₘ
          (prefixCode ⌢ₘ right) := by
    simpa [bodyTokens, bodyStage] using
      Metatheory.Derives.equality_symm hBodyEquality
  exact
    gq_concatenation_right_inversion_of_standard_equality
      prefixCode right prefixTokens rightTokens
      hPrefixFinite hRightFinite
      hPrefixDomain hRightDomain
      hPrefixRightEquality
      (hLeft := hPrefix) (hRight := hRight)

/--
标准蕴含整串等式同时恢复左右两个递归正文。
该联合接口是后续 parser 形状反演的公共递归入口。
-/
theorem gq_implication_bodies_eq_standard_token_sequences_of_domains
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
    (hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightTokens.length))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (implication_tokens leftTokens rightTokens) ≐ₘ
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
    (gq_implication_right_eq_standard_token_sequence_of_domains
      left right leftTokens rightTokens
      hLeftFinite hRightFinite
      hLeftDomain hRightDomain hEquality
      (hLeft := hLeft) (hRight := hRight))

/-- 标准输入与对象蕴含构造的总长度不符时，对象层推出矛盾。 -/
theorem gq_implication_standard_code_falsum_of_length_ne
    {Γ : Context signature}
    (left right : SetTerm)
    (tokens : List Nat)
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
          implication_formula_string_term left right)
    (hLength :
      tokens.length ≠ leftLength + rightLength + 3)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let code := imp_codeₘ(left, right)
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ implication_formula_string_term left right := by
    simpa [code] using
      gq_implication_formula_code_eq_string_of_context
        (Γ := Γ) left right
        (hLeft := hLeft) (hRight := hRight)
  have hCodeEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ standard_token_sequence tokens :=
    Metatheory.Derives.equality_trans
      hCodeString
      (Metatheory.Derives.equality_symm hEquality)
  have hCodeDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(tokens.length) := by
    simpa [code] using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        code tokens hCodeEquality
        (hCode := hCode)
  have hConstructorDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ
          numₘ(leftLength + rightLength + 3) := by
    simpa [code] using
      gq_implication_formula_domain_eq_numeral_lengths
        (Γ := Γ) left right leftLength rightLength
        hLeftFinite hRightFinite hLeftDomain hRightDomain
        (hLeft := hLeft) (hRight := hRight)
  have hNumeralEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(tokens.length) ≐ₘ
          numₘ(leftLength + rightLength + 3) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hCodeDomain)
      hConstructorDomain
  have hNotEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        ¬ₘ (numₘ(tokens.length) ≐ₘ
          numₘ(leftLength + rightLength + 3)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_ne hLength
  exact FirstOrder.Derives.negElim
    hNumeralEquality hNotEquality

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
