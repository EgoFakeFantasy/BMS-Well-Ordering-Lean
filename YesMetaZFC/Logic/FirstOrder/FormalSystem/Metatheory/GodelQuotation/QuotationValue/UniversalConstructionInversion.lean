import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstructionInversion

/-!
# Gödel quotation 的全称构造反演

本模块从规范全称 token 串与对象全称构造码的等式，反向恢复正文代码。
绑定变量固定为具名变量 singleton；正文只要求有限序列及其最弱的 numeral
定义域等式。
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
规范全称 token 串等于对象全称构造代码，且正文定义域已由对应 token 长度固定时，
正文代码就是该标准正文串。

证明逐点使用全称构造的固定偏移 `3`，不引入公式语义、模型或额外规范命名条件。
-/
theorem gq_universal_body_eq_standard_token_sequence_of_domain
    {Γ : Context signature}
    (name : Nat) (body : SetTerm) (bodyTokens : List Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyTokens.length))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) ≐ₘ
          forall_codeₘ(
            Numbered.named_variable_code name, body))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      body ≐ₘ standard_token_sequence bodyTokens := by
  have hBodyFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula body := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hBodyFinite
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
        numₘ(index) ∈ₘ numₘ(bodyTokens.length) :=
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
        (finite_numeral_term_admissible bodyTokens.length)
        hBodyDomain)
      hIndexNumeral
  have hBoundVariableEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        Numbered.named_variable_code name ≐ₘ
          standard_token_sequence
            [Numbered.variable_token name] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        named_variable_code_eq_standard_token_sequence name
  have hBodyPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(3 + index) ∈ₘ
            domₘ(forall_codeₘ(
              Numbered.named_variable_code name, body))) ∧ₘ
          ((forall_codeₘ(
              Numbered.named_variable_code name, body) ·ₘ
                numₘ(3 + index)) ≐ₘ
            (body ·ₘ numₘ(index)))) := by
    simpa using
      gq_universal_formula_body_point_at_standard_offset
        (Numbered.named_variable_code name) body
        [Numbered.variable_token name] index
        hBoundVariableEquality hBodyFinite hIndexBody
        (hBoundVariable := by prove_term_check)
        (hBody := hBody)
  have hBodySuffixGet :
      (bodyTokens ++
          [Numbered.logical_token .rightParenthesis])[index]? =
        some token := by
    rw [List.getElem?_append_left hIndex]
    exact hGet
  have hUniversalGet :
      (Numbered.universal_tokens name bodyTokens)[3 + index]? =
        some token := by
    have hRaw :
        ([Numbered.logical_token .leftParenthesis,
          Numbered.logical_token .universal,
          Numbered.variable_token name] ++
            (bodyTokens ++
              [Numbered.logical_token .rightParenthesis]))[3 + index]? =
          some token := by
      rw [List.getElem?_append_right]
      · simpa using hBodySuffixGet
      · simp
    simpa [Numbered.universal_tokens,
      List.append_assoc] using hRaw
  have hCodePoint :=
    gq_standard_token_sequence_point_inversion
      (forall_codeₘ(
        Numbered.named_variable_code name, body))
      (Numbered.universal_tokens name bodyTokens)
      (Metatheory.Derives.equality_symm hEquality)
      hUniversalGet
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight hBodyPoint)
    (FirstOrder.Derives.conjElimRight hCodePoint)

/-!
全称正文无需预先恢复自身长度即可严格落入整个构造定义域。具名绑定变量的
singleton 编码与两个固定逻辑 token 共同给出长度为 `3` 的正前缀。
-/
theorem gq_universal_body_domain_mem_code_domain
    {Γ : Context signature}
    (name : Nat) (body : SetTerm)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(body) ∈ₘ
        domₘ(forall_codeₘ(
          Numbered.named_variable_code name, body)) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let universalSymbol :=
    logical_symbol_code_term .universal
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let boundVariable :=
    Numbered.named_variable_code name
  let fixedPrefix :=
    leftParenthesis ⌢ₘ universalSymbol
  let prefixVariable :=
    fixedPrefix ⌢ₘ boundVariable
  let bodyStage := prefixVariable ⌢ₘ body
  let rawCode := bodyStage ⌢ₘ rightParenthesis
  let code :=
    forall_codeₘ(Numbered.named_variable_code name, body)
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hUniversalSymbol :
      Term.CheckCertificate universalSymbol SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hBoundVariable :
      Term.CheckCertificate boundVariable SetSort.set := by
    prove_term_check
  have hFixedPrefix :
      Term.CheckCertificate fixedPrefix SetSort.set := by
    prove_term_check
  have hPrefixVariable :
      Term.CheckCertificate prefixVariable SetSort.set := by
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
  have hUniversalFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition universalSymbol := by
    simpa [universalSymbol] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .universal
  have hUniversalDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(universalSymbol) ≐ₘ numₘ(1) := by
    simpa [universalSymbol] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .universal
  have hBoundVariableEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ≐ₘ
          standard_token_sequence
            [Numbered.variable_token name] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        named_variable_code_eq_standard_token_sequence name
  have hBoundVariableFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition boundVariable :=
    gq_finite_sequence_of_eq_standard_token_sequence
      boundVariable [Numbered.variable_token name]
      hBoundVariableEquality
      (hCode := hBoundVariable)
  have hBoundVariableDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(boundVariable) ≐ₘ numₘ(1) := by
    simpa using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        boundVariable [Numbered.variable_token name]
        hBoundVariableEquality
        (hCode := hBoundVariable)
  have hFixedPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition fixedPrefix := by
    simpa [fixedPrefix] using
      gq_concatenation_finite
        leftParenthesis universalSymbol
        hLeftParenthesisFinite hUniversalFinite
        (hLeft := hLeftParenthesis)
        (hRight := hUniversalSymbol)
  have hFixedPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(fixedPrefix) ≐ₘ numₘ(2) := by
    simpa [fixedPrefix] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        leftParenthesis universalSymbol 1 1
        hLeftParenthesisFinite hUniversalFinite
        hLeftParenthesisDomain hUniversalDomain
        (hLeft := hLeftParenthesis)
        (hRight := hUniversalSymbol)
  have hPrefixVariableFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixVariable := by
    simpa [prefixVariable] using
      gq_concatenation_finite
        fixedPrefix boundVariable
        hFixedPrefixFinite hBoundVariableFinite
        (hLeft := hFixedPrefix)
        (hRight := hBoundVariable)
  have hPrefixVariableDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixVariable) ≐ₘ numₘ(2 + 1) := by
    simpa [prefixVariable] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        fixedPrefix boundVariable 2 1
        hFixedPrefixFinite hBoundVariableFinite
        hFixedPrefixDomain hBoundVariableDomain
        (hLeft := hFixedPrefix)
        (hRight := hBoundVariable)
  have hBodyInBodyStage :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ∈ₘ domₘ(bodyStage) := by
    simpa [bodyStage] using
      gq_concatenation_right_domain_member_of_positive_left_length
        prefixVariable body 2
        hPrefixVariableFinite hBodyFinite
        hPrefixVariableDomain
        (hLeft := hPrefixVariable)
        (hRight := hBody)
  have hBodyStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition bodyStage := by
    simpa [bodyStage] using
      gq_concatenation_finite
        prefixVariable body
        hPrefixVariableFinite hBodyFinite
        (hLeft := hPrefixVariable)
        (hRight := hBody)
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hBodyInRawCode :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ∈ₘ domₘ(rawCode) := by
    simpa [rawCode] using
      gq_concatenation_left_domain_member
        bodyStage rightParenthesis
        (domₘ(body))
        hBodyStageFinite hRightParenthesisFinite
        hBodyInBodyStage
        (hLeft := hBodyStage)
        (hRight := hRightParenthesis)
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    simpa [code, rawCode, bodyStage, prefixVariable,
      fixedPrefix, boundVariable, leftParenthesis,
      universalSymbol, rightParenthesis,
      universal_formula_string_term] using
      gq_universal_formula_code_eq_string
        (Numbered.named_variable_code name) body
        hBoundVariable.admissible hBody.admissible
  have hCodeRawDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ domₘ(rawCode) :=
    domain_term_congr_of_equality
      code rawCode hCode.admissible hRawCode.admissible
      hCodeRaw
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      (domₘ(body))
      (domₘ(code)) (domₘ(rawCode))
      (domain_term_admissible body hBody.admissible)
      (domain_term_admissible code hCode.admissible)
      (domain_term_admissible rawCode hRawCode.admissible)
      hCodeRawDomain)
    hBodyInRawCode

/-!
全称正文的长度不是 replay 调用方的输入数据。父码等式已经把正文定义域
限制在父串的有限定义域内；在对象层按该有限定义域逐个消去，只有与规范
正文长度一致的分支可以存活。
-/
theorem gq_universal_body_eq_standard_token_sequence_of_standard_equality
    {Γ : Context signature}
    (name : Nat) (body : SetTerm) (bodyTokens : List Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) ≐ₘ
          forall_codeₘ(
            Numbered.named_variable_code name, body))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      body ≐ₘ standard_token_sequence bodyTokens := by
  let code : SetTerm :=
    forall_codeₘ(Numbered.named_variable_code name, body)
  let tokens : List Nat :=
    Numbered.universal_tokens name bodyTokens
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hBodyDomainMember :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ∈ₘ domₘ(code) := by
    simpa [code] using
      gq_universal_body_domain_mem_code_domain
        name body hBodyFinite (hBody := hBody)
  have hCodeDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(tokens.length) := by
    have hEquality' :
        Γ ⊢ₘ[godel_quotation_theory]
          standard_token_sequence tokens ≐ₘ code := by
      simpa [code, tokens] using hEquality
    simpa [code] using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        code tokens
        (Metatheory.Derives.equality_symm hEquality')
        (hCode := hCode)
  apply
    gq_domain_length_elim_of_member_of_standard_equality
      (child := body)
      (parent := code)
      tokens
      (body ≐ₘ standard_token_sequence bodyTokens)
      hBodyDomainMember
      (by simpa [code, tokens] using hEquality)
  intro length hLength
  let candidate : SetFormula :=
    domₘ(body) ≐ₘ numₘ(length)
  let Δ : Context signature :=
    candidate :: Γ
  have hCandidate :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(length) :=
    FirstOrder.Derives.assumption
      (by simp [candidate, Δ])
  have hBodyFinite' :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ)
      (by
        intro formula hFormula
        exact List.mem_cons_of_mem candidate hFormula)
      hBodyFinite
  have hBoundVariable :
      Term.CheckCertificate
        (Numbered.named_variable_code name)
        SetSort.set := by
    prove_term_check
  have hBoundVariableEquality :
      Δ ⊢ₘ[godel_quotation_theory]
        Numbered.named_variable_code name ≐ₘ
          standard_token_sequence
            [Numbered.variable_token name] := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp)
    exact named_variable_code_eq_standard_token_sequence name
  have hBoundVariableFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          (Numbered.named_variable_code name) :=
    gq_finite_sequence_of_eq_standard_token_sequence
      (Numbered.named_variable_code name)
      [Numbered.variable_token name]
      hBoundVariableEquality
      (hCode := hBoundVariable)
  have hBoundVariableDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(Numbered.named_variable_code name) ≐ₘ numₘ(1) := by
    simpa using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        (Numbered.named_variable_code name)
        [Numbered.variable_token name]
        hBoundVariableEquality
        (hCode := hBoundVariable)
  have hCandidateDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(length + 4) := by
    simpa [code, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      gq_universal_formula_domain_eq_numeral_lengths
        (Numbered.named_variable_code name) body
        1 length
        hBoundVariableFinite hBodyFinite'
        hBoundVariableDomain hCandidate
        (hBoundVariable := hBoundVariable)
        (hBody := hBody)
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
        numₘ(tokens.length) ≐ₘ numₘ(length + 4) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hCodeDomain')
      hCandidateDomain
  have hEquality' :
      Δ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) ≐ₘ
          code :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ)
      (by
        intro formula hFormula
        exact List.mem_cons_of_mem candidate hFormula)
      (by simpa [code] using hEquality)
  by_cases hCorrect : length = bodyTokens.length
  · have hBodyDomain :
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(body) ≐ₘ numₘ(bodyTokens.length) := by
      simpa [candidate, Δ, hCorrect] using hCandidate
    simpa [code] using
      gq_universal_body_eq_standard_token_sequence_of_domain
        name body bodyTokens
        hBodyFinite' hBodyDomain hEquality'
        (hBody := hBody)
  · have hDifferent :
        tokens.length ≠ length + 4 := by
      intro hNumeralLength
      apply hCorrect
      simp [tokens, Numbered.universal_tokens] at hNumeralLength
      omega
    have hNotEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          ¬ₘ (numₘ(tokens.length) ≐ₘ numₘ(length + 4)) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_ne hDifferent
    exact FirstOrder.Derives.falsumElim <|
      FirstOrder.Derives.negElim
        hNumeralEquality hNotEquality

/-!
任意标准父串的全称正文位于固定偏移 `3`。正文长度由调用方给出时，可以直接
恢复对应切片；父串总长度错误的分支由对象层定义域等式排除。
-/
theorem gq_universal_body_eq_standard_token_slice_of_domain
    {Γ : Context signature}
    (name : Nat) (body : SetTerm)
    (tokens : List Nat) (bodyLength : Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(
            Numbered.named_variable_code name, body))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      body ≐ₘ
        standard_token_sequence
          ((tokens.drop 3).take bodyLength) := by
  let bodyTokens :=
    (tokens.drop 3).take bodyLength
  by_cases hLength :
      tokens.length = bodyLength + 4
  · have hBodyTokensLength :
        bodyTokens.length = bodyLength := by
      simp only [bodyTokens, List.length_take,
        List.length_drop]
      omega
    have hBodyFunction :
        Γ ⊢ₘ[godel_quotation_theory]
          is_function_formula body := by
      simpa [finite_sequence_condition] using
        FirstOrder.Derives.conjElimLeft hBodyFinite
    have hBodyDomain' :
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(body) ≐ₘ numₘ(bodyTokens.length) := by
      simpa [hBodyTokensLength] using hBodyDomain
    apply
      gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
        (T := godel_quotation_theory)
        (Γ := Γ)
        (fun _ hAxiom => Or.inl hAxiom)
        (fun _ hFormula =>
          godel_quotation_theory_sentence hFormula)
        body bodyTokens hBodyFunction hBodyDomain'
        (hSource := hBody)
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
          hBodyDomain')
        hIndexNumeral
    have hBoundVariableEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          Numbered.named_variable_code name ≐ₘ
            standard_token_sequence
              [Numbered.variable_token name] :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          named_variable_code_eq_standard_token_sequence name
    have hBodyPoint :
        Γ ⊢ₘ[godel_quotation_theory]
          ((numₘ(3 + index) ∈ₘ
              domₘ(forall_codeₘ(
                Numbered.named_variable_code name, body))) ∧ₘ
            ((forall_codeₘ(
                Numbered.named_variable_code name, body) ·ₘ
                  numₘ(3 + index)) ≐ₘ
              (body ·ₘ numₘ(index)))) := by
      simpa using
        gq_universal_formula_body_point_at_standard_offset
          (Numbered.named_variable_code name) body
          [Numbered.variable_token name] index
          hBoundVariableEquality hBodyFinite hIndexBody
          (hBoundVariable := by prove_term_check)
          (hBody := hBody)
    have hSliceIndex :
        index < bodyLength := by
      simpa [hBodyTokensLength] using hIndex
    have hDropGet :
        (tokens.drop 3)[index]? = some token := by
      rw [List.getElem?_take_of_lt hSliceIndex] at hGet
      simpa [bodyTokens] using hGet
    have hTokenGet :
        tokens[3 + index]? = some token := by
      simpa [Nat.add_comm] using hDropGet
    have hCodePoint :=
      gq_standard_token_sequence_point_inversion
        (forall_codeₘ(
          Numbered.named_variable_code name, body))
        tokens
        (Metatheory.Derives.equality_symm hEquality)
        hTokenGet
    exact Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm <|
        FirstOrder.Derives.conjElimRight
          hBodyPoint)
      (FirstOrder.Derives.conjElimRight
        hCodePoint)
  · let boundVariable :=
      Numbered.named_variable_code name
    let code := forall_codeₘ(boundVariable, body)
    have hBoundVariable :
        Term.CheckCertificate boundVariable SetSort.set := by
      prove_term_check
    have hCode :
        Term.CheckCertificate code SetSort.set := by
      prove_term_check
    have hBoundVariableEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          boundVariable ≐ₘ
            standard_token_sequence
              [Numbered.variable_token name] :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <| by
          simpa [boundVariable] using
            named_variable_code_eq_standard_token_sequence name
    have hBoundVariableFinite :
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition boundVariable :=
      gq_finite_sequence_of_eq_standard_token_sequence
        boundVariable [Numbered.variable_token name]
        hBoundVariableEquality
        (hCode := hBoundVariable)
    have hBoundVariableDomain :
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(boundVariable) ≐ₘ numₘ(1) := by
      simpa using
        gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
          (fun _ hAxiom => hAxiom)
          boundVariable [Numbered.variable_token name]
          hBoundVariableEquality
          (hCode := hBoundVariable)
    have hActualDomain :
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(code) ≐ₘ numₘ(tokens.length) := by
      simpa [code, boundVariable] using
        gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
          (fun _ hAxiom => hAxiom)
          code tokens
          (Metatheory.Derives.equality_symm <| by
            simpa [code, boundVariable] using hEquality)
          (hCode := hCode)
    have hExpectedDomain :
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(code) ≐ₘ numₘ(bodyLength + 4) := by
      simpa [code, boundVariable, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        gq_universal_formula_domain_eq_numeral_lengths
          boundVariable body 1 bodyLength
          hBoundVariableFinite hBodyFinite
          hBoundVariableDomain hBodyDomain
          (hBoundVariable := hBoundVariable)
          (hBody := hBody)
    have hNumeralEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          numₘ(tokens.length) ≐ₘ
            numₘ(bodyLength + 4) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm hActualDomain)
        hExpectedDomain
    have hNotEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          ¬ₘ (numₘ(tokens.length) ≐ₘ
            numₘ(bodyLength + 4)) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_ne hLength
    exact FirstOrder.Derives.falsumElim <|
      FirstOrder.Derives.negElim
        hNumeralEquality hNotEquality

/--
任意整串不等于由全称 binder 与正文切片重建出的规范全称串时，对象构造等式
推出矛盾。该接口供 checked parser 的错误外壳分支直接使用。
-/
theorem gq_universal_standard_code_falsum_of_not_slice_shape
    {Γ : Context signature}
    (name : Nat) (body : SetTerm)
    (tokens : List Nat) (bodyLength : Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(
            Numbered.named_variable_code name, body))
    (hShape :
      tokens ≠
        Numbered.universal_tokens name
          ((tokens.drop 3).take bodyLength))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let bodyTokens :=
    (tokens.drop 3).take bodyLength
  have hBodyEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        body ≐ₘ standard_token_sequence bodyTokens := by
    simpa [bodyTokens] using
      gq_universal_body_eq_standard_token_slice_of_domain
        name body tokens bodyLength
        hBodyFinite hBodyDomain hEquality
        (hBody := hBody)
  have hCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        forall_codeₘ(
            Numbered.named_variable_code name, body) ≐ₘ
          universal_formula_string_term
            (Numbered.named_variable_code name) body :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_universal_formula_code_eq_string
          (Numbered.named_variable_code name) body
          (by
            exact
              (by
                prove_term_check :
                Term.CheckCertificate
                  (Numbered.named_variable_code name)
                  SetSort.set).admissible)
          hBody.admissible
  have hStringStandard :
      Γ ⊢ₘ[godel_quotation_theory]
        universal_formula_string_term
            (Numbered.named_variable_code name) body ≐ₘ
          standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) :=
    gq_universal_formula_string_eq_standard_token_sequence_of_context
      name bodyTokens body hBodyEquality
      (hBodyCode := hBody)
  have hStandardEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_trans
        hEquality hCodeString)
      hStringStandard
  have hNotEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        ¬ₘ (standard_token_sequence tokens ≐ₘ
          standard_token_sequence
            (Numbered.universal_tokens name bodyTokens)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_token_sequence_ne <| by
            simpa [bodyTokens] using hShape
  exact FirstOrder.Derives.negElim
    hStandardEquality hNotEquality

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
