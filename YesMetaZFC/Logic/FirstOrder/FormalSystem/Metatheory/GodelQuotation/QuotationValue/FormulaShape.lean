import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.Sequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.VariableSymbolInversion
/-!
# Gödel quotation 的公式外形语义
本模块证明蕴含、否定与全称公式代码的长度、前缀和正文反演。
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
universe u v w
/--
左右公式定义域长度分别为 numeral `leftLength`、`rightLength` 时，蕴含公式码的
定义域长度为 `leftLength + rightLength + 3`。
-/
theorem gq_implication_formula_domain_eq_numeral_lengths
    {Γ : Context signature} (left right : SetTerm)
    (leftLength rightLength : Nat) (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right) (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength)) (hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightLength))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(imp_codeₘ(left, right)) ≐ₘ
        numₘ(leftLength + rightLength + 3) := by
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
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence (Γ := Γ) .leftParenthesis
  have hLeftParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one (Γ := Γ) .leftParenthesis
  have hLeftStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftStage := by
    simpa [leftStage] using
      gq_concatenation_finite
        leftParenthesis left
        hLeftParenthesisFinite hLeftFinite
  have hLeftStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftStage) ≐ₘ numₘ(1 + leftLength) := by
    simpa [leftStage] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory (fun _ hAxiom => hAxiom)
        leftParenthesis left 1 leftLength
        hLeftParenthesisFinite hLeftFinite
        hLeftParenthesisDomain hLeftDomain
  have hImplicationSymbolFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition implicationSymbol := by
    simpa [implicationSymbol] using
      gq_logical_symbol_code_finite_sequence (Γ := Γ) .implication
  have hImplicationSymbolDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(implicationSymbol) ≐ₘ numₘ(1) := by
    simpa [implicationSymbol] using
      gq_logical_symbol_code_domain_eq_one (Γ := Γ) .implication
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        leftStage implicationSymbol
        hLeftStageFinite hImplicationSymbolFinite
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ numₘ(leftLength + 2) := by
    simpa [prefixCode, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory (fun _ hAxiom => hAxiom)
        leftStage implicationSymbol (1 + leftLength) 1
        hLeftStageFinite hImplicationSymbolFinite
        hLeftStageDomain hImplicationSymbolDomain
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence (Γ := Γ) .rightParenthesis
  have hRightParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(rightParenthesis) ≐ₘ numₘ(1) := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_domain_eq_one (Γ := Γ) .rightParenthesis
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    have hDefinition :
        Γ ⊢ₘ[godel_quotation_theory]
          implication_formula_code_definition_instance
            left right code :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_formula_constructor <|
            implication_formula_code_definition_instance_derives
              left right code hLeft.admissible hRight.admissible
                hCode.admissible
    have hReflexive :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ imp_codeₘ(left, right) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
          simpa [code] using
            FirstOrder.Derives.eq_refl_m code
    simpa [code, rawCode, prefixCode, leftStage,
      leftParenthesis, implicationSymbol,
      rightParenthesis,
      implication_formula_code_definition_instance,
      implication_formula_string_term] using
        FirstOrder.Derives.iffElimRight
          hDefinition hReflexive
  simpa [code, rawCode, prefixCode, leftStage,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      gq_three_part_domain_eq_numeral_lengths_of_theory (fun _ hAxiom => hAxiom)
        code prefixCode right rightParenthesis (leftLength + 2) rightLength 1
        (by simpa [rawCode] using hCodeRaw)
        hPrefixFinite hRightFinite hRightParenthesisFinite
        hPrefixDomain hRightDomain hRightParenthesisDomain
/--
否定公式构造把正文第 `index` 点平移到否定前缀之后，并保持逐点值。
正文只需在对象理论中是有限序列；该定理不要求正文已经展开为标准 token 序列，
因此可与全称、蕴含等构造子的点位平移组合，逐层反演任意公式骨架。
-/
theorem gq_negation_formula_body_point_at_standard_offset
    {Γ : Context signature} (body : SetTerm) (index : Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body) (hBodyIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(body))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory] ((numₘ(2 + index) ∈ₘ
          domₘ(neg_codeₘ(body))) ∧ₘ ((neg_codeₘ(body) ·ₘ
            numₘ(2 + index)) ≐ₘ (body ·ₘ numₘ(index)))) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let negationSymbol :=
    logical_symbol_code_term .negation
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let prefixCode := leftParenthesis ⌢ₘ negationSymbol
  let rawCode := (prefixCode ⌢ₘ body) ⌢ₘ rightParenthesis
  let code := neg_codeₘ(body)
  let prefixTokens :=
    [logical_token .leftParenthesis,
      logical_token .negation]
  let offset := prefixTokens.length + index
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
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence prefixTokens := by
    simpa [prefixCode, prefixTokens] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis]
        [logical_token .negation]
        leftParenthesis negationSymbol
        (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
            simpa [leftParenthesis] using
              logical_symbol_code_eq_standard_token_sequence
                .leftParenthesis) (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
            simpa [negationSymbol] using
              logical_symbol_code_eq_standard_token_sequence
                .negation)
  have hRightParenthesisEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        rightParenthesis ≐ₘ
          standard_token_sequence
            [logical_token .rightParenthesis] :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [rightParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .rightParenthesis
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis :=
    gq_finite_sequence_of_eq_standard_token_sequence
      rightParenthesis
      [logical_token .rightParenthesis]
      hRightParenthesisEquality
  have hRawPoint :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(offset) ∈ₘ domₘ(rawCode)) ∧ₘ ((rawCode ·ₘ numₘ(offset)) ≐ₘ (body ·ₘ numₘ(index)))) := by
    simpa [rawCode, offset] using
      gq_concatenation_middle_point_at_standard_offset
        prefixCode body rightParenthesis
        prefixTokens index
        hPrefixEquality hBodyFinite
        hRightParenthesisFinite hBodyIndex
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    have hDefinition :
        Γ ⊢ₘ[godel_quotation_theory]
          negation_formula_code_definition_instance
            body code :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_formula_constructor <|
            negation_formula_code_definition_instance_derives
              body code hBody.admissible hCode.admissible
    have hReflexive :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ neg_codeₘ(body) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
          simpa [code] using
            FirstOrder.Derives.eq_refl_m code
    simpa [code, rawCode, prefixCode,
      leftParenthesis, negationSymbol,
      rightParenthesis,
      negation_formula_code_definition_instance,
      negation_formula_string_term] using
        FirstOrder.Derives.iffElimRight
          hDefinition hReflexive
  have hCodePoint :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(offset) ∈ₘ domₘ(code)) ∧ₘ ((code ·ₘ numₘ(offset)) ≐ₘ (body ·ₘ numₘ(index)))) :=
    gq_point_inversion_of_equality
      code rawCode (numₘ(offset)) (body ·ₘ numₘ(index))
      hCodeRaw hRawPoint
  simpa [code, offset, prefixTokens] using hCodePoint
/--
正文定义域长度为 numeral `bodyLength` 时，否定公式码的定义域长度为
`bodyLength + 3`。
三个固定 token 分别是左括号、否定符号和右括号；正文内容本身无需预先恢复为标准串。
-/
theorem gq_negation_formula_domain_eq_numeral_length
    {Γ : Context signature} (body : SetTerm) (bodyLength : Nat)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body) (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(neg_codeₘ(body)) ≐ₘ
        numₘ(bodyLength + 3) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let negationSymbol :=
    logical_symbol_code_term .negation
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let prefixCode := leftParenthesis ⌢ₘ negationSymbol
  let rawCode := (prefixCode ⌢ₘ body) ⌢ₘ rightParenthesis
  let code := neg_codeₘ(body)
  let prefixTokens :=
    [logical_token .leftParenthesis,
      logical_token .negation]
  let suffixTokens :=
    [logical_token .rightParenthesis]
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
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence prefixTokens := by
    simpa [prefixCode, prefixTokens] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis]
        [logical_token .negation]
        leftParenthesis negationSymbol
        (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
            simpa [leftParenthesis] using
              logical_symbol_code_eq_standard_token_sequence
                .leftParenthesis) (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
            simpa [negationSymbol] using
              logical_symbol_code_eq_standard_token_sequence
                .negation)
  have hSuffixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        rightParenthesis ≐ₘ
          standard_token_sequence suffixTokens :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [rightParenthesis, suffixTokens] using
          logical_symbol_code_eq_standard_token_sequence
            .rightParenthesis
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode :=
    gq_finite_sequence_of_eq_standard_token_sequence
      prefixCode prefixTokens hPrefixEquality
  have hSuffixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis :=
    gq_finite_sequence_of_eq_standard_token_sequence
      rightParenthesis suffixTokens
      hSuffixEquality
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ numₘ(2) := by
    simpa [prefixTokens] using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory (fun _ hAxiom => hAxiom)
        prefixCode prefixTokens hPrefixEquality
  have hSuffixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(rightParenthesis) ≐ₘ numₘ(1) := by
    simpa [suffixTokens] using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory (fun _ hAxiom => hAxiom)
        rightParenthesis suffixTokens
        hSuffixEquality
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    have hDefinition :
        Γ ⊢ₘ[godel_quotation_theory]
          negation_formula_code_definition_instance
            body code :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_formula_constructor <|
            negation_formula_code_definition_instance_derives
              body code hBody.admissible hCode.admissible
    have hReflexive :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ neg_codeₘ(body) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
          simpa [code] using
            FirstOrder.Derives.eq_refl_m code
    simpa [code, rawCode, prefixCode,
      leftParenthesis, negationSymbol,
      rightParenthesis,
      negation_formula_code_definition_instance,
      negation_formula_string_term] using
        FirstOrder.Derives.iffElimRight
          hDefinition hReflexive
  simpa [code, rawCode, prefixCode,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      gq_three_part_domain_eq_numeral_lengths_of_theory (fun _ hAxiom => hAxiom)
        code prefixCode body rightParenthesis
        2 bodyLength 1
        (by simpa [rawCode] using hCodeRaw)
        hPrefixFinite hBodyFinite hSuffixFinite
        hPrefixDomain hBodyDomain hSuffixDomain
/--
全称公式构造把正文第 `index` 点平移到固定 binder 前缀之后，并保持逐点值。
绑定变量可由任意对象内标准序列等式给出；对规范 binder，该序列是单 token，
因此偏移正好为 `3 + index`。
-/
theorem gq_universal_formula_body_point_at_standard_offset
    {Γ : Context signature} (boundVariable body : SetTerm)
    (boundTokens : List Nat) (index : Nat) (hBoundVariableEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ≐ₘ standard_token_sequence boundTokens) (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body) (hBodyIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(body))
    (hBoundVariable :
      Term.CheckCertificate boundVariable SetSort.set := by
        prove_term_check)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory] ((numₘ( ([logical_token .leftParenthesis,
            logical_token .universal] ++ boundTokens).length +
              index) ∈ₘ
          domₘ(forall_codeₘ(boundVariable, body))) ∧ₘ ((forall_codeₘ(boundVariable, body) ·ₘ
            numₘ( ([logical_token .leftParenthesis,
                logical_token .universal] ++ boundTokens).length +
                  index)) ≐ₘ (body ·ₘ numₘ(index)))) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let universalSymbol :=
    logical_symbol_code_term .universal
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let fixedPrefix := leftParenthesis ⌢ₘ universalSymbol
  let prefixVariable := fixedPrefix ⌢ₘ boundVariable
  let rawCode := (prefixVariable ⌢ₘ body) ⌢ₘ rightParenthesis
  let code := forall_codeₘ(boundVariable, body)
  let fixedTokens :=
    [logical_token .leftParenthesis,
      logical_token .universal]
  let prefixTokens := fixedTokens ++ boundTokens
  let offset := prefixTokens.length + index
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hUniversalSymbol :
      Term.CheckCertificate universalSymbol SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hFixedPrefix :
      Term.CheckCertificate fixedPrefix SetSort.set := by
    prove_term_check
  have hPrefixVariable :
      Term.CheckCertificate prefixVariable SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hFixedPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        fixedPrefix ≐ₘ standard_token_sequence fixedTokens := by
    simpa [fixedPrefix, fixedTokens] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis]
        [logical_token .universal]
        leftParenthesis universalSymbol
        (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
            simpa [leftParenthesis] using
              logical_symbol_code_eq_standard_token_sequence
                .leftParenthesis) (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
            simpa [universalSymbol] using
              logical_symbol_code_eq_standard_token_sequence
                .universal)
  have hPrefixVariableEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixVariable ≐ₘ
          standard_token_sequence prefixTokens := by
    simpa [prefixVariable, prefixTokens] using
      gq_concatenation_eq_standard_token_sequence
        fixedTokens boundTokens
        fixedPrefix boundVariable
        hFixedPrefixEquality hBoundVariableEquality
  have hRightParenthesisEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        rightParenthesis ≐ₘ
          standard_token_sequence
            [logical_token .rightParenthesis] :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [rightParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .rightParenthesis
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis :=
    gq_finite_sequence_of_eq_standard_token_sequence
      rightParenthesis
      [logical_token .rightParenthesis]
      hRightParenthesisEquality
  have hRawPoint :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(offset) ∈ₘ domₘ(rawCode)) ∧ₘ ((rawCode ·ₘ numₘ(offset)) ≐ₘ (body ·ₘ numₘ(index)))) := by
    simpa [rawCode, offset] using
      gq_concatenation_middle_point_at_standard_offset
        prefixVariable body rightParenthesis
        prefixTokens index
        hPrefixVariableEquality hBodyFinite
        hRightParenthesisFinite hBodyIndex
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [code, rawCode, prefixVariable,
          fixedPrefix, leftParenthesis, universalSymbol,
          rightParenthesis, universal_formula_string_term] using
          gq_universal_formula_code_eq_string
            boundVariable body
              hBoundVariable.admissible hBody.admissible
  have hCodePoint :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(offset) ∈ₘ domₘ(code)) ∧ₘ ((code ·ₘ numₘ(offset)) ≐ₘ (body ·ₘ numₘ(index)))) :=
    gq_point_inversion_of_equality
      code rawCode (numₘ(offset)) (body ·ₘ numₘ(index))
      hCodeRaw hRawPoint
  simpa [code, offset, prefixTokens, fixedTokens] using
    hCodePoint
/--
绑定变量与正文定义域长度分别为 numeral `boundLength`、`bodyLength` 时，全称公式码的
定义域长度为 `boundLength + bodyLength + 3`。
-/
theorem gq_universal_formula_domain_eq_numeral_lengths
    {Γ : Context signature} (boundVariable body : SetTerm)
    (boundLength bodyLength : Nat) (hBoundVariableFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition boundVariable) (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body) (hBoundVariableDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(boundVariable) ≐ₘ numₘ(boundLength)) (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hBoundVariable :
      Term.CheckCertificate boundVariable SetSort.set := by
        prove_term_check)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(forall_codeₘ(boundVariable, body)) ≐ₘ
        numₘ(boundLength + bodyLength + 3) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let universalSymbol :=
    logical_symbol_code_term .universal
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let fixedPrefix := leftParenthesis ⌢ₘ universalSymbol
  let prefixVariable := fixedPrefix ⌢ₘ boundVariable
  let rawCode := (prefixVariable ⌢ₘ body) ⌢ₘ rightParenthesis
  let code := forall_codeₘ(boundVariable, body)
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hUniversalSymbol :
      Term.CheckCertificate universalSymbol SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hFixedPrefix :
      Term.CheckCertificate fixedPrefix SetSort.set := by
    prove_term_check
  have hPrefixVariable :
      Term.CheckCertificate prefixVariable SetSort.set := by
    prove_term_check
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence (Γ := Γ) .leftParenthesis
  have hLeftParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one (Γ := Γ) .leftParenthesis
  have hUniversalSymbolFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition universalSymbol := by
    simpa [universalSymbol] using
      gq_logical_symbol_code_finite_sequence (Γ := Γ) .universal
  have hUniversalSymbolDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(universalSymbol) ≐ₘ numₘ(1) := by
    simpa [universalSymbol] using
      gq_logical_symbol_code_domain_eq_one (Γ := Γ) .universal
  have hFixedPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition fixedPrefix := by
    simpa [fixedPrefix] using
      gq_concatenation_finite
        leftParenthesis universalSymbol
        hLeftParenthesisFinite hUniversalSymbolFinite
  have hFixedPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(fixedPrefix) ≐ₘ numₘ(2) := by
    simpa [fixedPrefix] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory (fun _ hAxiom => hAxiom)
        leftParenthesis universalSymbol 1 1
        hLeftParenthesisFinite hUniversalSymbolFinite
        hLeftParenthesisDomain hUniversalSymbolDomain
  have hPrefixVariableFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixVariable := by
    simpa [prefixVariable] using
      gq_concatenation_finite
        fixedPrefix boundVariable
        hFixedPrefixFinite hBoundVariableFinite
  have hPrefixVariableDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixVariable) ≐ₘ numₘ(boundLength + 2) := by
    simpa [prefixVariable, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory (fun _ hAxiom => hAxiom)
        fixedPrefix boundVariable 2 boundLength
        hFixedPrefixFinite hBoundVariableFinite
        hFixedPrefixDomain hBoundVariableDomain
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence (Γ := Γ) .rightParenthesis
  have hRightParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(rightParenthesis) ≐ₘ numₘ(1) := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_domain_eq_one (Γ := Γ) .rightParenthesis
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [code, rawCode, prefixVariable,
          fixedPrefix, leftParenthesis, universalSymbol,
          rightParenthesis, universal_formula_string_term] using
          gq_universal_formula_code_eq_string
            boundVariable body
              hBoundVariable.admissible hBody.admissible
  simpa [code, rawCode, prefixVariable, fixedPrefix,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      gq_three_part_domain_eq_numeral_lengths_of_theory (fun _ hAxiom => hAxiom)
        code prefixVariable body rightParenthesis (boundLength + 2) bodyLength 1
        (by simpa [rawCode] using hCodeRaw)
        hPrefixVariableFinite hBodyFinite
        hRightParenthesisFinite
        hPrefixVariableDomain hBodyDomain
        hRightParenthesisDomain
/--
全称构造子的固定开头反演。
只要绑定变量是变量符号、正文是代码字符串，就能在构造结果的下标 `0`、`1`、`2`
依次读到左括号、全称量词与绑定变量编码的首 token。结论同时携带三个下标的定义域
成员证书，供前缀解析与作用域反演直接使用。
-/
theorem gq_universal_formula_opening_inversion
    (boundVariable body : SetTerm)
    (hBoundVariable :
      Term.CheckCertificate boundVariable SetSort.set := by
        prove_term_check)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    ⊢ₘ[godel_quotation_theory] ((boundVariable ∈ₘ VarSymₘ) ∧ₘ (body ∈ₘ CodeStrₘ)) ⟶ₘ ( ((numₘ(0) ∈ₘ
                domₘ(forall_codeₘ(boundVariable, body))) ∧ₘ ((forall_codeₘ(boundVariable, body) ·ₘ
                  numₘ(0)) ≐ₘ
                numₘ(logical_token .leftParenthesis))) ∧ₘ ( ((numₘ(1) ∈ₘ
                    domₘ(forall_codeₘ(boundVariable, body))) ∧ₘ ((forall_codeₘ(boundVariable, body) ·ₘ
                      numₘ(1)) ≐ₘ
                    numₘ(logical_token .universal))) ∧ₘ ((numₘ(2) ∈ₘ
                    domₘ(forall_codeₘ(boundVariable, body))) ∧ₘ ((forall_codeₘ(boundVariable, body) ·ₘ
                      numₘ(2)) ≐ₘ (boundVariable ·ₘ numₘ(0))))
            )
        ) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let universalSymbol :=
    logical_symbol_code_term .universal
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let prefixCode := leftParenthesis ⌢ₘ universalSymbol
  let prefixVariable := prefixCode ⌢ₘ boundVariable
  let bodyStage := prefixVariable ⌢ₘ body
  let rawCode := bodyStage ⌢ₘ rightParenthesis
  let code := forall_codeₘ(boundVariable, body)
  let precondition : SetFormula := (boundVariable ∈ₘ VarSymₘ) ∧ₘ (body ∈ₘ CodeStrₘ)
  let Γ : Context signature := [precondition]
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hUniversalSymbol :
      Term.CheckCertificate universalSymbol SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hPrefix :
      Term.CheckCertificate prefixCode SetSort.set := by
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
  have hPrefixEquality :
      ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence
            [logical_token .leftParenthesis,
              logical_token .universal] := by
    simpa [prefixCode, leftParenthesis, universalSymbol] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis]
        [logical_token .universal]
        leftParenthesis universalSymbol
        (by
          simpa [leftParenthesis] using
            logical_symbol_code_eq_standard_token_sequence
              .leftParenthesis) (by
          simpa [universalSymbol] using
            logical_symbol_code_eq_standard_token_sequence
              .universal)
  have hPrefixPoint :
      ⊢ₘ[godel_quotation_theory] ((numₘ(1) ∈ₘ domₘ(prefixCode)) ∧ₘ ((prefixCode ·ₘ numₘ(1)) ≐ₘ
            numₘ(logical_token .universal))) := by
    simpa using
      gq_standard_token_sequence_point_inversion
        prefixCode
        [logical_token .leftParenthesis,
          logical_token .universal]
        hPrefixEquality (by simp)
  have hPrefixLeftPoint :
      ⊢ₘ[godel_quotation_theory] ((numₘ(0) ∈ₘ domₘ(prefixCode)) ∧ₘ ((prefixCode ·ₘ numₘ(0)) ≐ₘ
            numₘ(logical_token .leftParenthesis))) := by
    simpa using
      gq_standard_token_sequence_point_inversion
        prefixCode
        [logical_token .leftParenthesis,
          logical_token .universal]
        hPrefixEquality (by simp)
  have hRightParenthesisEquality :
      ⊢ₘ[godel_quotation_theory]
        rightParenthesis ≐ₘ
          standard_token_sequence
            [logical_token .rightParenthesis] := by
    simpa [rightParenthesis] using
      logical_symbol_code_eq_standard_token_sequence
        .rightParenthesis
  have hPreconditionCheck :
      Formula.CheckCertificate precondition := by
    prove_formula_check
  nd_apply FirstOrder.Derives.impIntro
  have hPrecondition :
      Γ ⊢ₘ[godel_quotation_theory]
        precondition :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hVariableMember :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ∈ₘ VarSymₘ :=
    FirstOrder.Derives.conjElimLeft hPrecondition
  have hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.conjElimRight hPrecondition
  have hVariableStructure :
      Γ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition boundVariable ∧ₘ
          (domₘ(boundVariable) ≐ₘ numₘ(1))) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken_cons <|
        gq_variable_symbol_member_implies_finite_domain_one
          boundVariable hBoundVariable.admissible)
      hVariableMember
  have hVariableFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition boundVariable :=
    FirstOrder.Derives.conjElimLeft hVariableStructure
  have hVariableDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(boundVariable) ≐ₘ numₘ(1) :=
    FirstOrder.Derives.conjElimRight hVariableStructure
  have hVariableZero :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(0) ∈ₘ domₘ(boundVariable) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(0)) (domₘ(boundVariable)) (numₘ(1))
        (finite_numeral_term_admissible 0)
        (domain_term_admissible boundVariable
          hBoundVariable.admissible)
        (finite_numeral_term_admissible 1)
        hVariableDomain)
      (FirstOrder.Derives.context_weaken_cons <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            0 1 (by omega))
  have hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
        gq_weaken_standard_sequence <|
          code_string_member_implies_finite_sequence_at
            body hBody.admissible)
      hBodyMember
  have hPrefixEqualityΓ :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence
            [logical_token .leftParenthesis,
              logical_token .universal] :=
    FirstOrder.Derives.context_weaken_cons hPrefixEquality
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode :=
    gq_finite_sequence_of_eq_standard_token_sequence
      prefixCode
      [logical_token .leftParenthesis,
        logical_token .universal]
      hPrefixEqualityΓ
  have hPrefixPointΓ :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(1) ∈ₘ domₘ(prefixCode)) ∧ₘ ((prefixCode ·ₘ numₘ(1)) ≐ₘ
            numₘ(logical_token .universal))) :=
    FirstOrder.Derives.context_weaken_cons hPrefixPoint
  have hPrefixLeftPointΓ :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(0) ∈ₘ domₘ(prefixCode)) ∧ₘ ((prefixCode ·ₘ numₘ(0)) ≐ₘ
            numₘ(logical_token .leftParenthesis))) :=
    FirstOrder.Derives.context_weaken_cons hPrefixLeftPoint
  have hPrefixVariablePointTwo :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(2) ∈ₘ domₘ(prefixVariable)) ∧ₘ ((prefixVariable ·ₘ numₘ(2)) ≐ₘ (boundVariable ·ₘ numₘ(0)))) := by
    simpa [prefixVariable] using
      gq_concatenation_right_zero_at_standard_length
        prefixCode boundVariable
        [logical_token .leftParenthesis,
          logical_token .universal]
        hPrefixEqualityΓ hVariableFinite hVariableZero
  have hPrefixVariableFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixVariable := by
    simpa [prefixVariable] using
      gq_concatenation_finite
        prefixCode boundVariable
        hPrefixFinite hVariableFinite
  have hPrefixVariablePointOne :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(1) ∈ₘ domₘ(prefixVariable)) ∧ₘ ((prefixVariable ·ₘ numₘ(1)) ≐ₘ
            numₘ(logical_token .universal))) := by
    simpa [prefixVariable] using
      gq_concatenation_left_point
        prefixCode boundVariable (numₘ(1)) (numₘ(logical_token .universal))
        hPrefixFinite hVariableFinite (FirstOrder.Derives.conjElimLeft hPrefixPointΓ) (FirstOrder.Derives.conjElimRight hPrefixPointΓ)
  have hPrefixVariablePointZero :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(0) ∈ₘ domₘ(prefixVariable)) ∧ₘ ((prefixVariable ·ₘ numₘ(0)) ≐ₘ
            numₘ(logical_token .leftParenthesis))) := by
    simpa [prefixVariable] using
      gq_concatenation_left_point
        prefixCode boundVariable (numₘ(0)) (numₘ(logical_token .leftParenthesis))
        hPrefixFinite hVariableFinite (FirstOrder.Derives.conjElimLeft hPrefixLeftPointΓ) (FirstOrder.Derives.conjElimRight hPrefixLeftPointΓ)
  have hBodyStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition bodyStage := by
    simpa [bodyStage] using
      gq_concatenation_finite
        prefixVariable body
        hPrefixVariableFinite hBodyFinite
  have hBodyStagePointOne :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(1) ∈ₘ domₘ(bodyStage)) ∧ₘ ((bodyStage ·ₘ numₘ(1)) ≐ₘ
            numₘ(logical_token .universal))) := by
    simpa [bodyStage] using
      gq_concatenation_left_point
        prefixVariable body (numₘ(1)) (numₘ(logical_token .universal))
        hPrefixVariableFinite hBodyFinite (FirstOrder.Derives.conjElimLeft
          hPrefixVariablePointOne) (FirstOrder.Derives.conjElimRight
          hPrefixVariablePointOne)
  have hBodyStagePointZero :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(0) ∈ₘ domₘ(bodyStage)) ∧ₘ ((bodyStage ·ₘ numₘ(0)) ≐ₘ
            numₘ(logical_token .leftParenthesis))) := by
    simpa [bodyStage] using
      gq_concatenation_left_point
        prefixVariable body (numₘ(0)) (numₘ(logical_token .leftParenthesis))
        hPrefixVariableFinite hBodyFinite (FirstOrder.Derives.conjElimLeft
          hPrefixVariablePointZero) (FirstOrder.Derives.conjElimRight
          hPrefixVariablePointZero)
  have hBodyStagePointTwo :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(2) ∈ₘ domₘ(bodyStage)) ∧ₘ ((bodyStage ·ₘ numₘ(2)) ≐ₘ (boundVariable ·ₘ numₘ(0)))) := by
    simpa [bodyStage] using
      gq_concatenation_left_point
        prefixVariable body (numₘ(2)) (boundVariable ·ₘ numₘ(0))
        hPrefixVariableFinite hBodyFinite (FirstOrder.Derives.conjElimLeft
          hPrefixVariablePointTwo) (FirstOrder.Derives.conjElimRight
          hPrefixVariablePointTwo)
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis :=
    gq_finite_sequence_of_eq_standard_token_sequence
      rightParenthesis
      [logical_token .rightParenthesis]
      (FirstOrder.Derives.context_weaken_cons
        hRightParenthesisEquality)
  have hRawPointOne :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(1) ∈ₘ domₘ(rawCode)) ∧ₘ ((rawCode ·ₘ numₘ(1)) ≐ₘ
            numₘ(logical_token .universal))) := by
    simpa [rawCode] using
      gq_concatenation_left_point
        bodyStage rightParenthesis (numₘ(1)) (numₘ(logical_token .universal))
        hBodyStageFinite hRightParenthesisFinite (FirstOrder.Derives.conjElimLeft
          hBodyStagePointOne) (FirstOrder.Derives.conjElimRight
          hBodyStagePointOne)
  have hRawPointZero :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(0) ∈ₘ domₘ(rawCode)) ∧ₘ ((rawCode ·ₘ numₘ(0)) ≐ₘ
            numₘ(logical_token .leftParenthesis))) := by
    simpa [rawCode] using
      gq_concatenation_left_point
        bodyStage rightParenthesis (numₘ(0)) (numₘ(logical_token .leftParenthesis))
        hBodyStageFinite hRightParenthesisFinite (FirstOrder.Derives.conjElimLeft
          hBodyStagePointZero) (FirstOrder.Derives.conjElimRight
          hBodyStagePointZero)
  have hRawPointTwo :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(2) ∈ₘ domₘ(rawCode)) ∧ₘ ((rawCode ·ₘ numₘ(2)) ≐ₘ (boundVariable ·ₘ numₘ(0)))) := by
    simpa [rawCode] using
      gq_concatenation_left_point
        bodyStage rightParenthesis (numₘ(2)) (boundVariable ·ₘ numₘ(0))
        hBodyStageFinite hRightParenthesisFinite (FirstOrder.Derives.conjElimLeft
          hBodyStagePointTwo) (FirstOrder.Derives.conjElimRight
          hBodyStagePointTwo)
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    simpa [code, rawCode, bodyStage, prefixVariable,
      prefixCode, leftParenthesis, universalSymbol,
      rightParenthesis,
      universal_formula_string_term] using
      FirstOrder.Derives.context_weaken_cons <|
        gq_universal_formula_code_eq_string
          boundVariable body
            hBoundVariable.admissible hBody.admissible
  have hCodePointOne :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(1) ∈ₘ domₘ(code)) ∧ₘ ((code ·ₘ numₘ(1)) ≐ₘ
            numₘ(logical_token .universal))) :=
    gq_point_inversion_of_equality
      code rawCode (numₘ(1)) (numₘ(logical_token .universal))
      hCodeRaw hRawPointOne
  have hCodePointZero :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(0) ∈ₘ domₘ(code)) ∧ₘ ((code ·ₘ numₘ(0)) ≐ₘ
            numₘ(logical_token .leftParenthesis))) :=
    gq_point_inversion_of_equality
      code rawCode (numₘ(0)) (numₘ(logical_token .leftParenthesis))
      hCodeRaw hRawPointZero
  have hCodePointTwo :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(2) ∈ₘ domₘ(code)) ∧ₘ ((code ·ₘ numₘ(2)) ≐ₘ (boundVariable ·ₘ numₘ(0)))) :=
    gq_point_inversion_of_equality
      code rawCode (numₘ(2)) (boundVariable ·ₘ numₘ(0))
      hCodeRaw hRawPointTwo
  simpa [code, precondition] using
    FirstOrder.Derives.conjIntro
      hCodePointZero <|
        FirstOrder.Derives.conjIntro
          hCodePointOne hCodePointTwo
/--
全称构造子的旧二点前缀接口。
该接口由更强的开头三点反演直接投影得到，保留给只消费全称 token 与 binder token
的调用方。
-/
theorem gq_universal_formula_prefix_inversion
    (boundVariable body : SetTerm)
    (hBoundVariable :
      Term.CheckCertificate boundVariable SetSort.set := by
        prove_term_check)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    ⊢ₘ[godel_quotation_theory] ((boundVariable ∈ₘ VarSymₘ) ∧ₘ (body ∈ₘ CodeStrₘ)) ⟶ₘ ((((numₘ(1) ∈ₘ
              domₘ(forall_codeₘ(boundVariable, body))) ∧ₘ ((forall_codeₘ(boundVariable, body) ·ₘ
                numₘ(1)) ≐ₘ
              numₘ(logical_token .universal))) ∧ₘ ((numₘ(2) ∈ₘ
              domₘ(forall_codeₘ(boundVariable, body))) ∧ₘ ((forall_codeₘ(boundVariable, body) ·ₘ
                numₘ(2)) ≐ₘ (boundVariable ·ₘ numₘ(0)))))) := by
  let precondition : SetFormula := (boundVariable ∈ₘ VarSymₘ) ∧ₘ (body ∈ₘ CodeStrₘ)
  have hOpening :=
    gq_universal_formula_opening_inversion
      boundVariable body
  have hPreconditionCheck :
      Formula.CheckCertificate precondition := by
    prove_formula_check
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [precondition]
  have hPrecondition :
      Γ ⊢ₘ[godel_quotation_theory]
        precondition :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hResult :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken_cons hOpening)
      hPrecondition
  simpa [Γ, precondition] using
    FirstOrder.Derives.conjElimRight hResult
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
