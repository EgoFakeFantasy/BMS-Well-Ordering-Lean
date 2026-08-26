import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TermCodeInversion.Opening
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SequenceInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.Opening

/-!
# 函数应用项码的参数区切片反演

本模块只把函数符号与左括号组成的固定二 token 前缀接到公共三段拼接切片反演。
参数族内部的逐分片反演由 `FiniteSequenceSemantics.FlattenInversion` 承担。
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

/-- 函数应用码对元数前驱和符号编号的已证等式保持合同。 -/
theorem gq_term_application_code_congr_indices
    {Γ : Context signature}
    (leftArity rightArity leftIndex rightIndex
      arguments : SetTerm)
    (hLeftArity :
      Term.Admissible leftArity SetSort.set)
    (hRightArity :
      Term.Admissible rightArity SetSort.set)
    (hLeftIndex :
      Term.Admissible leftIndex SetSort.set)
    (hRightIndex :
      Term.Admissible rightIndex SetSort.set)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hArityEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftArity ≐ₘ rightArity)
    (hIndexEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftIndex ≐ₘ rightIndex) :
    Γ ⊢ₘ[godel_quotation_theory]
      term_application_code_term
          leftArity leftIndex arguments ≐ₘ
        term_application_code_term
          rightArity rightIndex arguments := by
  let leftFunction : SetTerm :=
    coded_function_symbol_code_term
      leftArity leftIndex
  let rightFunction : SetTerm :=
    coded_function_symbol_code_term
      rightArity rightIndex
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let flattened : SetTerm :=
    flattenₘ(arguments)
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  have hLeftFunction :
      Term.Admissible leftFunction SetSort.set := by
    simpa [leftFunction] using
      coded_function_symbol_code_term_admissible
        leftArity leftIndex hLeftArity hLeftIndex
  have hRightFunction :
      Term.Admissible rightFunction SetSort.set := by
    simpa [rightFunction] using
      coded_function_symbol_code_term_admissible
        rightArity rightIndex hRightArity hRightIndex
  have hLeftParenthesis :
      Term.Admissible leftParenthesis SetSort.set := by
    simpa [leftParenthesis] using
      logical_symbol_code_term_admissible
        .leftParenthesis
  have hFlattened :
      Term.Admissible flattened SetSort.set := by
    simpa [flattened] using
      finite_sequence_flatten_term_admissible
        arguments hArguments
  have hRightParenthesis :
      Term.Admissible rightParenthesis SetSort.set := by
    simpa [rightParenthesis] using
      logical_symbol_code_term_admissible
        .rightParenthesis
  have hFunctionEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftFunction ≐ₘ rightFunction := by
    simpa [leftFunction, rightFunction] using
      gq_coded_function_symbol_code_term_congr_of_equalities
        leftArity rightArity leftIndex rightIndex
        hLeftArity hRightArity hLeftIndex hRightIndex
        hArityEquality hIndexEquality
  have hLeftEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ leftParenthesis :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) leftParenthesis
  have hFlattenedEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        flattened ≐ₘ flattened :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) flattened
  have hRightEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        rightParenthesis ≐ₘ rightParenthesis :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) rightParenthesis
  have hPrefixEquality :=
    finite_sequence_concatenation_term_congr_of_equalities
      leftFunction rightFunction
      leftParenthesis leftParenthesis
      hLeftFunction hRightFunction
      hLeftParenthesis hLeftParenthesis
      hFunctionEquality hLeftEquality
  have hMiddleEquality :=
    finite_sequence_concatenation_term_congr_of_equalities
      (leftFunction ⌢ₘ leftParenthesis)
      (rightFunction ⌢ₘ leftParenthesis)
      flattened flattened
      (finite_sequence_concatenation_term_admissible
        leftFunction leftParenthesis
        hLeftFunction hLeftParenthesis)
      (finite_sequence_concatenation_term_admissible
        rightFunction leftParenthesis
        hRightFunction hLeftParenthesis)
      hFlattened hFlattened
      hPrefixEquality hFlattenedEquality
  simpa [leftFunction, rightFunction,
    leftParenthesis, flattened, rightParenthesis,
    term_application_code_term] using
    finite_sequence_concatenation_term_congr_of_equalities
      ((leftFunction ⌢ₘ leftParenthesis) ⌢ₘ
        flattened)
      ((rightFunction ⌢ₘ leftParenthesis) ⌢ₘ
        flattened)
      rightParenthesis rightParenthesis
      (finite_sequence_concatenation_term_admissible
        (leftFunction ⌢ₘ leftParenthesis)
        flattened
        (finite_sequence_concatenation_term_admissible
          leftFunction leftParenthesis
          hLeftFunction hLeftParenthesis)
        hFlattened)
      (finite_sequence_concatenation_term_admissible
        (rightFunction ⌢ₘ leftParenthesis)
        flattened
        (finite_sequence_concatenation_term_admissible
          rightFunction leftParenthesis
          hRightFunction hLeftParenthesis)
        hFlattened)
      hRightParenthesis hRightParenthesis
      hMiddleEquality hRightEquality

/--
具体函数应用码的总定义域长度由固定二 token 前缀、参数 flatten 和右括号唯一
确定。
-/
theorem
    gq_term_application_code_domain_eq_of_flatten_domain
    {Γ : Context signature}
    (arityPredecessor symbolIndex : Nat)
    (arguments : SetTerm)
    (flattenLength : Nat)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hPositive :
      Γ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ))
    (hFlattenDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(flattenₘ(arguments)) ≐ₘ
          numₘ(flattenLength)) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(term_application_code_term
        (numₘ(arityPredecessor))
        (numₘ(symbolIndex))
        arguments) ≐ₘ
          numₘ(2 + flattenLength + 1) := by
  let arityTerm : SetTerm :=
    numₘ(arityPredecessor)
  let indexTerm : SetTerm :=
    numₘ(symbolIndex)
  let functionCode : SetTerm :=
    coded_function_symbol_code_term
      arityTerm indexTerm
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let prefixCode : SetTerm :=
    functionCode ⌢ₘ leftParenthesis
  let flattened : SetTerm :=
    flattenₘ(arguments)
  let middle : SetTerm :=
    prefixCode ⌢ₘ flattened
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  have hInputsFresh :
      ReservedIdsFresh [0, 1, 2]
        [arityTerm, indexTerm] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hTerm
    rcases hTerm with rfl | rfl
    all_goals
      simp [arityTerm, indexTerm,
        finite_numeral_term_freeSupport]
      exact List.not_mem_nil
  have hStructure :
      Γ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition
            (term_application_code_term
              arityTerm indexTerm arguments) ∧ₘ
          (finite_sequence_condition flattened ∧ₘ
            (domₘ(flattened) ∈ₘ
              domₘ(term_application_code_term
                arityTerm indexTerm arguments)))) := by
    simpa [flattened] using
      gq_term_application_code_finite_and_flattened_domain_member
        (Γ := Γ)
        arityTerm indexTerm arguments
        (finite_numeral_term_admissible
          arityPredecessor)
        (finite_numeral_term_admissible
          symbolIndex)
        hArguments hInputsFresh hPositive
  have hFlattenedFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition flattened :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hStructure
  have hFunctionEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        functionCode ≐ₘ
          standard_token_sequence
            [Numbered.function_token
              arityPredecessor symbolIndex] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [functionCode, arityTerm,
          indexTerm] using
          coded_function_symbol_code_eq_standard_token_sequence
            arityPredecessor symbolIndex
  have hFunctionFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition functionCode :=
    gq_finite_sequence_of_eq_standard_token_sequence
      functionCode
      [Numbered.function_token
        arityPredecessor symbolIndex]
      hFunctionEquality
  have hFunctionDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(functionCode) ≐ₘ numₘ(1) := by
    simpa using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        functionCode
        [Numbered.function_token
          arityPredecessor symbolIndex]
        hFunctionEquality
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        functionCode leftParenthesis
        hFunctionFinite hLeftFinite
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ numₘ(2) := by
    simpa [prefixCode] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        functionCode leftParenthesis 1 1
        hFunctionFinite hLeftFinite
        hFunctionDomain hLeftDomain
  have hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle := by
    simpa [middle] using
      gq_concatenation_finite
        prefixCode flattened
        hPrefixFinite hFlattenedFinite
  have hMiddleDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(middle) ≐ₘ
          numₘ(2 + flattenLength) := by
    simpa [middle, flattened] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        prefixCode flattened 2 flattenLength
        hPrefixFinite hFlattenedFinite
        hPrefixDomain hFlattenDomain
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(rightParenthesis) ≐ₘ numₘ(1) := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .rightParenthesis
  simpa [arityTerm, indexTerm, functionCode,
    leftParenthesis, prefixCode, flattened, middle,
    rightParenthesis, term_application_code_term] using
    gq_concatenation_domain_eq_numeral_lengths_of_theory
      (fun _ hAxiom => hAxiom)
      middle rightParenthesis
      (2 + flattenLength) 1
      hMiddleFinite hRightFinite
      hMiddleDomain hRightDomain

/--
标准输入长度与具体函数应用构造长度不相符时，对象层直接推出矛盾。
-/
theorem
    gq_term_application_standard_code_falsum_of_length_ne
    {Γ : Context signature}
    (arityPredecessor symbolIndex : Nat)
    (arguments : SetTerm)
    (tokens : List Nat)
    (flattenLength : Nat)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hPositive :
      Γ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ))
    (hFlattenDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(flattenₘ(arguments)) ≐ₘ
          numₘ(flattenLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          term_application_code_term
            (numₘ(arityPredecessor))
            (numₘ(symbolIndex))
            arguments)
    (hLength :
      tokens.length ≠ 2 + flattenLength + 1) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let code : SetTerm :=
    term_application_code_term
      (numₘ(arityPredecessor))
      (numₘ(symbolIndex))
      arguments
  have hCodeDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(tokens.length) :=
    gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
      (fun _ hAxiom => hAxiom)
      code tokens
      (Metatheory.Derives.equality_symm hEquality)
  have hConstructorDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ
          numₘ(2 + flattenLength + 1) := by
    simpa [code] using
      gq_term_application_code_domain_eq_of_flatten_domain
        (Γ := Γ)
        arityPredecessor symbolIndex
        arguments flattenLength
        hArguments hPositive hFlattenDomain
  have hNumeralEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(tokens.length) ≐ₘ
          numₘ(2 + flattenLength + 1) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hCodeDomain)
      hConstructorDomain
  have hNotEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        ¬ₘ (numₘ(tokens.length) ≐ₘ
          numₘ(2 + flattenLength + 1)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_ne
            hLength
  exact FirstOrder.Derives.negElim
    hNumeralEquality hNotEquality

/--
标准整串等于具体函数应用码时，已知 flatten 长度即可恢复参数区标准切片。

右括号内容保持为开放有限序列后缀；切片只依赖固定二 token 前缀。
-/
theorem
    gq_term_application_flatten_eq_standard_slice_of_domain
    {Γ : Context signature}
    (arityPredecessor symbolIndex : Nat)
    (arguments : SetTerm)
    (tokens : List Nat)
    (flattenLength : Nat)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hPositive :
      Γ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ))
    (hFlattenDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(flattenₘ(arguments)) ≐ₘ
          numₘ(flattenLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          term_application_code_term
            (numₘ(arityPredecessor))
            (numₘ(symbolIndex))
            arguments)
    (hSliceBound :
      2 + flattenLength ≤ tokens.length) :
    Γ ⊢ₘ[godel_quotation_theory]
      flattenₘ(arguments) ≐ₘ
        standard_token_sequence
          ((tokens.drop 2).take flattenLength) := by
  let arityTerm : SetTerm :=
    numₘ(arityPredecessor)
  let indexTerm : SetTerm :=
    numₘ(symbolIndex)
  let functionCode : SetTerm :=
    coded_function_symbol_code_term
      arityTerm indexTerm
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let prefixCode : SetTerm :=
    functionCode ⌢ₘ leftParenthesis
  let flattened : SetTerm :=
    flattenₘ(arguments)
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  let prefixTokens : List Nat :=
    [Numbered.function_token
        arityPredecessor symbolIndex,
      Numbered.logical_token .leftParenthesis]
  have hArity :
      Term.Admissible arityTerm SetSort.set := by
    simpa [arityTerm] using
      finite_numeral_term_admissible
        arityPredecessor
  have hIndex :
      Term.Admissible indexTerm SetSort.set := by
    simpa [indexTerm] using
      finite_numeral_term_admissible
        symbolIndex
  have hInputsFresh :
      ReservedIdsFresh [0, 1, 2]
        [arityTerm, indexTerm] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hTerm
    rcases hTerm with rfl | rfl
    all_goals
      simp [arityTerm, indexTerm,
        finite_numeral_term_freeSupport]
      exact List.not_mem_nil
  have hStructure :
      Γ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition
            (term_application_code_term
              arityTerm indexTerm arguments) ∧ₘ
          (finite_sequence_condition flattened ∧ₘ
            (domₘ(flattened) ∈ₘ
              domₘ(term_application_code_term
                arityTerm indexTerm arguments)))) := by
    simpa [arityTerm, indexTerm, flattened] using
      gq_term_application_code_finite_and_flattened_domain_member
        (Γ := Γ)
        arityTerm indexTerm arguments
        hArity hIndex hArguments
        hInputsFresh hPositive
  have hFlattenedFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition flattened :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight
        hStructure
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hFunctionEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        functionCode ≐ₘ
          standard_token_sequence
            [Numbered.function_token
              arityPredecessor symbolIndex] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [functionCode, arityTerm,
          indexTerm] using
          coded_function_symbol_code_eq_standard_token_sequence
            arityPredecessor symbolIndex
  have hLeftEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ
          standard_token_sequence
            [Numbered.logical_token
              .leftParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [leftParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis
  have hPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence prefixTokens := by
    simpa [prefixCode, prefixTokens] using
      gq_concatenation_eq_standard_token_sequence
        [Numbered.function_token
          arityPredecessor symbolIndex]
        [Numbered.logical_token
          .leftParenthesis]
        functionCode leftParenthesis
        hFunctionEquality hLeftEquality
  have hRawEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          ((prefixCode ⌢ₘ flattened) ⌢ₘ
            rightParenthesis) := by
    simpa [arityTerm, indexTerm, functionCode,
      leftParenthesis, prefixCode, flattened,
      rightParenthesis,
      term_application_code_term] using hEquality
  simpa [flattened, prefixTokens] using
    gq_concatenation_middle_eq_standard_slice_of_domain
      prefixCode flattened rightParenthesis
      prefixTokens tokens flattenLength
      hPrefixEquality hFlattenedFinite hRightFinite
      (by simpa [flattened] using hFlattenDomain)
      hRawEquality
      (by simpa [prefixTokens] using hSliceBound)
      (hPrefix := by prove_term_check)
      (hBody := by prove_term_check)
      (hSuffix := by prove_term_check)

/--
具体函数应用码在参数 flatten 之后的下一位置必为右括号 token。

该证书只消费 flatten 的 numeral 定义域，不要求参数族已被宿主 decoder 解析。
-/
theorem gq_term_application_code_right_parenthesis_point
    {Γ : Context signature}
    (arityPredecessor symbolIndex : Nat)
    (arguments : SetTerm)
    (flattenLength : Nat)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hPositive :
      Γ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ))
    (hFlattenDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(flattenₘ(arguments)) ≐ₘ
          numₘ(flattenLength)) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((numₘ(2 + flattenLength) ∈ₘ
          domₘ(term_application_code_term
            (numₘ(arityPredecessor))
            (numₘ(symbolIndex))
            arguments)) ∧ₘ
        ((term_application_code_term
              (numₘ(arityPredecessor))
              (numₘ(symbolIndex))
              arguments ·ₘ
            numₘ(2 + flattenLength)) ≐ₘ
          numₘ(Numbered.logical_token
            .rightParenthesis))) := by
  let arityTerm : SetTerm :=
    numₘ(arityPredecessor)
  let indexTerm : SetTerm :=
    numₘ(symbolIndex)
  let functionCode : SetTerm :=
    coded_function_symbol_code_term
      arityTerm indexTerm
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let prefixCode : SetTerm :=
    functionCode ⌢ₘ leftParenthesis
  let flattened : SetTerm :=
    flattenₘ(arguments)
  let middle : SetTerm :=
    prefixCode ⌢ₘ flattened
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  have hArity :
      Term.Admissible arityTerm SetSort.set := by
    simpa [arityTerm] using
      finite_numeral_term_admissible
        arityPredecessor
  have hIndex :
      Term.Admissible indexTerm SetSort.set := by
    simpa [indexTerm] using
      finite_numeral_term_admissible symbolIndex
  have hInputsFresh :
      ReservedIdsFresh [0, 1, 2]
        [arityTerm, indexTerm] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hTerm
    rcases hTerm with rfl | rfl
    all_goals
      simp [arityTerm, indexTerm,
        finite_numeral_term_freeSupport]
      exact List.not_mem_nil
  have hStructure :
      Γ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition
            (term_application_code_term
              arityTerm indexTerm arguments) ∧ₘ
          (finite_sequence_condition flattened ∧ₘ
            (domₘ(flattened) ∈ₘ
              domₘ(term_application_code_term
                arityTerm indexTerm arguments)))) := by
    simpa [flattened] using
      gq_term_application_code_finite_and_flattened_domain_member
        (Γ := Γ)
        arityTerm indexTerm arguments
        hArity hIndex hArguments
        hInputsFresh hPositive
  have hFlattenedFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition flattened :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hStructure
  have hFunctionEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        functionCode ≐ₘ
          standard_token_sequence
            [Numbered.function_token
              arityPredecessor symbolIndex] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [functionCode, arityTerm,
          indexTerm] using
          coded_function_symbol_code_eq_standard_token_sequence
            arityPredecessor symbolIndex
  have hFunctionFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition functionCode :=
    gq_finite_sequence_of_eq_standard_token_sequence
      functionCode
      [Numbered.function_token
        arityPredecessor symbolIndex]
      hFunctionEquality
  have hFunctionDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(functionCode) ≐ₘ numₘ(1) := by
    simpa using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        functionCode
        [Numbered.function_token
          arityPredecessor symbolIndex]
        hFunctionEquality
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        functionCode leftParenthesis
        hFunctionFinite hLeftFinite
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(prefixCode) ≐ₘ numₘ(2) := by
    simpa [prefixCode] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        functionCode leftParenthesis 1 1
        hFunctionFinite hLeftFinite
        hFunctionDomain hLeftDomain
  have hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle := by
    simpa [middle] using
      gq_concatenation_finite
        prefixCode flattened
        hPrefixFinite hFlattenedFinite
  have hMiddleDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(middle) ≐ₘ
          numₘ(2 + flattenLength) := by
    simpa [middle, flattened] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        prefixCode flattened 2 flattenLength
        hPrefixFinite hFlattenedFinite
        hPrefixDomain hFlattenDomain
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRightPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(rightParenthesis)) ∧ₘ
          ((rightParenthesis ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .rightParenthesis))) := by
    simpa [rightParenthesis] using
      gq_standard_token_sequence_point_inversion
        rightParenthesis
        [Numbered.logical_token .rightParenthesis]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            logical_symbol_code_eq_standard_token_sequence
              .rightParenthesis)
        (by simp)
  have hRaw :=
    gq_concatenation_right_point_at_numeral_offset
      middle rightParenthesis
      (2 + flattenLength) 0
      hMiddleFinite hRightFinite hMiddleDomain
      (FirstOrder.Derives.conjElimLeft
        hRightPoint)
  simpa [arityTerm, indexTerm, functionCode,
    leftParenthesis, prefixCode, flattened, middle,
    rightParenthesis, term_application_code_term] using
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjElimLeft hRaw)
      (Metatheory.Derives.equality_trans
        (FirstOrder.Derives.conjElimRight hRaw)
        (FirstOrder.Derives.conjElimRight
          hRightPoint))

/-- 标准输入末位不是右括号时，它不可能等于给定的具体函数应用码。 -/
theorem
    gq_term_application_standard_code_falsum_of_last_not_right
    {Γ : Context signature}
    (arityPredecessor symbolIndex : Nat)
    (arguments : SetTerm)
    (tokens : List Nat)
    (flattenLength : Nat)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hPositive :
      Γ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ))
    (hFlattenDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(flattenₘ(arguments)) ≐ₘ
          numₘ(flattenLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          term_application_code_term
            (numₘ(arityPredecessor))
            (numₘ(symbolIndex))
            arguments)
    (hLast :
      tokens[2 + flattenLength]? ≠
        some (Numbered.logical_token
          .rightParenthesis)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum :=
  gq_standard_token_sequence_falsum_of_point_not_expected
    tokens
    (term_application_code_term
      (numₘ(arityPredecessor))
      (numₘ(symbolIndex))
      arguments)
    (2 + flattenLength)
    (Numbered.logical_token .rightParenthesis)
    hLast hEquality
    (gq_term_application_code_right_parenthesis_point
      arityPredecessor symbolIndex
      arguments flattenLength
      hArguments hPositive hFlattenDomain)

/--
固定头、括号、参数区切片和总长度唯一重组出宿主函数应用 token 串。
-/
theorem fs_function_application_tokens_eq_of_slice
    (tokens : List Nat)
    (pieces : List (List Nat))
    (arityPredecessor symbolIndex : Nat)
    (hLength :
      tokens.length =
        2 + pieces.flatten.length + 1)
    (hHead :
      tokens[0]? =
        some (Numbered.function_token
          arityPredecessor symbolIndex))
    (hLeft :
      tokens[1]? =
        some (Numbered.logical_token
          .leftParenthesis))
    (hMiddle :
      pieces.flatten =
        (tokens.drop 2).take
          pieces.flatten.length)
    (hRight :
      tokens[2 + pieces.flatten.length]? =
        some (Numbered.logical_token
          .rightParenthesis)) :
    Numbered.function_application_tokens
        arityPredecessor symbolIndex pieces =
      tokens := by
  cases tokens with
  | nil =>
      simp at hHead
  | cons head tail =>
      simp at hHead
      subst head
      cases tail with
      | nil =>
          simp at hLeft
      | cons left rest =>
          simp at hLeft
          subst left
          have hRestLength :
              rest.length =
                pieces.flatten.length + 1 := by
            simp only [List.length_cons] at hLength
            omega
          have hMiddle' :
              pieces.flatten =
                rest.take pieces.flatten.length := by
            simpa using hMiddle
          have hRight' :
              rest[pieces.flatten.length]? =
                some (Numbered.logical_token
                  .rightParenthesis) := by
            simpa only [
              show 2 + pieces.flatten.length =
                pieces.flatten.length + 2 by omega,
              List.getElem?_cons_succ] using hRight
          have hIndex :
              pieces.flatten.length < rest.length := by
            omega
          have hGet :=
            List.getElem?_eq_getElem hIndex
          rw [hRight'] at hGet
          have hValue :
              rest[pieces.flatten.length] =
                Numbered.logical_token
                  .rightParenthesis :=
            Option.some.inj hGet.symm
          have hRest :
              rest =
                rest.take pieces.flatten.length ++
                  [Numbered.logical_token
                    .rightParenthesis] := by
            calc
              rest =
                  rest.take
                    (pieces.flatten.length + 1) := by
                rw [← hRestLength, List.take_length]
              _ =
                  rest.take pieces.flatten.length ++
                    [rest[pieces.flatten.length]] :=
                List.take_succ_eq_append_getElem hIndex
              _ =
                  rest.take pieces.flatten.length ++
                    [Numbered.logical_token
                      .rightParenthesis] := by
                rw [hValue]
          have hBody :
              pieces.flatten ++
                  [Numbered.logical_token
                    .rightParenthesis] =
                rest := by
            rw [hMiddle', ← hRest]
          change
            [Numbered.function_token
                arityPredecessor symbolIndex,
              Numbered.logical_token
                .leftParenthesis] ++
                (pieces.flatten ++
                  [Numbered.logical_token
                    .rightParenthesis]) =
              [Numbered.function_token
                  arityPredecessor symbolIndex,
                Numbered.logical_token
                  .leftParenthesis] ++ rest
          exact congrArg
            (fun body =>
              [Numbered.function_token
                  arityPredecessor symbolIndex,
                Numbered.logical_token
                  .leftParenthesis] ++ body)
            hBody

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
