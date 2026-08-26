import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TermCodeInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.Family
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FlattenBound
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SingletonOpening

/-!
# 项码的根点反演

本模块证明变量、常元和正元函数应用三类项码都在零位有定义。证明只使用项码最小
闭包的一步生成反演与标准有限序列关系。
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

private theorem gq_term_opening_theory_fresh
    (id : FreeVarId) :
    ∀ formula, godel_quotation_theory formula →
      (SetSort.set, id) ∉
        Formula.freeSupport formula := by
  intro formula hFormula
  rw [(godel_quotation_theory_sentence hFormula).2]
  exact List.not_mem_nil

/--
正元函数应用编码在零位取其动态函数符号编号，并在一位取左括号。

参数列这里只需要属于 `seq₊_spaceₘ(CodeStrₘ)`；逐项项码条件与参数个数等式均不参与
根点结论，因此不传播到本接口。
-/
theorem gq_term_application_code_opening
    {Γ : Context signature}
    (arityPredecessor symbolIndex arguments : SetTerm)
    (hArity :
      Term.Admissible arityPredecessor SetSort.set)
    (hIndex :
      Term.Admissible symbolIndex SetSort.set)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hSymbolInputsFresh :
      ReservedIdsFresh [0, 1, 2]
        [arityPredecessor, symbolIndex]) :
    Γ ⊢ₘ[godel_quotation_theory]
      (arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ)) ⟶ₘ
        ((numₘ(0) ∈ₘ
            domₘ(term_application_code_term
              arityPredecessor symbolIndex arguments)) ∧ₘ
          ((term_application_code_term
              arityPredecessor symbolIndex arguments ·ₘ
                numₘ(0)) ≐ₘ
            coded_function_symbol_number_term
              arityPredecessor symbolIndex)) ∧ₘ
        ((numₘ(1) ∈ₘ
            domₘ(term_application_code_term
              arityPredecessor symbolIndex arguments)) ∧ₘ
          ((term_application_code_term
              arityPredecessor symbolIndex arguments ·ₘ
                numₘ(1)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
  let functionNumber : SetTerm :=
    coded_function_symbol_number_term
      arityPredecessor symbolIndex
  let functionCode : SetTerm :=
    coded_function_symbol_code_term
      arityPredecessor symbolIndex
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let flattened : SetTerm :=
    flattenₘ(arguments)
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  let positive : SetFormula :=
    arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ)
  let Δ : Context signature := positive :: Γ
  have hFunctionNumber :
      Term.Admissible functionNumber SetSort.set := by
    simpa [functionNumber,
      coded_function_symbol_number_term] using
      natural_multiplication_term_admissible
        (indexed_prime_power_code_term
          3 arityPredecessor)
        (indexed_prime_power_code_term
          5 symbolIndex)
        (indexed_prime_power_code_term_admissible
          3 arityPredecessor hArity)
        (indexed_prime_power_code_term_admissible
          5 symbolIndex hIndex)
  have hFunctionNumberFresh :
      ReservedIdsFresh [0, 1, 2]
        [functionNumber] := by
    intro term hTerm id hId
    rw [List.mem_singleton] at hTerm
    subst term
    have hArityFresh :=
      hSymbolInputsFresh
        arityPredecessor (by simp) id hId
    have hIndexFresh :=
      hSymbolInputsFresh
        symbolIndex (by simp) id hId
    simp only [functionNumber,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      List.nil_append, List.append_nil]
    intro hMember
    rcases List.mem_append.mp hMember with
      hArityMember | hIndexMember
    · exact hArityFresh hArityMember
    · exact hIndexFresh hIndexMember
  have hPositiveAdmissible :
      Formula.Admissible positive := by
    simpa [positive] using
      membership_formula_admissible
        hArguments
        (nonempty_finite_sequence_space_term_admissible
          CodeStrₘ code_string_space_term_admissible)
  nd_apply FirstOrder.Derives.impIntro
  have hPositive :
      Δ ⊢ₘ[godel_quotation_theory] positive :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        hPositiveAdmissible)
  have hCodeStringsNonempty :
      Δ ⊢ₘ[godel_quotation_theory]
        CodeStrₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp [Δ]) <|
        gq_weaken_standard_sequence
          standard_token_sequence_code_string_ne_empty
  have hArgumentsSpace :
      Δ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq_spaceₘ(CodeStrₘ) := by
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_weaken_standard_sequence <|
              nonempty_sequence_space_member_implies_sequence_space
                CodeStrₘ arguments
                code_string_space_term_admissible
                hArguments)
        hCodeStringsNonempty)
      hPositive
  have hFamily :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition arguments :=
    code_string_sequence_member_implies_family_condition_of_theory
      (fun _ hFormula => Or.inl hFormula)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      arguments hArguments hArgumentsSpace
  have hFlattenSpec :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_flatten_spec
          arguments flattened :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ]) <|
          gq_weaken_standard_sequence <| by
            simpa [flattened] using
              finite_sequence_flatten_term_spec_derives
                arguments hArguments)
      hFamily
  have hFlattenedFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition flattened :=
    FirstOrder.Derives.conjElimLeft hFlattenSpec
  have hFunctionOpening :
      Δ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition functionCode ∧ₘ
          ((domₘ(functionCode) ≐ₘ numₘ(1)) ∧ₘ
            ((numₘ(0) ∈ₘ domₘ(functionCode)) ∧ₘ
              ((functionCode ·ₘ numₘ(0)) ≐ₘ
                functionNumber)))) := by
    simpa [functionCode, functionNumber] using
      gq_singleton_symbol_code_opening
        (Γ := Δ) functionNumber
        hFunctionNumber hFunctionNumberFresh
  have hFunctionFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition functionCode :=
    FirstOrder.Derives.conjElimLeft
      hFunctionOpening
  have hFunctionDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(functionCode) ≐ₘ numₘ(1) :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight
        hFunctionOpening
  have hFunctionPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(functionCode)) ∧ₘ
          ((functionCode ·ₘ numₘ(0)) ≐ₘ
            functionNumber)) :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight
        hFunctionOpening
  have hLeftFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .leftParenthesis
  have hLeftPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(leftParenthesis)) ∧ₘ
          ((leftParenthesis ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
    simpa [leftParenthesis] using
      gq_standard_token_sequence_point_inversion
        leftParenthesis
        [Numbered.logical_token .leftParenthesis]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) <|
            logical_symbol_code_eq_standard_token_sequence
              .leftParenthesis)
        (by simp)
  have hRightFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .rightParenthesis
  have hFirstPoint :=
    gq_concatenation_left_point
      functionCode leftParenthesis
      (numₘ(0)) functionNumber
      hFunctionFinite hLeftFinite
      (FirstOrder.Derives.conjElimLeft
        hFunctionPoint)
      (FirstOrder.Derives.conjElimRight
        hFunctionPoint)
  have hFirstFinite :=
    gq_concatenation_finite
      functionCode leftParenthesis
      hFunctionFinite hLeftFinite
  have hFirstRightPointRaw :=
    gq_concatenation_right_point_at_numeral_offset
      functionCode leftParenthesis 1 0
      hFunctionFinite hLeftFinite
      hFunctionDomain
      (FirstOrder.Derives.conjElimLeft
        hLeftPoint)
  have hFirstOnePoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1) ∈ₘ
            domₘ(functionCode ⌢ₘ leftParenthesis)) ∧ₘ
          (((functionCode ⌢ₘ leftParenthesis) ·ₘ
              numₘ(1)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
    exact FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjElimLeft
        hFirstRightPointRaw)
      (Metatheory.Derives.equality_trans
        (FirstOrder.Derives.conjElimRight
          hFirstRightPointRaw)
        (FirstOrder.Derives.conjElimRight
          hLeftPoint))
  have hSecondPoint :=
    gq_concatenation_left_point
      (functionCode ⌢ₘ leftParenthesis)
      flattened (numₘ(0)) functionNumber
      hFirstFinite hFlattenedFinite
      (FirstOrder.Derives.conjElimLeft
        hFirstPoint)
      (FirstOrder.Derives.conjElimRight
        hFirstPoint)
  have hSecondFinite :=
    gq_concatenation_finite
      (functionCode ⌢ₘ leftParenthesis)
      flattened hFirstFinite hFlattenedFinite
  have hSecondOnePoint :=
    gq_concatenation_left_point
      (functionCode ⌢ₘ leftParenthesis)
      flattened (numₘ(1))
      (numₘ(Numbered.logical_token
        .leftParenthesis))
      hFirstFinite hFlattenedFinite
      (FirstOrder.Derives.conjElimLeft
        hFirstOnePoint)
      (FirstOrder.Derives.conjElimRight
        hFirstOnePoint)
  have hZeroPoint :=
    gq_concatenation_left_point
      ((functionCode ⌢ₘ leftParenthesis) ⌢ₘ
        flattened)
      rightParenthesis (numₘ(0)) functionNumber
      hSecondFinite hRightFinite
      (FirstOrder.Derives.conjElimLeft
        hSecondPoint)
      (FirstOrder.Derives.conjElimRight
        hSecondPoint)
  have hOnePoint :=
    gq_concatenation_left_point
      ((functionCode ⌢ₘ leftParenthesis) ⌢ₘ
        flattened)
      rightParenthesis (numₘ(1))
      (numₘ(Numbered.logical_token
        .leftParenthesis))
      hSecondFinite hRightFinite
      (FirstOrder.Derives.conjElimLeft
        hSecondOnePoint)
      (FirstOrder.Derives.conjElimRight
        hSecondOnePoint)
  simpa [functionCode, functionNumber,
    leftParenthesis, flattened, rightParenthesis,
    term_application_code_term] using
    FirstOrder.Derives.conjIntro
      hZeroPoint hOnePoint

/--
正元函数应用码是有限序列，且参数 flatten 严格短于整个应用码。

固定的“函数符号 + 左括号”前缀长度为 `2`，因此 flatten 定义域属于加入该前缀
后的定义域；再沿末尾右括号的左段嵌入提升到完整应用码。
-/
theorem
    gq_term_application_code_finite_and_flattened_domain_member
    {Γ : Context signature}
    (arityPredecessor symbolIndex arguments : SetTerm)
    (hArity :
      Term.Admissible arityPredecessor SetSort.set)
    (hIndex :
      Term.Admissible symbolIndex SetSort.set)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hSymbolInputsFresh :
      ReservedIdsFresh [0, 1, 2]
        [arityPredecessor, symbolIndex])
    (hPositive :
      Γ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ)) :
    Γ ⊢ₘ[godel_quotation_theory]
      (finite_sequence_condition
          (term_application_code_term
            arityPredecessor symbolIndex arguments) ∧ₘ
        (finite_sequence_condition
            (flattenₘ(arguments)) ∧ₘ
          (domₘ(flattenₘ(arguments)) ∈ₘ
            domₘ(term_application_code_term
              arityPredecessor symbolIndex arguments)))) := by
  let functionNumber : SetTerm :=
    coded_function_symbol_number_term
      arityPredecessor symbolIndex
  let functionCode : SetTerm :=
    coded_function_symbol_code_term
      arityPredecessor symbolIndex
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let flattened : SetTerm :=
    flattenₘ(arguments)
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  let functionPrefix : SetTerm :=
    functionCode ⌢ₘ leftParenthesis
  let middle : SetTerm :=
    functionPrefix ⌢ₘ flattened
  have hFunctionNumber :
      Term.Admissible functionNumber SetSort.set := by
    simpa [functionNumber,
      coded_function_symbol_number_term] using
      natural_multiplication_term_admissible
        (indexed_prime_power_code_term
          3 arityPredecessor)
        (indexed_prime_power_code_term
          5 symbolIndex)
        (indexed_prime_power_code_term_admissible
          3 arityPredecessor hArity)
        (indexed_prime_power_code_term_admissible
          5 symbolIndex hIndex)
  have hFunctionNumberFresh :
      ReservedIdsFresh [0, 1, 2]
        [functionNumber] := by
    intro term hTerm id hId
    rw [List.mem_singleton] at hTerm
    subst term
    have hArityFresh :=
      hSymbolInputsFresh
        arityPredecessor (by simp) id hId
    have hIndexFresh :=
      hSymbolInputsFresh
        symbolIndex (by simp) id hId
    simp only [functionNumber,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      List.nil_append, List.append_nil]
    intro hMember
    rcases List.mem_append.mp hMember with
      hMember | hMember
    · exact hArityFresh hMember
    · exact hIndexFresh hMember
  have hCodeStringsNonempty :
      Γ ⊢ₘ[godel_quotation_theory]
        CodeStrₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence
          standard_token_sequence_code_string_ne_empty
  have hArgumentsSpace :
      Γ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq_spaceₘ(CodeStrₘ) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            gq_weaken_standard_sequence <|
              nonempty_sequence_space_member_implies_sequence_space
                CodeStrₘ arguments
                code_string_space_term_admissible
                hArguments)
        hCodeStringsNonempty)
      hPositive
  have hFamily :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition arguments :=
    code_string_sequence_member_implies_family_condition_of_theory
      (fun _ hFormula => Or.inl hFormula)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      arguments hArguments hArgumentsSpace
  have hFlattenSpec :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_flatten_spec
          arguments flattened :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <| by
            simpa [flattened] using
              finite_sequence_flatten_term_spec_derives
                arguments hArguments)
      hFamily
  have hFlattenedFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition flattened :=
    FirstOrder.Derives.conjElimLeft hFlattenSpec
  have hFunctionOpening :
      Γ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition functionCode ∧ₘ
          (domₘ(functionCode) ≐ₘ numₘ(1))) := by
    simpa [functionCode, functionNumber] using
      FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjElimLeft <|
          gq_singleton_symbol_code_opening
            (Γ := Γ) functionNumber
            hFunctionNumber hFunctionNumberFresh)
        (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight <|
            gq_singleton_symbol_code_opening
              (Γ := Γ) functionNumber
              hFunctionNumber hFunctionNumberFresh)
  have hFunctionFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition functionCode :=
    FirstOrder.Derives.conjElimLeft hFunctionOpening
  have hFunctionDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(functionCode) ≐ₘ numₘ(1) :=
    FirstOrder.Derives.conjElimRight hFunctionOpening
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
        finite_sequence_condition functionPrefix := by
    simpa [functionPrefix] using
      gq_concatenation_finite
        functionCode leftParenthesis
        hFunctionFinite hLeftFinite
  have hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(functionPrefix) ≐ₘ numₘ(1 + 1) := by
    simpa [functionPrefix] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        functionCode leftParenthesis 1 1
        hFunctionFinite hLeftFinite
        hFunctionDomain hLeftDomain
  have hFlattenedInMiddle :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(flattened) ∈ₘ domₘ(middle) := by
    simpa [middle] using
      gq_concatenation_right_domain_member_of_positive_left_length
        functionPrefix flattened 1
        hPrefixFinite hFlattenedFinite
        hPrefixDomain
  have hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle := by
    simpa [middle] using
      gq_concatenation_finite
        functionPrefix flattened
        hPrefixFinite hFlattenedFinite
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hWhole :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(flattened) ∈ₘ
          domₘ(middle ⌢ₘ rightParenthesis) :=
    gq_concatenation_left_domain_member
      middle rightParenthesis
      (domₘ(flattened))
      hMiddleFinite hRightFinite
      hFlattenedInMiddle
  have hWholeFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          (middle ⌢ₘ rightParenthesis) :=
    gq_concatenation_finite
      middle rightParenthesis
      hMiddleFinite hRightFinite
  simpa [functionCode, leftParenthesis,
    flattened, rightParenthesis, functionPrefix, middle,
    term_application_code_term] using
      FirstOrder.Derives.conjIntro
        hWholeFinite <|
          FirstOrder.Derives.conjIntro
            hFlattenedFinite hWhole

/--
函数应用码中任一外部 numeral 参数位置的子码都严格短于整个应用码。

证明先由 checked replay 得到该参数长度不超过参数 flatten，再使用对象自然数
`≤`-`<` 混合传递。接口只暴露参数族的定义域 numeral 证书，不暴露 flatten
累积器。
-/
theorem gq_term_application_code_argument_domain_member
    {Γ : Context signature}
    (arityPredecessor symbolIndex argumentIndex : Nat)
    (arguments : SetTerm)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hPositive :
      Γ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ))
    (hDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(arguments) ≐ₘ
          numₘ(arityPredecessor + 1))
    (hArgumentIndex :
      argumentIndex < arityPredecessor + 1) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(arguments ·ₘ numₘ(argumentIndex)) ∈ₘ
        domₘ(term_application_code_term
          (numₘ(arityPredecessor))
          (numₘ(symbolIndex))
          arguments) := by
  let arityTerm : SetTerm :=
    numₘ(arityPredecessor)
  let indexTerm : SetTerm :=
    numₘ(symbolIndex)
  let flattened : SetTerm :=
    flattenₘ(arguments)
  let code : SetTerm :=
    term_application_code_term
      arityTerm indexTerm arguments
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
        (finite_sequence_condition code ∧ₘ
          (finite_sequence_condition flattened ∧ₘ
            (domₘ(flattened) ∈ₘ domₘ(code)))) := by
    simpa [arityTerm, indexTerm, flattened, code] using
      gq_term_application_code_finite_and_flattened_domain_member
        (Γ := Γ)
        arityTerm indexTerm arguments
        hArity hIndex hArguments
        hInputsFresh hPositive
  have hCodeFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition code :=
    FirstOrder.Derives.conjElimLeft hStructure
  have hFlattenedFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition flattened :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hStructure
  have hFlattenedInCode :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(flattened) ∈ₘ domₘ(code) :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight hStructure
  have hCodeStringsNonempty :
      Γ ⊢ₘ[godel_quotation_theory]
        CodeStrₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence
          standard_token_sequence_code_string_ne_empty
  have hArgumentsSpace :
      Γ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq_spaceₘ(CodeStrₘ) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            gq_weaken_standard_sequence <|
              nonempty_sequence_space_member_implies_sequence_space
                CodeStrₘ arguments
                code_string_space_term_admissible
                hArguments)
        hCodeStringsNonempty)
      hPositive
  have hFamily :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition arguments :=
    code_string_sequence_member_implies_family_condition_of_theory
      (fun _ hFormula => Or.inl hFormula)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      arguments hArguments hArgumentsSpace
  have hArgumentLeFlattened :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(arguments ·ₘ numₘ(argumentIndex)) ∈ₘ
          Sₘ(domₘ(flattened)) := by
    simpa [flattened] using
      gq_flatten_numeral_point_domain_le
        (Γ := Γ)
        arguments
        (arityPredecessor + 1)
        argumentIndex hArguments
        hFamily hDomain hArgumentIndex
  have hArgumentDomain :
      Term.Admissible
        (domₘ(arguments ·ₘ
          numₘ(argumentIndex))) SetSort.set :=
    domain_term_admissible
      (arguments ·ₘ numₘ(argumentIndex))
      (function_application_term_admissible
        arguments (numₘ(argumentIndex))
        hArguments
        (finite_numeral_term_admissible
          argumentIndex))
  have hFlattenedDomain :
      Term.Admissible
        (domₘ(flattened)) SetSort.set :=
    domain_term_admissible
      flattened
      (by
        simpa [flattened] using
          finite_sequence_flatten_term_admissible
            arguments hArguments)
  have hCodeDomain :
      Term.Admissible
        (domₘ(code)) SetSort.set :=
    domain_term_admissible
      code
      (by
        simpa [arityTerm, indexTerm, code] using
          term_application_code_term_admissible
            arityTerm indexTerm arguments
            hArity hIndex hArguments)
  have hFlattenedOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(flattened) ∈ₘ ωₘ := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight
        hFlattenedFinite
  have hCodeOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ∈ₘ ωₘ := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight
        hCodeFinite
  simpa [arityTerm, indexTerm, flattened, code] using
    gq_natural_le_lt_transitivity
      (Γ := Γ)
      (domₘ(arguments ·ₘ numₘ(argumentIndex)))
      (domₘ(flattened))
      (domₘ(code))
      hArgumentDomain hFlattenedDomain hCodeDomain
      hFlattenedOmega hCodeOmega
      hArgumentLeFlattened hFlattenedInCode

/--
任意常元符号成员都是定义域为 `1` 的有限序列。

与变量符号反演相同，本定理保留对象层自然数见证，只恢复 singleton 结构；
因此不会把 `ConstSymₘ` 中的任意对象自然数提升为 Lean 自然数。
-/
theorem gq_constant_symbol_member_implies_finite_domain_one
    (symbol : SetTerm)
    (hSymbol : Term.Admissible symbol SetSort.set)
    (hFresh :
      (SetSort.set, 201) ∉
        Term.freeSupport symbol) :
    ⊢ₘ[godel_quotation_theory]
      (symbol ∈ₘ ConstSymₘ) ⟶ₘ
        (finite_sequence_condition symbol ∧ₘ
          (domₘ(symbol) ≐ₘ numₘ(1))) := by
  let witness : SetTerm := x#201
  let rawCode : SetTerm :=
    constant_symbol_code_term witness
  let number : SetTerm :=
    constant_symbol_number_term witness
  let witnessCondition : SetFormula :=
    (witness ∈ₘ ωₘ) ∧ₘ
      (symbol ≐ₘ rawCode)
  let conclusion : SetFormula :=
    finite_sequence_condition symbol ∧ₘ
      (domₘ(symbol) ≐ₘ numₘ(1))
  have hWitness :
      Term.Admissible witness SetSort.set := by
    simpa [witness] using
      set_variable_admissible 201
  have hNumber :
      Term.Admissible number SetSort.set := by
    simpa [number, constant_symbol_number_term] using
      indexed_prime_power_code_term_admissible
        5 witness hWitness
  have hRawCode :
      Term.Admissible rawCode SetSort.set := by
    simpa [rawCode] using
      constant_symbol_code_term_admissible
        witness hWitness
  have hWitnessConditionAdmissible :
      Formula.Admissible witnessCondition := by
    dsimp only [witnessCondition]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        hWitness omega_term_admissible)
      (Formula.Admissible.equal
        hSymbol hRawCode)
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        witnessCondition ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [witnessCondition]
    have hWitnessCondition :
        Γ ⊢ₘ[godel_quotation_theory]
          witnessCondition :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hWitnessConditionAdmissible)
    have hEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          symbol ≐ₘ rawCode := by
      simpa [witnessCondition] using
        FirstOrder.Derives.conjElimRight
          hWitnessCondition
    have hOpening :
        Γ ⊢ₘ[godel_quotation_theory]
          (finite_sequence_condition rawCode ∧ₘ
            ((domₘ(rawCode) ≐ₘ numₘ(1)) ∧ₘ
              ((numₘ(0) ∈ₘ domₘ(rawCode)) ∧ₘ
                ((rawCode ·ₘ numₘ(0)) ≐ₘ
                  number)))) := by
      simpa [rawCode, number] using
        gq_singleton_symbol_code_opening
          (Γ := Γ) number hNumber
          (by
            intro term hTerm id hId
            rw [List.mem_singleton] at hTerm
            subst term
            have hIdNe : id ≠ 201 := by
              simp only [List.mem_cons,
                List.not_mem_nil, or_false] at hId
              rcases hId with rfl | rfl | rfl <;>
                decide
            simp only [number, witness,
              Term.freeSupport, Term.freeSupportList,
              finite_numeral_term_freeSupport]
            intro hMember
            exact hIdNe <|
              congrArg Prod.snd <|
                List.mem_singleton.mp hMember)
    have hFinite :
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition symbol :=
      FirstOrder.Derives.iffElimLeft
        (finite_sequence_condition_iff_of_equality
          symbol rawCode hSymbol hRawCode hEquality)
        (FirstOrder.Derives.conjElimLeft hOpening)
    have hDomain :
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(symbol) ≐ₘ numₘ(1) :=
      Metatheory.Derives.equality_trans
        (domain_term_congr_of_equality
          symbol rawCode hSymbol hRawCode hEquality)
        (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hOpening)
    simpa [conclusion] using
      FirstOrder.Derives.conjIntro hFinite hDomain
  have hConclusionFresh :
      (SetSort.set, 201) ∉
        Formula.freeSupport conclusion := by
    simp only [conclusion, finite_sequence_condition,
      Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      List.append_nil]
    intro hMember
    rcases List.mem_append.mp hMember with
      hMember | hMember
    · rcases List.mem_append.mp hMember with
        hMember | hMember <;>
        exact hFresh hMember
    · exact hFresh hMember
  have hExistsImp :
      ⊢ₘ[godel_quotation_theory]
        (∃ₘ[SetSort.set, 201], witnessCondition) ⟶ₘ
          conclusion :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 201)
      (gq_term_opening_theory_fresh 201)
      (by
        intro formula hFormula
        cases hFormula)
      hConclusionFresh hPoint
  have hMembershipAdmissible :
      Formula.Admissible
        (symbol ∈ₘ ConstSymₘ) :=
    membership_formula_admissible
      hSymbol constant_symbol_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [symbol ∈ₘ ConstSymₘ]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        symbol ∈ₘ ConstSymₘ :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMembershipAdmissible)
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        constant_symbol_condition symbol :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_constant_symbol_definition_instance
          symbol hSymbol hFresh))
      hMember
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 201], witnessCondition := by
    simpa [constant_symbol_condition,
      witnessCondition, witness, rawCode,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable] using
      FirstOrder.Derives.conjElimRight hCondition
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ])
      hExistsImp)
    hExists

/-- 常元 singleton 结构的直接推论：零位属于其定义域。 -/
theorem gq_constant_symbol_zero_mem_domain
    (symbol : SetTerm)
    (hSymbol : Term.Admissible symbol SetSort.set)
    (hFresh :
      (SetSort.set, 201) ∉
        Term.freeSupport symbol) :
    ⊢ₘ[godel_quotation_theory]
      (symbol ∈ₘ ConstSymₘ) ⟶ₘ
        (numₘ(0) ∈ₘ domₘ(symbol)) := by
  let membership : SetFormula :=
    symbol ∈ₘ ConstSymₘ
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hSymbol constant_symbol_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [membership]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        symbol ∈ₘ ConstSymₘ := by
    simpa [Γ, membership] using
      FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ)
        (φ := membership)
        (by simp [Γ])
        (Formula.check_admissible_complete
          hMembershipAdmissible)
  have hStructure :
      Γ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition symbol ∧ₘ
          (domₘ(symbol) ≐ₘ numₘ(1))) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_constant_symbol_member_implies_finite_domain_one
          symbol hSymbol hFresh))
      hMember
  have hZeroOne :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(0) ∈ₘ numₘ(1) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            0 1 (by omega)
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      (numₘ(0)) (domₘ(symbol)) (numₘ(1))
      (finite_numeral_term_admissible 0)
      (domain_term_admissible symbol hSymbol)
      (finite_numeral_term_admissible 1)
      (FirstOrder.Derives.conjElimRight hStructure))
    hZeroOne

/--
一次函数应用生成条件同时给出零位定义与一位左括号。

零位值依赖存在量词中的动态函数符号编号，故这里只保留后续项码总反演所需的
零位定义；一位值则是固定 token，可以完整导出供 checked parser 拒绝使用。
-/
theorem
    gq_term_application_from_condition_implies_opening
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [210, 211, 212] [code]) :
    ⊢ₘ[godel_quotation_theory]
      term_application_from_condition TermCodeₘ code ⟶ₘ
        ((numₘ(0) ∈ₘ domₘ(code)) ∧ₘ
          ((numₘ(1) ∈ₘ domₘ(code)) ∧ₘ
            ((code ·ₘ numₘ(1)) ≐ₘ
              numₘ(Numbered.logical_token
                .leftParenthesis)))) := by
  let arity : SetTerm := x#210
  let symbolIndex : SetTerm := x#211
  let arguments : SetTerm := x#212
  let header : SetFormula :=
    (arity ∈ₘ ωₘ) ∧ₘ
      ((symbolIndex ∈ₘ ωₘ) ∧ₘ
        ((arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ)) ∧ₘ
          (domₘ(arguments) ≐ₘ Sₘ(arity))))
  let values : SetFormula :=
    ∀ₘ[SetSort.set, 213],
      (x#213 ∈ₘ domₘ(arguments)) ⟶ₘ
        ((arguments ·ₘ x#213) ∈ₘ TermCodeₘ)
  let equality : SetFormula :=
    code ≐ₘ
      term_application_code_term
        arity symbolIndex arguments
  let body : SetFormula :=
    header ∧ₘ (values ∧ₘ equality)
  let conclusion : SetFormula :=
    (numₘ(0) ∈ₘ domₘ(code)) ∧ₘ
      ((numₘ(1) ∈ₘ domₘ(code)) ∧ₘ
        ((code ·ₘ numₘ(1)) ≐ₘ
          numₘ(Numbered.logical_token
            .leftParenthesis)))
  have hArity :
      Term.Admissible arity SetSort.set := by
    simpa [arity] using
      set_variable_admissible 210
  have hIndex :
      Term.Admissible symbolIndex SetSort.set := by
    simpa [symbolIndex] using
      set_variable_admissible 211
  have hArguments :
      Term.Admissible arguments SetSort.set := by
    simpa [arguments] using
      set_variable_admissible 212
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body, header, values, equality]
    prove_admissible
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        body ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [body]
    have hBody :
        Γ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hBodyAdmissible)
    have hHeader :
        Γ ⊢ₘ[godel_quotation_theory] header :=
      FirstOrder.Derives.conjElimLeft hBody
    have hPositive :
        Γ ⊢ₘ[godel_quotation_theory]
          arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ) :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight hHeader
    have hEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ
            term_application_code_term
              arity symbolIndex arguments := by
      simpa [equality] using
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight hBody
    have hRawOpening :=
      FirstOrder.Derives.impElim
        (gq_term_application_code_opening
          (Γ := Γ)
          arity symbolIndex arguments
          hArity hIndex hArguments
          (reserved_ids_fresh_cons_variable
            210
            (by
              intro id hId
              simp only [List.mem_cons,
                List.not_mem_nil, or_false] at hId
              rcases hId with rfl | rfl | rfl <;>
                decide)
            (reserved_ids_fresh_cons_variable
              211
              (by
                intro id hId
                simp only [List.mem_cons,
                  List.not_mem_nil, or_false] at hId
                rcases hId with rfl | rfl | rfl <;>
                  decide)
              (reserved_ids_fresh_nil [0, 1, 2]))))
        hPositive
    have hCodeZeroPoint :=
      gq_point_inversion_of_equality
        code
        (term_application_code_term
          arity symbolIndex arguments)
        (numₘ(0))
        (coded_function_symbol_number_term
          arity symbolIndex)
        hEquality
        (FirstOrder.Derives.conjElimLeft
          hRawOpening)
    have hCodeOnePoint :=
      gq_point_inversion_of_equality
        code
        (term_application_code_term
          arity symbolIndex arguments)
        (numₘ(1))
        (numₘ(Numbered.logical_token
          .leftParenthesis))
        hEquality
        (FirstOrder.Derives.conjElimRight
          hRawOpening)
    simpa [conclusion] using
      FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjElimLeft
          hCodeZeroPoint)
        hCodeOnePoint
  have hConclusionFresh
      (id : FreeVarId)
      (hId : id ∈ [210, 211, 212]) :
      (SetSort.set, id) ∉
        Formula.freeSupport conclusion := by
    have hCodeFresh :
        (SetSort.set, id) ∉
          Term.freeSupport code :=
      hFresh code (by simp) id hId
    simp only [conclusion, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      List.nil_append, List.append_nil]
    intro hMember
    rcases List.mem_append.mp hMember with
      hMember | hMember
    · exact hCodeFresh hMember
    · rcases List.mem_append.mp hMember with
        hMember | hMember
      · exact hCodeFresh hMember
      · exact hCodeFresh hMember
  have hAt212 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 212)
      (gq_term_opening_theory_fresh 212)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 212 (by simp))
      hPoint
  have hAt211 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 211)
      (gq_term_opening_theory_fresh 211)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 211 (by simp))
      hAt212
  have hAt210 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 210)
      (gq_term_opening_theory_fresh 210)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 210 (by simp))
      hAt211
  simpa [term_application_from_condition,
    body, header, values, equality,
    arity, symbolIndex, arguments,
    conclusion] using hAt210

/-- 项码一步生成的三个分支统一导出零位定义域成员。 -/
theorem gq_term_code_generation_implies_zero_mem_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [200, 201, 210, 211, 212] [code]) :
    ⊢ₘ[godel_quotation_theory]
      term_code_generation_condition TermCodeₘ code ⟶ₘ
        (numₘ(0) ∈ₘ domₘ(code)) := by
  have hGenerationAdmissible :
      Formula.Admissible
        (term_code_generation_condition
          TermCodeₘ code) :=
    by
      unfold term_code_generation_condition
      prove_admissible
  have hApplicationFresh :
      ReservedIdsFresh [210, 211, 212] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with rfl | rfl | rfl <;>
      simp
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [term_code_generation_condition TermCodeₘ code]
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        term_code_generation_condition
          TermCodeₘ code :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hGenerationAdmissible)
  unfold term_code_generation_condition at hGeneration
  apply FirstOrder.Derives.disjElim hGeneration
  · let Δ : Context signature :=
      (code ∈ₘ VarSymₘ) :: Γ
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ])
        (gq_variable_symbol_zero_mem_domain
          code hCode
          (hFresh code (by simp) 200 (by simp))))
      (FirstOrder.Derives.assumption
        (by simp))
  · let tail : SetFormula :=
      (code ∈ₘ ConstSymₘ) ∨ₘ
        term_application_from_condition
          TermCodeₘ code
    let Δ : Context signature := tail :: Γ
    have hTail :
        Δ ⊢ₘ[godel_quotation_theory] tail :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    apply FirstOrder.Derives.disjElim hTail
    · let Ε : Context signature :=
        (code ∈ₘ ConstSymₘ) :: Δ
      exact FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp [Ε])
          (gq_constant_symbol_zero_mem_domain
            code hCode
            (hFresh code (by simp) 201 (by simp))))
        (FirstOrder.Derives.assumption
          (by simp))
    · let application : SetFormula :=
        term_application_from_condition
          TermCodeₘ code
      let Ε : Context signature :=
        application :: Δ
      exact FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ε) (by simp [Ε])
            (gq_term_application_from_condition_implies_opening
              code hCode hApplicationFresh))
          (FirstOrder.Derives.assumption
            (by simp))

/--
每个完整项码都在零位有定义；编号前提精确覆盖三类生成分支与最小性反演。
-/
theorem gq_term_code_member_implies_zero_mem_domain_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [200, 201, 210, 211, 212, 213, 610]
        [code]) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ TermCodeₘ) ⟶ₘ
        (numₘ(0) ∈ₘ domₘ(code)) := by
  have hMembershipAdmissible :
      Formula.Admissible
        (code ∈ₘ TermCodeₘ) :=
    membership_formula_admissible
      hCode term_code_set_term_admissible
  have hGenerationFresh :
      ReservedIdsFresh
        [210, 211, 212, 213, 610] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with rfl | rfl | rfl | rfl | rfl <;>
      simp
  have hOpeningFresh :
      ReservedIdsFresh
        [200, 201, 210, 211, 212] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with rfl | rfl | rfl | rfl | rfl <;>
      simp
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [code ∈ₘ TermCodeₘ]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMembershipAdmissible)
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        term_code_generation_condition
          TermCodeₘ code :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_term_code_member_implies_generation_of_fresh
          code hCode hGenerationFresh))
      hMember
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ])
      (gq_term_code_generation_implies_zero_mem_domain
        code hCode hOpeningFresh))
    hGeneration

/-- 闭项上的零位反演是精确新鲜度接口的直接推论。 -/
theorem gq_term_code_member_implies_zero_mem_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hClosed : Term.freeSupport code = []) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ TermCodeₘ) ⟶ₘ
        (numₘ(0) ∈ₘ domₘ(code)) :=
  gq_term_code_member_implies_zero_mem_domain_of_fresh
    code hCode <|
      reserved_ids_fresh_cons_closed hClosed <|
        reserved_ids_fresh_nil
          [200, 201, 210, 211, 212, 213, 610]

/--
标准 token 串没有零号位置时，它不是项码。

这是项 parser 的首个闭失败类；后续结构反演可在其上继续处理错误的根 token 与参数
个数。
-/
theorem
    gq_standard_token_sequence_term_code_not_of_zero_absent
    (tokens : List Nat)
    (hZero : tokens[0]? = none) :
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ (standard_token_sequence tokens ∈ₘ
        TermCodeₘ) := by
  let code : SetTerm :=
    standard_token_sequence tokens
  let membership : SetFormula :=
    code ∈ₘ TermCodeₘ
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hClosed :
      Term.freeSupport code = [] := by
    simp [code]
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    dsimp only [membership]
    exact membership_formula_admissible
      hCode term_code_set_term_admissible
  change ⊢ₘ[godel_quotation_theory]
    ¬ₘ membership
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hMembershipAdmissible)
  let Γ : Context signature := [membership]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory] membership :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMembershipAdmissible)
  have hZeroDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(0) ∈ₘ domₘ(code) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_term_code_member_implies_zero_mem_domain
          code hCode hClosed))
      (by simpa [membership] using hMember)
  have hDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(tokens.length) := by
    simpa [code] using
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_weaken_standard_sequence
            (standard_token_sequence_domain_eq_length
              tokens)
  have hLengthMember :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(0) ∈ₘ numₘ(tokens.length) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        (numₘ(0)) (domₘ(code))
        (numₘ(tokens.length))
        (finite_numeral_term_admissible 0)
        (domain_term_admissible code hCode)
        (finite_numeral_term_admissible
          tokens.length)
        hDomain)
      hZeroDomain
  have hNotLt : ¬ 0 < tokens.length := by
    intro hLt
    have hSome :
        tokens[0]? = some tokens[0] :=
      List.getElem?_eq_getElem hLt
    rw [hZero] at hSome
    contradiction
  have hNotMember :
      ⊢ₘ[godel_quotation_theory]
        ¬ₘ (numₘ(0) ∈ₘ
          numₘ(tokens.length)) :=
    gq_weaken_standard_sequence
      (standard_sequence_finite_numeral_not_mem_of_not_lt
        0 tokens.length hNotLt)
  exact FirstOrder.Derives.negElim
    hLengthMember
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ])
      hNotMember)

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
