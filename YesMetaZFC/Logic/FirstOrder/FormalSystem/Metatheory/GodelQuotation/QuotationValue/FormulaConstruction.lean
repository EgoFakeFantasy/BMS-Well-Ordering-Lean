import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaShape
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SequenceInversion
/-!
# Gödel quotation 的公式构造值
本模块把项应用与各类公式构造的对象代码对齐到标准 token 序列。
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
正元函数应用编码与函数符号、括号和参数 token 分片的外部拼接严格对应。
-/
theorem gq_term_application_code_eq_standard_token_sequence
    (arityPredecessor index : Nat)
    {codes : List SetTerm} {pieces : List (List Nat)} (hAligned : gq_code_token_aligned_list codes pieces) :
    ⊢ₘ[godel_quotation_theory]
      term_application_code_term (numₘ(arityPredecessor)) (numₘ(index)) (standard_sequence codes) ≐ₘ
        standard_token_sequence (Numbered.function_application_tokens
            arityPredecessor index pieces) := by
  let functionCode :=
    coded_function_symbol_code_term (numₘ(arityPredecessor)) (numₘ(index))
  let leftParenthesis := left_parenthesis_symbol_code_term
  let rightParenthesis := right_parenthesis_symbol_code_term
  let family := standard_sequence codes
  let flattened := flattenₘ(family)
  let prefixCode := functionCode ⌢ₘ leftParenthesis
  let bodyCode := prefixCode ⌢ₘ flattened
  have hFunctionCode :
      Term.CheckCertificate functionCode SetSort.set := by
    prove_term_check
  have hFamily :
      Term.CheckCertificate family SetSort.set := by
    apply standard_sequence_from_check
    intro code hCode
    exact
      (gq_aligned_codes_boundary hAligned code hCode).check_certificate
  have hFlattened :
      Term.CheckCertificate flattened SetSort.set := by
    prove_term_check
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hPrefixTerm :
      Term.CheckCertificate prefixCode SetSort.set := by
    prove_term_check
  have hBodyTerm :
      Term.CheckCertificate bodyCode SetSort.set := by
    prove_term_check
  have hPrefix :
      ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence
            [Numbered.function_token arityPredecessor index,
              Numbered.logical_token .leftParenthesis] := by
    simpa [prefixCode, functionCode, leftParenthesis] using
      gq_concatenation_eq_standard_token_sequence
        [Numbered.function_token arityPredecessor index]
        [Numbered.logical_token .leftParenthesis]
        functionCode leftParenthesis
        (coded_function_symbol_code_eq_standard_token_sequence
          arityPredecessor index) (logical_symbol_code_eq_standard_token_sequence .leftParenthesis)
  have hFlattenedValue :
      ⊢ₘ[godel_quotation_theory]
        flattened ≐ₘ
          standard_token_sequence pieces.flatten := by
    simpa [flattened, family] using
      gq_argument_family_flatten_eq_standard_token_sequence hAligned
  have hBody :
      ⊢ₘ[godel_quotation_theory]
        bodyCode ≐ₘ
          standard_token_sequence ([Numbered.function_token arityPredecessor index,
                Numbered.logical_token .leftParenthesis] ++
              pieces.flatten) := by
    simpa [bodyCode] using
      gq_concatenation_eq_standard_token_sequence
        [Numbered.function_token arityPredecessor index,
          Numbered.logical_token .leftParenthesis]
        pieces.flatten prefixCode flattened
        hPrefix hFlattenedValue
  have hComplete :=
    gq_concatenation_eq_standard_token_sequence ([Numbered.function_token arityPredecessor index,
          Numbered.logical_token .leftParenthesis] ++ pieces.flatten)
      [Numbered.logical_token .rightParenthesis]
      bodyCode rightParenthesis
      hBody (logical_symbol_code_eq_standard_token_sequence .rightParenthesis)
  simpa [Numbered.function_application_tokens,
    functionCode, leftParenthesis, rightParenthesis,
    family, flattened, prefixCode, bodyCode, List.append_assoc] using hComplete
/--
普通谓词应用编码与谓词符号、括号和参数 token 分片的外部拼接严格对应。
-/
theorem gq_predicate_application_code_eq_standard_token_sequence (arityPredecessor index : Nat)
    {codes : List SetTerm} {pieces : List (List Nat)} (hAligned : gq_code_token_aligned_list codes pieces) :
    ⊢ₘ[godel_quotation_theory]
      predicate_application_code_term (numₘ(arityPredecessor)) (numₘ(index)) (standard_sequence codes) ≐ₘ
        standard_token_sequence (Numbered.predicate_application_tokens
            arityPredecessor index pieces) := by
  let predicateCode :=
    coded_predicate_symbol_code_term (numₘ(arityPredecessor)) (numₘ(index))
  let leftParenthesis := left_parenthesis_symbol_code_term
  let rightParenthesis := right_parenthesis_symbol_code_term
  let family := standard_sequence codes
  let flattened := flattenₘ(family)
  let prefixCode := predicateCode ⌢ₘ leftParenthesis
  let bodyCode := prefixCode ⌢ₘ flattened
  have hPredicateCode :
      Term.CheckCertificate predicateCode SetSort.set := by
    prove_term_check
  have hFamily :
      Term.CheckCertificate family SetSort.set := by
    apply standard_sequence_from_check
    intro code hCode
    exact
      (gq_aligned_codes_boundary hAligned code hCode).check_certificate
  have hFlattened :
      Term.CheckCertificate flattened SetSort.set := by
    prove_term_check
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hRightParenthesis :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hPrefixTerm :
      Term.CheckCertificate prefixCode SetSort.set := by
    prove_term_check
  have hBodyTerm :
      Term.CheckCertificate bodyCode SetSort.set := by
    prove_term_check
  have hPrefix :
      ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence
            [Numbered.predicate_token arityPredecessor index,
              Numbered.logical_token .leftParenthesis] := by
    simpa [prefixCode, predicateCode, leftParenthesis] using
      gq_concatenation_eq_standard_token_sequence
        [Numbered.predicate_token arityPredecessor index]
        [Numbered.logical_token .leftParenthesis]
        predicateCode leftParenthesis
        (coded_predicate_symbol_code_eq_standard_token_sequence
          arityPredecessor index) (logical_symbol_code_eq_standard_token_sequence .leftParenthesis)
  have hFlattenedValue :
      ⊢ₘ[godel_quotation_theory]
        flattened ≐ₘ
          standard_token_sequence pieces.flatten := by
    simpa [flattened, family] using
      gq_argument_family_flatten_eq_standard_token_sequence hAligned
  have hBody :
      ⊢ₘ[godel_quotation_theory]
        bodyCode ≐ₘ
          standard_token_sequence ([Numbered.predicate_token arityPredecessor index,
                Numbered.logical_token .leftParenthesis] ++
              pieces.flatten) := by
    simpa [bodyCode] using
      gq_concatenation_eq_standard_token_sequence
        [Numbered.predicate_token arityPredecessor index,
          Numbered.logical_token .leftParenthesis]
        pieces.flatten prefixCode flattened
        hPrefix hFlattenedValue
  have hComplete :=
    gq_concatenation_eq_standard_token_sequence ([Numbered.predicate_token arityPredecessor index,
          Numbered.logical_token .leftParenthesis] ++ pieces.flatten)
      [Numbered.logical_token .rightParenthesis]
      bodyCode rightParenthesis
      hBody (logical_symbol_code_eq_standard_token_sequence .rightParenthesis)
  simpa [Numbered.predicate_application_tokens,
    predicateCode, leftParenthesis, rightParenthesis,
    family, flattened, prefixCode, bodyCode, List.append_assoc] using hComplete
/--
括号包围的三段字符串构造与五段外部 token 拼接一致。
该形状统一覆盖二元原子、蕴含和全称量化编码。
-/
theorem gq_bracketed_three_part_eq_standard_token_sequence (firstTokens middleTokens lastTokens : List Nat) (firstCode middleCode lastCode : SetTerm)
    (hFirst :
      ⊢ₘ[godel_quotation_theory]
        firstCode ≐ₘ standard_token_sequence firstTokens) (hMiddle :
      ⊢ₘ[godel_quotation_theory]
        middleCode ≐ₘ standard_token_sequence middleTokens) (hLast :
      ⊢ₘ[godel_quotation_theory]
        lastCode ≐ₘ standard_token_sequence lastTokens)
    (hFirstCode :
      Term.CheckCertificate firstCode SetSort.set := by
        prove_term_check)
    (hMiddleCode :
      Term.CheckCertificate middleCode SetSort.set := by
        prove_term_check)
    (hLastCode :
      Term.CheckCertificate lastCode SetSort.set := by
        prove_term_check) :
    ⊢ₘ[godel_quotation_theory] ((((left_parenthesis_symbol_code_term ⌢ₘ firstCode) ⌢ₘ
          middleCode) ⌢ₘ lastCode) ⌢ₘ
        right_parenthesis_symbol_code_term) ≐ₘ
      standard_token_sequence ([logical_token .leftParenthesis] ++ firstTokens ++
          middleTokens ++ lastTokens ++
            [logical_token .rightParenthesis]) := by
  let leftParenthesis := left_parenthesis_symbol_code_term
  let rightParenthesis := right_parenthesis_symbol_code_term
  let firstStage := leftParenthesis ⌢ₘ firstCode
  let middleStage := firstStage ⌢ₘ middleCode
  let lastStage := middleStage ⌢ₘ lastCode
  have hLeftParenthesisCheck :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hRightParenthesisCheck :
      Term.CheckCertificate rightParenthesis SetSort.set := by
    prove_term_check
  have hFirstStageTerm :
      Term.CheckCertificate firstStage SetSort.set := by
    prove_term_check
  have hMiddleStageTerm :
      Term.CheckCertificate middleStage SetSort.set := by
    prove_term_check
  have hLastStageTerm :
      Term.CheckCertificate lastStage SetSort.set := by
    prove_term_check
  have hLeftParenthesis :=
    logical_symbol_code_eq_standard_token_sequence
      LogicalSymbolKind.leftParenthesis
  have hRightParenthesis :=
    logical_symbol_code_eq_standard_token_sequence
      LogicalSymbolKind.rightParenthesis
  have hFirstStage :
      ⊢ₘ[godel_quotation_theory]
        firstStage ≐ₘ
          standard_token_sequence ([logical_token .leftParenthesis] ++ firstTokens) := by
    simpa [firstStage, leftParenthesis] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis] firstTokens
        leftParenthesis firstCode
        hLeftParenthesis hFirst
  have hMiddleStage :
      ⊢ₘ[godel_quotation_theory]
        middleStage ≐ₘ
          standard_token_sequence (([logical_token .leftParenthesis] ++ firstTokens) ++
              middleTokens) := by
    simpa [middleStage] using
      gq_concatenation_eq_standard_token_sequence ([logical_token .leftParenthesis] ++ firstTokens)
        middleTokens firstStage middleCode
        hFirstStage hMiddle
  have hLastStage :
      ⊢ₘ[godel_quotation_theory]
        lastStage ≐ₘ
          standard_token_sequence ((([logical_token .leftParenthesis] ++ firstTokens) ++
                middleTokens) ++ lastTokens) := by
    simpa [lastStage] using
      gq_concatenation_eq_standard_token_sequence (([logical_token .leftParenthesis] ++ firstTokens) ++ middleTokens)
        lastTokens middleStage lastCode
        hMiddleStage hLast
  have hComplete :=
    gq_concatenation_eq_standard_token_sequence ((([logical_token .leftParenthesis] ++ firstTokens) ++
          middleTokens) ++ lastTokens)
      [logical_token .rightParenthesis]
      lastStage rightParenthesis
      hLastStage hRightParenthesis
  simpa [leftParenthesis, rightParenthesis,
    firstStage, middleStage, lastStage, List.append_assoc] using hComplete
/-- 否定的四段括号串在任意局部上下文中与外部 token 构造一致。 -/
theorem gq_negation_formula_string_eq_standard_token_sequence_of_context
    {Γ : Context signature}
    (bodyTokens : List Nat) (bodyCode : SetTerm) (hBody :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyCode ≐ₘ standard_token_sequence bodyTokens)
    (hBodyCode :
      Term.CheckCertificate bodyCode SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      negation_formula_string_term bodyCode ≐ₘ
        standard_token_sequence (negation_tokens bodyTokens) := by
  let leftParenthesis := left_parenthesis_symbol_code_term
  let negationSymbol := logical_symbol_code_term .negation
  let prefixCode := leftParenthesis ⌢ₘ negationSymbol
  let bodyStage := prefixCode ⌢ₘ bodyCode
  have hLeftParenthesis :
      Term.CheckCertificate leftParenthesis SetSort.set := by
    prove_term_check
  have hNegationSymbol :
      Term.CheckCertificate negationSymbol SetSort.set := by
    prove_term_check
  have hPrefixTerm :
      Term.CheckCertificate prefixCode SetSort.set := by
    prove_term_check
  have hBodyStageTerm :
      Term.CheckCertificate bodyStage SetSort.set := by
    prove_term_check
  have hPrefix :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence
            [logical_token .leftParenthesis,
              logical_token .negation] := by
    simpa [prefixCode, leftParenthesis, negationSymbol] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis]
        [logical_token .negation]
        leftParenthesis negationSymbol
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            logical_symbol_code_eq_standard_token_sequence
              .leftParenthesis)
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            logical_symbol_code_eq_standard_token_sequence
              .negation)
  have hBodyStage :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyStage ≐ₘ
          standard_token_sequence ([logical_token .leftParenthesis,
                logical_token .negation] ++ bodyTokens) := by
    simpa [bodyStage] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis,
          logical_token .negation]
        bodyTokens prefixCode bodyCode
        hPrefix hBody
  have hComplete :=
    gq_concatenation_eq_standard_token_sequence ([logical_token .leftParenthesis,
          logical_token .negation] ++ bodyTokens)
      [logical_token .rightParenthesis]
      bodyStage right_parenthesis_symbol_code_term
      hBodyStage
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          logical_symbol_code_eq_standard_token_sequence
            .rightParenthesis)
  simpa [negation_formula_string_term, Numbered.negation_tokens,
    bodyStage, prefixCode, leftParenthesis, negationSymbol,
    List.append_assoc] using hComplete
/-- 否定四段括号串的闭上下文接口。 -/
theorem negation_formula_string_eq_standard_token_sequence
    (bodyTokens : List Nat) (bodyCode : SetTerm) (hBody :
      ⊢ₘ[godel_quotation_theory]
        bodyCode ≐ₘ standard_token_sequence bodyTokens)
    (hBodyCode :
      Term.CheckCertificate bodyCode SetSort.set := by
        prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      negation_formula_string_term bodyCode ≐ₘ
        standard_token_sequence (negation_tokens bodyTokens) :=
  gq_negation_formula_string_eq_standard_token_sequence_of_context
    bodyTokens bodyCode hBody
/-- 隶属原子的对象字符串等于对应标准 token 序列。 -/
theorem membership_formula_string_eq_standard_token_sequence (leftTokens rightTokens : List Nat) (leftCode rightCode : SetTerm)
    (hLeft :
      ⊢ₘ[godel_quotation_theory]
        leftCode ≐ₘ standard_token_sequence leftTokens) (hRight :
      ⊢ₘ[godel_quotation_theory]
        rightCode ≐ₘ standard_token_sequence rightTokens)
    (hLeftCode :
      Term.CheckCertificate leftCode SetSort.set := by
        prove_term_check)
    (hRightCode :
      Term.CheckCertificate rightCode SetSort.set := by
        prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      membership_atomic_formula_code_term leftCode rightCode ≐ₘ
        standard_token_sequence (membership_tokens leftTokens rightTokens) := by
  simpa [membership_atomic_formula_code_term,
    binary_atomic_formula_code_term, Numbered.membership_tokens,
    List.append_assoc] using
    gq_bracketed_three_part_eq_standard_token_sequence
      leftTokens [membership_token] rightTokens
      leftCode membership_symbol_code_term rightCode
      hLeft membership_symbol_code_eq_standard_token_sequence hRight
/-- 等式原子的原始括号串等于对应标准 token 序列。 -/
theorem equality_formula_string_eq_standard_token_sequence (leftTokens rightTokens : List Nat) (leftCode rightCode : SetTerm)
    (hLeft :
      ⊢ₘ[godel_quotation_theory]
        leftCode ≐ₘ standard_token_sequence leftTokens) (hRight :
      ⊢ₘ[godel_quotation_theory]
        rightCode ≐ₘ standard_token_sequence rightTokens)
    (hLeftCode :
      Term.CheckCertificate leftCode SetSort.set := by
        prove_term_check)
    (hRightCode :
      Term.CheckCertificate rightCode SetSort.set := by
        prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      equality_atomic_formula_code_term leftCode rightCode ≐ₘ
        standard_token_sequence (equality_tokens leftTokens rightTokens) := by
  simpa [equality_atomic_formula_code_term,
    binary_atomic_formula_code_term, Numbered.equality_tokens,
    List.append_assoc] using
    gq_bracketed_three_part_eq_standard_token_sequence
      leftTokens [logical_token .equality] rightTokens
      leftCode equality_symbol_code_term rightCode
      hLeft (logical_symbol_code_eq_standard_token_sequence .equality)
      hRight
/-- 蕴含的原始括号串在任意局部上下文中等于对应标准 token 序列。 -/
theorem
    gq_implication_formula_string_eq_standard_token_sequence_of_context
    {Γ : Context signature}
    (leftTokens rightTokens : List Nat)
    (leftCode rightCode : SetTerm)
    (hLeft :
      Γ ⊢ₘ[godel_quotation_theory]
        leftCode ≐ₘ standard_token_sequence leftTokens)
    (hRight :
      Γ ⊢ₘ[godel_quotation_theory]
        rightCode ≐ₘ standard_token_sequence rightTokens)
    (hLeftCode :
      Term.CheckCertificate leftCode SetSort.set := by
        prove_term_check)
    (hRightCode :
      Term.CheckCertificate rightCode SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      implication_formula_string_term leftCode rightCode ≐ₘ
        standard_token_sequence (implication_tokens leftTokens rightTokens) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let implicationSymbol :=
    logical_symbol_code_term .implication
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let leftStage := leftParenthesis ⌢ₘ leftCode
  let prefixCode := leftStage ⌢ₘ implicationSymbol
  let bodyStage := prefixCode ⌢ₘ rightCode
  have hLeftParenthesis :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ
          standard_token_sequence
            [logical_token .leftParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [leftParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis
  have hImplicationSymbol :
      Γ ⊢ₘ[godel_quotation_theory]
        implicationSymbol ≐ₘ
          standard_token_sequence
            [logical_token .implication] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [implicationSymbol] using
          logical_symbol_code_eq_standard_token_sequence
            .implication
  have hRightParenthesis :
      Γ ⊢ₘ[godel_quotation_theory]
        rightParenthesis ≐ₘ
          standard_token_sequence
            [logical_token .rightParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [rightParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .rightParenthesis
  have hLeftStage :
      Γ ⊢ₘ[godel_quotation_theory]
        leftStage ≐ₘ
          standard_token_sequence
            ([logical_token .leftParenthesis] ++ leftTokens) := by
    simpa [leftStage] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis] leftTokens
        leftParenthesis leftCode
        hLeftParenthesis hLeft
  have hPrefix :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence
            (([logical_token .leftParenthesis] ++ leftTokens) ++
              [logical_token .implication]) := by
    simpa [prefixCode] using
      gq_concatenation_eq_standard_token_sequence
        ([logical_token .leftParenthesis] ++ leftTokens)
        [logical_token .implication]
        leftStage implicationSymbol
        hLeftStage hImplicationSymbol
  have hBody :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyStage ≐ₘ
          standard_token_sequence
            ((([logical_token .leftParenthesis] ++ leftTokens) ++
              [logical_token .implication]) ++ rightTokens) := by
    simpa [bodyStage] using
      gq_concatenation_eq_standard_token_sequence
        (([logical_token .leftParenthesis] ++ leftTokens) ++
          [logical_token .implication])
        rightTokens prefixCode rightCode
        hPrefix hRight
  have hComplete :=
    gq_concatenation_eq_standard_token_sequence
      ((([logical_token .leftParenthesis] ++ leftTokens) ++
        [logical_token .implication]) ++ rightTokens)
      [logical_token .rightParenthesis]
      bodyStage rightParenthesis
      hBody hRightParenthesis
  simpa [implication_formula_string_term,
    Numbered.implication_tokens, leftParenthesis,
    implicationSymbol, rightParenthesis,
    leftStage, prefixCode, bodyStage,
    List.append_assoc] using hComplete

/-- 蕴含原始括号串的闭上下文接口。 -/
theorem implication_formula_string_eq_standard_token_sequence
    (leftTokens rightTokens : List Nat)
    (leftCode rightCode : SetTerm)
    (hLeft :
      ⊢ₘ[godel_quotation_theory]
        leftCode ≐ₘ standard_token_sequence leftTokens)
    (hRight :
      ⊢ₘ[godel_quotation_theory]
        rightCode ≐ₘ standard_token_sequence rightTokens)
    (hLeftCode :
      Term.CheckCertificate leftCode SetSort.set := by
        prove_term_check)
    (hRightCode :
      Term.CheckCertificate rightCode SetSort.set := by
        prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      implication_formula_string_term leftCode rightCode ≐ₘ
        standard_token_sequence
          (implication_tokens leftTokens rightTokens) :=
  gq_implication_formula_string_eq_standard_token_sequence_of_context
    leftTokens rightTokens leftCode rightCode
    hLeft hRight

/-- 全称原始括号串在任意局部上下文中等于对应标准 token 序列。 -/
theorem
    gq_universal_formula_string_eq_standard_token_sequence_of_context
    {Γ : Context signature}
    (name : Nat) (bodyTokens : List Nat)
    (bodyCode : SetTerm)
    (hBody :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyCode ≐ₘ standard_token_sequence bodyTokens)
    (hBodyCode :
      Term.CheckCertificate bodyCode SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      universal_formula_string_term
          (named_variable_code name) bodyCode ≐ₘ
        standard_token_sequence
          (universal_tokens name bodyTokens) := by
  let leftParenthesis :=
    logical_symbol_code_term .leftParenthesis
  let universalSymbol :=
    logical_symbol_code_term .universal
  let rightParenthesis :=
    logical_symbol_code_term .rightParenthesis
  let boundVariable := named_variable_code name
  let fixedPrefix :=
    leftParenthesis ⌢ₘ universalSymbol
  let prefixVariable :=
    fixedPrefix ⌢ₘ boundVariable
  let bodyStage := prefixVariable ⌢ₘ bodyCode
  have hLeftParenthesis :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ
          standard_token_sequence
            [logical_token .leftParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [leftParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis
  have hUniversalSymbol :
      Γ ⊢ₘ[godel_quotation_theory]
        universalSymbol ≐ₘ
          standard_token_sequence
            [logical_token .universal] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [universalSymbol] using
          logical_symbol_code_eq_standard_token_sequence
            .universal
  have hBoundVariable :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ≐ₘ
          standard_token_sequence
            [variable_token name] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [boundVariable] using
          named_variable_code_eq_standard_token_sequence name
  have hRightParenthesis :
      Γ ⊢ₘ[godel_quotation_theory]
        rightParenthesis ≐ₘ
          standard_token_sequence
            [logical_token .rightParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [rightParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .rightParenthesis
  have hFixedPrefix :
      Γ ⊢ₘ[godel_quotation_theory]
        fixedPrefix ≐ₘ
          standard_token_sequence
            [logical_token .leftParenthesis,
              logical_token .universal] := by
    simpa [fixedPrefix] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis]
        [logical_token .universal]
        leftParenthesis universalSymbol
        hLeftParenthesis hUniversalSymbol
  have hPrefixVariable :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixVariable ≐ₘ
          standard_token_sequence
            ([logical_token .leftParenthesis,
              logical_token .universal] ++
                [variable_token name]) := by
    simpa [prefixVariable] using
      gq_concatenation_eq_standard_token_sequence
        [logical_token .leftParenthesis,
          logical_token .universal]
        [variable_token name]
        fixedPrefix boundVariable
        hFixedPrefix hBoundVariable
  have hBodyStage :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyStage ≐ₘ
          standard_token_sequence
            (([logical_token .leftParenthesis,
              logical_token .universal] ++
                [variable_token name]) ++ bodyTokens) := by
    simpa [bodyStage] using
      gq_concatenation_eq_standard_token_sequence
        ([logical_token .leftParenthesis,
          logical_token .universal] ++
            [variable_token name])
        bodyTokens prefixVariable bodyCode
        hPrefixVariable hBody
  have hComplete :=
    gq_concatenation_eq_standard_token_sequence
      (([logical_token .leftParenthesis,
        logical_token .universal] ++
          [variable_token name]) ++ bodyTokens)
      [logical_token .rightParenthesis]
      bodyStage rightParenthesis
      hBodyStage hRightParenthesis
  simpa [universal_formula_string_term,
    Numbered.universal_tokens, leftParenthesis,
    universalSymbol, rightParenthesis,
    boundVariable, fixedPrefix, prefixVariable,
    bodyStage, List.append_assoc] using hComplete

/-- 蕴含构造码在任意局部上下文中展开为其原始括号串。 -/
theorem
    gq_implication_formula_code_eq_string_of_context
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft :
      Term.CheckCertificate left SetSort.set := by
        prove_term_check)
    (hRight :
      Term.CheckCertificate right SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      imp_codeₘ(left, right) ≐ₘ
        implication_formula_string_term left right := by
  let code := imp_codeₘ(left, right)
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hDefinition :
      Γ ⊢ₘ[godel_quotation_theory]
        implication_formula_code_definition_instance
          left right code := by
    exact
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_formula_constructor <|
          implication_formula_code_definition_instance_derives
            left right code
            hLeft.admissible hRight.admissible
            hCode.admissible
  have hReflexive :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ imp_codeₘ(left, right) := by
    simpa [code] using
      FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code
  simpa [code,
    implication_formula_code_definition_instance] using
    FirstOrder.Derives.iffElimRight
      hDefinition hReflexive
/-- 全称量化的原始括号串等于对应标准 token 序列。 -/
theorem universal_formula_string_eq_standard_token_sequence (name : Nat) (bodyTokens : List Nat) (bodyCode : SetTerm)
    (hBody :
      ⊢ₘ[godel_quotation_theory]
        bodyCode ≐ₘ standard_token_sequence bodyTokens)
    (hBodyCode :
      Term.CheckCertificate bodyCode SetSort.set := by
        prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      universal_formula_string_term (named_variable_code name) bodyCode ≐ₘ
        standard_token_sequence (universal_tokens name bodyTokens) := by
  simpa [universal_formula_string_term, Numbered.universal_tokens,
    List.append_assoc] using
    gq_bracketed_three_part_eq_standard_token_sequence
      [logical_token .universal] [variable_token name] bodyTokens (logical_symbol_code_term .universal) (named_variable_code name) bodyCode
      (logical_symbol_code_eq_standard_token_sequence .universal)
      (named_variable_code_eq_standard_token_sequence name)
      hBody
/-- 等式公式构造运算的 quotation 值与标准 token 构造一致。 -/
theorem equality_formula_code_eq_standard_token_sequence (leftTokens rightTokens : List Nat) (leftCode rightCode : SetTerm)
    (hLeftTerm :
      ⊢ₘ[godel_quotation_theory] term_codeₘ(leftCode)) (hRightTerm :
      ⊢ₘ[godel_quotation_theory] term_codeₘ(rightCode)) (hLeft :
      ⊢ₘ[godel_quotation_theory]
        leftCode ≐ₘ standard_token_sequence leftTokens) (hRight :
      ⊢ₘ[godel_quotation_theory]
        rightCode ≐ₘ standard_token_sequence rightTokens)
    (hLeftCode :
      Term.CheckCertificate leftCode SetSort.set := by
        prove_term_check)
    (hRightCode :
      Term.CheckCertificate rightCode SetSort.set := by
        prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      eq_codeₘ(leftCode, rightCode) ≐ₘ
        standard_token_sequence (equality_tokens leftTokens rightTokens) := by
  let code := eq_codeₘ(leftCode, rightCode)
  let rawCode := equality_atomic_formula_code_term leftCode rightCode
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hDefinition :=
    gq_weaken_formula_constructor <|
      equality_formula_code_definition_instance_derives
        leftCode rightCode code
          hLeftCode.admissible hRightCode.admissible
          hCode.admissible
  have hContract := FirstOrder.Derives.impElim hDefinition (FirstOrder.Derives.conjIntro hLeftTerm hRightTerm)
  have hReflexive :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ eq_codeₘ(leftCode, rightCode) := by
    simpa [code] using FirstOrder.Derives.eq_refl_m code
  have hCodeRaw :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    simpa [code, rawCode,
      equality_formula_code_definition_instance] using
      FirstOrder.Derives.iffElimRight hContract hReflexive
  have hRawStandard :
      ⊢ₘ[godel_quotation_theory]
        rawCode ≐ₘ
          standard_token_sequence (equality_tokens leftTokens rightTokens) := by
    simpa [rawCode] using
      equality_formula_string_eq_standard_token_sequence
        leftTokens rightTokens leftCode rightCode
        hLeft hRight
  exact Metatheory.Derives.equality_trans
    hCodeRaw hRawStandard
/-- 否定公式构造运算在任意局部上下文中的 quotation 值。 -/
theorem gq_negation_formula_code_eq_standard_token_sequence_of_context
    {Γ : Context signature}
    (bodyTokens : List Nat) (bodyCode : SetTerm) (hBody :
      Γ ⊢ₘ[godel_quotation_theory]
        bodyCode ≐ₘ standard_token_sequence bodyTokens)
    (hBodyCode :
      Term.CheckCertificate bodyCode SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      neg_codeₘ(bodyCode) ≐ₘ
        standard_token_sequence (negation_tokens bodyTokens) := by
  let code := neg_codeₘ(bodyCode)
  let rawCode := negation_formula_string_term bodyCode
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hDefinition :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_formula_constructor <|
          negation_formula_code_definition_instance_derives
            bodyCode code hBodyCode.admissible hCode.admissible
  have hReflexive :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ neg_codeₘ(bodyCode) := by
    exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [code] using FirstOrder.Derives.eq_refl_m code
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    simpa [code, rawCode,
      negation_formula_code_definition_instance] using
      FirstOrder.Derives.iffElimRight hDefinition hReflexive
  have hRawStandard :
      Γ ⊢ₘ[godel_quotation_theory]
        rawCode ≐ₘ
          standard_token_sequence (negation_tokens bodyTokens) := by
    simpa [rawCode] using
      gq_negation_formula_string_eq_standard_token_sequence_of_context
        bodyTokens bodyCode hBody
  exact Metatheory.Derives.equality_trans
    hCodeRaw hRawStandard
/-- 否定公式构造 quotation 值的闭上下文接口。 -/
theorem negation_formula_code_eq_standard_token_sequence
    (bodyTokens : List Nat) (bodyCode : SetTerm) (hBody :
      ⊢ₘ[godel_quotation_theory]
        bodyCode ≐ₘ standard_token_sequence bodyTokens)
    (hBodyCode :
      Term.CheckCertificate bodyCode SetSort.set := by
        prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      neg_codeₘ(bodyCode) ≐ₘ
        standard_token_sequence (negation_tokens bodyTokens) :=
  gq_negation_formula_code_eq_standard_token_sequence_of_context
    bodyTokens bodyCode hBody
/-- 蕴含公式构造运算的 quotation 值与标准 token 构造一致。 -/
theorem implication_formula_code_eq_standard_token_sequence (leftTokens rightTokens : List Nat) (leftCode rightCode : SetTerm)
    (hLeft :
      ⊢ₘ[godel_quotation_theory]
        leftCode ≐ₘ standard_token_sequence leftTokens) (hRight :
      ⊢ₘ[godel_quotation_theory]
        rightCode ≐ₘ standard_token_sequence rightTokens)
    (hLeftCode :
      Term.CheckCertificate leftCode SetSort.set := by
        prove_term_check)
    (hRightCode :
      Term.CheckCertificate rightCode SetSort.set := by
        prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      imp_codeₘ(leftCode, rightCode) ≐ₘ
        standard_token_sequence (implication_tokens leftTokens rightTokens) := by
  let code := imp_codeₘ(leftCode, rightCode)
  let rawCode := implication_formula_string_term leftCode rightCode
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hDefinition :=
    gq_weaken_formula_constructor <|
      implication_formula_code_definition_instance_derives
        leftCode rightCode code
          hLeftCode.admissible hRightCode.admissible
          hCode.admissible
  have hReflexive :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ imp_codeₘ(leftCode, rightCode) := by
    simpa [code] using FirstOrder.Derives.eq_refl_m code
  have hCodeRaw :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    simpa [code, rawCode,
      implication_formula_code_definition_instance] using
      FirstOrder.Derives.iffElimRight hDefinition hReflexive
  have hRawStandard :
      ⊢ₘ[godel_quotation_theory]
        rawCode ≐ₘ
          standard_token_sequence (implication_tokens leftTokens rightTokens) := by
    simpa [rawCode] using
      implication_formula_string_eq_standard_token_sequence
        leftTokens rightTokens leftCode rightCode
        hLeft hRight
  exact Metatheory.Derives.equality_trans
    hCodeRaw hRawStandard
/-- 全称公式构造运算的 quotation 值与标准 token 构造一致。 -/
theorem universal_formula_code_eq_standard_token_sequence (name : Nat) (bodyTokens : List Nat) (bodyCode : SetTerm)
    (hBody :
      ⊢ₘ[godel_quotation_theory]
        bodyCode ≐ₘ standard_token_sequence bodyTokens)
    (hBodyCode :
      Term.CheckCertificate bodyCode SetSort.set := by
        prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      forall_codeₘ(named_variable_code name, bodyCode) ≐ₘ
        standard_token_sequence (universal_tokens name bodyTokens) := by
  let variableCode := named_variable_code name
  let code := forall_codeₘ(variableCode, bodyCode)
  let rawCode := universal_formula_string_term variableCode bodyCode
  have hVariableCode :
      Term.CheckCertificate variableCode SetSort.set := by
    prove_term_check
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hDefinition :=
    gq_weaken_formula_constructor <|
      universal_formula_code_definition_instance_derives
        variableCode bodyCode code
        hVariableCode.admissible hBodyCode.admissible
          hCode.admissible
  have hReflexive :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ forall_codeₘ(variableCode, bodyCode) := by
    simpa [code] using FirstOrder.Derives.eq_refl_m code
  have hCodeRaw :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    simpa [code, rawCode,
      universal_formula_code_definition_instance] using
      FirstOrder.Derives.iffElimRight hDefinition hReflexive
  have hRawStandard :
      ⊢ₘ[godel_quotation_theory]
        rawCode ≐ₘ
          standard_token_sequence (universal_tokens name bodyTokens) := by
    simpa [rawCode, variableCode] using
      universal_formula_string_eq_standard_token_sequence
        name bodyTokens bodyCode hBody
  exact Metatheory.Derives.equality_trans
    hCodeRaw hRawStandard
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
