import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNumbering
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TokenReflection

/-!
# FormalSystem 规范 token 的构造性反解码

本模块只处理当前有限 FormalSystem 签名。解码器先恢复规范变量、函数和关系符号，
再用公共可计算良构检查过滤 arity、sort 与 locally nameless scope。成功结果因此
直接携带可供 checked proof replay 使用的对象公式。

这里不枚举公式全集，也不使用选择公理；所有搜索都限制在输入 token 或有限符号表内。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-! ## 有限编码查找 -/

/-- 在有限列表中查找编码等于目标值的第一个元素。 -/
def fs_find_encoded
    {α : Type}
    (encode : α → Nat) (target : Nat) :
    List α → Option α
  | [] =>
      none
  | head :: tail =>
      if encode head = target then
        some head
      else
        fs_find_encoded encode target tail

/-- 单射编码下，列表中的元素可由其编码精确恢复。 -/
theorem fs_find_encoded_encode_of_mem
    {α : Type}
    {encode : α → Nat}
    (hInjective : Function.Injective encode)
    {item : α} {items : List α}
    (hItem : item ∈ items) :
    fs_find_encoded encode (encode item) items =
      some item := by
  induction items with
  | nil =>
      cases hItem
  | cons head tail ih =>
      rcases List.mem_cons.mp hItem with rfl | hTail
      · simp [fs_find_encoded]
      · by_cases hCode :
          encode head = encode item
        · have hHead : head = item :=
            hInjective hCode
          subst head
          simp [fs_find_encoded]
        · simp [fs_find_encoded, hCode, ih hTail]

/-- 若有限表中没有元素编码为目标值，查找结果为空。 -/
theorem fs_find_encoded_eq_none
    {α : Type}
    {encode : α → Nat}
    {target : Nat} {items : List α}
    (hMissing :
      ∀ item, item ∈ items →
        encode item ≠ target) :
    fs_find_encoded encode target items =
      none := by
  induction items with
  | nil =>
      rfl
  | cons head tail ih =>
      have hHead :
          encode head ≠ target :=
        hMissing head (by simp)
      have hTail :
          ∀ item, item ∈ tail →
            encode item ≠ target := by
        intro item hItem
        exact hMissing item (by simp [hItem])
      simp [fs_find_encoded, hHead, ih hTail]

/-- 有限编码查找成功时，返回项的编码就是目标值。 -/
theorem fs_find_encoded_value_of_some
    {α : Type}
    {encode : α → Nat}
    {target : Nat} :
    ∀ {items : List α} {item : α},
      fs_find_encoded encode target items = some item →
        encode item = target
  | .nil, item, hFind => by
      simp [fs_find_encoded] at hFind
  | .cons head tail, item, hFind => by
      by_cases hHead : encode head = target
      · simp [fs_find_encoded, hHead] at hFind
        subst item
        exact hHead
      · simp [fs_find_encoded, hHead] at hFind
        exact fs_find_encoded_value_of_some hFind

/-- `Option.mapM` 成功时，结果列表与输入列表等长。 -/
theorem fs_option_mapM_length
    {α β : Type}
    {transform : α → Option β}
    {items : List α} {results : List β}
    (hMap :
      items.mapM transform = some results) :
    results.length = items.length := by
  induction items generalizing results with
  | nil =>
      simpa using Option.some.inj hMap.symm
  | cons head tail ih =>
      cases hHead : transform head with
      | none =>
          simp [hHead] at hMap
      | some headResult =>
          cases hTail :
              tail.mapM transform with
          | none =>
              simp [hHead, hTail] at hMap
          | some tailResults =>
              simp [List.mapM_cons, hHead,
                hTail] at hMap
              subst results
              simp [ih hTail]

/-- 每个输入都给出成功结果时，`Option` 列表遍历整体成功。 -/
theorem fs_option_mapM_exists_of_forall_some
    {α β : Type}
    (transform : α → Option β)
    (items : List α)
    (hTransform :
      ∀ item, item ∈ items →
        ∃ result, transform item = some result) :
    ∃ results,
      items.mapM transform = some results := by
  induction items with
  | nil =>
      exact ⟨([] : List β), rfl⟩
  | cons head tail ih =>
      rcases hTransform head (by simp) with
        ⟨headResult, hHead⟩
      rcases ih (fun item hItem =>
          hTransform item (by simp [hItem])) with
        ⟨tailResults, hTail⟩
      exact
        ⟨headResult :: tailResults, by
          simp [List.mapM_cons, hHead, hTail]⟩

/-- `Option` 列表遍历失败时，输入中存在一个具体失败项。 -/
theorem fs_option_mapM_none_exists
    {α β : Type}
    (transform : α → Option β) :
    ∀ {items : List α},
      items.mapM transform = none →
        ∃ item,
          item ∈ items ∧ transform item = none
  | .nil, hMap => by
      simp at hMap
  | .cons head tail, hMap => by
      cases hHead : transform head with
      | none =>
          exact ⟨head, by simp, hHead⟩
      | some headResult =>
          cases hTail :
              tail.mapM transform with
          | none =>
              rcases
                  fs_option_mapM_none_exists
                    transform hTail with
                ⟨item, hItem, hFailure⟩
              exact
                ⟨item,
                  List.mem_cons_of_mem head hItem,
                  hFailure⟩
          | some tailResults =>
              simp [List.mapM_cons, hHead,
                hTail] at hMap

/-- FormalSystem 的完整函数符号表。 -/
def fs_function_symbols : List FunctionSymbol :=
  [ .emptySet,
    .powerSet,
    .unorderedPair,
    .singleton,
    .orderedPair,
    .leftProjection,
    .rightProjection,
    .orderedPairReverse,
    .cartesianProduct,
    .domain,
    .range,
    .relationConverse,
    .relationComposition,
    .application,
    .union,
    .binaryUnion,
    .successor,
    .intersection,
    .binaryIntersection,
    .identity,
    .mappingCollection,
    .membershipRelation,
    .image,
    .restriction,
    .minimum,
    .maximum,
    .initialSegment,
    .relationRestriction,
    .wellOrderComparisonMap,
    .orderSum,
    .orderProduct,
    .mappingProduct,
    .minimumDifference,
    .indexOrder,
    .powerSetBijection,
    .symmetricDifference,
    .inductiveCore,
    .omega,
    .naturalOrderType,
    .naturalSubsetType,
    .naturalAddition,
    .naturalMultiplication,
    .naturalExponentiation,
    .finiteSequenceSpace,
    .finiteSequenceConcatenation,
    .nonemptyFiniteSequenceSpace,
    .finiteSequenceFlatten,
    .recursiveSequenceSpace,
    .omegaRecursiveSequence,
    .naturalDifference,
    .godelPairing,
    .transitiveClosure,
    .finiteHierarchy,
    .finiteUniverse,
    .finiteSubsetCollection,
    .logicalSymbolSet,
    .membershipSymbolSet,
    .variableSymbolSet,
    .constantSymbolSet,
    .codedFunctionSymbolSet,
    .codedPredicateSymbolSet,
    .termCodeSet,
    .termSequenceSet,
    .atomicFormulaCodeSet,
    .formulaCodeSet,
    .equalityFormulaCode,
    .predicateFormulaCode,
    .negationFormulaCode,
    .implicationFormulaCode,
    .universalFormulaCode,
    .variableCode,
    .constantCode,
    .codedFunctionSymbolCode,
    .codedPredicateSymbolCode,
    .codeSubstitution,
    .variableCollection,
    .freeOccurrencePositions,
    .implicationDistributionAxiomSet,
    .selfImplicationAxiomSet,
    .weakeningAxiomSet,
    .contradictionAxiomSet,
    .classicalAxiomSet,
    .explosionAxiomSet,
    .caseAnalysisAxiomSet,
    .specializationAxiomSet,
    .quantifierDistributionAxiomSet,
    .vacuousQuantifierAxiomSet,
    .equalitySubstitutionAxiomSet,
    .equalityReflexivityAxiomSet,
    .baseLogicalAxiomSet,
    .logicalAxiomSet,
    .relatedNonlogicalSymbolSet,
    .relatedTermSet,
    .relatedFormulaSet,
    .relatedFormulaStageSet,
    .canonicalNameCode,
    .numeralNameCode,
    .zfcAxiomCodeSet,
    .completeAxiomCodeSet ]

theorem fs_function_symbols_complete
    (symbol : FunctionSymbol) :
    symbol ∈ fs_function_symbols := by
  cases symbol <;> simp [fs_function_symbols]

/-- FormalSystem 的完整关系符号表。 -/
def fs_relation_symbols : List RelationSymbol :=
  [ .membership,
    .subset,
    .properSubset,
    .isOrderedPair,
    .isRelation,
    .isEquivalenceRelation,
    .isFunction,
    .isMapping,
    .isInjective,
    .isSurjective,
    .isBijection,
    .isTransitiveSet,
    .isLinearOrder,
    .isOrderIsomorphism,
    .isOrderIsomorphic,
    .isOrderEmbedding,
    .isOrderEmbeddable,
    .isNaturalDiscreteLinearOrder,
    .isWellOrder,
    .isOrdinal,
    .isNaturalNumber,
    .isFinite,
    .isEquinumerous,
    .cardinalityLeq,
    .cardinalityStrictLess,
    .isDedekindFinite,
    .isInductiveSet,
    .isUnboundedSubset,
    .isBoundedSubset,
    .isInfinite,
    .isCountable,
    .isUncountable,
    .isCountablyInfinite,
    .isHereditarilyFinite,
    .omegaPairLess,
    .isTermCode,
    .isAtomicFormulaCode,
    .isFormulaCode,
    .quantifierOccurs,
    .boundOccurrence,
    .freeOccurrence,
    .isSubstitutable,
    .isLogicalAxiomCode,
    .modusPonens,
    .isStructure,
    .isTermEvaluation,
    .termValue,
    .atomicSatisfaction,
    .formulaSatisfactionAtStage,
    .formulaSatisfaction,
    .isTruth,
    .isModel,
    .logicalConsequence,
    .isTheorem ]

theorem fs_relation_symbols_complete
    (symbol : RelationSymbol) :
    symbol ∈ fs_relation_symbols := by
  cases symbol <;> simp [fs_relation_symbols]

/-! ## 规范变量反解码 -/

/-- 从变量 token 中有限搜索其规范名字。 -/
def fs_variable_name_decode
    (token : Nat) : Option Nat :=
  fs_find_encoded Numbered.variable_token token
    (List.range (token + 1))

/-- 变量名字严格落在以其 token 后继为界的有限搜索区间内。 -/
theorem fs_name_lt_variable_token_succ
    (name : Nat) :
    name < Numbered.variable_token name + 1 :=
  Numbered.variable_name_lt_token_succ name

@[simp]
theorem fs_variable_name_decode_encode
    (name : Nat) :
    fs_variable_name_decode
        (Numbered.variable_token name) =
      some name := by
  unfold fs_variable_name_decode
  apply fs_find_encoded_encode_of_mem
    token_reflection_variable_token_injective
  exact List.mem_range.mpr
    (fs_name_lt_variable_token_succ name)

/-- 变量名字解码成功时，输入 token 正是该名字的规范变量 token。 -/
theorem fs_variable_name_decode_value_of_some
    {token name : Nat}
    (hDecode :
      fs_variable_name_decode token = some name) :
    Numbered.variable_token name = token := by
  exact fs_find_encoded_value_of_some <| by
    simpa [fs_variable_name_decode] using hDecode

/--
规范名字的偶数分支恢复自由变量；奇数分支在当前绝对深度内恢复 de Bruijn index。
-/
def fs_variable_of_name
    (depth name : Nat) :
    Option (Var signature) :=
  if name % 2 = 0 then
    let id := name / 2
    if free_name id = name then
      some (.fvar SetSort.set id)
    else
      none
  else
    let prior := name / 2
    if prior < depth then
      some (.bvar SetSort.set
        (depth - prior - 1))
    else
      none

/-- 变量 token 到当前规范 scope 中变量的完整解码。 -/
def fs_variable_decode
    (depth token : Nat) :
    Option (Var signature) := do
  let name ← fs_variable_name_decode token
  fs_variable_of_name depth name

@[simp]
theorem fs_variable_of_name_free
    (depth id : Nat) :
    fs_variable_of_name depth (free_name id) =
      some (.fvar SetSort.set id) := by
  simp [fs_variable_of_name, free_name]

@[simp]
theorem fs_variable_decode_free
    (depth id : Nat) :
    fs_variable_decode depth
        (Numbered.variable_token (free_name id)) =
      some (.fvar SetSort.set id) := by
  simp [fs_variable_decode]

@[simp]
theorem fs_variable_of_name_bound
    (depth index : Nat)
    (hIndex : index < depth) :
    fs_variable_of_name depth
        (bound_name (depth - index - 1)) =
      some (.bvar SetSort.set index) := by
  have hPrior :
      depth - index - 1 < depth := by
    omega
  simp [fs_variable_of_name, bound_name,
    Nat.add_mod]
  omega

@[simp]
theorem fs_variable_decode_bound
    (depth index : Nat)
    (hIndex : index < depth) :
    fs_variable_decode depth
        (Numbered.variable_token
          (bound_name (depth - index - 1))) =
      some (.bvar SetSort.set index) := by
  simp [fs_variable_decode,
    fs_variable_of_name_bound depth index hIndex]

@[simp]
theorem fs_variable_name_decode_constant
    (index : Nat) :
    fs_variable_name_decode
        (Numbered.constant_token index) =
      none := by
  unfold fs_variable_name_decode
  apply fs_find_encoded_eq_none
  intro name hName
  exact
    (token_reflection_constant_token_ne_variable_token
      index name).symm

@[simp]
theorem fs_variable_decode_constant
    (depth index : Nat) :
    fs_variable_decode depth
        (Numbered.constant_token index) =
      none := by
  simp [fs_variable_decode]

/-! ## 项与公式树解码 -/

/-- 给定参数个数时，正元函数 token 对函数符号保持单射。 -/
private theorem fs_function_head_injective
    (arityPredecessor : Nat) :
    Function.Injective
      (fun symbol : FunctionSymbol =>
        Numbered.function_token
          arityPredecessor symbol.ctorIdx) := by
  intro left right hCode
  have hIndex :=
    (token_reflection_function_token_injective
      hCode).2
  exact
    fs_quotation_numbering.function_number_injective
      hIndex

/-- 常元 token 对 FormalSystem 函数符号保持单射。 -/
private theorem fs_constant_head_injective :
    Function.Injective
      (fun symbol : FunctionSymbol =>
        Numbered.constant_token symbol.ctorIdx) := by
  intro left right hCode
  exact
    fs_quotation_numbering.function_number_injective
      (token_reflection_constant_token_injective
        hCode)

/-- 给定参数个数时，谓词 token 对关系符号保持单射。 -/
private theorem fs_predicate_head_injective
    (arityPredecessor : Nat) :
    Function.Injective
      (fun symbol : RelationSymbol =>
        Numbered.predicate_token
          arityPredecessor symbol.ctorIdx) := by
  intro left right hCode
  have hIndex :=
    (token_reflection_predicate_token_injective
      hCode).2
  exact
    fs_quotation_numbering.relation_number_injective
      hIndex

@[simp]
theorem fs_constant_symbol_lookup
    (symbol : FunctionSymbol) :
    fs_find_encoded
        (fun candidate : FunctionSymbol =>
          Numbered.constant_token
            candidate.ctorIdx)
        (Numbered.constant_token symbol.ctorIdx)
        fs_function_symbols =
      some symbol := by
  exact fs_find_encoded_encode_of_mem
    fs_constant_head_injective
    (fs_function_symbols_complete symbol)

@[simp]
theorem fs_function_symbol_lookup
    (arityPredecessor : Nat)
    (symbol : FunctionSymbol) :
    fs_find_encoded
        (fun candidate : FunctionSymbol =>
          Numbered.function_token
            arityPredecessor candidate.ctorIdx)
        (Numbered.function_token
          arityPredecessor symbol.ctorIdx)
        fs_function_symbols =
      some symbol := by
  exact fs_find_encoded_encode_of_mem
    (fs_function_head_injective
      arityPredecessor)
    (fs_function_symbols_complete symbol)

@[simp]
theorem fs_predicate_symbol_lookup
    (arityPredecessor : Nat)
    (symbol : RelationSymbol) :
    fs_find_encoded
        (fun candidate : RelationSymbol =>
          Numbered.predicate_token
            arityPredecessor candidate.ctorIdx)
        (Numbered.predicate_token
          arityPredecessor symbol.ctorIdx)
        fs_relation_symbols =
      some symbol := by
  exact fs_find_encoded_encode_of_mem
    (fs_predicate_head_injective
      arityPredecessor)
    (fs_relation_symbols_complete symbol)

/-- 原始项树到 FormalSystem 项的规范解码。 -/
def fs_term_token_tree_decode
    (depth : Nat) :
    RawTermTokenTree → Option SetTerm
  | .atom token =>
      match fs_variable_decode depth token with
      | some decodedVariable =>
          some (.var decodedVariable)
      | none =>
          match fs_find_encoded
              (fun symbol : FunctionSymbol =>
                Numbered.constant_token symbol.ctorIdx)
              token fs_function_symbols with
          | none =>
              none
          | some symbol =>
              if signature.funcDomain symbol = [] then
                some (.app symbol [])
              else
                none
  | .application head arguments =>
      if arguments = [] then
        none
      else do
        let symbol ←
          fs_find_encoded
            (fun candidate : FunctionSymbol =>
              Numbered.function_token
                (arguments.length - 1)
                candidate.ctorIdx)
            head fs_function_symbols
        let decoded ←
          arguments.mapM
            (fs_term_token_tree_decode depth)
        if Term.check_args_wellSorted decoded
            (signature.funcDomain symbol) then
          some (.app symbol decoded)
        else
          none
termination_by tree => tree

/-! ## 规范项 quotation 的 checked 回放 -/

mutual
  /--
  在规范偶/奇变量环境中，良构且 scope 正确的项由其 quotation 树精确恢复。
  -/
  theorem fs_term_token_tree_decode_quote
      (depth : Nat) :
      ∀ {term : SetTerm}
          {tree : RawTermTokenTree},
        TermWellSorted term SetSort.set →
        TermScoped
            (Numbered.scope_of_names
              (canonical_bound_names depth))
            term →
        quote_term_token_tree_with?
            free_name
            (canonical_bound_names depth)
            term =
          some tree →
        fs_term_token_tree_decode depth tree =
          some term
    | .var (.bvar sort index), tree,
        hWellSorted, hScoped, hQuote => by
        cases hWellSorted
        cases hScoped with
        | bvar hIndex =>
            have hIndexDepth :
                index < depth := by
              simpa [Numbered.scope_of_names,
                canonical_bound_names_length]
                using hIndex
            have hName :=
              canonical_bound_names_getElem?
                depth index hIndexDepth
            simp [quote_term_token_tree_with?,
              hName] at hQuote
            subst tree
            simp [fs_term_token_tree_decode,
              fs_variable_decode_bound
                depth index hIndexDepth]
    | .var (.fvar sort id), tree,
        hWellSorted, hScoped, hQuote => by
        cases hWellSorted
        simp [quote_term_token_tree_with?] at hQuote
        subst tree
        simp [fs_term_token_tree_decode,
          fs_variable_decode_free]
    | .app function arguments, tree,
        hWellSorted, hScoped, hQuote => by
        cases hWellSorted with
        | app _ hArguments =>
            cases hScoped with
            | app _ _ hArgumentsScoped =>
                cases hTrees :
                    arguments.mapM
                      (quote_term_token_tree_with?
                        free_name
                        (canonical_bound_names depth)) with
                | none =>
                    simp [quote_term_token_tree_with?,
                      hTrees] at hQuote
                | some trees =>
                    have hDecoded :=
                      fs_term_token_trees_decode_quote
                        depth hArguments
                        hArgumentsScoped hTrees
                    cases trees with
                    | nil =>
                        simp [quote_term_token_tree_with?,
                          hTrees] at hQuote
                        subst tree
                        have hArgumentsNil :
                            arguments = [] := by
                          exact
                            (Option.some.inj
                              hDecoded).symm
                        subst arguments
                        have hDomain :
                            signature.funcDomain
                                function =
                              [] := by
                          apply
                            List.eq_nil_of_length_eq_zero
                          simpa using
                            (Numbered.args_well_sorted_length_eq
                              hArguments).symm
                        simp [fs_term_token_tree_decode,
                          hDomain]
                    | cons first rest =>
                        simp [quote_term_token_tree_with?,
                          hTrees] at hQuote
                        subst tree
                        have hLength :
                            (first :: rest).length =
                              arguments.length :=
                          fs_option_mapM_length hTrees
                        simp [fs_term_token_tree_decode,
                          hLength, hDecoded,
                          Term.check_args_wellSorted_complete
                            hArguments]
  termination_by term => sizeOf term

  /--
  参数列的规范 quotation 逐项回放；该接口保留原始逐位置 sort 证书。
  -/
  theorem fs_term_token_trees_decode_quote
      (depth : Nat) :
      ∀ {terms : List SetTerm}
          {sorts : List SetSort}
          {trees : List RawTermTokenTree},
        ArgsWellSorted terms sorts →
        (∀ term, term ∈ terms →
          TermScoped
            (Numbered.scope_of_names
              (canonical_bound_names depth))
            term) →
        terms.mapM
            (quote_term_token_tree_with?
              free_name
              (canonical_bound_names depth)) =
          some trees →
        trees.mapM
            (fs_term_token_tree_decode depth) =
          some terms
    | .nil, sorts, trees,
        hWellSorted, hScoped, hQuote => by
        cases hWellSorted
        have hTrees : trees = [] := by
          simpa using Option.some.inj hQuote.symm
        subst trees
        rfl
    | .cons head tail, sorts, trees,
        hWellSorted, hScoped, hQuote => by
        cases hWellSorted with
        | cons hHeadWellSorted
            hTailWellSorted =>
            cases hHeadQuote :
                quote_term_token_tree_with?
                  free_name
                  (canonical_bound_names depth)
                  head with
            | none =>
                simp [hHeadQuote] at hQuote
            | some headTree =>
                cases hTailQuote :
                    tail.mapM
                      (quote_term_token_tree_with?
                        free_name
                        (canonical_bound_names depth)) with
                | none =>
                    simp [hHeadQuote,
                      hTailQuote] at hQuote
                | some tailTrees =>
                    simp [List.mapM_cons,
                      hHeadQuote, hTailQuote] at hQuote
                    subst trees
                    have hHeadDecoded :=
                      fs_term_token_tree_decode_quote
                        depth hHeadWellSorted
                        (hScoped head (by simp))
                        hHeadQuote
                    have hTailDecoded :=
                      fs_term_token_trees_decode_quote
                        depth hTailWellSorted
                        (by
                          intro term hTerm
                          exact hScoped term
                            (by simp [hTerm]))
                        hTailQuote
                    simp [hHeadDecoded,
                      hTailDecoded]
  termination_by terms => sizeOf terms
end

/-- 原始 Hilbert 树到 FormalSystem Hilbert 核公式的规范解码。 -/
def fs_hilbert_token_tree_decode :
    (depth : Nat) →
      RawHilbertTokenTree →
        Option SetFormula
  | depth, .equality left right => do
      let leftTerm ←
        fs_term_token_tree_decode depth left
      let rightTerm ←
        fs_term_token_tree_decode depth right
      if Term.check_wellSorted SetSort.set leftTerm &&
          Term.check_wellSorted SetSort.set rightTerm then
        some (.equal leftTerm rightTerm)
      else
        none
  | depth, .membership left right => do
      let leftTerm ←
        fs_term_token_tree_decode depth left
      let rightTerm ←
        fs_term_token_tree_decode depth right
      if Term.check_args_wellSorted
          [leftTerm, rightTerm]
          (signature.relDomain
            RelationSymbol.membership) then
        some (.rel RelationSymbol.membership
          [leftTerm, rightTerm])
      else
        none
  | depth, .predicate head arguments => do
      let relation ←
        fs_find_encoded
          (fun candidate : RelationSymbol =>
            Numbered.predicate_token
              (arguments.length - 1)
              candidate.ctorIdx)
          head fs_relation_symbols
      if fs_relation_kind relation =
          QuotationRelationKind.predicate then
        let decoded ←
          arguments.mapM
            (fs_term_token_tree_decode depth)
        if Term.check_args_wellSorted decoded
            (signature.relDomain relation) then
          some (.rel relation decoded)
        else
          none
      else
        none
  | depth, .negation body =>
      do
        let bodyFormula ←
          fs_hilbert_token_tree_decode
            depth body
        pure (.neg bodyFormula)
  | depth, .implication left right => do
      let leftFormula ←
        fs_hilbert_token_tree_decode depth left
      let rightFormula ←
        fs_hilbert_token_tree_decode depth right
      pure (.imp leftFormula rightFormula)
  | depth, .universal variableToken body =>
      if variableToken =
          Numbered.variable_token
            (bound_name depth) then
        do
          let bodyFormula ←
            fs_hilbert_token_tree_decode
              (depth + 1) body
          pure (.forallE SetSort.set bodyFormula)
      else
        none
termination_by
  _ tree => sizeOf tree

/-! ## 规范 Hilbert quotation 的 checked 回放 -/

/-- FormalSystem 单排序签名中，任意项 sort 证书都可规范到集合 sort。 -/
theorem fs_term_well_sorted_set
    {term : SetTerm} {sort : SetSort}
    (hTerm : TermWellSorted term sort) :
    TermWellSorted term SetSort.set := by
  cases sort
  exact hTerm

/-- 从 FormalSystem 实参列中抽取任意成员的集合 sort 证书。 -/
theorem fs_args_well_sorted_member_set :
    ∀ {arguments : List SetTerm}
        {sorts : List SetSort}
        {term : SetTerm},
      ArgsWellSorted arguments sorts →
      term ∈ arguments →
      TermWellSorted term SetSort.set
  | .nil, sorts, term, hArguments, hTerm => by
      simp at hTerm
  | .cons head tail, sorts, term,
      hArguments, hTerm => by
      cases hArguments with
      | cons hHead hTail =>
          rcases List.mem_cons.mp hTerm with
            rfl | hTailTerm
          · exact
              fs_term_well_sorted_set hHead
          · exact
              fs_args_well_sorted_member_set
                hTail hTailTerm
termination_by arguments => sizeOf arguments

/--
规范环境中，良构且 scope 正确的 Hilbert 核公式由 quotation 树精确恢复。
-/
theorem fs_hilbert_token_tree_decode_quote
    (depth : Nat)
    {formula : SetFormula}
    {tree : RawHilbertTokenTree}
    (hCore : Numbered.HilbertCore formula)
    (hWellFormed : FormulaWellFormed formula)
    (hScoped :
      FormulaScoped
        (Numbered.scope_of_names
          (canonical_bound_names depth))
        formula)
    (hQuote :
      quote_hilbert_token_tree_with?
          free_name bound_name
          (canonical_bound_names depth)
          depth formula =
        some tree) :
    fs_hilbert_token_tree_decode depth tree =
      some formula := by
  induction hCore generalizing depth tree with
  | relation relation arguments =>
      cases hWellFormed with
      | rel _ hArgumentsWellSorted =>
          cases hScoped with
          | rel _ _ hArgumentsScoped =>
              cases hKind :
                  QuotationNumbering.relation_kind
                    relation with
              | membership =>
                  have hRelation :
                      relation =
                        RelationSymbol.membership :=
                    fs_quotation_numbering.membership_unique
                      hKind
                      fs_membership_relation_kind
                  subst relation
                  cases arguments with
                  | nil =>
                      simp [quote_hilbert_token_tree_with?,
                        quote_relation_token_tree_with?,
                        hKind] at hQuote
                  | cons left tail =>
                      cases tail with
                      | nil =>
                          simp [quote_hilbert_token_tree_with?,
                            quote_relation_token_tree_with?,
                            hKind] at hQuote
                      | cons right extra =>
                          cases extra with
                          | cons third rest =>
                              simp [quote_hilbert_token_tree_with?,
                                quote_relation_token_tree_with?,
                                hKind] at hQuote
                          | nil =>
                              cases hLeftQuote :
                                  quote_term_token_tree_with?
                                    free_name
                                    (canonical_bound_names depth)
                                    left with
                              | none =>
                                  simp [quote_hilbert_token_tree_with?,
                                    quote_relation_token_tree_with?,
                                    hKind,
                                    hLeftQuote] at hQuote
                              | some leftTree =>
                                  cases hRightQuote :
                                      quote_term_token_tree_with?
                                        free_name
                                        (canonical_bound_names depth)
                                        right with
                                  | none =>
                                      simp [quote_hilbert_token_tree_with?,
                                        quote_relation_token_tree_with?,
                                        hKind,
                                        hLeftQuote,
                                        hRightQuote] at hQuote
                                  | some rightTree =>
                                      simp [quote_hilbert_token_tree_with?,
                                        quote_relation_token_tree_with?,
                                        hKind,
                                        hLeftQuote,
                                        hRightQuote] at hQuote
                                      subst tree
                                      have hLeftWellSorted :
                                          TermWellSorted left
                                            SetSort.set :=
                                        fs_args_well_sorted_member_set
                                          hArgumentsWellSorted
                                          (by simp)
                                      have hRightWellSorted :
                                          TermWellSorted right
                                            SetSort.set :=
                                        fs_args_well_sorted_member_set
                                          hArgumentsWellSorted
                                          (by simp)
                                      have hLeftDecoded :=
                                        fs_term_token_tree_decode_quote
                                          depth hLeftWellSorted
                                          (hArgumentsScoped left
                                            (by simp))
                                          hLeftQuote
                                      have hRightDecoded :=
                                        fs_term_token_tree_decode_quote
                                          depth hRightWellSorted
                                          (hArgumentsScoped right
                                            (by simp))
                                          hRightQuote
                                      simp [fs_hilbert_token_tree_decode,
                                        hLeftDecoded,
                                        hRightDecoded,
                                        Term.check_args_wellSorted_complete
                                          hArgumentsWellSorted]
              | predicate =>
                  cases arguments with
                  | nil =>
                      simp [quote_hilbert_token_tree_with?,
                        quote_relation_token_tree_with?,
                        hKind] at hQuote
                  | cons head tail =>
                      cases hTrees :
                          (head :: tail).mapM
                            (quote_term_token_tree_with?
                              free_name
                              (canonical_bound_names depth)) with
                      | none =>
                          simp [quote_hilbert_token_tree_with?,
                            quote_relation_token_tree_with?,
                            hKind, hTrees] at hQuote
                      | some trees =>
                          have hDecoded :=
                            fs_term_token_trees_decode_quote
                              depth hArgumentsWellSorted
                              hArgumentsScoped hTrees
                          have hLength :
                              trees.length =
                                (head :: tail).length :=
                            fs_option_mapM_length hTrees
                          simp [quote_hilbert_token_tree_with?,
                            quote_relation_token_tree_with?,
                            hKind, hTrees] at hQuote
                          subst tree
                          simp [fs_hilbert_token_tree_decode,
                            hLength,
                            (show fs_relation_kind relation =
                                QuotationRelationKind.predicate
                              by simpa [fs_quotation_numbering,
                                fs_relation_kind] using hKind),
                            hDecoded,
                            Term.check_args_wellSorted_complete
                              hArgumentsWellSorted]
  | equality left right =>
      cases hWellFormed with
      | equal hLeftWellSorted
          hRightWellSorted =>
          cases hScoped with
          | equal hLeftScoped hRightScoped =>
              cases hLeftQuote :
                  quote_term_token_tree_with?
                    free_name
                    (canonical_bound_names depth)
                    left with
              | none =>
                  simp [quote_hilbert_token_tree_with?,
                    hLeftQuote] at hQuote
              | some leftTree =>
                  cases hRightQuote :
                      quote_term_token_tree_with?
                        free_name
                        (canonical_bound_names depth)
                        right with
                  | none =>
                      simp [quote_hilbert_token_tree_with?,
                        hLeftQuote, hRightQuote] at hQuote
                  | some rightTree =>
                      simp [quote_hilbert_token_tree_with?,
                        hLeftQuote, hRightQuote] at hQuote
                      subst tree
                      have hLeftWellSortedSet :=
                        fs_term_well_sorted_set
                          hLeftWellSorted
                      have hRightWellSortedSet :=
                        fs_term_well_sorted_set
                          hRightWellSorted
                      have hLeftDecoded :=
                        fs_term_token_tree_decode_quote
                          depth hLeftWellSortedSet
                          hLeftScoped hLeftQuote
                      have hRightDecoded :=
                        fs_term_token_tree_decode_quote
                          depth hRightWellSortedSet
                          hRightScoped hRightQuote
                      simp [fs_hilbert_token_tree_decode,
                        hLeftDecoded, hRightDecoded,
                        Term.check_wellSorted_complete
                          hLeftWellSortedSet,
                        Term.check_wellSorted_complete
                          hRightWellSortedSet]
  | negation hBody ih =>
      rename_i body
      cases hWellFormed with
      | neg hBodyWellFormed =>
          cases hScoped with
          | neg hBodyScoped =>
              cases hBodyQuote :
                    quote_hilbert_token_tree_with?
                      free_name bound_name
                    (canonical_bound_names depth)
                    depth body with
              | none =>
                  simp [quote_hilbert_token_tree_with?,
                    hBodyQuote] at hQuote
              | some bodyTree =>
                  simp [quote_hilbert_token_tree_with?,
                    hBodyQuote] at hQuote
                  subst tree
                  have hBodyDecoded :=
                    ih depth hBodyWellFormed
                      hBodyScoped hBodyQuote
                  simp [fs_hilbert_token_tree_decode,
                    hBodyDecoded]
  | implication hLeft hRight ihLeft ihRight =>
      rename_i left right
      cases hWellFormed with
      | imp hLeftWellFormed
          hRightWellFormed =>
          cases hScoped with
          | imp hLeftScoped hRightScoped =>
              cases hLeftQuote :
                    quote_hilbert_token_tree_with?
                      free_name bound_name
                    (canonical_bound_names depth)
                    depth left with
              | none =>
                  simp [quote_hilbert_token_tree_with?,
                    hLeftQuote] at hQuote
              | some leftTree =>
                  cases hRightQuote :
                        quote_hilbert_token_tree_with?
                          free_name bound_name
                        (canonical_bound_names depth)
                        depth right with
                  | none =>
                      simp [quote_hilbert_token_tree_with?,
                        hLeftQuote, hRightQuote] at hQuote
                  | some rightTree =>
                      simp [quote_hilbert_token_tree_with?,
                        hLeftQuote, hRightQuote] at hQuote
                      subst tree
                      have hLeftDecoded :=
                        ihLeft depth hLeftWellFormed
                          hLeftScoped hLeftQuote
                      have hRightDecoded :=
                        ihRight depth hRightWellFormed
                          hRightScoped hRightQuote
                      simp [fs_hilbert_token_tree_decode,
                        hLeftDecoded, hRightDecoded]
  | universal sort hBody ih =>
      rename_i body
      cases sort
      cases hWellFormed with
      | forallE _ hBodyWellFormed =>
          cases hScoped with
          | forallE _ hBodyScoped =>
              cases hBodyQuote :
                    quote_hilbert_token_tree_with?
                      free_name bound_name
                    (bound_name depth ::
                      canonical_bound_names depth)
                    (depth + 1) body with
              | none =>
                  simp [quote_hilbert_token_tree_with?,
                    hBodyQuote] at hQuote
              | some bodyTree =>
                  simp [quote_hilbert_token_tree_with?,
                    hBodyQuote] at hQuote
                  subst tree
                  have hBodyScopedCanonical :
                      FormulaScoped
                        (Numbered.scope_of_names
                          (canonical_bound_names
                            (depth + 1)))
                        body := by
                    simpa [Numbered.scope_of_names,
                      canonical_bound_names,
                      Scope.push]
                      using hBodyScoped
                  have hBodyQuoteCanonical :
                      quote_hilbert_token_tree_with?
                          free_name bound_name
                          (canonical_bound_names
                            (depth + 1))
                          (depth + 1) body =
                        some bodyTree := by
                    simpa [canonical_bound_names]
                      using hBodyQuote
                  have hBodyDecoded :=
                    ih (depth + 1)
                      hBodyWellFormed
                      hBodyScopedCanonical
                      hBodyQuoteCanonical
                  simp [fs_hilbert_token_tree_decode,
                    hBodyDecoded]

/-- token 串到 admissible FormalSystem Hilbert 核公式的 checked 解码。 -/
def fs_hilbert_tokens_decode
    (tokens : List Nat) :
    Option SetFormula := do
  let tree ← RawHilbertTokenTree.parse? tokens
  let formula ←
    fs_hilbert_token_tree_decode 0 tree
  if Formula.check_admissible formula then
    some formula
  else
    none

/-- 规范 token 树经公开 parser 与 checked decoder 后还原原公式。 -/
theorem fs_hilbert_tokens_decode_tree_quote
    {formula : SetFormula}
    {tree : RawHilbertTokenTree}
    (hCore : Numbered.HilbertCore formula)
    (hWellFormed : FormulaWellFormed formula)
    (hScoped :
      FormulaScoped
        (Numbered.scope_of_names ([] : List Nat))
        formula)
    (hQuote :
      quote_hilbert_token_tree_with?
          free_name bound_name [] 0 formula =
        some tree) :
    fs_hilbert_tokens_decode tree.tokens = some formula := by
  have hSeparated :=
    quote_hilbert_token_tree_with?_lexically_separated
      free_name bound_name [] 0 hQuote
  have hDecoded :=
    fs_hilbert_token_tree_decode_quote
      0 hCore hWellFormed hScoped hQuote
  have hAdmissible : Formula.Admissible formula := by
    refine ⟨hWellFormed, ?_⟩
    simpa [Numbered.scope_of_names, Scope.empty] using hScoped
  unfold fs_hilbert_tokens_decode
  rw [RawHilbertTokenTree.parse?_tokens tree hSeparated]
  simp [hDecoded, Formula.check_admissible_complete hAdmissible]

/-- 公共 quotation 经过 token parser 后还原为 Hilbert 归约公式。 -/
theorem fs_hilbert_tokens_decode_quote
    {formula : SetFormula}
    {tokens : List Nat}
    (hFormula : Formula.Admissible formula)
    (hQuote : Numbered.quote_tokens? formula = some tokens) :
    fs_hilbert_tokens_decode tokens =
      some (Formula.hilbertize SetSort.set formula) := by
  let target : SetFormula :=
    Formula.hilbertize SetSort.set formula
  have hCore : Numbered.HilbertCore target := by
    simpa [target] using
      Numbered.hilbertize_hilbert_core SetSort.set hFormula.1
  have hWellFormed : FormulaWellFormed target := by
    simpa [target] using
      Numbered.hilbertize_well_formed SetSort.set hFormula.1
  have hScoped :
      FormulaScoped
        (Numbered.scope_of_names ([] : List Nat))
        target := by
    have hScoped' :=
      Numbered.hilbertize_scoped SetSort.set hFormula.2
    simpa [target, Numbered.scope_of_names, Scope.empty] using hScoped'
  cases hTree :
      quote_hilbert_token_tree_with?
        free_name bound_name [] 0 target with
  | none =>
      have hSync :=
        quote_hilbert_tokens_with?_eq_generic_token_tree
          free_name bound_name [] 0 target
      have hNone : Numbered.quote_tokens? formula = none := by
        simpa [Numbered.quote_tokens?, Numbered.quote_tokens_with?,
          target, hTree] using hSync
      simp [hNone] at hQuote
  | some tree =>
      have hTreeQuote :
          quote_hilbert_token_tree_with?
              free_name bound_name [] 0 target =
            some tree :=
        hTree
      have hSync :=
        quote_hilbert_tokens_with?_eq_generic_token_tree
          free_name bound_name [] 0 target
      have hQuoteTree :
          Numbered.quote_tokens? formula = some tree.tokens := by
        simpa [Numbered.quote_tokens?, Numbered.quote_tokens_with?,
          target, hTree] using hSync
      have hTokens : tokens = tree.tokens := by
        exact Option.some.inj (hQuote.symm.trans hQuoteTree)
      subst tokens
      simpa [target] using
        fs_hilbert_tokens_decode_tree_quote
          hCore hWellFormed hScoped hTreeQuote

/-- checked token 解码成功时，结果满足公共 admissibility 边界。 -/
theorem fs_hilbert_tokens_decode_admissible
    {tokens : List Nat}
    {formula : SetFormula}
    (hDecode :
      fs_hilbert_tokens_decode tokens =
        some formula) :
    Formula.Admissible formula := by
  unfold fs_hilbert_tokens_decode at hDecode
  cases hParse :
      RawHilbertTokenTree.parse? tokens with
  | none =>
      simp [hParse] at hDecode
  | some tree =>
      cases hTree :
          fs_hilbert_token_tree_decode 0 tree with
      | none =>
          simp [hParse, hTree] at hDecode
      | some decoded =>
          simp [hParse, hTree] at hDecode
          by_cases hCheck :
              Formula.check_admissible decoded =
                true
          · have hFormula :
                decoded = formula := by
              simpa [hCheck] using hDecode
            subst formula
            exact Formula.check_admissible_sound
              hCheck
          · simp [hCheck] at hDecode

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
