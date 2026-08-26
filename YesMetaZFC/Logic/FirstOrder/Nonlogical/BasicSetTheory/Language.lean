import YesMetaZFC.Logic.FirstOrder.Admissibility
import YesMetaZFC.Logic.FirstOrder.Metatheory.Notation
/-!
# 基本集合论的具体一阶语言
本模块给元数学层提供一个真正扩展过的单排序签名。等号仍由一阶逻辑核心原生
支持；空集、幂集、配对、关系代数、集合运算、函数运算、序极值、严格初始段、
关系限制以及一阶语义解释都作为定义扩张后的真实符号存在。函数限制与关系限制
使用不同符号，关系像与严格初始段也保持独立。`∈ₘ`、`⊆ₘ` 与 `⊂ₘ` 对应三个
二元关系符号，`is_ordered_pair_formula`、`is_relation_formula` 与语义层谓词则
对应各自的原子公式。所有符号的数学含义都由后续非逻辑公理给出，而不是在语法
层直接展开。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
/-- 基本集合论语言只有一个对象 sort。 -/
inductive SetSort where
  | set
  deriving DecidableEq, Repr
/-- 基本集合构造对应的函数符号。 -/
inductive FunctionSymbol where
  | emptySet
  | powerSet
  | unorderedPair
  | singleton
  | orderedPair
  | leftProjection
  | rightProjection
  | orderedPairReverse
  | cartesianProduct
  | domain
  | range
  | relationConverse
  | relationComposition
  | application
  | union
  | binaryUnion
  | successor
  | intersection
  | binaryIntersection
  | identity
  | mappingCollection
  | membershipRelation
  | image
  | restriction
  | minimum
  | maximum
  | initialSegment
  | relationRestriction
  | wellOrderComparisonMap
  | orderSum
  | orderProduct
  | mappingProduct
  | minimumDifference
  | indexOrder
  | powerSetBijection
  | symmetricDifference
  | inductiveCore
  | omega
  | naturalOrderType
  | naturalSubsetType
  | naturalAddition
  | naturalMultiplication
  | naturalExponentiation
  | finiteSequenceSpace
  | finiteSequenceConcatenation
  | nonemptyFiniteSequenceSpace
  | finiteSequenceFlatten
  | recursiveSequenceSpace
  | omegaRecursiveSequence
  | naturalDifference
  | godelPairing
  | transitiveClosure
  | finiteHierarchy
  | finiteUniverse
  | finiteSubsetCollection
  | logicalSymbolSet
  | membershipSymbolSet
  | variableSymbolSet
  | constantSymbolSet
  | codedFunctionSymbolSet
  | codedPredicateSymbolSet
  | termCodeSet
  | termSequenceSet
  | atomicFormulaCodeSet
  | formulaCodeSet
  | equalityFormulaCode
  | predicateFormulaCode
  | negationFormulaCode
  | implicationFormulaCode
  | universalFormulaCode
  | variableCode
  | constantCode
  | codedFunctionSymbolCode
  | codedPredicateSymbolCode
  | codeSubstitution
  | variableCollection
  | freeOccurrencePositions
  | implicationDistributionAxiomSet
  | selfImplicationAxiomSet
  | weakeningAxiomSet
  | contradictionAxiomSet
  | classicalAxiomSet
  | explosionAxiomSet
  | caseAnalysisAxiomSet
  | specializationAxiomSet
  | quantifierDistributionAxiomSet
  | vacuousQuantifierAxiomSet
  | equalitySubstitutionAxiomSet
  | equalityReflexivityAxiomSet
  | baseLogicalAxiomSet
  | logicalAxiomSet
  | relatedNonlogicalSymbolSet
  | relatedTermSet
  | relatedFormulaSet
  | relatedFormulaStageSet
  | canonicalNameCode
  | numeralNameCode
  | zfcAxiomCodeSet
  | completeAxiomCodeSet
  deriving DecidableEq, Repr
/-- 基本集合论关系符号。 -/
inductive RelationSymbol where
  | membership
  | subset
  | properSubset
  | isOrderedPair
  | isRelation
  | isEquivalenceRelation
  | isFunction
  | isMapping
  | isInjective
  | isSurjective
  | isBijection
  | isTransitiveSet
  | isLinearOrder
  | isOrderIsomorphism
  | isOrderIsomorphic
  | isOrderEmbedding
  | isOrderEmbeddable
  | isNaturalDiscreteLinearOrder
  | isWellOrder
  | isOrdinal
  | isNaturalNumber
  | isFinite
  | isEquinumerous
  | cardinalityLeq
  | cardinalityStrictLess
  | isDedekindFinite
  | isInductiveSet
  | isUnboundedSubset
  | isBoundedSubset
  | isInfinite
  | isCountable
  | isUncountable
  | isCountablyInfinite
  | isHereditarilyFinite
  | omegaPairLess
  | isTermCode
  | isAtomicFormulaCode
  | isFormulaCode
  | quantifierOccurs
  | boundOccurrence
  | freeOccurrence
  | isSubstitutable
  | isLogicalAxiomCode
  | modusPonens
  | isStructure
  | isTermEvaluation
  | termValue
  | atomicSatisfaction
  | formulaSatisfactionAtStage
  | formulaSatisfaction
  | isTruth
  | isModel
  | logicalConsequence
  | isTheorem
  deriving DecidableEq, Repr
/-- 带有基本集合构造和关系谓词的具体一阶签名。 -/
def signature : Signature where
  SortSymbol := SetSort
  FuncSymbol := FunctionSymbol
  RelSymbol := RelationSymbol
  funcDomain
    | .emptySet => []
    | .powerSet => [.set]
    | .unorderedPair => [.set, .set]
    | .singleton => [.set]
    | .orderedPair => [.set, .set]
    | .leftProjection => [.set]
    | .rightProjection => [.set]
    | .orderedPairReverse => [.set]
    | .cartesianProduct => [.set, .set]
    | .domain => [.set]
    | .range => [.set]
    | .relationConverse => [.set]
    | .relationComposition => [.set, .set]
    | .application => [.set, .set]
    | .union => [.set]
    | .binaryUnion => [.set, .set]
    | .successor => [.set]
    | .intersection => [.set]
    | .binaryIntersection => [.set, .set]
    | .identity => [.set]
    | .mappingCollection => [.set, .set]
    | .membershipRelation => [.set]
    | .image => [.set, .set]
    | .restriction => [.set, .set]
    | .minimum => [.set, .set]
    | .maximum => [.set, .set]
    | .initialSegment => [.set, .set, .set]
    | .relationRestriction => [.set, .set]
    | .wellOrderComparisonMap => [.set, .set, .set, .set]
    | .orderSum => [.set, .set, .set, .set]
    | .orderProduct => [.set, .set, .set, .set]
    | .mappingProduct => [.set, .set]
    | .minimumDifference => [.set, .set]
    | .indexOrder => [.set, .set, .set, .set]
    | .powerSetBijection => [.set]
    | .symmetricDifference => [.set, .set]
    | .inductiveCore => [.set]
    | .omega => []
    | .naturalOrderType => [.set, .set]
    | .naturalSubsetType => [.set]
    | .naturalAddition => [.set, .set]
    | .naturalMultiplication => [.set, .set]
    | .naturalExponentiation => [.set, .set]
    | .finiteSequenceSpace => [.set]
    | .finiteSequenceConcatenation => [.set, .set]
    | .nonemptyFiniteSequenceSpace => [.set]
    | .finiteSequenceFlatten => [.set]
    | .recursiveSequenceSpace => [.set, .set, .set]
    | .omegaRecursiveSequence => [.set, .set, .set]
    | .naturalDifference => [.set, .set]
    | .godelPairing => [.set]
    | .transitiveClosure => [.set]
    | .finiteHierarchy => []
    | .finiteUniverse => []
    | .finiteSubsetCollection => [.set]
    | .logicalSymbolSet => []
    | .membershipSymbolSet => []
    | .variableSymbolSet => []
    | .constantSymbolSet => []
    | .codedFunctionSymbolSet => []
    | .codedPredicateSymbolSet => []
    | .termCodeSet => []
    | .termSequenceSet => []
    | .atomicFormulaCodeSet => []
    | .formulaCodeSet => []
    | .equalityFormulaCode => [.set, .set]
    | .predicateFormulaCode => [.set, .set, .set]
    | .negationFormulaCode => [.set]
    | .implicationFormulaCode => [.set, .set]
    | .universalFormulaCode => [.set, .set]
    | .variableCode => [.set]
    | .constantCode => [.set]
    | .codedFunctionSymbolCode => [.set, .set]
    | .codedPredicateSymbolCode => [.set, .set]
    | .codeSubstitution => [.set, .set, .set]
    | .variableCollection => [.set]
    | .freeOccurrencePositions => [.set, .set]
    | .implicationDistributionAxiomSet => []
    | .selfImplicationAxiomSet => []
    | .weakeningAxiomSet => []
    | .contradictionAxiomSet => []
    | .classicalAxiomSet => []
    | .explosionAxiomSet => []
    | .caseAnalysisAxiomSet => []
    | .specializationAxiomSet => []
    | .quantifierDistributionAxiomSet => []
    | .vacuousQuantifierAxiomSet => []
    | .equalitySubstitutionAxiomSet => []
    | .equalityReflexivityAxiomSet => []
    | .baseLogicalAxiomSet => []
    | .logicalAxiomSet => []
    | .relatedNonlogicalSymbolSet => []
    | .relatedTermSet => [.set]
    | .relatedFormulaSet => [.set]
    | .relatedFormulaStageSet => [.set, .set]
    | .canonicalNameCode => [.set]
    | .numeralNameCode => [.set]
    | .zfcAxiomCodeSet => []
    | .completeAxiomCodeSet => []
  funcCodomain
    | .emptySet => .set
    | .powerSet => .set
    | .unorderedPair => .set
    | .singleton => .set
    | .orderedPair => .set
    | .leftProjection => .set
    | .rightProjection => .set
    | .orderedPairReverse => .set
    | .cartesianProduct => .set
    | .domain => .set
    | .range => .set
    | .relationConverse => .set
    | .relationComposition => .set
    | .application => .set
    | .union => .set
    | .binaryUnion => .set
    | .successor => .set
    | .intersection => .set
    | .binaryIntersection => .set
    | .identity => .set
    | .mappingCollection => .set
    | .membershipRelation => .set
    | .image => .set
    | .restriction => .set
    | .minimum => .set
    | .maximum => .set
    | .initialSegment => .set
    | .relationRestriction => .set
    | .wellOrderComparisonMap => .set
    | .orderSum => .set
    | .orderProduct => .set
    | .mappingProduct => .set
    | .minimumDifference => .set
    | .indexOrder => .set
    | .powerSetBijection => .set
    | .symmetricDifference => .set
    | .inductiveCore => .set
    | .omega => .set
    | .naturalOrderType => .set
    | .naturalSubsetType => .set
    | .naturalAddition => .set
    | .naturalMultiplication => .set
    | .naturalExponentiation => .set
    | .finiteSequenceSpace => .set
    | .finiteSequenceConcatenation => .set
    | .nonemptyFiniteSequenceSpace => .set
    | .finiteSequenceFlatten => .set
    | .recursiveSequenceSpace => .set
    | .omegaRecursiveSequence => .set
    | .naturalDifference => .set
    | .godelPairing => .set
    | .transitiveClosure => .set
    | .finiteHierarchy => .set
    | .finiteUniverse => .set
    | .finiteSubsetCollection => .set
    | .logicalSymbolSet => .set
    | .membershipSymbolSet => .set
    | .variableSymbolSet => .set
    | .constantSymbolSet => .set
    | .codedFunctionSymbolSet => .set
    | .codedPredicateSymbolSet => .set
    | .termCodeSet => .set
    | .termSequenceSet => .set
    | .atomicFormulaCodeSet => .set
    | .formulaCodeSet => .set
    | .equalityFormulaCode => .set
    | .predicateFormulaCode => .set
    | .negationFormulaCode => .set
    | .implicationFormulaCode => .set
    | .universalFormulaCode => .set
    | .variableCode => .set
    | .constantCode => .set
    | .codedFunctionSymbolCode => .set
    | .codedPredicateSymbolCode => .set
    | .codeSubstitution => .set
    | .variableCollection => .set
    | .freeOccurrencePositions => .set
    | .implicationDistributionAxiomSet => .set
    | .selfImplicationAxiomSet => .set
    | .weakeningAxiomSet => .set
    | .contradictionAxiomSet => .set
    | .classicalAxiomSet => .set
    | .explosionAxiomSet => .set
    | .caseAnalysisAxiomSet => .set
    | .specializationAxiomSet => .set
    | .quantifierDistributionAxiomSet => .set
    | .vacuousQuantifierAxiomSet => .set
    | .equalitySubstitutionAxiomSet => .set
    | .equalityReflexivityAxiomSet => .set
    | .baseLogicalAxiomSet => .set
    | .logicalAxiomSet => .set
    | .relatedNonlogicalSymbolSet => .set
    | .relatedTermSet => .set
    | .relatedFormulaSet => .set
    | .relatedFormulaStageSet => .set
    | .canonicalNameCode => .set
    | .numeralNameCode => .set
    | .zfcAxiomCodeSet => .set
    | .completeAxiomCodeSet => .set
  relDomain
    | .membership => [.set, .set]
    | .subset => [.set, .set]
    | .properSubset => [.set, .set]
    | .isOrderedPair => [.set]
    | .isRelation => [.set]
    | .isEquivalenceRelation => [.set]
    | .isFunction => [.set]
    | .isMapping => [.set, .set, .set]
    | .isInjective => [.set, .set, .set]
    | .isSurjective => [.set, .set, .set]
    | .isBijection => [.set, .set, .set]
    | .isTransitiveSet => [.set]
    | .isLinearOrder => [.set, .set]
    | .isOrderIsomorphism => [.set, .set, .set, .set, .set]
    | .isOrderIsomorphic => [.set, .set, .set, .set]
    | .isOrderEmbedding => [.set, .set, .set, .set, .set]
    | .isOrderEmbeddable => [.set, .set, .set, .set]
    | .isNaturalDiscreteLinearOrder => [.set, .set]
    | .isWellOrder => [.set, .set]
    | .isOrdinal => [.set]
    | .isNaturalNumber => [.set]
    | .isFinite => [.set]
    | .isEquinumerous => [.set, .set]
    | .cardinalityLeq => [.set, .set]
    | .cardinalityStrictLess => [.set, .set]
    | .isDedekindFinite => [.set]
    | .isInductiveSet => [.set]
    | .isUnboundedSubset => [.set, .set, .set]
    | .isBoundedSubset => [.set, .set, .set]
    | .isInfinite => [.set]
    | .isCountable => [.set]
    | .isUncountable => [.set]
    | .isCountablyInfinite => [.set]
    | .isHereditarilyFinite => [.set]
    | .omegaPairLess => [.set, .set]
    | .isTermCode => [.set]
    | .isAtomicFormulaCode => [.set]
    | .isFormulaCode => [.set]
    | .quantifierOccurs => [.set, .set]
    | .boundOccurrence => [.set, .set]
    | .freeOccurrence => [.set, .set]
    | .isSubstitutable => [.set, .set, .set]
    | .isLogicalAxiomCode => [.set]
    | .modusPonens => [.set, .set, .set]
    | .isStructure => [.set, .set, .set]
    | .isTermEvaluation => [.set, .set, .set, .set]
    | .termValue => [.set, .set, .set, .set, .set, .set, .set]
    | .atomicSatisfaction => [.set, .set, .set, .set, .set, .set]
    | .formulaSatisfactionAtStage =>
      [.set, .set, .set, .set, .set, .set, .set]
    | .formulaSatisfaction => [.set, .set, .set, .set, .set, .set]
    | .isTruth => [.set, .set, .set, .set, .set]
    | .isModel => [.set, .set, .set, .set, .set]
    | .logicalConsequence => [.set, .set, .set]
    | .isTheorem => [.set, .set]
instance signature_sort_decidable_eq : DecidableEq signature.SortSymbol := by
  unfold signature
  infer_instance
instance signature_relation_decidable_eq : DecidableEq signature.RelSymbol := by
  unfold signature
  infer_instance
instance signature_function_decidable_eq : DecidableEq signature.FuncSymbol := by
  unfold signature
  infer_instance
/-- 当前具体语言中的项。 -/
abbrev SetTerm := Term signature
/-- 当前具体语言中的公式。 -/
abbrev SetFormula := Formula signature
/-- 当前具体语言中的非逻辑理论。 -/
abbrev SetTheory := Theory signature
/-- 单排序集合论语言中，任意原始项的可计算目标 sort 都规范为集合 sort。 -/
@[term_check]
theorem set_term_inferred_sort (term : SetTerm) :
    Term.inferredSort term = SetSort.set := by
  cases Term.inferredSort term
  rfl

/-- 单排序集合论语言中，每个函数符号的参数域都是集合 sort 的复制表。 -/
theorem set_function_domain_replicate
    (symbol : FunctionSymbol) :
    signature.funcDomain symbol =
      List.replicate
        (signature.funcDomain symbol).length SetSort.set := by
  cases symbol <;> rfl

/-- 单排序集合论语言中，每个关系符号的参数域都是集合 sort 的复制表。 -/
theorem set_relation_domain_replicate
    (symbol : RelationSymbol) :
    signature.relDomain symbol =
      List.replicate
        (signature.relDomain symbol).length SetSort.set := by
  cases symbol <;> rfl

/-- 单排序语言中的 free 变量项。 -/
abbrev set_variable (id : FreeVarId) : SetTerm :=
  v#[SetSort.set, id]
/-- 单排序语言中的 bound 变量项。 -/
abbrev set_bound_variable (index : Nat) : SetTerm :=
  b#[SetSort.set, index]
/-- 自由集合变量满足公共 proof-carrying 项边界。 -/
theorem set_variable_admissible (id : FreeVarId) :
    Term.Admissible (set_variable id) SetSort.set :=
  ⟨
    TermWellSorted.fvar (σ := signature) SetSort.set id,
    TermScoped.fvar (σ := signature) (ctx := (Scope.empty : Scope signature))
      SetSort.set id⟩
/--
单排序签名中的函数应用只需携带 proof-carrying 参数列表。
函数的 domain/codomain 等式由具体符号定义规约给出，参数的 sort 与 scope
证书在这里统一组装。
-/
theorem set_function_application_admissible
    (function : FunctionSymbol)
    (arguments : List {term : SetTerm // Term.Admissible term SetSort.set})
    (hDomain :
      signature.funcDomain function =
        List.replicate arguments.length SetSort.set)
    (hCodomain : signature.funcCodomain function = SetSort.set) :
    Term.Admissible
      (.app function (arguments.map Subtype.val))
      SetSort.set := by
  have hSorted :
      ArgsWellSorted
        (arguments.map Subtype.val)
        (List.replicate arguments.length SetSort.set) := by
    clear hDomain hCodomain
    induction arguments with
    | nil =>
        exact .nil
    | cons argument rest ih =>
        simpa using ArgsWellSorted.cons argument.property.1 ih
  constructor
  · rw [← hCodomain]
    apply TermWellSorted.app (σ := signature) function
    rw [hDomain]
    exact hSorted
  · exact TermScoped.app (σ := signature)
      (ctx := (Scope.empty : Scope signature)) function _ (by
      intro term hTerm
      rcases List.mem_map.mp hTerm with ⟨argument, _, rfl⟩
      exact Subtype.property argument |>.2)
/-- 定义扩张后的空集常量项。 -/
abbrev empty_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.emptySet]()
/-- 定义扩张后的一元幂集项。 -/
abbrev power_set_term (set : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.powerSet](set)
/-- 定义扩张后的二元无序对项。 -/
abbrev unordered_pair_term (left right : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.unorderedPair](left, right)
/-- 定义扩张后的一元单点集项。 -/
abbrev singleton_term (element : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.singleton](element)
/-- 定义扩张后的二元有序对项。 -/
abbrev ordered_pair_term (left right : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.orderedPair](left, right)
/-- 定义扩张后的有序对左投影项。 -/
abbrev left_projection_term (pair : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.leftProjection](pair)
/-- 定义扩张后的有序对右投影项。 -/
abbrev right_projection_term (pair : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.rightProjection](pair)
/-- 定义扩张后的有序对反转项。 -/
abbrev ordered_pair_reverse_term (pair : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.orderedPairReverse](pair)
/-- 定义扩张后的笛卡尔积项。 -/
abbrev cartesian_product_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.cartesianProduct](left, right)
/-- 定义扩张后的关系定义域项。 -/
abbrev domain_term (relation : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.domain](relation)
/-- 定义扩张后的关系值域项。文献中的 `rng` 只保留为索引，公共接口使用 `range`。 -/
abbrev range_term (relation : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.range](relation)
/-- 定义扩张后的关系逆项；与单个有序对的反转项严格区分。 -/
abbrev relation_converse_term (relation : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.relationConverse](relation)
/-- 定义扩张后的关系复合项，参数顺序对应 `second ∘ first`。 -/
abbrev relation_composition_term (second first : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.relationComposition](second, first)
/-- 定义扩张后的函数求值项。 -/
abbrev function_application_term (function argument : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.application](function, argument)
/-- 定义扩张后的一元并集项。 -/
abbrev union_term (set : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.union](set)
/-- 定义扩张后的二元并项。 -/
abbrev binary_union_term (left right : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.binaryUnion](left, right)
/-- 定义扩张后的一元后继项。 -/
abbrev successor_term (set : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.successor](set)
/-- 定义扩张后的非空族交集项。 -/
abbrev intersection_term (set : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.intersection](set)
/-- 定义扩张后的二元交项。 -/
abbrev binary_intersection_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.binaryIntersection](left, right)
/-- 定义扩张后的恒等映射项。 -/
abbrev identity_term (source : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.identity](source)
/-- 定义扩张后的映射收集项。 -/
abbrev mapping_collection_term (source target : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.mappingCollection](source, target)
/-- 定义扩张后的成员关系限制项。 -/
abbrev membership_relation_term (source : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.membershipRelation](source)
/-- 定义扩张后的映像项。 -/
abbrev image_term (function subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.image](function, subset)
/-- 定义扩张后的函数限制项。 -/
abbrev restriction_term (function subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.restriction](function, subset)
/-- 定义扩张后的最小元项。 -/
abbrev minimum_term (relation subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.minimum](relation, subset)
/-- 定义扩张后的最大元项。 -/
abbrev maximum_term (relation subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.maximum](relation, subset)
/-- 指定点在严格序下的初始段项。 -/
abbrev initial_segment_term (point relation carrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.initialSegment](point, relation, carrier)
/-- 关系在指定子集上的限制项。 -/
abbrev relation_restriction_term (relation subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.relationRestriction](relation, subset)
/-- 两个良序之间的规范比较映射项。文献索引为 `QR`。 -/
abbrev well_order_comparison_map_term (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.wellOrderComparisonMap](
    sourceRelation, sourceCarrier, targetRelation, targetCarrier)
/-- 两个带载体线性序的序和项。文献记号 `⊕` 只保留为索引。 -/
abbrev order_sum_term (firstRelation firstCarrier secondRelation secondCarrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.orderSum](
    firstRelation, firstCarrier, secondRelation, secondCarrier)
/-- 两个带载体线性序的词典序积项。文献记号 `⊗` 只保留为索引。 -/
abbrev order_product_term (firstRelation firstCarrier secondRelation secondCarrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.orderProduct](
    firstRelation, firstCarrier, secondRelation, secondCarrier)
/-- 定义扩张后的映射直积项；文献记号 `⊗` 只保留为索引。 -/
abbrev mapping_product_term (firstFunction secondFunction : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.mappingProduct](firstFunction, secondFunction)
/-- 定义扩张后的最小差异点项。 -/
abbrev minimum_difference_term (firstFunction secondFunction : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.minimumDifference](firstFunction, secondFunction)
/-- 定义扩张后的指数序关系项。 -/
abbrev index_order_term (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.indexOrder](
    sourceRelation, sourceCarrier, targetRelation, targetCarrier)
/-- 定义扩张后的幂集编码双射项。 -/
abbrev power_set_bijection_term (natural : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.powerSetBijection](natural)
/-- 定义扩张后的对称差项。 -/
abbrev symmetric_difference_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.symmetricDifference](left, right)
/-- 定义扩张后的归纳核项；文献中的 `U` 仅保留为索引。 -/
abbrev inductive_core_term (set : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.inductiveCore](set)
/-- 定义扩张后的常元 `ω`。 -/
abbrev omega_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.omega]()
/-- 关系在自然离散线性序上的序型项。 -/
abbrev natural_order_type_term (relation carrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.naturalOrderType](relation, carrier)
/-- 自然数子集的序型项。 -/
abbrev natural_subset_type_term (subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.naturalSubsetType](subset)
/-- 自然数加法项。 -/
abbrev natural_addition_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.naturalAddition](left, right)
/-- 自然数乘法项。 -/
abbrev natural_multiplication_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.naturalMultiplication](left, right)
/-- 自然数幂项。 -/
abbrev natural_exponentiation_term (base exponent : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.naturalExponentiation](base, exponent)
/-- 给定集合上的有限序列空间项。 -/
abbrev finite_sequence_space_term (source : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.finiteSequenceSpace](source)
/-- 两个有限序列的顺序合并项。 -/
abbrev finite_sequence_concatenation_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.finiteSequenceConcatenation](left, right)
/-- 给定集合上的非空有限序列空间项。 -/
abbrev nonempty_finite_sequence_space_term (source : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.nonemptyFiniteSequenceSpace](source)
/-- 有限序列族的有限折叠项。 -/
abbrev finite_sequence_flatten_term (sequence : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.finiteSequenceFlatten](sequence)
/-- 递归序列空间项。 -/
abbrev recursive_sequence_space_term (source seed recursion : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.recursiveSequenceSpace](source, seed, recursion)
/-- 以 `ω` 为索引的递归序列项。 -/
abbrev omega_recursive_sequence_term (source seed recursion : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.omegaRecursiveSequence](source, seed, recursion)
/-- 自然数截断减法项。 -/
abbrev natural_difference_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.naturalDifference](left, right)
/-- Gödel 配对编码项。 -/
abbrev godel_pairing_term (pair : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.godelPairing](pair)
/-- 定义扩张后的传递闭包项。文献索引为 `CDBB`。 -/
abbrev transitive_closure_term (set : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.transitiveClosure](set)
/-- 由空集和幂集递归生成的有限层级序列。 -/
abbrev finite_hierarchy_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.finiteHierarchy]()
/-- 有限层级的并集常元，即通常记作 `V_ω` 的集合。 -/
abbrev finite_universe_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.finiteUniverse]()
/-- 给定集合的所有有限子集组成的集合。文献索引为 `YXZJ`。 -/
abbrev finite_subset_collection_term (source : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.finiteSubsetCollection](source)
/-- 一阶形式语言的逻辑符号编码集合。 -/
abbrev logical_symbol_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.logicalSymbolSet]()
/-- 一阶集合论语言的隶属关系符号编码集合。 -/
abbrev membership_symbol_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.membershipSymbolSet]()
/-- 对象语言变量符号的编码集合。 -/
abbrev variable_symbol_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.variableSymbolSet]()
/-- 对象语言常元符号的编码集合。 -/
abbrev constant_symbol_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.constantSymbolSet]()
/-- 对象语言函数符号的编码集合。 -/
abbrev coded_function_symbol_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.codedFunctionSymbolSet]()
/-- 对象语言谓词符号的编码集合。 -/
abbrev coded_predicate_symbol_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.codedPredicateSymbolSet]()
/-- 对象语言项编码组成的集合。 -/
abbrev term_code_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.termCodeSet]()
/-- 非空有限项列编码组成的集合。 -/
abbrev term_sequence_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.termSequenceSet]()
/-- 原子公式编码组成的集合。 -/
abbrev atomic_formula_code_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.atomicFormulaCodeSet]()
/-- 一阶公式编码组成的集合。 -/
abbrev formula_code_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.formulaCodeSet]()
/-- 等式原子编码运算符。 -/
abbrev equality_formula_code_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.equalityFormulaCode](left, right)
/-- 一般谓词应用原子编码运算符。 -/
abbrev predicate_formula_code_term (arityPredecessor symbolIndex arguments : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.predicateFormulaCode](
    arityPredecessor, symbolIndex, arguments)
/-- 否定公式编码运算符。 -/
abbrev negation_formula_code_term (body : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.negationFormulaCode](body)
/-- 蕴含公式编码运算符。 -/
abbrev implication_formula_code_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.implicationFormulaCode](left, right)
/-- 全称量化公式编码运算符。 -/
abbrev universal_formula_code_term (boundVariable body : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.universalFormulaCode](boundVariable, body)
/-- 变量符号编码运算符。 -/
abbrev variable_code_term (index : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.variableCode](index)
/-- 常元符号编码运算符。 -/
abbrev constant_code_term (index : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.constantCode](index)
/-- 函数符号编码运算符。 -/
abbrev coded_function_symbol_code_operator_term (arityPredecessor symbolIndex : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.codedFunctionSymbolCode](
    arityPredecessor, symbolIndex)
/-- 谓词符号编码运算符。 -/
abbrev coded_predicate_symbol_code_operator_term (arityPredecessor symbolIndex : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.codedPredicateSymbolCode](
    arityPredecessor, symbolIndex)
/-- 对编码字符串作变量替换。 -/
abbrev code_substitution_term (source boundVariable replacement : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.codeSubstitution](
    source, boundVariable, replacement)
/-- token 串的规范闭项代码。 -/
abbrev canonical_name_code_term (source : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.canonicalNameCode](source)
/-- 标准自然数项的对象 quotation 代码。 -/
abbrev numeral_name_code_term (number : SetTerm) : SetTerm :=
  𝒇ₘ[FunctionSymbol.numeralNameCode](number)
/-- 编码字符串中出现的变量符号集合。 -/
abbrev variable_collection_term (source : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.variableCollection](source)
/-- 变量在公式编码中自由出现的位置集合。 -/
abbrev free_occurrence_positions_term (boundVariable formula : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.freeOccurrencePositions](
    boundVariable, formula)
/-- 第一类蕴含分配公理模式的编码集合。 -/
abbrev implication_distribution_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.implicationDistributionAxiomSet]()
/-- 自蕴含公理模式的编码集合。 -/
abbrev self_implication_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.selfImplicationAxiomSet]()
/-- 弱化公理模式的编码集合。 -/
abbrev weakening_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.weakeningAxiomSet]()
/-- 矛盾前件公理模式的编码集合。 -/
abbrev contradiction_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.contradictionAxiomSet]()
/-- 经典逻辑公理模式的编码集合。 -/
abbrev classical_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.classicalAxiomSet]()
/-- 爆炸律公理模式的编码集合。 -/
abbrev explosion_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.explosionAxiomSet]()
/-- 分类讨论公理模式的编码集合。 -/
abbrev case_analysis_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.caseAnalysisAxiomSet]()
/-- 全称特化公理模式的编码集合。 -/
abbrev specialization_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.specializationAxiomSet]()
/-- 全称量词分配公理模式的编码集合。 -/
abbrev quantifier_distribution_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.quantifierDistributionAxiomSet]()
/-- 无关量词引入公理模式的编码集合。 -/
abbrev vacuous_quantifier_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.vacuousQuantifierAxiomSet]()
/-- 等同律公理模式的编码集合。 -/
abbrev equality_substitution_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.equalitySubstitutionAxiomSet]()
/-- 恒等律公理模式的编码集合。 -/
abbrev equality_reflexivity_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.equalityReflexivityAxiomSet]()
/-- 未作全称闭包的基础逻辑公理编码集合。 -/
abbrev base_logical_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.baseLogicalAxiomSet]()
/-- 在全称量化下闭合后的逻辑公理编码集合。 -/
abbrev logical_axiom_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.logicalAxiomSet]()
/-- ZFC 外部公理 quotation 码的专用正向枚举集合。 -/
abbrev zfc_axiom_code_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.zfcAxiomCodeSet]()
/--
固定目标理论完整公理 quotation 码的专用正向枚举集合。
它与只枚举基础 ZFC 公理的 `zfc_axiom_code_set_term` 分离；具体目标理论由使用该项的
元理论模块明确给出。
-/
abbrev complete_axiom_code_set_term : SetTerm :=
  𝒇ₘ[FunctionSymbol.completeAxiomCodeSet]()
/-- 当前形式语言可使用的全部非逻辑符号编码。文献索引为 `XGFH`。 -/
abbrev related_nonlogical_symbol_set_term :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.relatedNonlogicalSymbolSet]()
/-- 仅使用给定非逻辑符号集的项编码集合。文献索引为 `XXng`。 -/
abbrev related_term_set_term (symbols : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.relatedTermSet](symbols)
/-- 仅使用给定非逻辑符号集的公式编码集合。文献索引为 `XBDS`。 -/
abbrev related_formula_set_term (symbols : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.relatedFormulaSet](symbols)
/-- 指定语言中递归深度不超过给定自然数的公式编码。文献索引为 `BDS*`。 -/
abbrev related_formula_stage_set_term (symbols stage : SetTerm) :
    SetTerm :=
  𝒇ₘ[FunctionSymbol.relatedFormulaStageSet](symbols, stage)
/-- 隶属关系原子。 -/
abbrev membership_formula (element set : SetTerm) : SetFormula :=
  Formula.rel RelationSymbol.membership [element, set]
/-- 两个合法集合项组成合法隶属原子。 -/
theorem membership_formula_admissible
    {element set : SetTerm} (hElement : Term.Admissible element SetSort.set) (hSet : Term.Admissible set SetSort.set) :
    Formula.Admissible (membership_formula element set) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hElement (ArgsAdmissible.cons hSet ArgsAdmissible.nil))
/-- 隶属原子的计算证书由两个集合项证书直接组合。 -/
@[formula_check]
theorem membership_formula_check
    {element set : SetTerm}
    (hElement : Term.CheckCertificate element SetSort.set)
    (hSet : Term.CheckCertificate set SetSort.set) :
    Formula.CheckCertificate
      (membership_formula element set) :=
  Formula.check_admissible_complete
    (membership_formula_admissible
      hElement.admissible hSet.admissible)
/-- 单排序集合论中的等式证书不再要求调用方显式给出 sort。 -/
@[formula_check]
theorem set_equality_formula_check
    {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Formula.CheckCertificate (Formula.equal left right) :=
  Formula.CheckCertificate.equal hLeft hRight
/-- 子集关系原子。 -/
abbrev subset_formula (left right : SetTerm) : SetFormula :=
  Formula.rel RelationSymbol.subset [left, right]
/-- 两个合法集合项组成合法子集原子。 -/
theorem subset_formula_admissible
    {left right : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (subset_formula left right) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hLeft (ArgsAdmissible.cons hRight ArgsAdmissible.nil))
/-- 子集原子的计算证书由两个集合项证书组合。 -/
@[formula_check]
theorem subset_formula_check
    {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Formula.CheckCertificate (subset_formula left right) :=
  Formula.check_admissible_complete <|
    subset_formula_admissible
      hLeft.admissible hRight.admissible
/-- 真子集关系原子。 -/
abbrev proper_subset_formula (left right : SetTerm) : SetFormula :=
  Formula.rel RelationSymbol.properSubset [left, right]
/-- 有序对谓词原子。 -/
abbrev is_ordered_pair_formula (pair : SetTerm) : SetFormula :=
  Formula.rel RelationSymbol.isOrderedPair [pair]
/-- 关系谓词原子。 -/
abbrev is_relation_formula (relation : SetTerm) : SetFormula :=
  Formula.rel RelationSymbol.isRelation [relation]
/-- 等价关系谓词原子；文献索引为 `DJGX`。 -/
abbrev is_equivalence_relation_formula (relation : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isEquivalenceRelation
    [relation]
/-- 集合编码函数谓词原子；文献索引为 `HanS`。 -/
abbrev is_function_formula (function : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isFunction [function]
/-- 从指定定义域映入目标集合的映射谓词原子；文献索引为 `InSh`。 -/
abbrev is_mapping_formula (function source target : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isMapping
    [function, source, target]
/-- 单射映射谓词原子。文献索引为 `DanS`。 -/
abbrev is_injective_formula (function source target : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isInjective
    [function, source, target]
/-- 满射映射谓词原子。文献索引为 `ManS`。 -/
abbrev is_surjective_formula (function source target : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isSurjective
    [function, source, target]
/-- 双射映射谓词原子。文献索引为 `ShuS`。 -/
abbrev is_bijection_formula (function source target : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isBijection
    [function, source, target]
/-- 传递集谓词原子。文献索引为 `ChuD`。 -/
abbrev is_transitive_set_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isTransitiveSet [set]
/-- 线性序谓词原子。文献索引为 `XiXn`。 -/
abbrev is_linear_order_formula (relation carrier : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isLinearOrder [relation, carrier]
/-- 序同构映射谓词原子。文献索引为 `TGYS`。 -/
abbrev is_order_isomorphism_formula (function sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isOrderIsomorphism
    [function, sourceRelation, sourceCarrier, targetRelation, targetCarrier]
/-- 序同构关系谓词原子。文献索引为 `XuTG`。 -/
abbrev is_order_isomorphic_formula (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isOrderIsomorphic
    [sourceRelation, sourceCarrier, targetRelation, targetCarrier]
/-- 序嵌入映射谓词原子。文献索引为 `QRYS`。 -/
abbrev is_order_embedding_formula (function sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isOrderEmbedding
    [function, sourceRelation, sourceCarrier, targetRelation, targetCarrier]
/-- 序可嵌入关系谓词原子。文献索引为 `XuQR`。 -/
abbrev is_order_embeddable_formula (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isOrderEmbeddable
    [sourceRelation, sourceCarrier, targetRelation, targetCarrier]
/-- 自然离散线性序谓词原子。文献索引为 `Zrlx`。 -/
abbrev is_natural_discrete_linear_order_formula (relation carrier : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isNaturalDiscreteLinearOrder
    [relation, carrier]
/-- 良序谓词原子。文献索引为 `ZX`。 -/
abbrev is_well_order_formula (relation carrier : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isWellOrder [relation, carrier]
/-- 序数谓词原子。文献索引为 `XuS`。 -/
abbrev is_ordinal_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isOrdinal [set]
/-- 自然数谓词原子。文献索引为 `ZRS`。 -/
abbrev is_natural_number_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isNaturalNumber [set]
/-- 有穷集谓词原子。文献索引为 `YuQn`。 -/
abbrev is_finite_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isFinite [set]
/-- 等势关系原子。文献记号为 `|left| = |right|`。 -/
abbrev is_equinumerous_formula (left right : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isEquinumerous [left, right]
/-- 基数不强于关系原子。文献记号为 `|left| ≤ |right|`。 -/
abbrev cardinality_leq_formula (left right : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.cardinalityLeq [left, right]
/-- 基数严格弱于关系原子。文献记号为 `|left| < |right|`。 -/
abbrev cardinality_strict_less_formula (left right : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.cardinalityStrictLess [left, right]
/-- 戴德金有限谓词原子。 -/
abbrev is_dedekind_finite_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isDedekindFinite [set]
/-- 归纳集谓词原子。文献索引为 `Inf`。 -/
abbrev is_inductive_set_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isInductiveSet [set]
/-- 无界子集谓词原子；文献索引为 `WuJ`。 -/
abbrev is_unbounded_subset_formula (subset relation carrier : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isUnboundedSubset
    [subset, relation, carrier]
/-- 有界子集谓词原子；文献索引为 `YuJ`。 -/
abbrev is_bounded_subset_formula (subset relation carrier : SetTerm) :
    SetFormula :=
  Formula.rel
    RelationSymbol.isBoundedSubset
    [subset, relation, carrier]
/-- 无限集谓词原子；文献索引为 `WuQn`。 -/
abbrev is_infinite_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isInfinite [set]
/-- 可数集谓词原子；文献索引为 `KeSu`。 -/
abbrev is_countable_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isCountable [set]
/-- 不可数集谓词原子；文献索引为 `BKeS`。 -/
abbrev is_uncountable_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isUncountable [set]
/-- 与 `ω` 等势的可数无限集谓词原子；文献索引为 `KSWQ`。 -/
abbrev is_countably_infinite_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isCountablyInfinite [set]
/-- 遗传有限集谓词原子。文献索引为 `CDYQ`。 -/
abbrev is_hereditarily_finite_formula (set : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isHereditarilyFinite [set]
/-- `ω × ω` 上的典型严格关系原子。 -/
abbrev omega_pair_less_formula (left right : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.omegaPairLess [left, right]
/-- “是对象语言项编码”谓词原子。文献索引为 `Xng`。 -/
abbrev is_term_code_formula (code : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isTermCode [code]
/-- “是项编码”原子保持其代码项的 admissibility。 -/
theorem is_term_code_formula_admissible
    {code : SetTerm} (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (is_term_code_formula code) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hCode ArgsAdmissible.nil)
/-- “是对象语言原子公式编码”谓词原子。 -/
abbrev is_atomic_formula_code_formula (code : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isAtomicFormulaCode [code]
/-- “是对象语言公式编码”谓词原子。文献索引为 `BDS`。 -/
abbrev is_formula_code_formula (code : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isFormulaCode [code]
/-- “是公式编码”原子保持其代码项的 admissibility。 -/
theorem is_formula_code_formula_admissible
    {code : SetTerm} (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (is_formula_code_formula code) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hCode ArgsAdmissible.nil)
/-- 某变量的量词在公式编码中出现。 -/
abbrev quantifier_occurs_formula (boundVariable formula : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.quantifierOccurs
    [boundVariable, formula]
/-- 两个合法代码项组成合法的“量词出现”原子。 -/
theorem quantifier_occurs_formula_admissible
    {boundVariable formula : SetTerm} (hBoundVariable : Term.Admissible boundVariable SetSort.set) (hFormula : Term.Admissible formula SetSort.set) :
    Formula.Admissible (quantifier_occurs_formula boundVariable formula) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hBoundVariable (ArgsAdmissible.cons hFormula ArgsAdmissible.nil))
/-- 某变量在公式编码中受约束地出现。 -/
abbrev bound_occurrence_formula (boundVariable formula : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.boundOccurrence
    [boundVariable, formula]
/-- 两个合法代码项组成合法的“受约束出现”原子。 -/
theorem bound_occurrence_formula_admissible
    {boundVariable formula : SetTerm} (hBoundVariable : Term.Admissible boundVariable SetSort.set) (hFormula : Term.Admissible formula SetSort.set) :
    Formula.Admissible (bound_occurrence_formula boundVariable formula) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hBoundVariable (ArgsAdmissible.cons hFormula ArgsAdmissible.nil))
/-- 某变量在公式编码中自由出现。 -/
abbrev free_occurrence_formula (boundVariable formula : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.freeOccurrence
    [boundVariable, formula]
/-- 两个合法代码项组成合法的“自由出现”原子。 -/
theorem free_occurrence_formula_admissible
    {boundVariable formula : SetTerm} (hBoundVariable : Term.Admissible boundVariable SetSort.set) (hFormula : Term.Admissible formula SetSort.set) :
    Formula.Admissible (free_occurrence_formula boundVariable formula) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hBoundVariable (ArgsAdmissible.cons hFormula ArgsAdmissible.nil))
/-- 替换项可自由代入变量在公式中的自由出现位置。文献索引为 `KTHn`。 -/
abbrev is_substitutable_formula (boundVariable replacement formula : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isSubstitutable
    [boundVariable, replacement, formula]
/-- 三个合法代码项组成合法的“可代入”原子。 -/
theorem is_substitutable_formula_admissible
    {boundVariable replacement formula : SetTerm} (hBoundVariable :
      Term.Admissible boundVariable SetSort.set) (hReplacement :
      Term.Admissible replacement SetSort.set) (hFormula :
      Term.Admissible formula SetSort.set) :
    Formula.Admissible (is_substitutable_formula
        boundVariable replacement formula) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hBoundVariable (ArgsAdmissible.cons hReplacement (ArgsAdmissible.cons hFormula ArgsAdmissible.nil)))
/-- 对象是一条逻辑公理编码。文献索引为 `LJGL`。 -/
abbrev is_logical_axiom_code_formula (code : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isLogicalAxiomCode [code]
/-- 三个公式编码构成一次 modus ponens 步骤。 -/
abbrev modus_ponens_formula (premise implication conclusion : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.modusPonens
    [premise, implication, conclusion]
/-- `interpretation` 在非空论域 `carrier` 上解释给定非逻辑符号集。 -/
abbrev is_structure_formula (carrier interpretation symbols : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isStructure
    [carrier, interpretation, symbols]
/-- `evaluation` 是给定结构上的项求值函数。文献索引为 `FuZh`。 -/
abbrev is_term_evaluation_formula (carrier interpretation symbols evaluation : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isTermEvaluation
    [carrier, interpretation, symbols, evaluation]
/-- 指定项在给定结构、求值函数和变量赋值下的值。 -/
abbrev term_value_formula (carrier interpretation symbols evaluation assignment term value : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.termValue
    [carrier, interpretation, symbols, evaluation, assignment, term, value]
/-- 原子公式在给定结构与赋值下成立。 -/
abbrev atomic_satisfaction_formula (carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.atomicSatisfaction
    [carrier, interpretation, symbols, evaluation, assignment, formula]
/-- 公式在指定递归阶段、结构与赋值下成立。 -/
abbrev formula_satisfaction_at_stage_formula (stage carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.formulaSatisfactionAtStage
    [stage, carrier, interpretation, symbols, evaluation, assignment, formula]
/-- 公式在给定结构与赋值下成立。文献索引为 `MnZu`。 -/
abbrev formula_satisfaction_formula (carrier interpretation symbols evaluation assignment formula : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.formulaSatisfaction
    [carrier, interpretation, symbols, evaluation, assignment, formula]
/-- 公式在给定结构中对所有变量赋值为真。文献索引为 `ZhnS`。 -/
abbrev is_truth_formula (carrier interpretation symbols evaluation formula : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isTruth
    [carrier, interpretation, symbols, evaluation, formula]
/-- 给定结构是一个公式理论的模型。文献索引为 `ManZ`、`ZhSh`。 -/
abbrev is_model_formula (carrier interpretation symbols evaluation theory : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isModel
    [carrier, interpretation, symbols, evaluation, theory]
/-- 一个公式是给定理论在指定语言中的语义后承。文献索引为 `LJTL`。 -/
abbrev logical_consequence_formula (symbols theory conclusion : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.logicalConsequence
    [symbols, theory, conclusion]
/-- 一个公式在指定语言的所有结构中为真。文献索引为 `PBZS`。 -/
abbrev is_theorem_formula (symbols formula : SetTerm) :
    SetFormula :=
  Formula.rel RelationSymbol.isTheorem
    [symbols, formula]
namespace Symbols
/-- 单排序具体语言中的简写自由变量。 -/
scoped notation:max "x#" id:max => set_variable id
/-- 单排序具体语言中的简写 bound 变量。 -/
scoped notation:max "bₛ#" index:max => set_bound_variable index
/-- 定义扩张后的空集常量。 -/
scoped notation:max "∅ₘ" => empty_set_term
/-- 定义扩张后的一元幂集项。 -/
scoped notation:max "𝒫ₘ(" set ")" => power_set_term set
/-- 定义扩张后的无序对项。 -/
scoped notation:max "{" left ", " right "}ₘ" =>
  unordered_pair_term left right
/-- 定义扩张后的单点集项。 -/
scoped notation:max "{" element "}ₘ" =>
  singleton_term element
/-- 定义扩张后的 Kuratowski 有序对项。 -/
scoped notation:max "⟨" left ", " right "⟩ₘ" =>
  ordered_pair_term left right
/-- 有序对左投影。 -/
scoped notation:max "(" pair ")₀ₘ" =>
  left_projection_term pair
/-- 有序对右投影。 -/
scoped notation:max "(" pair ")₁ₘ" =>
  right_projection_term pair
/-- 有序对反转。 -/
scoped postfix:max "⁻¹ₘ" =>
  ordered_pair_reverse_term
/-- 定义扩张后的笛卡尔积。 -/
scoped infixl:75 " ×ₘ " =>
  cartesian_product_term
/-- 定义扩张后的关系定义域。 -/
scoped notation:max "domₘ(" relation ")" =>
  domain_term relation
/-- 定义扩张后的关系值域项；文献记号 `rng` 不进入公共语法。 -/
scoped notation:max "ranₘ(" relation ")" =>
  range_term relation
/-- 恒等映射项。 -/
scoped notation:max "Idₘ(" source ")" =>
  identity_term source
/-- 从源集到目标集的映射收集项。 -/
scoped notation:max "Mapₘ(" source ", " target ")" =>
  mapping_collection_term source target
/-- 关系 `∈` 在集合上的限制项。 -/
scoped notation:max "εₘ(" source ")" =>
  membership_relation_term source
/-- 映像项。 -/
scoped notation:max "imgₘ(" function ", " subset ")" =>
  image_term function subset
/-- 函数限制项。 -/
scoped notation:max "restrictₘ(" function ", " subset ")" =>
  restriction_term function subset
/-- 最小元项。 -/
scoped notation:max "minₘ(" relation ", " subset ")" =>
  minimum_term relation subset
/-- 最大元项。 -/
scoped notation:max "maxₘ(" relation ", " subset ")" =>
  maximum_term relation subset
/-- 严格初始段项；文献记号为 `W[point, relation, carrier]`。 -/
scoped notation:max "segₘ(" point ", " relation ", " carrier ")" =>
  initial_segment_term point relation carrier
/-- 关系在子集上的限制；区别于函数限制 `restrictₘ`。 -/
scoped notation:max "rel_restrictₘ(" relation ", " subset ")" =>
  relation_restriction_term relation subset
/-- 两个良序之间的规范比较映射。文献记号 `QR` 只保留为索引。 -/
scoped notation:max
  "wo_compareₘ(" sourceRelation ", " sourceCarrier ", "
    targetRelation ", " targetCarrier ")" =>
  well_order_comparison_map_term
    sourceRelation sourceCarrier targetRelation targetCarrier
/-- 带载体的线性序和。 -/
scoped notation:max
  "ord_sumₘ(" firstRelation ", " firstCarrier ", "
    secondRelation ", " secondCarrier ")" =>
  order_sum_term
    firstRelation firstCarrier secondRelation secondCarrier
/-- 带载体的词典序积。 -/
scoped notation:max
  "ord_prodₘ(" firstRelation ", " firstCarrier ", "
    secondRelation ", " secondCarrier ")" =>
  order_product_term
    firstRelation firstCarrier secondRelation secondCarrier
/-- 两个映射的直积。 -/
scoped notation:max
  "map_prodₘ(" firstFunction ", " secondFunction ")" =>
  mapping_product_term firstFunction secondFunction
/-- 最小差异点。 -/
scoped notation:max
  "min_diffₘ(" firstFunction ", " secondFunction ")" =>
  minimum_difference_term firstFunction secondFunction
/-- 指数序关系。 -/
scoped notation:max
  "idx_ordₘ(" sourceRelation ", " sourceCarrier ", "
    targetRelation ", " targetCarrier ")" =>
  index_order_term
    sourceRelation sourceCarrier targetRelation targetCarrier
/-- 幂集到二值函数空间的规范编码双射。 -/
scoped notation:max "chiₘ(" natural ")" =>
  power_set_bijection_term natural
/-- 对称差。 -/
scoped notation:max
  "sym_diffₘ(" left ", " right ")" =>
  symmetric_difference_term left right
/-- 归纳集族的公共归纳核；文献函数记号 `U` 只保留为索引。 -/
scoped notation:max "coreₘ(" set ")" =>
  inductive_core_term set
/-- 常元 `ω`。 -/
scoped notation:max "ωₘ" => omega_term
/-- 自然离散线性序的序型项；文献函数记号 `XuXn` 只保留为索引。 -/
scoped notation:max
  "ord_typeₘ(" relation ", " carrier ")" =>
  natural_order_type_term relation carrier
/-- 自然数子集的序型项；文献函数记号 `ZrBS` 只保留为索引。 -/
scoped notation:max "nat_subset_typeₘ(" subset ")" =>
  natural_subset_type_term subset
/-- 自然数加法；文献符号 `+` 只保留为索引。 -/
scoped infixl:65 " +ₘ " =>
  natural_addition_term
/-- 自然数乘法；文献符号 `·` 只保留为索引。 -/
scoped infixl:70 " *ₘ " =>
  natural_multiplication_term
/-- 自然数幂；文献幂运算符只保留为索引。 -/
scoped infixr:72 " ^ₘ " =>
  natural_exponentiation_term
/-- 给定集合上的有限序列空间。 -/
scoped notation:max "seq_spaceₘ(" source ")" =>
  finite_sequence_space_term source
/-- 有限序列的顺序合并；文献符号 `*` 只保留为索引。 -/
scoped infixr:65 " ⌢ₘ " =>
  finite_sequence_concatenation_term
/-- 给定集合上的非空有限序列空间；文献索引为 `YXXL`。 -/
scoped notation:max "seq₊_spaceₘ(" source ")" =>
  nonempty_finite_sequence_space_term source
/-- 有限序列族的有限折叠；文献符号 `⊕` 只保留为索引。 -/
scoped notation:max "flattenₘ(" sequence ")" =>
  finite_sequence_flatten_term sequence
/-- 递归序列空间。 -/
scoped notation:max
  "rec_seq_spaceₘ(" source ", " seed ", " recursion ")" =>
  recursive_sequence_space_term source seed recursion
/-- 以 `ω` 为索引的递归序列。 -/
scoped notation:max
  "ω_rec_seqₘ(" source ", " seed ", " recursion ")" =>
  omega_recursive_sequence_term source seed recursion
/-- 自然数截断减法。 -/
scoped infixl:65 " -ₘ " =>
  natural_difference_term
/-- Gödel 配对编码。 -/
scoped notation:max "godel_pairₘ(" pair ")" =>
  godel_pairing_term pair
/-- 传递闭包。 -/
scoped notation:max "tcₘ(" set ")" =>
  transitive_closure_term set
/-- 有限层级递归序列。 -/
scoped notation:max "Vseqₘ" =>
  finite_hierarchy_term
/-- 有限层级的并集 `V_ω`。 -/
scoped notation:max "Vωₘ" =>
  finite_universe_term
/-- 集合的有限子集收集。 -/
scoped notation:max "FinSubₘ(" source ")" =>
  finite_subset_collection_term source
/-- 一阶逻辑符号的编码集合。 -/
scoped notation:max "LogicSymₘ" =>
  logical_symbol_set_term
/-- 隶属关系符号的编码集合。 -/
scoped notation:max "MembershipSymₘ" =>
  membership_symbol_set_term
/-- 变量符号的编码集合。 -/
scoped notation:max "VarSymₘ" =>
  variable_symbol_set_term
/-- 常元符号的编码集合。 -/
scoped notation:max "ConstSymₘ" =>
  constant_symbol_set_term
/-- 函数符号的编码集合。 -/
scoped notation:max "FuncSymₘ" =>
  coded_function_symbol_set_term
/-- 谓词符号的编码集合。 -/
scoped notation:max "PredSymₘ" =>
  coded_predicate_symbol_set_term
/-- 对象语言项编码的集合。 -/
scoped notation:max "TermCodeₘ" =>
  term_code_set_term
/-- 非空有限项列编码的集合。 -/
scoped notation:max "TermSeqₘ" =>
  term_sequence_set_term
/-- 原子公式编码的集合。 -/
scoped notation:max "AtomicCodeₘ" =>
  atomic_formula_code_set_term
/-- 一阶公式编码的集合。 -/
scoped notation:max "FormulaCodeₘ" =>
  formula_code_set_term
/-- 等式原子编码运算。 -/
scoped notation:max
  "eq_codeₘ(" left ", " right ")" =>
  equality_formula_code_term left right
/-- 一般谓词应用原子编码运算。 -/
scoped notation:max
  "pred_codeₘ(" arity ", " index ", " arguments ")" =>
  predicate_formula_code_term arity index arguments
/-- 否定编码运算。 -/
scoped notation:max "neg_codeₘ(" body ")" =>
  negation_formula_code_term body
/-- 蕴含编码运算。 -/
scoped notation:max
  "imp_codeₘ(" left ", " right ")" =>
  implication_formula_code_term left right
/-- 全称量化编码运算。 -/
scoped notation:max
  "forall_codeₘ(" boundVariable ", " body ")" =>
  universal_formula_code_term boundVariable body
/-- 变量符号编码运算。 -/
scoped notation:max "var_codeₘ(" index ")" =>
  variable_code_term index
/-- 常元符号编码运算。 -/
scoped notation:max "const_codeₘ(" index ")" =>
  constant_code_term index
/-- 函数符号编码运算。 -/
scoped notation:max
  "func_sym_codeₘ(" arity ", " index ")" =>
  coded_function_symbol_code_operator_term arity index
/-- 谓词符号编码运算。 -/
scoped notation:max
  "pred_sym_codeₘ(" arity ", " index ")" =>
  coded_predicate_symbol_code_operator_term arity index
/-- 编码字符串中的变量替换。 -/
scoped notation:max
  "subst_codeₘ(" source ", " boundVariable ", " replacement ")" =>
  code_substitution_term source boundVariable replacement
/-- token 串对应的规范闭项代码。 -/
scoped notation:max "name_codeₘ(" source ")" =>
  canonical_name_code_term source
/-- 标准自然数项的对象 quotation 代码。 -/
scoped notation:max "num_name_codeₘ(" number ")" =>
  numeral_name_code_term number
/-- 编码字符串中出现的变量符号集合。 -/
scoped notation:max "varsₘ(" source ")" =>
  variable_collection_term source
/-- 变量自由出现的位置集合。 -/
scoped notation:max
  "free_posₘ(" boundVariable ", " formula ")" =>
  free_occurrence_positions_term boundVariable formula
/-- 蕴含分配公理模式集合。 -/
scoped notation:max "ImpDistribAxiomsₘ" =>
  implication_distribution_axiom_set_term
/-- 自蕴含公理模式集合。 -/
scoped notation:max "SelfImpAxiomsₘ" =>
  self_implication_axiom_set_term
/-- 弱化公理模式集合。 -/
scoped notation:max "WeakeningAxiomsₘ" =>
  weakening_axiom_set_term
/-- 矛盾前件公理模式集合。 -/
scoped notation:max "ContradictionAxiomsₘ" =>
  contradiction_axiom_set_term
/-- 经典逻辑公理模式集合。 -/
scoped notation:max "ClassicalAxiomsₘ" =>
  classical_axiom_set_term
/-- 爆炸律公理模式集合。 -/
scoped notation:max "ExplosionAxiomsₘ" =>
  explosion_axiom_set_term
/-- 分类讨论公理模式集合。 -/
scoped notation:max "CaseAnalysisAxiomsₘ" =>
  case_analysis_axiom_set_term
/-- 全称特化公理模式集合。 -/
scoped notation:max "SpecializationAxiomsₘ" =>
  specialization_axiom_set_term
/-- 全称量词分配公理模式集合。 -/
scoped notation:max "ForallDistribAxiomsₘ" =>
  quantifier_distribution_axiom_set_term
/-- 无关量词引入公理模式集合。 -/
scoped notation:max "VacuousForallAxiomsₘ" =>
  vacuous_quantifier_axiom_set_term
/-- 等同律公理模式集合。 -/
scoped notation:max "EqualitySubstAxiomsₘ" =>
  equality_substitution_axiom_set_term
/-- 恒等律公理模式集合。 -/
scoped notation:max "EqualityReflAxiomsₘ" =>
  equality_reflexivity_axiom_set_term
/-- 尚未作全称闭包的基础逻辑公理集合。 -/
scoped notation:max "BaseLogicAxiomsₘ" =>
  base_logical_axiom_set_term
/-- 完整逻辑公理编码集合。 -/
scoped notation:max "LogicAxiomsₘ" =>
  logical_axiom_set_term
/-- ZFC 外部公理 quotation 码的专用正向枚举集合。 -/
scoped notation:max "ZFCAxiomCodesₘ" =>
  zfc_axiom_code_set_term
/-- 固定目标理论完整公理 quotation 码的专用正向枚举集合。 -/
scoped notation:max "CompleteAxiomCodesₘ" =>
  complete_axiom_code_set_term
/-- 全部可用非逻辑符号编码。 -/
scoped notation:max "NonlogicalSymₘ" =>
  related_nonlogical_symbol_set_term
/-- 相对于给定非逻辑符号集的项编码。 -/
scoped notation:max "RelTermCodeₘ(" symbols ")" =>
  related_term_set_term symbols
/-- 相对于给定非逻辑符号集的公式编码。 -/
scoped notation:max "RelFormulaCodeₘ(" symbols ")" =>
  related_formula_set_term symbols
/-- 指定语言与递归深度下的公式编码阶段。 -/
scoped notation:max "FormulaStageₘ(" symbols ", " stage ")" =>
  related_formula_stage_set_term symbols stage
/-- 对象是一个项编码。 -/
scoped notation:max "term_codeₘ(" code ")" =>
  is_term_code_formula code
/-- 对象是一个原子公式编码。 -/
scoped notation:max "atomic_formula_codeₘ(" code ")" =>
  is_atomic_formula_code_formula code
/-- 对象是一个一阶公式编码。 -/
scoped notation:max "formula_codeₘ(" code ")" =>
  is_formula_code_formula code
/-- 变量量词在公式中出现。 -/
scoped notation:max
  "quantifier_occursₘ(" boundVariable ", " formula ")" =>
  quantifier_occurs_formula boundVariable formula
/-- 变量在公式中受约束出现。 -/
scoped notation:max
  "bound_occursₘ(" boundVariable ", " formula ")" =>
  bound_occurrence_formula boundVariable formula
/-- 变量在公式中自由出现。 -/
scoped notation:max
  "free_occursₘ(" boundVariable ", " formula ")" =>
  free_occurrence_formula boundVariable formula
/-- 项编码可自由代入公式中的指定变量。 -/
scoped notation:max
  "substitutableₘ(" boundVariable ", " replacement ", " formula ")" =>
  is_substitutable_formula boundVariable replacement formula
/-- 对象是一条逻辑公理编码。 -/
scoped notation:max "logical_axiom_codeₘ(" code ")" =>
  is_logical_axiom_code_formula code
/-- 一次 modus ponens 关系。 -/
scoped notation:max
  "modus_ponensₘ(" premise ", " implication ", " conclusion ")" =>
  modus_ponens_formula premise implication conclusion
/-- 给定论域与解释构成指定语言的结构。 -/
scoped notation:max
  "structureₘ(" carrier ", " interpretation ", " symbols ")" =>
  is_structure_formula carrier interpretation symbols
/-- 指定对象是给定结构上的项求值函数。 -/
scoped notation:max
  "term_evaluationₘ(" carrier ", " interpretation ", " symbols ", "
    evaluation ")" =>
  is_term_evaluation_formula carrier interpretation symbols evaluation
/-- 项在给定结构、求值函数和变量赋值下取指定值。 -/
scoped notation:max
  "term_valueₘ(" carrier ", " interpretation ", " symbols ", "
    evaluation ", " assignment ", " term ", " value ")" =>
  term_value_formula
    carrier interpretation symbols evaluation assignment term value
/-- 原子公式在给定结构与变量赋值下成立。 -/
scoped notation:max
  "atomic_satisfiesₘ(" carrier ", " interpretation ", " symbols ", "
    evaluation ", " assignment ", " formula ")" =>
  atomic_satisfaction_formula
    carrier interpretation symbols evaluation assignment formula
/-- 公式在指定递归阶段、结构与变量赋值下成立。 -/
scoped notation:max
  "satisfies_stageₘ(" stage ", " carrier ", " interpretation ", "
    symbols ", " evaluation ", " assignment ", " formula ")" =>
  formula_satisfaction_at_stage_formula
    stage carrier interpretation symbols evaluation assignment formula
/-- 公式在给定结构与变量赋值下成立。 -/
scoped notation:max
  "satisfies_codeₘ(" carrier ", " interpretation ", " symbols ", "
    evaluation ", " assignment ", " formula ")" =>
  formula_satisfaction_formula
    carrier interpretation symbols evaluation assignment formula
/-- 公式在给定结构中对所有变量赋值为真。 -/
scoped notation:max
  "true_inₘ(" carrier ", " interpretation ", " symbols ", "
    evaluation ", " formula ")" =>
  is_truth_formula carrier interpretation symbols evaluation formula
/-- 给定结构满足一个公式理论。 -/
scoped notation:max
  "model_ofₘ(" carrier ", " interpretation ", " symbols ", "
    evaluation ", " theory ")" =>
  is_model_formula carrier interpretation symbols evaluation theory
/-- 给定理论语义蕴涵一个公式。 -/
scoped notation:max
  "semantic_consequenceₘ(" symbols ", " theory ", " conclusion ")" =>
  logical_consequence_formula symbols theory conclusion
/-- 一个公式在给定语言的所有结构中为真。 -/
scoped notation:max "valid_codeₘ(" symbols ", " formula ")" =>
  is_theorem_formula symbols formula
/-- 序数子集在成员关系下的最小元；复用公共二元最小元算子。 -/
scoped notation:max "minεₘ(" ordinal ", " subset ")" =>
  minimum_term (membership_relation_term ordinal) subset
/-- 自然数子集在成员关系下的最大元；复用公共二元最大元算子。 -/
scoped notation:max "maxεₘ(" natural ", " subset ")" =>
  maximum_term (membership_relation_term natural) subset
/-- 关系逆；单个有序对的反转仍使用 postfix `⁻¹ₘ`。 -/
scoped notation:max "converseₘ(" relation ")" =>
  relation_converse_term relation
/-- 关系复合，纸面顺序为 `second ∘ first`。 -/
scoped infixr:75 " ∘ₘ " =>
  relation_composition_term
/-- 集合编码函数的对象语言求值。 -/
scoped infixl:80 " ·ₘ " =>
  function_application_term
/-- 定义扩张后的一元并集项。 -/
scoped prefix:max "⋃ₘ " => union_term
/-- 定义扩张后的二元并项。 -/
scoped infixl:65 " ∪ₘ " => binary_union_term
/-- 定义扩张后的一元后继项。 -/
scoped notation:max "Sₘ(" set ")" => successor_term set
/-- 定义扩张后的非空族交集项。 -/
scoped prefix:max "⋂ₘ " => intersection_term
/-- 定义扩张后的二元交项。 -/
scoped infixl:70 " ∩ₘ " => binary_intersection_term
scoped infix:70 " ∈ₘ " => membership_formula
scoped infix:70 " ⊆ₘ " => subset_formula
scoped infix:70 " ⊂ₘ " => proper_subset_formula
/-- 有穷集谓词。 -/
scoped notation:max "finiteₘ(" set ")" =>
  is_finite_formula set
/-- 集合等势。 -/
scoped infix:70 " ≈ₘ " =>
  is_equinumerous_formula
/-- 集合基数不强于。 -/
scoped infix:70 " ≼ₘ " =>
  cardinality_leq_formula
/-- 集合基数严格弱于。 -/
scoped infix:70 " ≺ₘ " =>
  cardinality_strict_less_formula
/-- 戴德金有限集谓词。 -/
scoped notation:max "dedekind_finiteₘ(" set ")" =>
  is_dedekind_finite_formula set
/-- 归纳集谓词。 -/
scoped notation:max "inductiveₘ(" set ")" =>
  is_inductive_set_formula set
/-- 子集在指定关系与载体下无界。 -/
scoped notation:max
  "unboundedₘ(" subset ", " relation ", " carrier ")" =>
  is_unbounded_subset_formula subset relation carrier
/-- 子集在指定关系与载体下有界。 -/
scoped notation:max
  "boundedₘ(" subset ", " relation ", " carrier ")" =>
  is_bounded_subset_formula subset relation carrier
/-- 无限集。 -/
scoped notation:max "infiniteₘ(" set ")" =>
  is_infinite_formula set
/-- 可数集。 -/
scoped notation:max "countableₘ(" set ")" =>
  is_countable_formula set
/-- 不可数集。 -/
scoped notation:max "uncountableₘ(" set ")" =>
  is_uncountable_formula set
/-- 可数无限集。 -/
scoped notation:max "countably_infiniteₘ(" set ")" =>
  is_countably_infinite_formula set
/-- 遗传有限集。 -/
scoped notation:max "hereditarily_finiteₘ(" set ")" =>
  is_hereditarily_finite_formula set
/-- `ω × ω` 上的典型严格关系。 -/
scoped infix:70 " <ωₘ " =>
  omega_pair_less_formula
end Symbols
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
