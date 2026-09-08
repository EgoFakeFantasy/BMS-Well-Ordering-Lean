import YesMetaZFC.Logic.Syntax
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
  | zfcAxiomCodeSet
  | completeAxiomCodeSet
  | syntaxNumeralCode
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
  | isTermCodeAt
  | isTermListCodeAt
  | isFormulaCodeAt
  | syntaxTransform
  | freeVariableOccurs
  | isLogicalAxiomCode
  | modusPonens
  | isStructure
  | termValue
  | atomicSatisfaction
  | formulaSatisfactionAtStage
  | formulaSatisfaction
  | isTruth
  | isModel
  | logicalConsequence
  | isTheorem
  | isRelatedTermCodeAt
  | isRelatedTermListCodeAt
  | isRelatedFormulaCodeAt
  | termListValue
  deriving DecidableEq, Repr
/-- 带有基本集合构造和关系谓词的具体一阶签名。 -/
abbrev signature : Signature where
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
    | .minimumDifference => [.set, .set, .set, .set]
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
    | .godelPairing => [.set, .set]
    | .transitiveClosure => [.set]
    | .finiteHierarchy => []
    | .finiteUniverse => []
    | .finiteSubsetCollection => [.set]
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
    | .zfcAxiomCodeSet => []
    | .completeAxiomCodeSet => []
    | .syntaxNumeralCode => [.set]
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
    | .zfcAxiomCodeSet => .set
    | .completeAxiomCodeSet => .set
    | .syntaxNumeralCode => .set
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
    | .isTermCodeAt => [.set, .set]
    | .isTermListCodeAt => [.set, .set, .set]
    | .isFormulaCodeAt => [.set, .set]
    | .syntaxTransform =>
      [.set, .set, .set, .set, .set, .set, .set]
    | .freeVariableOccurs => [.set, .set, .set]
    | .isLogicalAxiomCode => [.set]
    | .modusPonens => [.set, .set, .set]
    | .isStructure => [.set, .set, .set]
    | .termValue => [.set, .set, .set, .set, .set, .set]
    | .atomicSatisfaction => [.set, .set, .set, .set, .set]
    | .formulaSatisfactionAtStage =>
      [.set, .set, .set, .set, .set, .set]
    | .formulaSatisfaction => [.set, .set, .set, .set, .set]
    | .isTruth => [.set, .set, .set, .set]
    | .isModel => [.set, .set, .set, .set]
    | .logicalConsequence => [.set, .set, .set]
    | .isTheorem => [.set, .set]
    | .isRelatedTermCodeAt => [.set, .set, .set]
    | .isRelatedTermListCodeAt => [.set, .set, .set, .set]
    | .isRelatedFormulaCodeAt => [.set, .set, .set]
    | .termListValue =>
      [.set, .set, .set, .set, .set, .set, .set]
instance signature_sort_decidable_eq : DecidableEq signature.SortSymbol := by
  unfold signature
  infer_instance
instance signature_relation_decidable_eq : DecidableEq signature.RelSymbol := by
  unfold signature
  infer_instance
instance signature_function_decidable_eq : DecidableEq signature.FuncSymbol := by
  unfold signature
  infer_instance
/-- 当前具体语言中的排序上下文。 -/
abbrev SetContext := SortContext signature
/-- 当前具体语言中的内在良构项。 -/
abbrev SetTerm (bound free : SetContext) :=
  Term signature bound free SetSort.set
/-- 当前具体语言中的内在良构公式。 -/
abbrev SetFormula (bound free : SetContext) :=
  Formula signature bound free
/-- 没有外层 bound 变量的集合项。 -/
abbrev SetOpenTerm (free : SetContext) := SetTerm [] free
/-- 没有外层 bound 变量的集合论公式。 -/
abbrev SetOpenFormula (free : SetContext) := SetFormula [] free
/-- 集合论闭句。 -/
abbrev SetSentence := SetFormula [] []
/-- 当前具体语言中的非逻辑理论。 -/
abbrev SetTheory := Theory signature

variable {bound free : SetContext}

local notation "SetTerm" => BasicSetTheory.SetTerm bound free
local notation "SetFormula" => BasicSetTheory.SetFormula bound free

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

/-- 单排序语言中的 free 变量项；上下文成员关系由类型携带。 -/
abbrev set_variable (entry : Variable free SetSort.set) : SetTerm :=
  vₘ[entry]
/-- 单排序语言中的 bound 变量项；作用域由类型携带。 -/
abbrev set_bound_variable (entry : Variable bound SetSort.set) : SetTerm :=
  bₘ[entry]
/-- 定义扩张后的空集常量项。 -/
abbrev empty_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.emptySet]()
/-- 定义扩张后的一元幂集项。 -/
abbrev power_set_term (set : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.powerSet](set)
/-- 定义扩张后的二元无序对项。 -/
abbrev unordered_pair_term (left right : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.unorderedPair](left, right)
/-- 定义扩张后的一元单点集项。 -/
abbrev singleton_term (element : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.singleton](element)
/-- 定义扩张后的二元有序对项。 -/
abbrev ordered_pair_term (left right : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.orderedPair](left, right)
/-- 定义扩张后的有序对左投影项。 -/
abbrev left_projection_term (pair : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.leftProjection](pair)
/-- 定义扩张后的有序对右投影项。 -/
abbrev right_projection_term (pair : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.rightProjection](pair)
/-- 定义扩张后的有序对反转项。 -/
abbrev ordered_pair_reverse_term (pair : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.orderedPairReverse](pair)
/-- 定义扩张后的笛卡尔积项。 -/
abbrev cartesian_product_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.cartesianProduct](left, right)
/-- 定义扩张后的关系定义域项。 -/
abbrev domain_term (relation : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.domain](relation)
/-- 定义扩张后的关系值域项。文献中的 `rng` 只保留为索引，公共接口使用 `range`。 -/
abbrev range_term (relation : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.range](relation)
/-- 定义扩张后的关系逆项；与单个有序对的反转项严格区分。 -/
abbrev relation_converse_term (relation : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.relationConverse](relation)
/-- 定义扩张后的关系复合项，参数顺序对应 `second ∘ first`。 -/
abbrev relation_composition_term (second first : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.relationComposition](second, first)
/-- 定义扩张后的函数求值项。 -/
abbrev function_application_term (function argument : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.application](function, argument)
/-- 定义扩张后的一元并集项。 -/
abbrev union_term (set : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.union](set)
/-- 定义扩张后的二元并项。 -/
abbrev binary_union_term (left right : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.binaryUnion](left, right)
/-- 定义扩张后的一元后继项。 -/
abbrev successor_term (set : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.successor](set)
/-- 定义扩张后的非空族交集项。 -/
abbrev intersection_term (set : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.intersection](set)
/-- 定义扩张后的二元交项。 -/
abbrev binary_intersection_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.binaryIntersection](left, right)
/-- 定义扩张后的恒等映射项。 -/
abbrev identity_term (source : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.identity](source)
/-- 定义扩张后的映射收集项。 -/
abbrev mapping_collection_term (source target : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.mappingCollection](source, target)
/-- 定义扩张后的成员关系限制项。 -/
abbrev membership_relation_term (source : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.membershipRelation](source)
/-- 定义扩张后的映像项。 -/
abbrev image_term (function subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.image](function, subset)
/-- 定义扩张后的函数限制项。 -/
abbrev restriction_term (function subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.restriction](function, subset)
/-- 定义扩张后的最小元项。 -/
abbrev minimum_term (relation subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.minimum](relation, subset)
/-- 定义扩张后的最大元项。 -/
abbrev maximum_term (relation subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.maximum](relation, subset)
/-- 指定点在严格序下的初始段项。 -/
abbrev initial_segment_term (point relation carrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.initialSegment](point, relation, carrier)
/-- 关系在指定子集上的限制项。 -/
abbrev relation_restriction_term (relation subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.relationRestriction](relation, subset)
/-- 两个良序之间的规范比较映射项。文献索引为 `QR`。 -/
abbrev well_order_comparison_map_term (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.wellOrderComparisonMap](
    sourceRelation, sourceCarrier, targetRelation, targetCarrier)
/-- 两个带载体线性序的序和项。文献记号 `⊕` 只保留为索引。 -/
abbrev order_sum_term (firstRelation firstCarrier secondRelation secondCarrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.orderSum](
    firstRelation, firstCarrier, secondRelation, secondCarrier)
/-- 两个带载体线性序的词典序积项。文献记号 `⊗` 只保留为索引。 -/
abbrev order_product_term (firstRelation firstCarrier secondRelation secondCarrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.orderProduct](
    firstRelation, firstCarrier, secondRelation, secondCarrier)
/-- 定义扩张后的映射直积项；文献记号 `⊗` 只保留为索引。 -/
abbrev mapping_product_term (firstFunction secondFunction : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.mappingProduct](firstFunction, secondFunction)
/-- 定义扩张后的最小差异点项。 -/
abbrev minimum_difference_term (sourceRelation sourceCarrier firstFunction secondFunction : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.minimumDifference](sourceRelation, sourceCarrier, firstFunction, secondFunction)
/-- 定义扩张后的指数序关系项。 -/
abbrev index_order_term (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.indexOrder](
    sourceRelation, sourceCarrier, targetRelation, targetCarrier)
/-- 定义扩张后的幂集编码双射项。 -/
abbrev power_set_bijection_term (natural : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.powerSetBijection](natural)
/-- 定义扩张后的对称差项。 -/
abbrev symmetric_difference_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.symmetricDifference](left, right)
/-- 定义扩张后的归纳核项；文献中的 `U` 仅保留为索引。 -/
abbrev inductive_core_term (set : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.inductiveCore](set)
/-- 定义扩张后的常元 `ω`。 -/
abbrev omega_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.omega]()
/-- 关系在自然离散线性序上的序型项。 -/
abbrev natural_order_type_term (relation carrier : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.naturalOrderType](relation, carrier)
/-- 自然数子集的序型项。 -/
abbrev natural_subset_type_term (subset : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.naturalSubsetType](subset)
/-- 自然数加法项。 -/
abbrev natural_addition_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.naturalAddition](left, right)
/-- 自然数乘法项。 -/
abbrev natural_multiplication_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.naturalMultiplication](left, right)
/-- 自然数幂项。 -/
abbrev natural_exponentiation_term (base exponent : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.naturalExponentiation](base, exponent)
/-- 给定集合上的有限序列空间项。 -/
abbrev finite_sequence_space_term (source : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.finiteSequenceSpace](source)
/-- 两个有限序列的顺序合并项。 -/
abbrev finite_sequence_concatenation_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.finiteSequenceConcatenation](left, right)
/-- 给定集合上的非空有限序列空间项。 -/
abbrev nonempty_finite_sequence_space_term (source : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.nonemptyFiniteSequenceSpace](source)
/-- 有限序列族的有限折叠项。 -/
abbrev finite_sequence_flatten_term (sequence : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.finiteSequenceFlatten](sequence)
/-- 递归序列空间项。 -/
abbrev recursive_sequence_space_term (source seed recursion : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.recursiveSequenceSpace](source, seed, recursion)
/-- 以 `ω` 为索引的递归序列项。 -/
abbrev omega_recursive_sequence_term (source seed recursion : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.omegaRecursiveSequence](source, seed, recursion)
/-- 自然数截断减法项。 -/
abbrev natural_difference_term (left right : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.naturalDifference](left, right)
/-- 二元 Gödel 配数项；不再先构造对象有序对。 -/
abbrev godel_pairing_term (left right : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.godelPairing](left, right)
/-- 标准有限 numeral 的结构码函数项。 -/
abbrev syntax_numeral_code_term (number : SetTerm) : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.syntaxNumeralCode](number)
/-- 定义扩张后的传递闭包项。文献索引为 `CDBB`。 -/
abbrev transitive_closure_term (set : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.transitiveClosure](set)
/-- 由空集和幂集递归生成的有限层级序列。 -/
abbrev finite_hierarchy_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.finiteHierarchy]()
/-- 有限层级的并集常元，即通常记作 `V_ω` 的集合。 -/
abbrev finite_universe_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.finiteUniverse]()
/-- 给定集合的所有有限子集组成的集合。文献索引为 `YXZJ`。 -/
abbrev finite_subset_collection_term (source : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.finiteSubsetCollection](source)
/-- 第一类蕴含分配公理模式的编码集合。 -/
abbrev implication_distribution_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.implicationDistributionAxiomSet]()
/-- 自蕴含公理模式的编码集合。 -/
abbrev self_implication_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.selfImplicationAxiomSet]()
/-- 弱化公理模式的编码集合。 -/
abbrev weakening_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.weakeningAxiomSet]()
/-- 矛盾前件公理模式的编码集合。 -/
abbrev contradiction_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.contradictionAxiomSet]()
/-- 经典逻辑公理模式的编码集合。 -/
abbrev classical_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.classicalAxiomSet]()
/-- 爆炸律公理模式的编码集合。 -/
abbrev explosion_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.explosionAxiomSet]()
/-- 分类讨论公理模式的编码集合。 -/
abbrev case_analysis_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.caseAnalysisAxiomSet]()
/-- 全称特化公理模式的编码集合。 -/
abbrev specialization_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.specializationAxiomSet]()
/-- 全称量词分配公理模式的编码集合。 -/
abbrev quantifier_distribution_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.quantifierDistributionAxiomSet]()
/-- 无关量词引入公理模式的编码集合。 -/
abbrev vacuous_quantifier_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.vacuousQuantifierAxiomSet]()
/-- 等同律公理模式的编码集合。 -/
abbrev equality_substitution_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.equalitySubstitutionAxiomSet]()
/-- 恒等律公理模式的编码集合。 -/
abbrev equality_reflexivity_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.equalityReflexivityAxiomSet]()
/-- 未作全称闭包的基础逻辑公理编码集合。 -/
abbrev base_logical_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.baseLogicalAxiomSet]()
/-- 在全称量化下闭合后的逻辑公理编码集合。 -/
abbrev logical_axiom_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.logicalAxiomSet]()
/-- ZFC 外部公理 quotation 码的专用正向枚举集合。 -/
abbrev zfc_axiom_code_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.zfcAxiomCodeSet]()
/--
固定目标理论完整公理 quotation 码的专用正向枚举集合。
它与只枚举基础 ZFC 公理的 `zfc_axiom_code_set_term` 分离；具体目标理论由使用该项的
元理论模块明确给出。
-/
abbrev complete_axiom_code_set_term : SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.completeAxiomCodeSet]()
/-- 当前形式语言可使用的全部非逻辑符号编码。文献索引为 `XGFH`。 -/
abbrev related_nonlogical_symbol_set_term :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.relatedNonlogicalSymbolSet]()
/-- 仅使用给定非逻辑符号集的项编码集合。文献索引为 `XXng`。 -/
abbrev related_term_set_term (symbols : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.relatedTermSet](symbols)
/-- 仅使用给定非逻辑符号集的公式编码集合。文献索引为 `XBDS`。 -/
abbrev related_formula_set_term (symbols : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.relatedFormulaSet](symbols)
/-- 指定语言中递归深度不超过给定自然数的公式编码。文献索引为 `BDS*`。 -/
abbrev related_formula_stage_set_term (symbols stage : SetTerm) :
    SetTerm :=
  𝒇ₘ[signature; FunctionSymbol.relatedFormulaStageSet](symbols, stage)
/-- 隶属关系原子。 -/
abbrev membership_formula (element set : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.membership](element, set)
/-- 子集关系原子。 -/
abbrev subset_formula (left right : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.subset](left, right)
/-- 真子集关系原子。 -/
abbrev proper_subset_formula (left right : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.properSubset](left, right)
/-- 有序对谓词原子。 -/
abbrev is_ordered_pair_formula (pair : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.isOrderedPair](pair)
/-- 关系谓词原子。 -/
abbrev is_relation_formula (relation : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.isRelation](relation)
/-- 等价关系谓词原子；文献索引为 `DJGX`。 -/
abbrev is_equivalence_relation_formula (relation : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isEquivalenceRelation](relation)
/-- 集合编码函数谓词原子；文献索引为 `HanS`。 -/
abbrev is_function_formula (function : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isFunction](function)
/-- 从指定定义域映入目标集合的映射谓词原子；文献索引为 `InSh`。 -/
abbrev is_mapping_formula (function source target : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isMapping](function, source, target)
/-- 单射映射谓词原子。文献索引为 `DanS`。 -/
abbrev is_injective_formula (function source target : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isInjective](function, source, target)
/-- 满射映射谓词原子。文献索引为 `ManS`。 -/
abbrev is_surjective_formula (function source target : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isSurjective](function, source, target)
/-- 双射映射谓词原子。文献索引为 `ShuS`。 -/
abbrev is_bijection_formula (function source target : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isBijection](function, source, target)
/-- 传递集谓词原子。文献索引为 `ChuD`。 -/
abbrev is_transitive_set_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isTransitiveSet](set)
/-- 线性序谓词原子。文献索引为 `XiXn`。 -/
abbrev is_linear_order_formula (relation carrier : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isLinearOrder](relation, carrier)
/-- 序同构映射谓词原子。文献索引为 `TGYS`。 -/
abbrev is_order_isomorphism_formula (function sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isOrderIsomorphism](function, sourceRelation, sourceCarrier, targetRelation, targetCarrier)
/-- 序同构关系谓词原子。文献索引为 `XuTG`。 -/
abbrev is_order_isomorphic_formula (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isOrderIsomorphic](sourceRelation, sourceCarrier, targetRelation, targetCarrier)
/-- 序嵌入映射谓词原子。文献索引为 `QRYS`。 -/
abbrev is_order_embedding_formula (function sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isOrderEmbedding](function, sourceRelation, sourceCarrier, targetRelation, targetCarrier)
/-- 序可嵌入关系谓词原子。文献索引为 `XuQR`。 -/
abbrev is_order_embeddable_formula (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isOrderEmbeddable](sourceRelation, sourceCarrier, targetRelation, targetCarrier)
/-- 自然离散线性序谓词原子。文献索引为 `Zrlx`。 -/
abbrev is_natural_discrete_linear_order_formula (relation carrier : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isNaturalDiscreteLinearOrder](relation, carrier)
/-- 良序谓词原子。文献索引为 `ZX`。 -/
abbrev is_well_order_formula (relation carrier : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isWellOrder](relation, carrier)
/-- 序数谓词原子。文献索引为 `XuS`。 -/
abbrev is_ordinal_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isOrdinal](set)
/-- 自然数谓词原子。文献索引为 `ZRS`。 -/
abbrev is_natural_number_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isNaturalNumber](set)
/-- 有穷集谓词原子。文献索引为 `YuQn`。 -/
abbrev is_finite_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isFinite](set)
/-- 等势关系原子。文献记号为 `|left| = |right|`。 -/
abbrev is_equinumerous_formula (left right : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isEquinumerous](left, right)
/-- 基数不强于关系原子。文献记号为 `|left| ≤ |right|`。 -/
abbrev cardinality_leq_formula (left right : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.cardinalityLeq](left, right)
/-- 基数严格弱于关系原子。文献记号为 `|left| < |right|`。 -/
abbrev cardinality_strict_less_formula (left right : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.cardinalityStrictLess](left, right)
/-- 戴德金有限谓词原子。 -/
abbrev is_dedekind_finite_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isDedekindFinite](set)
/-- 归纳集谓词原子。文献索引为 `Inf`。 -/
abbrev is_inductive_set_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isInductiveSet](set)
/-- 无界子集谓词原子；文献索引为 `WuJ`。 -/
abbrev is_unbounded_subset_formula (subset relation carrier : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isUnboundedSubset](subset, relation, carrier)
/-- 有界子集谓词原子；文献索引为 `YuJ`。 -/
abbrev is_bounded_subset_formula (subset relation carrier : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isBoundedSubset](subset, relation, carrier)
/-- 无限集谓词原子；文献索引为 `WuQn`。 -/
abbrev is_infinite_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isInfinite](set)
/-- 可数集谓词原子；文献索引为 `KeSu`。 -/
abbrev is_countable_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isCountable](set)
/-- 不可数集谓词原子；文献索引为 `BKeS`。 -/
abbrev is_uncountable_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isUncountable](set)
/-- 与 `ω` 等势的可数无限集谓词原子；文献索引为 `KSWQ`。 -/
abbrev is_countably_infinite_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isCountablyInfinite](set)
/-- 遗传有限集谓词原子。文献索引为 `CDYQ`。 -/
abbrev is_hereditarily_finite_formula (set : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isHereditarilyFinite](set)
/-- `ω × ω` 上的典型严格关系原子。 -/
abbrev omega_pair_less_formula (left right : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.omegaPairLess](left, right)
/-- 在 de Bruijn 深度 `depth` 下是内在良构项码。 -/
abbrev is_term_code_at_formula (depth code : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.isTermCodeAt](depth, code)
/-- 在 de Bruijn 深度 `depth` 下是内在良构参数列码。 -/
abbrev is_term_list_code_at_formula (depth length code : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.isTermListCodeAt](depth, length, code)
/-- 在 de Bruijn 深度 `depth` 下是内在良构公式码。 -/
abbrev is_formula_code_at_formula (depth code : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.isFormulaCodeAt](depth, code)
/-- 统一的结构语法变换图。 -/
abbrev syntax_transform_formula
    (kind operation depth variableIndex replacement source target : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.syntaxTransform](
    kind, operation, depth, variableIndex, replacement, source, target)
/-- 指定 free 变量在结构公式码中出现。 -/
abbrev free_variable_occurs_formula
    (kind variableIndex code : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.freeVariableOccurs](kind, variableIndex, code)
/-- 对象是一条逻辑公理编码。文献索引为 `LJGL`。 -/
abbrev is_logical_axiom_code_formula (code : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isLogicalAxiomCode](code)
/-- 三个公式编码构成一次 modus ponens 步骤。 -/
abbrev modus_ponens_formula (premise implication conclusion : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.modusPonens](premise, implication, conclusion)
/-- `interpretation` 在非空论域 `carrier` 上解释给定非逻辑符号集。 -/
abbrev is_structure_formula (carrier interpretation symbols : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isStructure](carrier, interpretation, symbols)
/-- 指定项在给定结构和变量赋值下的值。 -/
abbrev term_value_formula (carrier interpretation symbols assignment term value : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.termValue](carrier, interpretation, symbols, assignment, term, value)
/-- 原子公式在给定结构与赋值下成立。 -/
abbrev atomic_satisfaction_formula (carrier interpretation symbols assignment formula : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.atomicSatisfaction](carrier, interpretation, symbols, assignment, formula)
/-- 公式在指定递归阶段、结构与赋值下成立。 -/
abbrev formula_satisfaction_at_stage_formula (stage carrier interpretation symbols assignment formula : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.formulaSatisfactionAtStage](stage, carrier, interpretation, symbols, assignment, formula)
/-- 公式在给定结构与赋值下成立。文献索引为 `MnZu`。 -/
abbrev formula_satisfaction_formula (carrier interpretation symbols assignment formula : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.formulaSatisfaction](carrier, interpretation, symbols, assignment, formula)
/-- 公式在给定结构中对所有变量赋值为真。文献索引为 `ZhnS`。 -/
abbrev is_truth_formula (carrier interpretation symbols formula : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isTruth](carrier, interpretation, symbols, formula)
/-- 给定结构是一个公式理论的模型。文献索引为 `ManZ`、`ZhSh`。 -/
abbrev is_model_formula (carrier interpretation symbols theory : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isModel](carrier, interpretation, symbols, theory)
/-- 一个公式是给定理论在指定语言中的语义后承。文献索引为 `LJTL`。 -/
abbrev logical_consequence_formula (symbols theory conclusion : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.logicalConsequence](symbols, theory, conclusion)
/-- 一个公式在指定语言的所有结构中为真。文献索引为 `PBZS`。 -/
abbrev is_theorem_formula (symbols formula : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.isTheorem](symbols, formula)
/-- 指定非逻辑符号集、de Bruijn 深度下是项码。 -/
abbrev is_related_term_code_at_formula
    (symbols depth code : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.isRelatedTermCodeAt](symbols, depth, code)
/-- 指定非逻辑符号集、深度和长度下是参数列码。 -/
abbrev is_related_term_list_code_at_formula
    (symbols depth length code : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.isRelatedTermListCodeAt](
    symbols, depth, length, code)
/-- 指定非逻辑符号集、de Bruijn 深度下是公式码。 -/
abbrev is_related_formula_code_at_formula
    (symbols depth code : SetTerm) : SetFormula :=
  ℛₘ[signature; RelationSymbol.isRelatedFormulaCodeAt](symbols, depth, code)
/-- 结构参数列在给定赋值下的逐项值关系。 -/
abbrev term_list_value_formula
    (carrier interpretation symbols assignment length arguments values : SetTerm) :
    SetFormula :=
  ℛₘ[signature; RelationSymbol.termListValue](
    carrier, interpretation, symbols, assignment,
    length, arguments, values)
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
  "min_diffₘ(" sourceRelation ", " sourceCarrier ", " firstFunction ", " secondFunction ")" =>
  minimum_difference_term sourceRelation sourceCarrier firstFunction secondFunction
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
/-- 二元 Gödel 配数。 -/
scoped notation:max "godel_pairₘ(" left ", " right ")" =>
  godel_pairing_term left right
scoped notation:max "syntax_num_codeₘ(" number ")" =>
  syntax_numeral_code_term number
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
/-- 在给定 de Bruijn 深度下是项码。 -/
scoped notation:max "term_code_atₘ(" depth ", " code ")" =>
  is_term_code_at_formula depth code
/-- 在给定 de Bruijn 深度下是参数列码。 -/
scoped notation:max "term_list_code_atₘ(" depth ", " length ", " code ")" =>
  is_term_list_code_at_formula depth length code
/-- 在给定 de Bruijn 深度下是公式码。 -/
scoped notation:max "formula_code_atₘ(" depth ", " code ")" =>
  is_formula_code_at_formula depth code
/-- 没有外层 binder 的项码。 -/
scoped notation:max "term_codeₘ(" code ")" =>
  is_term_code_at_formula empty_set_term code
/-- 没有外层 binder 的公式码。 -/
scoped notation:max "formula_codeₘ(" code ")" =>
  is_formula_code_at_formula empty_set_term code
/-- 统一结构语法变换图。 -/
scoped notation:max
  "syntax_transformₘ(" kind ", " operation ", " depth ", " variableIndex ", "
    replacement ", " source ", " target ")" =>
  syntax_transform_formula
    kind operation depth variableIndex replacement source target
/-- free 变量在公式码中出现。 -/
scoped notation:max
  "free_var_occursₘ(" kind ", " variableIndex ", " code ")" =>
  free_variable_occurs_formula kind variableIndex code
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
/-- 项在给定结构和变量赋值下取指定值。 -/
scoped notation:max
  "term_valueₘ(" carrier ", " interpretation ", " symbols ", "
    assignment ", " term ", " value ")" =>
  term_value_formula carrier interpretation symbols assignment term value
/-- 原子公式在给定结构与变量赋值下成立。 -/
scoped notation:max
  "atomic_satisfiesₘ(" carrier ", " interpretation ", " symbols ", "
    assignment ", " formula ")" =>
  atomic_satisfaction_formula carrier interpretation symbols assignment formula
/-- 公式在指定递归阶段、结构与变量赋值下成立。 -/
scoped notation:max
  "satisfies_stageₘ(" stage ", " carrier ", " interpretation ", "
    symbols ", " assignment ", " formula ")" =>
  formula_satisfaction_at_stage_formula
    stage carrier interpretation symbols assignment formula
/-- 公式在给定结构与变量赋值下成立。 -/
scoped notation:max
  "satisfies_codeₘ(" carrier ", " interpretation ", " symbols ", "
    assignment ", " formula ")" =>
  formula_satisfaction_formula carrier interpretation symbols assignment formula
/-- 公式在给定结构中对所有变量赋值为真。 -/
scoped notation:max
  "true_inₘ(" carrier ", " interpretation ", " symbols ", " formula ")" =>
  is_truth_formula carrier interpretation symbols formula
/-- 给定结构满足一个公式理论。 -/
scoped notation:max
  "model_ofₘ(" carrier ", " interpretation ", " symbols ", " theory ")" =>
  is_model_formula carrier interpretation symbols theory
/-- 给定理论语义蕴涵一个公式。 -/
scoped notation:max
  "semantic_consequenceₘ(" symbols ", " theory ", " conclusion ")" =>
  logical_consequence_formula symbols theory conclusion
/-- 一个公式在给定语言的所有结构中为真。 -/
scoped notation:max "valid_codeₘ(" symbols ", " formula ")" =>
  is_theorem_formula symbols formula
/-- 指定语言中的相对项码关系。 -/
scoped notation:max
  "related_term_code_atₘ(" symbols ", " depth ", " code ")" =>
  is_related_term_code_at_formula symbols depth code
/-- 指定语言中的相对参数列码关系。 -/
scoped notation:max
  "related_term_list_code_atₘ(" symbols ", " depth ", " length ", " code ")" =>
  is_related_term_list_code_at_formula symbols depth length code
/-- 指定语言中的相对公式码关系。 -/
scoped notation:max
  "related_formula_code_atₘ(" symbols ", " depth ", " code ")" =>
  is_related_formula_code_at_formula symbols depth code
/-- 结构参数列的逐项求值关系。 -/
scoped notation:max
  "term_list_valueₘ(" carrier ", " interpretation ", " symbols ", "
    assignment ", " length ", " arguments ", " values ")" =>
  term_list_value_formula carrier interpretation symbols assignment
    length arguments values
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
