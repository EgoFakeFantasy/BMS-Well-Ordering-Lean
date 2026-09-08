import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatPacket
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.SyntaxCoding

/-!
# 自然数数据树到内在语法的解码

符号编号沿用 `FunctionSymbol.ctorIdx` 与 `RelationSymbol.ctorIdx`。
项标签为 bound/free/application 三类；公式标签沿用宿主 `SyntaxCoding.FormulaCode`
的构造子顺序。越界变量、未知符号、参数数目错误与多余子树均返回 `none`。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxDecode

open Nonlogical.BasicSetTheory NatPacket
open QuineEncoding.SyntaxCoding
set_option autoImplicit false

def functionSymbols : Array FunctionSymbol := #[
  .emptySet,
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
  .zfcAxiomCodeSet,
  .completeAxiomCodeSet,
  .syntaxNumeralCode]

def relationSymbols : Array RelationSymbol := #[
  .membership,
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
  .isTermCodeAt,
  .isTermListCodeAt,
  .isFormulaCodeAt,
  .syntaxTransform,
  .freeVariableOccurs,
  .isLogicalAxiomCode,
  .modusPonens,
  .isStructure,
  .termValue,
  .atomicSatisfaction,
  .formulaSatisfactionAtStage,
  .formulaSatisfaction,
  .isTruth,
  .isModel,
  .logicalConsequence,
  .isTheorem,
  .isRelatedTermCodeAt,
  .isRelatedTermListCodeAt,
  .isRelatedFormulaCodeAt,
  .termListValue]

/-- 自由上下文用叶子的数值记录其长度；唯一排序由语言固定。 -/
def context (tree : Tree) : Option SetContext :=
  (scalar tree).map (fun count => List.replicate count SetSort.set)

def decodeVariable : (context : SetContext) → Nat → Option (Variable context SetSort.set)
  | [] , _ => none
  | .set :: _, 0 => some .here
  | .set :: tail, index + 1 => (decodeVariable tail index).map Variable.there

def application {bound free : SetContext} (symbol : FunctionSymbol)
    (arguments : Arguments signature bound free (signature.funcDomain symbol)) :
    SetTerm bound free :=
  Eq.mp (congrArg (Term signature bound free)
    (show signature.funcCodomain symbol = SetSort.set from by cases symbol <;> rfl))
    (Term.app symbol arguments)

mutual

def term (bound free : SetContext) (tree : Tree) : Option (SetTerm bound free) :=
      match tree with
      | .node 0 [index] => do return .bvar (← decodeVariable bound (← scalar index))
      | .node 1 [index] => do return .fvar (← decodeVariable free (← scalar index))
      | .node 2 (symbol :: arguments) => do
          let function ← functionSymbols[← scalar symbol]?
          let terms ← argumentsList bound free (signature.funcDomain function) arguments
          return application function terms
      | _ => none

termination_by sizeOf tree

def argumentsList (bound free : SetContext) (sorts : SetContext) (trees : List Tree) :
    Option (Arguments signature bound free sorts) :=
  match sorts, trees with
  | [] , [] => some .nil
  | .set :: sorts, head :: tail => do
      let headTerm ← term bound free head
      let terms ← argumentsList bound free sorts tail
      return .cons headTerm terms
  | _, _ => none
termination_by sizeOf trees

end

/-- 参数列长度严格匹配源上下文。 -/
def arguments (bound free sorts : SetContext) : Tree →
    Option (Arguments signature bound free sorts)
  | .node 0 children => argumentsList bound free sorts children
  | _ => none

/-- 沿有限语法树直接递归，无额外燃料参数。 -/
def formula (bound free : SetContext) (tree : Tree) : Option (SetFormula bound free) :=
      match tree with
      | .node 0 [] => some .falsum
      | .node 1 [] => some .truth
      | .node 2 (symbol :: args) => do
          let relation ← relationSymbols[← scalar symbol]?
          let terms ← argumentsList bound free (signature.relDomain relation) args
          return .rel relation terms
      | .node 3 [left, right] => do return .equal (← term bound free left) (← term bound free right)
      | .node 4 [body] => do return .neg (← formula bound free body)
      | .node 5 [left, right] => do
          return .conj (← formula bound free left) (← formula bound free right)
      | .node 6 [left, right] => do
          return .disj (← formula bound free left) (← formula bound free right)
      | .node 7 [left, right] => do
          return .imp (← formula bound free left) (← formula bound free right)
      | .node 8 [left, right] => do
          return .iff (← formula bound free left) (← formula bound free right)
      | .node 9 [body] => do return .forallE .set (← formula (.set :: bound) free body)
      | .node 10 [body] => do return .existsE .set (← formula (.set :: bound) free body)
      | _ => none

termination_by sizeOf tree

/-- 用已证明单射的结构码提供内在公式的可计算相等判定。 -/
def formulaEq {bound free : SetContext} (left right : SetFormula bound free) :
    Decidable (left = right) :=
  if h : formula_code left = formula_code right then
    isTrue (formula_code_injective h)
  else isFalse (fun hEq => h (congrArg formula_code hEq))

/-- 异质参数列直接组成统一 free 替换，替换范围由类型保证。 -/
def substitution {bound free : SetContext} : {sorts : SetContext} →
    Arguments signature bound free sorts → VariableSubstitution signature sorts bound free
  | [] , .nil => VariableSubstitution.empty
  | _ :: _, .cons head tail => VariableSubstitution.cons head (substitution tail)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxDecode
