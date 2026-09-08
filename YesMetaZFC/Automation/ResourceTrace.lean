import YesMetaZFC.Automation.Resolution
/-!
# 自动化后端资源轨迹
本模块只保存搜索器额外计算出来的纯数据：规则父节点、fact/source 线索、
重写位置和 CDCL residual 初始字句映射。它不依赖 LCF theorem token，也不生成证明项。
后续的小 checker 应该消费这里的 witness，并在已有父字句已经认证的前提下，只检查
“当前新增 clause 是否由这些父节点和资源合法推出”。
-/
namespace YesMetaZFC
namespace Automation
namespace ResourceTrace
abbrev ClauseId := Nat
abbrev NodeId := Nat
abbrev Clause := CoreSyntax.Search.Clause
abbrev Literal := CoreSyntax.Search.Literal
abbrev Term := CoreSyntax.Search.Term
abbrev Substitution := CoreSyntax.Search.Substitution
abbrev TermPath := List Nat
inductive LiteralSide where
  | left
  | right
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
structure PositionedTerm where
  side : LiteralSide
  path : TermPath
  term : Term
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
structure ClauseRef where
  id : ClauseId
  clause? : Option Clause := none
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure StandardizeApartSideMetadata where
  original : Clause
  offset : Nat := 0
  renamed : Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr
/--
二元规则的 standardize-apart 元数据。
resolution 中 `left/right` 表示左右父字句；rewrite/superposition 中表示
`equality/target` 父字句。
-/
structure StandardizeApartMetadata where
  left : StandardizeApartSideMetadata
  right : StandardizeApartSideMetadata
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure FactFeature where
  id : NodeId
  clause : Clause
  originLabel : String := ""
  certificateSummary? : Option String := none
  deriving Repr, Inhabited, BEq, Lean.ToExpr
inductive UnaryKind where
  | ordinaryFactoring
  | equalityFactoring
  | equalityResolution
  | booleanExtensionality
  | argumentCongruence
  | functionExtensionality
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace UnaryKind
def label : UnaryKind → String
  | ordinaryFactoring => "ordinary factoring"
  | equalityFactoring => "equality factoring"
  | equalityResolution => "equality resolution"
  | booleanExtensionality => "boolean extensionality"
  | argumentCongruence => "argument congruence"
  | functionExtensionality => "function extensionality"
end UnaryKind
inductive RewriteKind where
  | demodulation
  | contextualDemodulation
  | positiveSuperposition
  | negativeSuperposition
  | extensionalParamodulation
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace RewriteKind
def label : RewriteKind → String
  | demodulation => "demodulation"
  | contextualDemodulation => "contextual demodulation"
  | positiveSuperposition => "positive superposition"
  | negativeSuperposition => "negative superposition"
  | extensionalParamodulation => "extensional paramodulation"
end RewriteKind
inductive TargetPolarity where
  | positive
  | negative
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace TargetPolarity
def label : TargetPolarity → String
  | positive => "positive"
  | negative => "negative"
end TargetPolarity
structure UnaryResource where
  kind : UnaryKind
  parent : ClauseRef
  literalIndex? : Option Nat := none
  otherLiteralIndex? : Option Nat := none
  substitution : Substitution := []
  result : Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure ResolutionResource where
  left : ClauseRef
  right : ClauseRef
  leftLiteralIndex? : Option Nat := none
  rightLiteralIndex? : Option Nat := none
  standardizeApart? : Option StandardizeApartMetadata := none
  substitution : Substitution := []
  result : Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure RewriteResource where
  kind : RewriteKind
  equality : ClauseRef
  target : ClauseRef
  equalityLiteral : Nat
  targetLiteral : Nat
  targetPosition : PositionedTerm
  orientedLhs : Term
  orientedRhs : Term
  standardizeApart? : Option StandardizeApartMetadata := none
  substitution : Substitution := []
  result : Clause
  contextual : Bool := false
  targetPolarity? : Option TargetPolarity := none
  deriving Repr, BEq, Lean.ToExpr
inductive LocalStepWitness where
  | unary (resource : UnaryResource)
  | resolution (resource : ResolutionResource)
  | rewrite (resource : RewriteResource)
  deriving Repr, BEq, Lean.ToExpr
namespace LocalStepWitness
def parents : LocalStepWitness → Array ClauseRef
  | unary resource => #[resource.parent]
  | resolution resource => #[resource.left, resource.right]
  | rewrite resource => #[resource.equality, resource.target]
def result : LocalStepWitness → Clause
  | unary resource => resource.result
  | resolution resource => resource.result
  | rewrite resource => resource.result
def withResult (witness : LocalStepWitness) (clause : Clause) : LocalStepWitness :=
  match witness with
  | unary resource => unary { resource with result := clause }
  | resolution resource => resolution { resource with result := clause }
  | rewrite resource => rewrite { resource with result := clause }
private def remapRefWith? (remap : ClauseId → Option ClauseId) (ref : ClauseRef) : Option ClauseRef := do
  let id ← remap ref.id
  some { ref with id := id }
/--
按调用方给出的总映射重写 witness 中的父节点编号。
该入口用于把 persistent search arena 的 dense clause id 映射回既有 DAG node id；
输入节点和搜索派生节点因此可以共享同一套回放逻辑。
-/
def remapParentsWith? (remap : ClauseId → Option ClauseId) :
    LocalStepWitness → Option LocalStepWitness
  | unary resource => do
      let parent ← remapRefWith? remap resource.parent
      some (unary { resource with parent := parent })
  | resolution resource => do
      let left ← remapRefWith? remap resource.left
      let right ← remapRefWith? remap resource.right
      some (resolution { resource with left := left, right := right })
  | rewrite resource => do
      let equality ← remapRefWith? remap resource.equality
      let target ← remapRefWith? remap resource.target
      some (rewrite { resource with equality := equality, target := target })
def remapParents? (inputSize : Nat) (mapping : Array (Option ClauseId)) :
    LocalStepWitness → Option LocalStepWitness :=
  remapParentsWith? fun id =>
    if id < inputSize then
      some id
    else
      let index := id - inputSize
      if h : index < mapping.size then
        mapping[index]
      else
        none
def resultMatches (witness : LocalStepWitness) (clause : Clause) : Bool :=
  CoreSyntax.Search.clauseEq witness.result clause
end LocalStepWitness
/-! ## 原生高阶搜索资源 -/
/--
高阶搜索器交给 HO-DAG 材料化器的统一资源。
β/η 是无父边的外延公理实例；其余局部推理继续复用 `LocalStepWitness`，从而让
resolution、重写和外延规则共享同一套搜索 journal 形状。
-/
inductive HigherOrderResource where
  | beta (redex : Term)
  | eta (redex : Term)
  | local (witness : LocalStepWitness)
  deriving Repr, BEq, Lean.ToExpr
namespace HigherOrderResource
def label : HigherOrderResource → String
  | .beta _ => "beta"
  | .eta _ => "eta"
  | .local (.unary resource) => resource.kind.label
  | .local (.resolution _) => "resolution"
  | .local (.rewrite resource) => resource.kind.label
def parents : HigherOrderResource → Array ClauseRef
  | .beta _ => #[]
  | .eta _ => #[]
  | .local witness => witness.parents
def result? : HigherOrderResource → Option Clause
  | .beta _ => none
  | .eta _ => none
  | .local witness => some witness.result
end HigherOrderResource
structure CdclInitialFeature where
  initialIndex : Nat
  clauseId : NodeId
  sourceClause : Clause
  encodedClause : PropResolution.Clause
  originLabel? : Option String := none
  deriving Repr, Inhabited, Lean.ToExpr
structure CdclResourceSummary where
  phase : String := ""
  initialFeatures : Array CdclInitialFeature := #[]
  usedInitialIndices : Array Nat := #[]
  journalSize : Nat := 0
  learnedClauses : Nat := 0
  resolutionSteps : Nat := 0
  deriving Repr, Inhabited, Lean.ToExpr
namespace CdclResourceSummary
def empty : CdclResourceSummary := {}
def usedInitialFeatures (summary : CdclResourceSummary) : Array CdclInitialFeature :=
  summary.initialFeatures.filter fun feature =>
    summary.usedInitialIndices.contains feature.initialIndex
end CdclResourceSummary
end ResourceTrace
end Automation
end YesMetaZFC
