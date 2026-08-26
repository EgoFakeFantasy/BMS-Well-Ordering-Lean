import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.CoreNormalForm.CheckedPreprocessing
import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.Guards
import YesMetaZFC.Automation.DAGCertificate
import YesMetaZFC.Automation.AvatarRegistrySoundness
import YesMetaZFC.Automation.ResourceTrace
import YesMetaZFC.Automation.Scheduler
import YesMetaZFC.Automation.Data.StableIdMap
import YesMetaZFC.Automation.Data.CertificateWorkspace
/-!
# 搜索器到新 DAG 的材料化层
本模块定义一个轻量 search-DAG 输入协议，并把它材料化为
`Automation.DAGCertificate` 的 `Type 0` 可计算 DAG。它刻意不 import 旧 LCF replay/MF1
模块；旧搜索器只需要把自己的 `ProverState` 投影到这里的 `SearchDAG` 数据结构即可。
设计边界：
* `SearchDAG` 持有 canonical initial-clause table；source 只能引用其中的唯一索引；
* 材料化前会完整核对 search table 与 `ClauseProblem.initialClauses`，不从 source 切片猜来源；
* AVATAR guard 会材料化进 DAG 节点；全局 selector registry checker 负责闭合其语义；
* residual CDCL 会重建普通对象父字句、AVATAR selector skeleton、theory-conflict learned
  clause 与 guard activation 四类 initial 链接；
* selector skeleton 通过 fixed-bound-stack AVATAR 拓扑定理进入专用 soundness 出口；
* 带 substitution 的一阶规则会材料化成 substituted local evidence；这些 evidence 已经可计算
  检查 result clause，但在 substitution soundness 引理补齐前不进入 soundness-supported 片段；
-/
namespace YesMetaZFC
namespace Automation
namespace SearchMaterialization
universe x
open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Automation.LogicSoundness
abbrev SearchTerm := CoreSyntax.Search.Term
abbrev SearchLiteral := CoreSyntax.Search.Literal
abbrev SearchClause := CoreSyntax.Search.Clause
abbrev SearchFunc := CoreSyntax.Search.FunctionSymbol
abbrev SearchSort := CoreSyntax.CoreSort
abbrev Substitution := CoreSyntax.Search.Substitution
abbrev NodeId := Nat
/-! ## 轻量 search-DAG 输入协议 -/
structure ClauseRef where
  id : NodeId
  clause? : Option SearchClause := none
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure StandardizeApartSideMetadata where
  original : SearchClause
  offset : Nat := 0
  renamed : SearchClause
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
structure ProofParent where
  id : NodeId
  clause : SearchClause
  deriving Repr, Inhabited, BEq, Lean.ToExpr
abbrev GuardLit := Guards.Lit
abbrev GuardSet := Guards.Set
abbrev GuardedClause := Guards.GuardedClause SearchClause
namespace GuardedClause
def plain (clause : SearchClause) : GuardedClause :=
  Guards.GuardedClause.plain clause
def unguarded (gclause : GuardedClause) : Bool :=
  Guards.GuardedClause.unguarded gclause
def globallyEmpty (gclause : GuardedClause) : Bool :=
  Guards.GuardedClause.globallyEmpty Array.isEmpty gclause
def theoryConflict (gclause : GuardedClause) : Bool :=
  Guards.GuardedClause.theoryConflict Array.isEmpty gclause
def eq (left right : GuardedClause) : Bool :=
  Guards.GuardedClause.eq CoreSyntax.Search.clauseEq left right
end GuardedClause
structure SourcePayload where
  initialIndex : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
structure AvatarSplitPayload where
  source : ProofParent
  partitions : Array (Array Nat)
  selectors : PropResolution.Clause
  note : String := ""
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure AvatarComponentPayload where
  split : ProofParent
  componentIndex : Nat
  note : String := ""
  deriving Repr, Inhabited, BEq, Lean.ToExpr
inductive UnaryKind where
  | ordinaryFactoring
  | equalityFactoring
  | equalityResolution
  | booleanExtensionality
  | argumentCongruence
  | functionExtensionality
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
inductive RewriteKind where
  | demodulation
  | contextualDemodulation
  | positiveSuperposition
  | negativeSuperposition
  | extensionalParamodulation
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
abbrev TermPath := List Nat
inductive LiteralSide where
  | left
  | right
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
structure PositionedTerm where
  side : LiteralSide
  path : TermPath
  term : SearchTerm
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
structure UnaryResource where
  kind : UnaryKind
  parent : ClauseRef
  literalIndex? : Option Nat := none
  otherLiteralIndex? : Option Nat := none
  substitution : Substitution := []
  result : SearchClause
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure ResolutionResource where
  left : ClauseRef
  right : ClauseRef
  leftLiteralIndex? : Option Nat := none
  rightLiteralIndex? : Option Nat := none
  standardizeApart? : Option StandardizeApartMetadata := none
  substitution : Substitution := []
  result : SearchClause
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure RewriteResource where
  kind : RewriteKind
  equality : ClauseRef
  target : ClauseRef
  equalityLiteral : Nat
  targetLiteral : Nat
  targetPosition : PositionedTerm
  orientedLhs : SearchTerm
  orientedRhs : SearchTerm
  standardizeApart? : Option StandardizeApartMetadata := none
  substitution : Substitution := []
  result : SearchClause
  contextual : Bool := false
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
def result : LocalStepWitness → SearchClause
  | unary resource => resource.result
  | resolution resource => resource.result
  | rewrite resource => resource.result
def resultMatches (witness : LocalStepWitness) (clause : SearchClause) : Bool :=
  CoreSyntax.Search.clauseEq witness.result clause
end LocalStepWitness
/-! ### ResourceTrace 原生适配
搜索器内部只记录轻量资源轨迹；进入可信边界前统一转换为本模块的 search-DAG
witness。这里仍然只是纯数据搬运，具体规则合法性由后续 DAG checker 复算。
-/
def clauseRefOfResource (ref : ResourceTrace.ClauseRef) : ClauseRef :=
  { id := ref.id, clause? := ref.clause? }
def standardizeApartSideMetadataOfResource (metadata : ResourceTrace.StandardizeApartSideMetadata) :
    StandardizeApartSideMetadata := {
  original := metadata.original
  offset := metadata.offset
  renamed := metadata.renamed
}
def standardizeApartMetadataOfResource (metadata : ResourceTrace.StandardizeApartMetadata) :
    StandardizeApartMetadata := {
  left := standardizeApartSideMetadataOfResource metadata.left
  right := standardizeApartSideMetadataOfResource metadata.right
}
def unaryKindOfResource : ResourceTrace.UnaryKind → UnaryKind
  | .ordinaryFactoring => .ordinaryFactoring
  | .equalityFactoring => .equalityFactoring
  | .equalityResolution => .equalityResolution
  | .booleanExtensionality => .booleanExtensionality
  | .argumentCongruence => .argumentCongruence
  | .functionExtensionality => .functionExtensionality
def rewriteKindOfResource : ResourceTrace.RewriteKind → RewriteKind
  | .demodulation => .demodulation
  | .contextualDemodulation => .contextualDemodulation
  | .positiveSuperposition => .positiveSuperposition
  | .negativeSuperposition => .negativeSuperposition
  | .extensionalParamodulation => .extensionalParamodulation
def literalSideOfResource : ResourceTrace.LiteralSide → LiteralSide
  | .left => .left
  | .right => .right
def positionedTermOfResource (position : ResourceTrace.PositionedTerm) :
    PositionedTerm := {
  side := literalSideOfResource position.side
  path := position.path
  term := position.term
}
def unaryResourceOfTrace (resource : ResourceTrace.UnaryResource) :
    UnaryResource := {
  kind := unaryKindOfResource resource.kind
  parent := clauseRefOfResource resource.parent
  literalIndex? := resource.literalIndex?
  otherLiteralIndex? := resource.otherLiteralIndex?
  substitution := resource.substitution
  result := resource.result
}
def resolutionResourceOfTrace (resource : ResourceTrace.ResolutionResource) :
    ResolutionResource := {
  left := clauseRefOfResource resource.left
  right := clauseRefOfResource resource.right
  leftLiteralIndex? := resource.leftLiteralIndex?
  rightLiteralIndex? := resource.rightLiteralIndex?
  standardizeApart? := resource.standardizeApart?.map standardizeApartMetadataOfResource
  substitution := resource.substitution
  result := resource.result
}
def rewriteResourceOfTrace (resource : ResourceTrace.RewriteResource) :
    RewriteResource := {
  kind := rewriteKindOfResource resource.kind
  equality := clauseRefOfResource resource.equality
  target := clauseRefOfResource resource.target
  equalityLiteral := resource.equalityLiteral
  targetLiteral := resource.targetLiteral
  targetPosition := positionedTermOfResource resource.targetPosition
  orientedLhs := resource.orientedLhs
  orientedRhs := resource.orientedRhs
  standardizeApart? := resource.standardizeApart?.map standardizeApartMetadataOfResource
  substitution := resource.substitution
  result := resource.result
  contextual := resource.contextual
}
def localStepWitnessOfResource :
    ResourceTrace.LocalStepWitness → LocalStepWitness
  | .unary resource => .unary (unaryResourceOfTrace resource)
  | .resolution resource => .resolution (resolutionResourceOfTrace resource)
  | .rewrite resource => .rewrite (rewriteResourceOfTrace resource)
structure CdclInitialFeature where
  initialIndex : Nat
  clauseId : NodeId
  sourceClause : SearchClause
  encodedClause : PropResolution.Clause
  originLabel? : Option String := none
  deriving Repr, Inhabited, Lean.ToExpr
structure CdclLearnedFeature where
  initialIndex : Nat
  learnedNode : NodeId
  encodedClause : PropResolution.Clause
  originLabel? : Option String := none
  deriving Repr, Inhabited, Lean.ToExpr
structure CdclGuardActivationFeature where
  initialIndex : Nat
  clauseId : NodeId
  sourceClause : SearchClause
  guards : GuardSet
  encodedClause : PropResolution.Clause
  originLabel? : Option String := none
  deriving Repr, Inhabited, Lean.ToExpr
structure CdclAvatarSkeletonFeature where
  initialIndex : Nat
  splitId : NodeId
  skeleton : PropResolution.Clause
  originLabel? : Option String := none
  deriving Repr, Inhabited, Lean.ToExpr
structure CdclResourceSummary where
  phase : String := ""
  initialFeatures : Array CdclInitialFeature := #[]
  avatarSkeletonFeatures : Array CdclAvatarSkeletonFeature := #[]
  learnedFeatures : Array CdclLearnedFeature := #[]
  guardActivationFeatures : Array CdclGuardActivationFeature := #[]
  objectAtomCount : Nat := 0
  usedInitialIndices : Array Nat := #[]
  journalSize : Nat := 0
  learnedClauses : Nat := 0
  resolutionSteps : Nat := 0
  deriving Repr, Inhabited, Lean.ToExpr
structure ResidualCdclPayload where
  initialClauses : Array PropResolution.InitialClause
  proof : PropResolution.CdclProof
  summary : CdclResourceSummary
  deriving Repr, Lean.ToExpr
structure TheoryConflictPayload where
  conflict : ProofParent
  note : String := ""
  deriving Repr, Inhabited, Lean.ToExpr
structure PropositionalLearnedClausePayload where
  conflict : NodeId
  learned : PropResolution.Clause
  note : String := ""
  deriving Repr, Inhabited, Lean.ToExpr
inductive NodePayload where
  | source (payload : SourcePayload)
  | avatarSplit (payload : AvatarSplitPayload)
  | avatarComponent (payload : AvatarComponentPayload)
  | localStep (witness : LocalStepWitness)
  | theoryConflict (payload : TheoryConflictPayload)
  | propositionalLearnedClause (payload : PropositionalLearnedClausePayload)
  | residualCdcl (payload : ResidualCdclPayload)
  deriving Repr, Lean.ToExpr
namespace NodePayload
def rootClosureEligible : NodePayload → Bool
  | propositionalLearnedClause _ => false
  | _ => true
end NodePayload
structure ClauseInfo where
  id : NodeId
  guards : GuardSet := #[]
  clause : SearchClause
  parents : Array ProofParent := #[]
  payload : NodePayload
  deriving Repr, Lean.ToExpr
namespace ClauseInfo
def guarded (info : ClauseInfo) : GuardedClause :=
  { guards := info.guards, clause := info.clause }
def toParent (info : ClauseInfo) : ProofParent :=
  { id := info.id, clause := info.clause }
def globallyEmpty (info : ClauseInfo) : Bool :=
  info.guarded.globallyEmpty
def theoryConflict (info : ClauseInfo) : Bool :=
  info.guarded.theoryConflict
end ClauseInfo
structure SearchDAG where
  initialClauses : Array SearchClause := #[]
  clauses : Array ClauseInfo := #[]
  emptyClause? : Option NodeId := none
  deriving Repr, Lean.ToExpr
namespace SearchDAG
def ofInitialClauses (initialClauses : Array SearchClause) : SearchDAG :=
  { initialClauses := initialClauses }
def nextId (dag : SearchDAG) : NodeId :=
  dag.clauses.size
def get? (dag : SearchDAG) (id : NodeId) : Option ClauseInfo :=
  dag.clauses[id]?
def addClause (dag : SearchDAG) (gclause : GuardedClause) (parents : Array ProofParent) (payload : NodePayload) :
    SearchDAG × ClauseInfo :=
  let info : ClauseInfo := {
    id := dag.nextId
    guards := Guards.canonical gclause.guards
    clause := gclause.clause
    parents := parents
    payload := payload
  }
  let emptyClause? :=
    match dag.emptyClause? with
    | some id => some id
    | none =>
        if info.globallyEmpty && payload.rootClosureEligible then
          some info.id
        else
          none
  ({ dag with clauses := dag.clauses.push info, emptyClause? := emptyClause? }, info)
def addPlainClause (dag : SearchDAG) (clause : SearchClause) (parents : Array ProofParent) (payload : NodePayload) :
    SearchDAG × ClauseInfo :=
  dag.addClause (GuardedClause.plain clause) parents payload
def parentOk (dag : SearchDAG) (childId : NodeId) (parent : ProofParent) : Bool :=
  parent.id < childId &&
    match dag.get? parent.id with
    | some info => CoreSyntax.Search.clauseEq info.clause parent.clause
    | none => false
def parentGuards? (dag : SearchDAG) (parent : ProofParent) : Option GuardSet := do
  let info ← dag.get? parent.id
  if CoreSyntax.Search.clauseEq info.clause parent.clause then
    some info.guards
  else
    none
def parentGuardUnion? (dag : SearchDAG) (parents : Array ProofParent) :
    Option GuardSet := do
  let mut guards : GuardSet := #[]
  for parent in parents do
    let parentGuards ← dag.parentGuards? parent
    guards := Guards.merge guards parentGuards
  some guards
def localGuardsOk (dag : SearchDAG) (info : ClauseInfo) : Bool :=
  match dag.parentGuardUnion? info.parents with
  | some guards => Guards.eq info.guards guards
  | none => false
def guardedLocalResult? (dag : SearchDAG) (parents : Array ProofParent) (witness : LocalStepWitness) : Option GuardedClause := do
  let guards ← dag.parentGuardUnion? parents
  some { guards := guards, clause := witness.result }
private def addSourceAt? (dag : SearchDAG) (guards : GuardSet) (initialIndex : Nat) :
    Option (SearchDAG × ClauseInfo) := do
  let initial ← dag.initialClauses[initialIndex]?
  some (dag.addClause { guards := guards, clause := initial } #[] (.source { initialIndex := initialIndex }))
def addSourceKnownUnused? (dag : SearchDAG) (guards : GuardSet) (initialIndex : Nat) :
    Option (SearchDAG × ClauseInfo) :=
  dag.addSourceAt? guards initialIndex
private def addAvatarSplitAt? (dag : SearchDAG) (source : ClauseInfo) (partitions : Array (Array Nat)) (selectors : PropResolution.Clause) :
    Option (SearchDAG × ClauseInfo) := do
  match source.payload with
  | .source _ =>
      if !source.guards.isEmpty ||
          !AvatarSplit.indexPartitionOk source.clause.size partitions ||
          !AvatarSplit.selectorsOk partitions selectors then
        none
      else
        let parent := source.toParent
        let payload : AvatarSplitPayload := {
          source := parent
          partitions := partitions
          selectors := selectors
          note := "materialized AVATAR source split"
        }
        some (dag.addPlainClause source.clause #[parent] (.avatarSplit payload))
  | _ => none
def addAvatarSplitKnownUnused? (dag : SearchDAG) (source : ClauseInfo) (partitions : Array (Array Nat)) (selectors : PropResolution.Clause) :
    Option (SearchDAG × ClauseInfo) :=
  dag.addAvatarSplitAt? source partitions selectors
private def addAvatarComponentAt? (dag : SearchDAG) (split : ClauseInfo) (componentIndex : Nat) : Option (SearchDAG × ClauseInfo) := do
  match split.payload with
  | .avatarSplit splitPayload =>
      let indices ← splitPayload.partitions[componentIndex]?
      let selector ← AvatarSplit.selectorAt? splitPayload.selectors componentIndex
      let parent := split.toParent
      let payload : AvatarComponentPayload := {
        split := parent
        componentIndex := componentIndex
        note := "materialized AVATAR component"
      }
      some (dag.addClause {
        guards := #[selector]
        clause := AvatarSplit.clauseAtIndices split.clause indices
      } #[parent] (.avatarComponent payload))
  | _ => none
def addAvatarComponentKnownUnused? (dag : SearchDAG) (split : ClauseInfo) (componentIndex : Nat) : Option (SearchDAG × ClauseInfo) :=
  dag.addAvatarComponentAt? split componentIndex
def addLocalStep? (dag : SearchDAG) (parents : Array ProofParent) (witness : LocalStepWitness) : Option (SearchDAG × ClauseInfo) := do
  let gclause ← dag.guardedLocalResult? parents witness
  some (dag.addClause gclause parents (.localStep witness))
private def clauseRefSnapshotMatches (ref : ClauseRef) (actual : SearchClause) : Bool :=
  match ref.clause? with
  | some snapshot => CoreSyntax.Search.clauseEq snapshot actual
  | none => true
def parentFromClauseRef? (dag : SearchDAG) (ref : ClauseRef) :
    Option ProofParent := do
  let info ← dag.get? ref.id
  if clauseRefSnapshotMatches ref info.clause then
    some info.toParent
  else
    none
def addLocalWitness? (dag : SearchDAG) (witness : LocalStepWitness) :
    Option (SearchDAG × ClauseInfo) := do
  let parents ← witness.parents.mapM dag.parentFromClauseRef?
  dag.addLocalStep? parents witness
def addResourceTraceLocalWitness? (dag : SearchDAG) (witness : ResourceTrace.LocalStepWitness) :
    Option (SearchDAG × ClauseInfo) :=
  dag.addLocalWitness? (localStepWitnessOfResource witness)
def addTheoryConflict? (dag : SearchDAG) (conflict : ClauseInfo) :
    Option (SearchDAG × ClauseInfo) := do
  if !conflict.theoryConflict then
    none
  else
    let parent := conflict.toParent
    let payload : TheoryConflictPayload := {
      conflict := parent
      note := "materialized theory conflict"
    }
    some (dag.addClause conflict.guarded #[parent] (.theoryConflict payload))
def addPropositionalLearnedClause? (dag : SearchDAG) (conflict : ClauseInfo) :
    Option (SearchDAG × ClauseInfo) := do
  match conflict.payload with
  | .theoryConflict _ =>
      let learned := Guards.learnedClause conflict.guards
      let parent := conflict.toParent
      let payload : PropositionalLearnedClausePayload := {
        conflict := conflict.id
        learned := learned
        note := "learned from theory conflict"
      }
      some (dag.addClause conflict.guarded #[parent] (.propositionalLearnedClause payload))
  | _ => none
def theoryConflicts (dag : SearchDAG) : Array ClauseInfo :=
  dag.clauses.filter ClauseInfo.theoryConflict
def cdclInitialSlotOk (initialClauses : Array PropResolution.InitialClause) (index : Nat) (encodedClause : PropResolution.Clause) : Bool :=
  match initialClauses[index]? with
  | some initial => PropResolution.clauseEq initial.clause encodedClause
  | none => false
def initialFeatureOk (dag : SearchDAG) (initialClauses : Array PropResolution.InitialClause) (feature : CdclInitialFeature) : Bool :=
  cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause &&
    match dag.get? feature.clauseId with
    | some info =>
        info.guards.isEmpty &&
          CoreSyntax.Search.clauseEq info.clause feature.sourceClause
    | none => false
def learnedFeatureOk (dag : SearchDAG) (initialClauses : Array PropResolution.InitialClause) (feature : CdclLearnedFeature) : Bool :=
  cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause &&
    match dag.get? feature.learnedNode with
    | some info =>
        match info.payload with
        | .propositionalLearnedClause payload =>
            PropResolution.clauseEq (PropResolution.canonicalClause feature.encodedClause) payload.learned
        | _ => false
    | none => false
def guardActivationFeatureOk (dag : SearchDAG) (initialClauses : Array PropResolution.InitialClause) (feature : CdclGuardActivationFeature) : Bool :=
  cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause &&
    match dag.get? feature.clauseId with
    | some info =>
        !info.guards.isEmpty &&
          CoreSyntax.Search.clauseEq info.clause feature.sourceClause &&
            Guards.eq info.guards feature.guards
    | none => false
def avatarSkeletonFeatureOk (dag : SearchDAG) (initialClauses : Array PropResolution.InitialClause) (feature : CdclAvatarSkeletonFeature) : Bool :=
  cdclInitialSlotOk initialClauses feature.initialIndex feature.skeleton &&
    match dag.get? feature.splitId with
    | some info =>
        info.guards.isEmpty &&
          match info.payload with
          | .avatarSplit payload =>
              PropResolution.clauseEq feature.skeleton (PropResolution.canonicalClause payload.selectors)
          | _ => false
    | none => false
def cdclFeatureCount (summary : CdclResourceSummary) : Nat :=
  summary.initialFeatures.size + summary.avatarSkeletonFeatures.size +
    summary.learnedFeatures.size + summary.guardActivationFeatures.size
def cdclFeatureSlots (summary : CdclResourceSummary) : Array Nat := (summary.initialFeatures.map fun feature => feature.initialIndex) ++
    (summary.avatarSkeletonFeatures.map fun feature => feature.initialIndex) ++ (summary.learnedFeatures.map fun feature => feature.initialIndex) ++
        (summary.guardActivationFeatures.map fun feature => feature.initialIndex)
private def pushNatUnique (values : Array Nat) (value : Nat) : Array Nat :=
  if values.contains value then values else values.push value
def sourceInitialIndices (dag : SearchDAG) : Array Nat :=
  dag.clauses.filterMap fun info =>
    match info.payload with
    | .source payload => some payload.initialIndex
    | _ => none
def sourceIndicesUnique (dag : SearchDAG) : Bool := Id.run do
  let mut seen := (List.replicate dag.initialClauses.size false).toArray
  for info in dag.clauses do
    match info.payload with
    | .source payload =>
        if h : payload.initialIndex < seen.size then
          if seen[payload.initialIndex] then
            return false
          else
            seen := seen.set payload.initialIndex true h
        else
          return false
    | _ => pure ()
  return true
def avatarSplitSourcesUnique (dag : SearchDAG) : Bool := Id.run do
  let mut seen : Array NodeId := #[]
  for info in dag.clauses do
    match info.payload with
    | .avatarSplit payload =>
        if seen.contains payload.source.id then
          return false
        else
          seen := seen.push payload.source.id
    | _ => pure ()
  return true
def avatarComponentSlotsUnique (dag : SearchDAG) : Bool := Id.run do
  let mut seen : Array (NodeId × Nat) := #[]
  for info in dag.clauses do
    match info.payload with
    | .avatarComponent payload =>
        let key := (payload.split.id, payload.componentIndex)
        if seen.contains key then
          return false
        else
          seen := seen.push key
    | _ => pure ()
  return true
def cdclFeatureSlotsComplete (summary : CdclResourceSummary) (initialClauses : Array PropResolution.InitialClause) : Bool :=
  let slots := cdclFeatureSlots summary
  let unique := slots.foldl pushNatUnique #[]
  cdclFeatureCount summary == initialClauses.size &&
    unique.size == slots.size &&
      unique.size == initialClauses.size
def guardLiteralOutsideObjectAtoms (objectAtomCount : Nat) (literal : PropResolution.Lit) : Bool :=
  decide (objectAtomCount <= literal.var)
def guardSetOutsideObjectAtoms (objectAtomCount : Nat) (guards : GuardSet) : Bool :=
  guards.all fun literal => guardLiteralOutsideObjectAtoms objectAtomCount literal
def propClauseOutsideObjectAtoms (objectAtomCount : Nat) (clause : PropResolution.Clause) : Bool :=
  clause.all fun literal => guardLiteralOutsideObjectAtoms objectAtomCount literal
def cdclGuardVariablesOk (summary : CdclResourceSummary) : Bool :=
  summary.guardActivationFeatures.all (fun feature => guardSetOutsideObjectAtoms summary.objectAtomCount feature.guards) &&
    summary.avatarSkeletonFeatures.all (fun feature =>
        propClauseOutsideObjectAtoms summary.objectAtomCount feature.skeleton) &&
      summary.learnedFeatures.all (fun feature =>
          propClauseOutsideObjectAtoms summary.objectAtomCount feature.encodedClause)
def clauseRefSnapshotOk (ref : ClauseRef) (actual : SearchClause) : Bool :=
  match ref.clause? with
  | some snapshot => CoreSyntax.Search.clauseEq snapshot actual
  | none => true
def standardizeApartSideOk (ref : ClauseRef) (actual : SearchClause) (side : StandardizeApartSideMetadata) : Bool :=
  clauseRefSnapshotOk ref actual &&
    CoreSyntax.Search.clauseEq side.original actual &&
      CoreSyntax.Search.clauseEq side.renamed (CoreSyntax.Search.Clause.renameVars side.offset side.original)
def standardizeApartMetadataOk (dag : SearchDAG) (leftRef rightRef : ClauseRef) (metadata : StandardizeApartMetadata) : Bool :=
  match dag.get? leftRef.id, dag.get? rightRef.id with
  | some leftInfo, some rightInfo =>
      standardizeApartSideOk leftRef leftInfo.clause metadata.left &&
        standardizeApartSideOk rightRef rightInfo.clause metadata.right
  | _, _ => false
def localWitnessStandardizeApartOk (dag : SearchDAG) (witness : LocalStepWitness) : Bool :=
  match witness with
  | .unary _ => true
  | .resolution resource =>
      match resource.standardizeApart? with
      | some metadata => dag.standardizeApartMetadataOk resource.left resource.right metadata
      | none => true
  | .rewrite resource =>
      match resource.standardizeApart? with
      | some metadata =>
          dag.standardizeApartMetadataOk resource.equality resource.target metadata
      | none => true
def sourceOk (dag : SearchDAG) (info : ClauseInfo) (payload : SourcePayload) : Bool :=
  info.parents.isEmpty &&
    match dag.initialClauses[payload.initialIndex]? with
    | some initial => CoreSyntax.Search.clauseEq info.clause initial
    | none => false
def avatarSplitOk (dag : SearchDAG) (info : ClauseInfo) (payload : AvatarSplitPayload) : Bool :=
  info.parents.size == 1 &&
    info.parents.contains payload.source &&
      info.guards.isEmpty &&
        AvatarSplit.indexPartitionOk payload.source.clause.size payload.partitions &&
          AvatarSplit.selectorsOk payload.partitions payload.selectors &&
            match dag.get? payload.source.id with
            | some source =>
                source.guards.isEmpty &&
                  CoreSyntax.Search.clauseEq source.clause payload.source.clause &&
                    CoreSyntax.Search.clauseEq info.clause source.clause &&
                      match source.payload with
                      | .source _ => true
                      | _ => false
            | none => false
def avatarComponentOk (dag : SearchDAG) (info : ClauseInfo) (payload : AvatarComponentPayload) : Bool :=
  info.parents.size == 1 &&
    info.parents.contains payload.split &&
      match dag.get? payload.split.id with
      | some split =>
          split.guards.isEmpty &&
            CoreSyntax.Search.clauseEq split.clause payload.split.clause &&
              match split.payload with
              | .avatarSplit splitPayload =>
                  match splitPayload.partitions[payload.componentIndex]?,
                      AvatarSplit.selectorAt? splitPayload.selectors payload.componentIndex with
                  | some indices, some selector =>
                      CoreSyntax.Search.clauseEq info.clause (AvatarSplit.clauseAtIndices split.clause indices) &&
                        Guards.eq info.guards #[selector]
                  | _, _ => false
              | _ => false
      | none => false
def payloadGuardsOk (dag : SearchDAG) (info : ClauseInfo) : Bool :=
  match info.payload with
  | .source payload => dag.sourceOk info payload
  | .avatarSplit payload => dag.avatarSplitOk info payload
  | .avatarComponent payload => dag.avatarComponentOk info payload
  | .localStep witness => localGuardsOk dag info && localWitnessStandardizeApartOk dag witness
  | .theoryConflict _ => localGuardsOk dag info
  | .propositionalLearnedClause payload =>
      info.clause.isEmpty &&
        match dag.get? payload.conflict with
        | some conflict =>
          conflict.theoryConflict &&
            Guards.eq info.guards conflict.guards &&
              PropResolution.clauseEq payload.learned (Guards.learnedClause conflict.guards)
        | none => false
  | .residualCdcl payload =>
      cdclFeatureSlotsComplete payload.summary payload.initialClauses &&
        cdclGuardVariablesOk payload.summary &&
        payload.summary.initialFeatures.all (fun feature => dag.initialFeatureOk payload.initialClauses feature) &&
          payload.summary.avatarSkeletonFeatures.all (fun feature =>
              dag.avatarSkeletonFeatureOk payload.initialClauses feature) &&
            payload.summary.learnedFeatures.all (fun feature => dag.learnedFeatureOk payload.initialClauses feature) &&
              payload.summary.guardActivationFeatures.all (fun feature =>
                  dag.guardActivationFeatureOk payload.initialClauses feature)
def infoOk (dag : SearchDAG) (index : Nat) (info : ClauseInfo) : Bool :=
  info.id == index &&
    info.parents.all (fun parent => dag.parentOk info.id parent) &&
      payloadGuardsOk dag info
private def infosOkFrom (dag : SearchDAG) (index : Nat) : List ClauseInfo → Bool
  | [] => true
  | info :: rest => dag.infoOk index info && infosOkFrom dag (index + 1) rest
def check (dag : SearchDAG) : Bool :=
  infosOkFrom dag 0 dag.clauses.toList && dag.sourceIndicesUnique &&
    dag.avatarSplitSourcesUnique && dag.avatarComponentSlotsUnique &&
    match dag.emptyClause? with
    | some id =>
        match dag.get? id with
        | some info => info.globallyEmpty
        | none => false
    | none => true
private partial def collectIdsWith (dag : SearchDAG) :
    Nat → Array Bool → Array NodeId → NodeId → Option (Array Bool × Array NodeId)
  | 0, _, _, _ => none
  | fuel + 1, seen, acc, id => do
      match seen[id]? with
      | none => none
      | some true => some (seen, acc)
      | some false =>
          let info ← dag.get? id
          let mut seen := seen.set! id true
          let mut acc := acc
          for parent in info.parents do
            let result ← collectIdsWith dag fuel seen acc parent.id
            seen := result.1
            acc := result.2
          pure (seen, acc.push id)
def collectDependencies? (dag : SearchDAG) (id : NodeId) : Option (Array ClauseInfo) := do
  if !dag.check then
    none
  else
    let seen := (List.replicate dag.clauses.size false).toArray
    let (_, ids) ← collectIdsWith dag (dag.clauses.size + 1) seen #[] id
    ids.mapM (fun id => dag.get? id)
def collectEmptyDependencies? (dag : SearchDAG) : Option (Array ClauseInfo) := do
  let id ← dag.emptyClause?
  dag.collectDependencies? id
end SearchDAG
/-! ## 新 DAG 签名与基础翻译 -/
inductive RelSymbol where
  | member
  | boolHolds
  | definition (id arity : Nat)
  | predicate (symbol : CoreSyntax.PredicateSymbol)
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace RelSymbol
def label : RelSymbol → String
  | member => "member"
  | boolHolds => "boolHolds"
  | definition id arity => s!"definition[{id}/{arity}]"
  | predicate symbol => s!"predicate[{symbol.id}/{symbol.arity}]"
end RelSymbol
def SearchSignature : LogicSoundness.SetLevel.Signature where
  SortSymbol := SearchSort
  FuncSymbol := SearchFunc
  RelSymbol := RelSymbol
  funcDomain f :=
    if f.inputSorts.isEmpty then
      List.replicate f.arity CoreSyntax.CoreSort.object
    else
      f.inputSorts
  funcCodomain f := f.outputSort
  relDomain
    | .member => [CoreSyntax.CoreSort.object, CoreSyntax.CoreSort.object]
    | .boolHolds => [CoreSyntax.CoreSort.bool]
    | .definition .. => [CoreSyntax.CoreSort.object]
    | .predicate symbol =>
        if symbol.inputSorts.isEmpty then
          List.replicate symbol.arity CoreSyntax.CoreSort.object
        else
          symbol.inputSorts
abbrev Term := DAGCertificate.Term SearchSignature
abbrev Formula := DAGCertificate.Formula SearchSignature
abbrev Literal := DAGCertificate.Literal SearchSignature
abbrev Clause := DAGCertificate.Clause SearchSignature
abbrev ParentClause := DAGCertificate.ParentClause SearchSignature
abbrev Node := DAGCertificate.Node SearchSignature
abbrev Payload := DAGCertificate.Payload SearchSignature
abbrev DeepProblem := DAGCertificate.DeepProblem SearchSignature
abbrev ClauseProblem := DAGCertificate.ClauseProblem SearchSignature
abbrev DAG := DAGCertificate.DAG SearchSignature
instance instSearchSignatureSortDecidableEq :
    DecidableEq SearchSignature.SortSymbol := by
  change DecidableEq SearchSort
  infer_instance
instance instSearchSignatureFuncDecidableEq :
    DecidableEq SearchSignature.FuncSymbol := by
  change DecidableEq SearchFunc
  infer_instance
instance instSearchSignatureRelDecidableEq :
    DecidableEq SearchSignature.RelSymbol := by
  change DecidableEq RelSymbol
  infer_instance
abbrev CheckedDAG := DAGCertificate.CheckedDAG (σ := SearchSignature)
abbrev Result (α : Type) := LogicSoundness.SetLevel.BackendResult α
def diagnostic (phase : Certificate.Phase) (message : String) :
    Certificate.Diagnostic :=
  Certificate.Diagnostic.ofMessage .dagReflection phase message
def requireSome {α : Type} (phase : Certificate.Phase) (message : String) :
    Option α → Result α
  | some value => pure value
  | none => throw (diagnostic phase message)
def firstOrderSortOk : SearchSort → Bool
  | .arrow .. => false
  | _ => true
def functionSymbolFirstOrderOk (symbol : SearchFunc) : Bool :=
  firstOrderSortOk symbol.outputSort &&
    symbol.inputSorts.all firstOrderSortOk
def checkFunctionSymbol (symbol : SearchFunc) (actualArity : Nat) : Result Unit := do
  if !functionSymbolFirstOrderOk symbol then
    throw (diagnostic .sourceMaterialization (s!"function symbol {reprStr symbol} uses arrow sort; " ++
        "first-order DAG materialization rejected it"))
  if actualArity != symbol.arity then
    throw (diagnostic .sourceMaterialization
      s!"function symbol arity mismatch: symbol={reprStr symbol}, actual={actualArity}")
  if !(symbol.inputSorts.isEmpty || symbol.inputSorts.length == symbol.arity) then
    throw (diagnostic .sourceMaterialization
      s!"function symbol input sort arity mismatch: {reprStr symbol}")
partial def term (input : SearchTerm) : Result Term := do
  match input with
  | .var id =>
      pure (.var (.fvar CoreSyntax.CoreSort.object id))
  | .bvar sort index =>
      if firstOrderSortOk sort then
        pure (.var (.bvar sort index))
      else
        throw (diagnostic .sourceMaterialization
          s!"bound variable uses arrow sort: {reprStr sort}")
  | .fvar sort id =>
      if firstOrderSortOk sort then
        pure (.var (.fvar sort id))
      else
        throw (diagnostic .sourceMaterialization
          s!"free variable uses arrow sort: {reprStr sort}")
  | .app symbol args =>
      checkFunctionSymbol symbol args.length
      pure (.app symbol (← args.mapM term))
  | .apply .. =>
      throw (diagnostic .sourceMaterialization
        "higher-order application is not representable in the current first-order DAG")
  | .lam .. =>
      throw (diagnostic .sourceMaterialization
        "lambda term is not representable in the current first-order DAG")
def projectedPredicateArguments (predicate : CoreSyntax.PredicateSymbol) (input : SearchTerm) : Result (List SearchTerm) := do
  match input with
  | .app tuple arguments =>
      let expected : SearchFunc := {
        id := predicate.id
        arity := arguments.length
        kind := CoreSyntax.Search.SymbolKind.tuple
        inputSorts := predicate.inputSorts
      }
      if tuple != expected then
        throw (diagnostic .sourceMaterialization
          s!"predicate tuple marker mismatch: predicate={reprStr predicate}, tuple={reprStr tuple}")
      if arguments.length != predicate.arity then
        throw (diagnostic .sourceMaterialization (s!"predicate tuple arity mismatch: predicate={reprStr predicate}, " ++
            s!"actual={arguments.length}"))
      pure arguments
  | _ =>
      throw (diagnostic .sourceMaterialization
        s!"predicate arguments are not carried by a checked tuple: {reprStr input}")
def atom (predicate : CoreSyntax.Search.PredicateKind) (left right : SearchTerm) : Result Formula := do
  match predicate with
  | .equal =>
      pure (.equal (← term left) (← term right))
  | .member =>
      pure (.rel .member [← term left, ← term right])
  | .boolHolds =>
      pure (.rel .boolHolds [← term left])
  | .definition id arity =>
      -- 旧搜索层 `Literal.toCoreAtom` 对 definition predicate 只消费 `left`；
      -- 这里保持同一对象形状，`arity` 仅作为关系符号的审计元数据。
      pure (.rel (.definition id arity) [← term left])
  | .predicate symbol =>
      let arguments ← projectedPredicateArguments symbol left
      pure (.rel (.predicate symbol) (← arguments.mapM term))
def literal (input : SearchLiteral) : Result Literal := do
  pure { polarity := input.positive, atom := (← atom input.predicate input.left input.right) }
def clause (input : SearchClause) : Result Clause := do
  pure { literals := (← input.mapM literal) }
def coreTerm : CoreSyntax.Term → Term
  | .fvar sort id => .var (.fvar sort id)
  | .app symbol arguments =>
      .app (CoreSyntax.NormalForm.FirstOrderProjection.functionSymbol symbol) (arguments.map coreTerm)
  | .bvar _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .apply _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .bool _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .notE _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .andE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .orE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .impE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .iffE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .quote _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .lam _ _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .ite _ _ _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
def coreAtom : CoreSyntax.NormalForm.Atom → Formula
  | .predicate symbol arguments =>
      .rel (.predicate symbol) (arguments.map coreTerm)
  | .equal _ left right =>
      .equal (coreTerm left) (coreTerm right)
  | .boolTerm term =>
      .rel .boolHolds [coreTerm term]
def coreLiteral (input : CoreSyntax.NormalForm.Literal) : Literal :=
  { polarity := input.positive, atom := coreAtom input.atom }
def coreClause (input : CoreSyntax.NormalForm.Clause) : Clause :=
  { literals := input.map coreLiteral }
def coreClauseSet (input : CoreSyntax.NormalForm.ClauseSet) : Array Clause :=
  input.map coreClause
/-
Kernel replay 使用显式结构递归引用 canonical core projection。
搜索与语义层继续保留上面的 Array/List map 接口；这里只提供 definitionally
transparent 的同值视图，避免 concrete DAG checker 展开容器实现。
-/
namespace ReplayCoreProjection
mutual
  def term : CoreSyntax.Term → Term
    | .bvar _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .fvar sort id => .var (.fvar sort id)
    | .app symbol arguments =>
        .app (CoreSyntax.NormalForm.FirstOrderProjection.functionSymbol symbol) (termList arguments)
    | .apply _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .bool _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .notE _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .andE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .orE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .impE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .iffE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .quote _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .lam _ _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .ite _ _ _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  def termList : List CoreSyntax.Term → List Term
    | [] => []
    | head :: tail => term head :: termList tail
end
mutual
  theorem term_eq_coreTerm :
      ∀ input : CoreSyntax.Term, term input = coreTerm input
    | .bvar sort index => by
        rw [term.eq_1, coreTerm.eq_3]
    | .fvar sort id => by
        rw [term.eq_2, coreTerm.eq_1]
    | .app symbol arguments => by
        rw [term.eq_3, coreTerm.eq_2]
        exact congrArg (fun translated =>
            (.app (CoreSyntax.NormalForm.FirstOrderProjection.functionSymbol symbol)
              translated : Term)) (termList_eq_map arguments)
    | .apply function argument => by
        rw [term.eq_4, coreTerm.eq_4]
    | .bool value => by
        rw [term.eq_5, coreTerm.eq_5]
    | .notE body => by
        rw [term.eq_6, coreTerm.eq_6]
    | .andE left right => by
        rw [term.eq_7, coreTerm.eq_7]
    | .orE left right => by
        rw [term.eq_8, coreTerm.eq_8]
    | .impE left right => by
        rw [term.eq_9, coreTerm.eq_9]
    | .iffE left right => by
        rw [term.eq_10, coreTerm.eq_10]
    | .quote formula => by
        rw [term.eq_11, coreTerm.eq_11]
    | .lam domain codomain body => by
        rw [term.eq_12, coreTerm.eq_12]
    | .ite sort condition thenTerm elseTerm => by
        rw [term.eq_13, coreTerm.eq_13]
  theorem termList_eq_map :
      ∀ terms : List CoreSyntax.Term, termList terms = terms.map coreTerm
    | [] => rfl
    | head :: tail => by
        rw [termList, List.map, term_eq_coreTerm, termList_eq_map]
end
def atom : CoreSyntax.NormalForm.Atom → Formula
  | .predicate symbol arguments =>
      .rel (.predicate symbol) (termList arguments)
  | .equal _ left right =>
      .equal (term left) (term right)
  | .boolTerm input =>
      .rel .boolHolds [term input]
theorem atom_eq_coreAtom :
    ∀ input : CoreSyntax.NormalForm.Atom, atom input = coreAtom input
  | .predicate symbol arguments =>
      congrArg (fun translated =>
          (.rel (RelSymbol.predicate symbol) translated : Formula)) (termList_eq_map arguments)
  | .equal sort left right => by
      rw [atom, coreAtom, term_eq_coreTerm, term_eq_coreTerm]
  | .boolTerm input => by
      rw [atom, coreAtom, term_eq_coreTerm]
def literal (input : CoreSyntax.NormalForm.Literal) : Literal :=
  { polarity := input.positive, atom := atom input.atom }
theorem literal_eq_coreLiteral (input : CoreSyntax.NormalForm.Literal) :
    literal input = coreLiteral input := by
  exact congrArg (fun translated =>
      ({ polarity := input.positive, atom := translated } : Literal)) (atom_eq_coreAtom input.atom)
def literalList : List CoreSyntax.NormalForm.Literal → List Literal
  | [] => []
  | head :: tail => literal head :: literalList tail
theorem literalList_eq_map :
    ∀ literals : List CoreSyntax.NormalForm.Literal,
      literalList literals = literals.map coreLiteral
  | [] => rfl
  | head :: tail => by
      rw [literalList, List.map, literal_eq_coreLiteral, literalList_eq_map]
def clause (input : CoreSyntax.NormalForm.Clause) : Clause :=
  { literals := (literalList input.toList).toArray }
theorem clause_eq_coreClause (input : CoreSyntax.NormalForm.Clause) :
    clause input = coreClause input := by
  apply congrArg (fun literals => ({ literals := literals } : Clause))
  apply Array.toList_inj.mp
  simp [literalList_eq_map]
def clauseList : List CoreSyntax.NormalForm.Clause → List Clause
  | [] => []
  | head :: tail => clause head :: clauseList tail
theorem clauseList_eq_map :
    ∀ clauses : List CoreSyntax.NormalForm.Clause,
      clauseList clauses = clauses.map coreClause
  | [] => rfl
  | head :: tail => by
      rw [clauseList, List.map, clause_eq_coreClause, clauseList_eq_map]
def clauseSet (input : CoreSyntax.NormalForm.ClauseSet) : Array Clause := (clauseList input.toList).toArray
theorem clauseSet_eq_coreClauseSet (input : CoreSyntax.NormalForm.ClauseSet) :
    clauseSet input = coreClauseSet input := by
  apply Array.toList_inj.mp
  simp [clauseSet, coreClauseSet, clauseList_eq_map]
end ReplayCoreProjection
private def clauseListEq : List Clause → List Clause → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      left.eq right && clauseListEq leftRest rightRest
  | _, _ => false
def clauseArrayEq (left right : Array Clause) : Bool :=
  clauseListEq left.toList right.toList
private theorem clauseListEq_sound :
    ∀ {left right : List Clause}, clauseListEq left right = true → left = right
  | [], [], _ => rfl
  | left :: leftRest, right :: rightRest, h => by
      simp only [clauseListEq, Bool.and_eq_true_iff] at h
      have hHead := DAGCertificate.Clause.eq_sound left right h.1
      have hRest := clauseListEq_sound h.2
      cases hHead
      cases hRest
      rfl
  | [], _ :: _, h => by
      simp [clauseListEq] at h
  | _ :: _, [], h => by
      simp [clauseListEq] at h
theorem clauseArrayEq_sound {left right : Array Clause} (h : clauseArrayEq left right = true) : left = right := by
  apply Array.toList_inj.mp
  exact clauseListEq_sound h
namespace SearchDAG
def materializedInitialClauses (dag : SearchDAG) : Result (Array Clause) :=
  dag.initialClauses.mapM clause
/--
确认 search-DAG initial table 与调用者要求的原生字句问题完全一致。
材料化只接受完整表的一一对应，不允许依赖当前 root 切片猜测 source 来自哪个问题。
-/
def ensureInitialClausesMatchProblem (dag : SearchDAG) (problem : ClauseProblem) : Result Unit := do
  let initialClauses ← dag.materializedInitialClauses
  if clauseArrayEq initialClauses problem.initialClauses then
    pure ()
  else
    throw (diagnostic .sourceMaterialization
      "search DAG canonical initial-clause table does not match the requested clause problem")
end SearchDAG
def termSubstitution (input : Substitution) :
    Result (DAGCertificate.TermSubstitution SearchSignature) := do
  input.mapM fun binding => do
    if !firstOrderSortOk binding.key.sort then
      throw (diagnostic .sourceMaterialization
        s!"first-order substitution key uses arrow sort: {reprStr binding.key}")
    if binding.replacement.inferSort? != some binding.key.sort then
      throw (diagnostic .sourceMaterialization
        s!"substitution replacement sort does not match key: {reprStr binding}")
    pure (binding.key.sort, binding.key.id, ← term binding.replacement)
structure PropAtom where
  predicate : CoreSyntax.Search.PredicateKind
  left : SearchTerm
  right : SearchTerm
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
namespace PropAtom
def ofLiteral (literal : SearchLiteral) : PropAtom where
  predicate := literal.predicate
  left := literal.left
  right := literal.right
def toFormula (input : PropAtom) : Result Formula :=
  atom input.predicate input.left input.right
end PropAtom
def findPropAtom? (atoms : Array PropAtom) (atom : PropAtom) : Option Nat := Id.run do
  for h : index in [:atoms.size] do
    if atoms[index] == atom then
      return some index
  return none
def internPropAtom (atoms : Array PropAtom) (atom : PropAtom) :
    Nat × Array PropAtom :=
  match findPropAtom? atoms atom with
  | some index => (index, atoms)
  | none => (atoms.size, atoms.push atom)
def encodeLiteral (atoms : Array PropAtom) (literal : SearchLiteral) :
    PropResolution.Lit × Array PropAtom :=
  let (var, atoms) := internPropAtom atoms (PropAtom.ofLiteral literal)
  ({ var := var, positive := literal.positive }, atoms)
def encodePropClause (atoms : Array PropAtom) (input : SearchClause) :
    PropResolution.Clause × Array PropAtom := Id.run do
  let mut atoms := atoms
  let mut encoded : PropResolution.Clause := #[]
  for literal in input do
    let (propLiteral, atoms') := encodeLiteral atoms literal
    atoms := atoms'
    encoded := encoded.push propLiteral
  return (encoded, atoms)
def guardActivationEncodedClause (guards : GuardSet) (encodedObject : PropResolution.Clause) : PropResolution.Clause :=
  PropResolution.canonicalClause (guards.map PropResolution.Lit.neg ++ encodedObject)
def allInitialIndices (size : Nat) : Array Nat := Id.run do
  let mut out := #[]
  for _h : index in [:size] do
    out := out.push index
  return out
/-! ## residual CDCL 搜索层自动材料化 -/
namespace SearchDAG
private abbrev CdclFeatureWorkspace :=
  Data.ResidualCdclWorkspace
    PropAtom ProofParent CdclInitialFeature CdclAvatarSkeletonFeature
      CdclLearnedFeature CdclGuardActivationFeature
private structure CdclFeatureBuildState where
  dag : SearchDAG
  workspace : CdclFeatureWorkspace := {}
private def requireCurrentInfo (dag : SearchDAG) (info : ClauseInfo) :
    Result ClauseInfo := do
  let current ← requireSome .residualSplit
    s!"residual CDCL source node {info.id} is not present in search DAG" <|
      dag.get? info.id
  if GuardedClause.eq current.guarded info.guarded then
    pure current
  else
    throw (diagnostic .residualSplit
      s!"residual CDCL source node {info.id} does not match current search DAG clause")
private def requireInitialSlot (initialClauses : Array PropResolution.InitialClause)
    (index : Nat) (encoded : PropResolution.Clause) (label : String) : Result Unit := do
  if cdclInitialSlotOk initialClauses index encoded then
    pure ()
  else
    throw (diagnostic .residualSplit
      s!"residual CDCL {label} feature does not match initial slot {index}")
private def addParentFeature (initialClauses : Array PropResolution.InitialClause) (state : CdclFeatureBuildState) (info : ClauseInfo) :
    Result CdclFeatureBuildState := do
  let (encodedRaw, atoms) := encodePropClause state.workspace.atoms info.clause
  match PropResolution.canonicalClause? encodedRaw with
  | none =>
      pure { state with workspace := state.workspace.setAtoms atoms }
  | some encoded =>
      requireInitialSlot initialClauses state.workspace.initialIndex encoded "parent"
      let feature : CdclInitialFeature := {
        initialIndex := state.workspace.initialIndex
        clauseId := info.id
        sourceClause := info.clause
        encodedClause := encoded
        originLabel? := some "parent"
      }
      pure {
        state with
        workspace :=
          state.workspace.pushInitial info.id info.toParent atoms feature
      }
private def addGuardActivationFeature (initialClauses : Array PropResolution.InitialClause) (state : CdclFeatureBuildState) (info : ClauseInfo) :
    Result CdclFeatureBuildState := do
  let (encodedObject, atoms) :=
    encodePropClause state.workspace.atoms info.clause
  let encoded := guardActivationEncodedClause info.guards encodedObject
  match PropResolution.canonicalClause? encoded with
  | none =>
      pure { state with workspace := state.workspace.setAtoms atoms }
  | some encoded =>
      requireInitialSlot initialClauses state.workspace.initialIndex
        encoded "guard activation"
      let feature : CdclGuardActivationFeature := {
        initialIndex := state.workspace.initialIndex
        clauseId := info.id
        sourceClause := info.clause
        guards := Guards.canonical info.guards
        encodedClause := encoded
        originLabel? := some "guard activation"
      }
      pure {
        state with
        workspace :=
          state.workspace.pushGuard info.id info.toParent atoms feature
      }
private def addAvatarSkeletonFeature (initialClauses : Array PropResolution.InitialClause) (state : CdclFeatureBuildState) (info : ClauseInfo)
    (payload : AvatarSplitPayload) :
    Result CdclFeatureBuildState := do
  let skeleton := PropResolution.canonicalClause payload.selectors
  requireInitialSlot initialClauses state.workspace.initialIndex
    skeleton "AVATAR skeleton"
  let feature : CdclAvatarSkeletonFeature := {
    initialIndex := state.workspace.initialIndex
    splitId := info.id
    skeleton := skeleton
    originLabel? := some "AVATAR selector skeleton"
  }
  pure {
    state with
    workspace := state.workspace.pushAvatar info.id info.toParent feature
  }
private def ensureTheoryConflictAndLearned (state : CdclFeatureBuildState) (info : ClauseInfo) :
    Result (CdclFeatureBuildState × ClauseInfo) := do
  let (dag, conflict) ←
    match info.payload with
    | .theoryConflict _ =>
        pure (state.dag, info)
    | _ =>
        requireSome .residualSplit
          s!"residual CDCL source node {info.id} is not a theory conflict" <|
            state.dag.addTheoryConflict? info
  let (dag, learned) ← requireSome .residualSplit
    s!"residual CDCL could not materialize learned clause for conflict {conflict.id}" <|
      dag.addPropositionalLearnedClause? conflict
  pure ({ state with dag := dag }, learned)
private def addLearnedFeature (initialClauses : Array PropResolution.InitialClause) (state : CdclFeatureBuildState) (learned : ClauseInfo)
    (encoded : PropResolution.Clause) :
    Result CdclFeatureBuildState := do
  match PropResolution.canonicalClause? encoded with
  | none =>
      pure state
  | some encoded =>
      requireInitialSlot initialClauses state.workspace.initialIndex encoded "learned"
      let feature : CdclLearnedFeature := {
        initialIndex := state.workspace.initialIndex
        learnedNode := learned.id
        encodedClause := encoded
        originLabel? := some "theory conflict learned"
      }
      pure {
        state with
        workspace :=
          state.workspace.pushLearned learned.id learned.toParent feature
      }
private def addSourceInitialFeature (initialClauses : Array PropResolution.InitialClause) (state : CdclFeatureBuildState) (source : ClauseInfo) :
    Result CdclFeatureBuildState := do
  let info ← requireCurrentInfo state.dag source
  match info.payload with
  | .avatarSplit payload =>
      addAvatarSkeletonFeature initialClauses state info payload
  | .propositionalLearnedClause payload =>
      addLearnedFeature initialClauses state info payload.learned
  | _ =>
      if info.guards.isEmpty then
        addParentFeature initialClauses state info
      else if info.clause.isEmpty then
        let (state, learned) ← ensureTheoryConflictAndLearned state info
        addLearnedFeature initialClauses state learned (Guards.learnedClause info.guards)
      else
        addGuardActivationFeature initialClauses state info
private def finishCdclSummary (initialClauses : Array PropResolution.InitialClause) (certificate : PropResolution.CheckedUnsatCertificate)
    (phase : String) (state : CdclFeatureBuildState) :
    Result CdclResourceSummary := do
  let workspace := state.workspace
  if workspace.initialIndex != initialClauses.size then
    throw (diagnostic .residualSplit (s!"residual CDCL feature slots ended at {workspace.initialIndex}, " ++
        s!"expected {initialClauses.size}"))
  let summary : CdclResourceSummary := {
    phase := phase
    initialFeatures := workspace.initialFeatures
    avatarSkeletonFeatures := workspace.avatarFeatures
    learnedFeatures := workspace.learnedFeatures
    guardActivationFeatures := workspace.guardFeatures
    objectAtomCount := workspace.atoms.size
    usedInitialIndices := allInitialIndices initialClauses.size
    journalSize := certificate.proof.journal.learns.size
    learnedClauses := certificate.proof.journal.learns.size
    resolutionSteps := certificate.proof.journal.steps.size
  }
  if cdclFeatureSlotsComplete summary initialClauses &&
      cdclGuardVariablesOk summary then
    pure summary
  else
    throw (diagnostic .residualSplit
      "residual CDCL generated features failed slot or guard-variable checks")
/--
从一组按 CDCL initial 顺序排列的 search-DAG 字句自动生成 residual CDCL 根节点。
AVATAR split descriptor 生成 selector skeleton initial；普通无 guard 字句生成 parent
initial；guarded 非空字句生成 activation initial；guarded empty 字句会先物化
theory-conflict 与 propositional learned clause，再生成 learned initial。返回的新根已经
通过 SearchDAG 结构 checker。
-/
def addResidualCdclFromSources (dag : SearchDAG) (sources : Array ClauseInfo) (certificate : PropResolution.CheckedUnsatCertificate)
    (phase : String := "search residual CDCL") :
    Result (SearchDAG × ClauseInfo) := do
  if sources.size != certificate.initialClauses.size then
    throw (diagnostic .residualSplit
      "residual CDCL sources and certificate initial clauses are not slot-aligned")
  let initialClauses := certificate.initialClauses
  let mut state : CdclFeatureBuildState := { dag := dag }
  for source in sources do
    state ← addSourceInitialFeature initialClauses state source
  let summary ← finishCdclSummary initialClauses certificate phase state
  if state.workspace.parents.isEmpty then
    throw (diagnostic .residualSplit
      "residual CDCL root has no materialized parent initial sources")
  let payload : ResidualCdclPayload := {
    initialClauses := certificate.initialClauses
    proof := certificate.proof
    summary := summary
  }
  let (dag, info) :=
    state.dag.addPlainClause #[] state.workspace.parents (.residualCdcl payload)
  if dag.check then
    pure (dag, info)
  else
    throw (diagnostic .dagCheck
      s!"search DAG failed checker after residual CDCL materialization at node {info.id}")
end SearchDAG
/-! ## 材料化状态与父快照 -/
structure MaterializedEntry where
  newId : DAGCertificate.NodeId
  clause : Clause
structure MaterializationState where
  entries : Data.StableIdMap MaterializedEntry := {}
  nodes : Array Node := #[]
namespace MaterializationState
def emptyWithCapacity (capacity : Nat) : MaterializationState :=
  {
    entries := Data.StableIdMap.emptyWithCapacity capacity
    nodes := Array.emptyWithCapacity capacity
  }
def newId? (state : MaterializationState) (oldId : NodeId) :
    Option DAGCertificate.NodeId := (state.entries.get? oldId).map (·.newId)
def clause? (state : MaterializationState) (oldId : NodeId) :
    Option Clause := (state.entries.get? oldId).map (·.clause)
def push (state : MaterializationState) (oldId : NodeId) (node : Node) : MaterializationState :=
  { entries := state.entries.insert oldId { newId := node.id, clause := node.conclusion }
    nodes := state.nodes.push node }
end MaterializationState
def parentFromProofParent (state : MaterializationState) (parent : ProofParent) : Result ParentClause := do
  let id ← requireSome .sourceMaterialization
    s!"parent id {parent.id} has not been materialized before child" <|
      state.newId? parent.id
  let stored ← requireSome .sourceMaterialization
    s!"parent id {parent.id} has no materialized clause snapshot" <|
      state.clause? parent.id
  let recorded ← clause parent.clause
  if stored.eq recorded then
    pure { id := id, clause := stored }
  else
    throw (diagnostic .sourceMaterialization
      s!"parent snapshot mismatch for old id {parent.id}")
/--
普通父边只需要物化后的节点编号。

仍然复核搜索器携带的父字句快照，但不构造随后立即丢弃的 `ParentClause`。
-/
def parentIdFromProofParent (state : MaterializationState)
    (parent : ProofParent) : Result DAGCertificate.NodeId := do
  let id ← requireSome .sourceMaterialization
    s!"parent id {parent.id} has not been materialized before child" <|
      state.newId? parent.id
  let stored ← requireSome .sourceMaterialization
    s!"parent id {parent.id} has no materialized clause snapshot" <|
      state.clause? parent.id
  let recorded ← clause parent.clause
  if stored.eq recorded then
    pure id
  else
    throw (diagnostic .sourceMaterialization
      s!"parent snapshot mismatch for old id {parent.id}")
def parentFromRef (state : MaterializationState) (ref : ClauseRef) : Result ParentClause := do
  let id ← requireSome .sourceMaterialization
    s!"resource parent id {ref.id} has not been materialized before child" <|
      state.newId? ref.id
  let stored ← requireSome .sourceMaterialization
    s!"resource parent id {ref.id} has no materialized clause snapshot" <|
      state.clause? ref.id
  match ref.clause? with
  | none =>
      pure { id := id, clause := stored }
  | some raw =>
      let recorded ← clause raw
      if stored.eq recorded then
        pure { id := id, clause := stored }
      else
        throw (diagnostic .sourceMaterialization
          s!"resource parent snapshot mismatch for old id {ref.id}")
def standardizeApartSideEvidence (state : MaterializationState) (ref : ClauseRef) (side : StandardizeApartSideMetadata) :
    Result (DAGCertificate.StandardizeApartSideEvidence SearchSignature) := do
  let parent ← parentFromRef state ref
  let original ← clause side.original
  if !parent.clause.eq original then
    throw (diagnostic .sourceMaterialization
      s!"standardize-apart original snapshot mismatch for old id {ref.id}")
  let renamed ← clause side.renamed
  let evidence : DAGCertificate.StandardizeApartSideEvidence SearchSignature := {
    original := original
    offset := side.offset
    renamed := renamed
  }
  if evidence.check then
    pure evidence
  else
    throw (diagnostic .sourceMaterialization
      s!"standardize-apart renamed snapshot does not replay for old id {ref.id}")
def standardizeApartEvidence (state : MaterializationState) (leftRef rightRef : ClauseRef) (metadata : StandardizeApartMetadata) :
    Result (DAGCertificate.StandardizeApartEvidence SearchSignature) := do
  pure {
    left := (← standardizeApartSideEvidence state leftRef metadata.left)
    right := (← standardizeApartSideEvidence state rightRef metadata.right)
  }
def getSearchLiteral (parentLabel : String) (clause : SearchClause) (index : Nat) : Result SearchLiteral :=
  requireSome .sourceMaterialization
    s!"literal index {index} out of bounds in {parentLabel}" clause[index]?
def requireLiteralIndex (label : String) (index? : Option Nat) : Result Nat :=
  requireSome .sourceMaterialization
    s!"{label} literal index is missing from local rule witness" index?
def getDagLiteral (parentLabel : String) (clause : Clause) (index : Nat) : Result Literal :=
  requireSome .sourceMaterialization
    s!"literal index {index} out of bounds in {parentLabel}" clause.literals[index]?
def equalityAtom? (lit : Literal) : Option (Term × Term) :=
  match lit.atom with
  | .equal left right => some (left, right)
  | _ => none
def ensureLocalEvidenceChecks (label : String) (parentIds : Array NodeId) (result : SearchClause)
    (evidence : DAGCertificate.LocalRuleEvidence SearchSignature) : Result Unit := do
  let conclusion ← clause result
  if DAGCertificate.LocalRuleEvidence.check parentIds conclusion evidence then
    pure ()
  else
    throw (diagnostic .sourceMaterialization
      s!"{label} local rule witness does not replay to its recorded result")
/-! ## 本地规则材料化 -/
def resolutionEvidence (state : MaterializationState) (resource : ResolutionResource) :
    Result (DAGCertificate.LocalRuleEvidence SearchSignature) := do
  let subst ← termSubstitution resource.substitution
  let left ← parentFromRef state resource.left
  let right ← parentFromRef state resource.right
  let standardizeApart? ←
    match resource.standardizeApart? with
    | some metadata => do
        pure (some (← standardizeApartEvidence state resource.left resource.right metadata))
    | none => pure none
  let leftBaseClause :=
    match standardizeApart? with
    | some evidence => evidence.left.renamed
    | none => left.clause
  let rightBaseClause :=
    match standardizeApart? with
    | some evidence => evidence.right.renamed
    | none => right.clause
  let leftClause := DAGCertificate.Clause.applySubstitution subst leftBaseClause
  let rightClause := DAGCertificate.Clause.applySubstitution subst rightBaseClause
  let leftIndex ← requireLiteralIndex "resolution left pivot" resource.leftLiteralIndex?
  let rightIndex ← requireLiteralIndex "resolution right pivot" resource.rightLiteralIndex?
  let leftLit ← getDagLiteral "resolution left parent after substitution" leftClause leftIndex
  let rightLit ← getDagLiteral "resolution right parent after substitution" rightClause rightIndex
  let pivot := leftLit.atom
  if rightLit.matchesAtom (!leftLit.polarity) pivot then
    let evidence : DAGCertificate.LocalRuleEvidence SearchSignature :=
      .resolution {
        left := left
        right := right
        pivot := pivot
        leftPolarity := leftLit.polarity
        substitution := subst
        standardizeApart? := standardizeApart?
      }
    ensureLocalEvidenceChecks "resolution" #[left.id, right.id] resource.result evidence
    pure evidence
  else
    throw (diagnostic .sourceMaterialization
      "resolution indexed pivots are not complementary after first-order materialization")
def factoringEvidence (state : MaterializationState) (resource : UnaryResource) :
    Result (DAGCertificate.LocalRuleEvidence SearchSignature) := do
  let subst ← termSubstitution resource.substitution
  let parent ← parentFromRef state resource.parent
  let firstIndex ← requireLiteralIndex "factoring first literal" resource.literalIndex?
  let secondIndex ← requireLiteralIndex "factoring second literal" resource.otherLiteralIndex?
  if firstIndex == secondIndex then
    throw (diagnostic .sourceMaterialization
      "factoring witness points both occurrences at the same literal index")
  let parentClause := DAGCertificate.Clause.applySubstitution subst parent.clause
  let _ ← getDagLiteral "factoring parent after substitution" parentClause firstIndex
  let _ ← getDagLiteral "factoring parent after substitution" parentClause secondIndex
  let evidence : DAGCertificate.LocalRuleEvidence SearchSignature :=
    .factoring { parent := parent, substitution := subst }
  ensureLocalEvidenceChecks "factoring" #[parent.id] resource.result evidence
  pure evidence
def equalityResolutionEvidence (state : MaterializationState) (resource : UnaryResource) :
    Result (DAGCertificate.LocalRuleEvidence SearchSignature) := do
  let subst ← termSubstitution resource.substitution
  let parent ← parentFromRef state resource.parent
  let literalIndex ←
    requireLiteralIndex "equality-resolution reflexive equality" resource.literalIndex?
  let parentClause := DAGCertificate.Clause.applySubstitution subst parent.clause
  let lit ← getDagLiteral "equality-resolution parent after substitution"
    parentClause literalIndex
  match equalityAtom? lit with
  | some (left, right) =>
      if !lit.polarity && DAGCertificate.StructuralEq.term left right then
        let evidence : DAGCertificate.LocalRuleEvidence SearchSignature :=
          .equalityResolution {
            parent := parent
            left := left
            right := right
            substitution := subst
          }
        ensureLocalEvidenceChecks "equality-resolution" #[parent.id] resource.result evidence
        pure evidence
      else
        throw (diagnostic .sourceMaterialization
          "selected equality-resolution literal is not a negative reflexive equality")
  | none =>
      throw (diagnostic .sourceMaterialization
        "selected equality-resolution literal is not an equality atom")
def splitAt? {α : Type} : List α → Nat → Option (List α × α × List α)
  | [], _ => none
  | head :: rest, 0 => some ([], head, rest)
  | head :: rest, index + 1 => do
      let (before, value, suffix) ← splitAt? rest index
      some (head :: before, value, suffix)
partial def termContextAt? (input : SearchTerm) (path : TermPath) :
    Result (DAGCertificate.TermContext SearchSignature × SearchTerm) := do
  match path with
  | [] =>
      pure (.hole, input)
  | index :: rest =>
      match input with
      | .app symbol args =>
          checkFunctionSymbol symbol args.length
          let (before, selected, suffix) ← requireSome .sourceMaterialization
            s!"term path index {index} out of bounds in application {reprStr symbol}" <|
              splitAt? args index
          let (ctx, hole) ← termContextAt? selected rest
          let before' ← before.mapM term
          let suffix' ← suffix.mapM term
          pure (.app symbol before' ctx suffix', hole)
      | .apply .. =>
          throw (diagnostic .sourceMaterialization
            "rewrite position enters higher-order application; first-order DAG rejected it")
      | .lam .. =>
          throw (diagnostic .sourceMaterialization
            "rewrite position enters lambda body; first-order DAG rejected it")
      | _ =>
          throw (diagnostic .sourceMaterialization
            s!"nonempty rewrite path enters non-application term: {reprStr input}")
def atomContextAt? (targetLiteral : SearchLiteral) (position : PositionedTerm) :
    Result (DAGCertificate.AtomContext SearchSignature × Term × Bool) := do
  match targetLiteral.predicate with
  | .equal =>
      match position.side with
      | .left =>
          let (ctx, hole) ← termContextAt? targetLiteral.left position.path
          pure (.equalLeft ctx (← term targetLiteral.right), (← term hole), targetLiteral.positive)
      | .right =>
          let (ctx, hole) ← termContextAt? targetLiteral.right position.path
          pure (.equalRight (← term targetLiteral.left) ctx, (← term hole), targetLiteral.positive)
  | .member =>
      match position.side with
      | .left =>
          let (ctx, hole) ← termContextAt? targetLiteral.left position.path
          pure (.rel .member [] ctx [← term targetLiteral.right], (← term hole),
            targetLiteral.positive)
      | .right =>
          let (ctx, hole) ← termContextAt? targetLiteral.right position.path
          pure (.rel .member [← term targetLiteral.left] ctx [], (← term hole),
            targetLiteral.positive)
  | .boolHolds =>
      match position.side with
      | .left =>
          let (ctx, hole) ← termContextAt? targetLiteral.left position.path
          pure (.rel .boolHolds [] ctx [], (← term hole), targetLiteral.positive)
      | .right =>
          throw (diagnostic .sourceMaterialization
            "boolHolds right side is metadata in the binary search surface and cannot be rewritten")
  | .definition id arity =>
      match position.side with
      | .left =>
          let (ctx, hole) ← termContextAt? targetLiteral.left position.path
          pure (.rel (.definition id arity) [] ctx [], (← term hole), targetLiteral.positive)
      | .right =>
          throw (diagnostic .sourceMaterialization ("definition predicate right side is metadata in the old search literal " ++
              "and cannot be rewritten"))
  | .predicate symbol =>
      match position.side, position.path with
      | .left, index :: rest =>
          let arguments ← projectedPredicateArguments symbol targetLiteral.left
          let (before, selected, suffix) ← requireSome .sourceMaterialization
            s!"predicate argument index {index} out of bounds for {reprStr symbol}" <|
              splitAt? arguments index
          let (ctx, hole) ← termContextAt? selected rest
          pure (.rel (.predicate symbol) (← before.mapM term) ctx (← suffix.mapM term), (← term hole), targetLiteral.positive)
      | .left, [] =>
          throw (diagnostic .sourceMaterialization ("the predicate tuple wrapper is search metadata and cannot be rewritten " ++
              "as an object term"))
      | .right, _ =>
          throw (diagnostic .sourceMaterialization
            "predicate right side is metadata in the binary search surface and cannot be rewritten")
def rewriteEvidence (state : MaterializationState) (resource : RewriteResource) :
    Result (DAGCertificate.LocalRuleEvidence SearchSignature) := do
  let subst ← termSubstitution resource.substitution
  let equality ← parentFromRef state resource.equality
  let target ← parentFromRef state resource.target
  let standardizeApart? ←
    match resource.standardizeApart? with
    | some metadata => do
        pure (some (← standardizeApartEvidence state resource.equality resource.target metadata))
    | none => pure none
  let rawTargetBase ←
    match resource.standardizeApart? with
    | some metadata => pure metadata.right.renamed
    | none =>
        match resource.target.clause? with
        | some raw => pure raw
        | none =>
            throw (diagnostic .sourceMaterialization
              "rewrite resource does not carry target clause snapshot; cannot rebuild atom context")
  let rawTarget := CoreSyntax.Search.Substitution.applyClause resource.substitution rawTargetBase
  let targetLiteral ← getSearchLiteral "rewrite target parent" rawTarget resource.targetLiteral
  let (context, hole, polarity) ← atomContextAt? targetLiteral resource.targetPosition
  let expectedHole ←
    term (CoreSyntax.Search.Substitution.applyTerm resource.substitution
      resource.targetPosition.term)
  if !(DAGCertificate.StructuralEq.term expectedHole hole) then
    throw (diagnostic .sourceMaterialization
      "rewrite target position snapshot does not match the selected target literal")
  let lhsRaw := CoreSyntax.Search.Substitution.applyTerm resource.substitution resource.orientedLhs
  let rhsRaw := CoreSyntax.Search.Substitution.applyTerm resource.substitution resource.orientedRhs
  let lhs ← term lhsRaw
  let rhs ← term rhsRaw
  if !(DAGCertificate.StructuralEq.term hole lhs) then
    throw (diagnostic .sourceMaterialization
      "rewrite target position is not the substituted oriented lhs")
  let equalityBaseClause :=
    match standardizeApart? with
    | some evidence => evidence.left.renamed
    | none => equality.clause
  let equalityClause := DAGCertificate.Clause.applySubstitution subst equalityBaseClause
  let equalityLiteral ←
    getDagLiteral "rewrite equality parent after substitution"
      equalityClause resource.equalityLiteral
  let equalityReversed ←
    if equalityLiteral.matchesAtom true (.equal lhs rhs) then
      pure false
    else if equalityLiteral.matchesAtom true (.equal rhs lhs) then
      pure true
    else
      throw (diagnostic .sourceMaterialization
        "rewrite equality literal index does not point at either orientation of the equality")
  let kind : DAGCertificate.RewriteKind ←
    match resource.kind with
    | .demodulation =>
        if resource.contextual then
          throw (diagnostic .sourceMaterialization
            "contextual demodulation needs a non-unit equality rule in the new DAG evidence")
        else
          pure .demodulation
    | .positiveSuperposition => pure .positiveSuperposition
    | .negativeSuperposition => pure .negativeSuperposition
    | .contextualDemodulation =>
        throw (diagnostic .sourceMaterialization
          "contextual demodulation is not representable by the current unit demodulation evidence")
    | .extensionalParamodulation =>
        throw (diagnostic .sourceMaterialization
          "extensional paramodulation needs function-theory evidence in the new DAG")
  let localEvidence : DAGCertificate.LocalRuleEvidence SearchSignature :=
    .rewrite kind {
      equality := equality
      target := target
      substitution := subst
      standardizeApart? := standardizeApart?
      context := context
      lhs := lhs
      rhs := rhs
      equalityReversed := equalityReversed
      targetPolarity := polarity
    }
  ensureLocalEvidenceChecks "rewrite/superposition" #[equality.id, target.id]
    resource.result localEvidence
  pure localEvidence
def localRulePayload (state : MaterializationState) (witness : LocalStepWitness) :
    Result (DAGCertificate.LocalRulePayload SearchSignature) := do
  let evidence ←
    match witness with
    | .resolution resource =>
        resolutionEvidence state resource
    | .unary resource =>
        match resource.kind with
        | .ordinaryFactoring | .equalityFactoring =>
            factoringEvidence state resource
        | .equalityResolution =>
            equalityResolutionEvidence state resource
        | .booleanExtensionality =>
            throw (diagnostic .sourceMaterialization
              "boolean extensionality needs FOOL-specific DAG evidence")
        | .argumentCongruence =>
            throw (diagnostic .sourceMaterialization
              "argument congruence needs function-theory DAG evidence")
        | .functionExtensionality =>
            throw (diagnostic .sourceMaterialization
              "function extensionality needs function-theory DAG evidence")
    | .rewrite resource =>
        rewriteEvidence state resource
  pure {
    family := evidence.family
    evidence := evidence
    note := "materialized from search local witness"
  }
/-! ## residual CDCL 材料化 -/
structure CdclMaterial where
  atomMap : Array Formula
  justifications : Array (DAGCertificate.PropInitialJustification SearchSignature)
def cdclMaterial (state : MaterializationState) (summary : CdclResourceSummary) (initialClauses : Array PropResolution.InitialClause) :
    Result CdclMaterial := do
  let mut atoms : Array PropAtom := #[]
  let mut justifications :
    Array (Option (DAGCertificate.PropInitialJustification SearchSignature)) := (List.replicate initialClauses.size none).toArray
  for feature in summary.initialFeatures do
    if _hIndex : feature.initialIndex < initialClauses.size then
      if justifications[feature.initialIndex]!.isSome then
        throw (diagnostic .residualSplit
          s!"duplicate residual CDCL initial justification at slot {feature.initialIndex}")
    else
      throw (diagnostic .residualSplit
        s!"residual CDCL parent feature index out of range: {feature.initialIndex}")
    if !SearchDAG.cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause then
      throw (diagnostic .residualSplit
        s!"residual CDCL parent feature does not match initial slot {feature.initialIndex}")
    let parentId ← requireSome .residualSplit
      s!"residual CDCL parent id {feature.clauseId} has not been materialized" <|
        state.newId? feature.clauseId
    let parentClause ← requireSome .residualSplit
      s!"residual CDCL parent clause {feature.clauseId} has not been materialized" <|
        state.clause? feature.clauseId
    let translatedSource ← clause feature.sourceClause
    if !parentClause.eq translatedSource then
      throw (diagnostic .residualSplit
        s!"residual CDCL source clause mismatch for parent {feature.clauseId}")
    let mut links : Array (DAGCertificate.PropLiteralLink SearchSignature) := #[]
    for lit in feature.sourceClause do
      let (propLit, atoms') := encodeLiteral atoms lit
      atoms := atoms'
      links := links.push {
        prop := propLit
        object := (← literal lit)
      }
    let link : DAGCertificate.PropParentClauseLink SearchSignature := {
      parent := { id := parentId, clause := parentClause }
      literalLinks := links
    }
    justifications :=
      justifications.set! feature.initialIndex (some (.parentClause link))
  for feature in summary.avatarSkeletonFeatures do
    if _hIndex : feature.initialIndex < initialClauses.size then
      if justifications[feature.initialIndex]!.isSome then
        throw (diagnostic .residualSplit
          s!"duplicate residual CDCL initial justification at slot {feature.initialIndex}")
    else
      throw (diagnostic .residualSplit
        s!"residual CDCL AVATAR skeleton feature index out of range: {feature.initialIndex}")
    if !SearchDAG.cdclInitialSlotOk
        initialClauses feature.initialIndex feature.skeleton then
      throw (diagnostic .residualSplit
        s!"residual CDCL AVATAR skeleton does not match initial slot {feature.initialIndex}")
    let splitId ← requireSome .residualSplit
      s!"residual CDCL AVATAR split node {feature.splitId} has not been materialized" <|
        state.newId? feature.splitId
    justifications :=
      justifications.set! feature.initialIndex (some (.avatarSkeleton {
          parent := splitId
          skeleton := feature.skeleton
        }))
  for feature in summary.guardActivationFeatures do
    if _hIndex : feature.initialIndex < initialClauses.size then
      if justifications[feature.initialIndex]!.isSome then
        throw (diagnostic .residualSplit
          s!"duplicate residual CDCL initial justification at slot {feature.initialIndex}")
    else
      throw (diagnostic .residualSplit
        s!"residual CDCL guard activation feature index out of range: {feature.initialIndex}")
    if !SearchDAG.cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause then
      throw (diagnostic .residualSplit (s!"residual CDCL guard activation feature does not match initial slot " ++
          s!"{feature.initialIndex}"))
    let parentId ← requireSome .residualSplit
      s!"residual CDCL guard activation parent id {feature.clauseId} has not been materialized" <|
        state.newId? feature.clauseId
    let parentClause ← requireSome .residualSplit (s!"residual CDCL guard activation parent clause {feature.clauseId} " ++
        "has not been materialized") <|
        state.clause? feature.clauseId
    let translatedSource ← clause feature.sourceClause
    if !parentClause.eq translatedSource then
      throw (diagnostic .residualSplit
        s!"residual CDCL guard activation source clause mismatch for parent {feature.clauseId}")
    let mut links : Array (DAGCertificate.PropLiteralLink SearchSignature) := #[]
    for lit in feature.sourceClause do
      let (propLit, atoms') := encodeLiteral atoms lit
      atoms := atoms'
      links := links.push {
        prop := propLit
        object := (← literal lit)
      }
    let link : DAGCertificate.PropGuardActivationLink SearchSignature := {
      parent := { id := parentId, clause := parentClause }
      guards := Guards.canonical feature.guards
      literalLinks := links
    }
    justifications :=
      justifications.set! feature.initialIndex (some (.guardActivationClause link))
  for feature in summary.learnedFeatures do
    if _hIndex : feature.initialIndex < initialClauses.size then
      if justifications[feature.initialIndex]!.isSome then
        throw (diagnostic .residualSplit
          s!"duplicate residual CDCL initial justification at slot {feature.initialIndex}")
    else
      throw (diagnostic .residualSplit
        s!"residual CDCL learned feature index out of range: {feature.initialIndex}")
    if !SearchDAG.cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause then
      throw (diagnostic .residualSplit
        s!"residual CDCL learned feature does not match initial slot {feature.initialIndex}")
    let learnedId ← requireSome .residualSplit
      s!"residual CDCL learned node {feature.learnedNode} has not been materialized" <|
        state.newId? feature.learnedNode
    justifications :=
      justifications.set! feature.initialIndex (some (.propLearnedClause {
          parent := learnedId
          clause := PropResolution.canonicalClause feature.encodedClause
        }))
  let mut packed :
      Array (DAGCertificate.PropInitialJustification SearchSignature) := #[]
  for h : index in [:justifications.size] do
    match justifications[index] with
    | some justification =>
        packed := packed.push justification
    | none =>
        throw (diagnostic .residualSplit
          s!"missing residual CDCL initial justification at slot {index}")
  let atomMap ← atoms.mapM PropAtom.toFormula
  pure { atomMap := atomMap, justifications := packed }
def residualPayload (state : MaterializationState) (payload : ResidualCdclPayload) :
    Result (DAGCertificate.PropositionalClosurePayload SearchSignature) := do
  let material ← cdclMaterial state payload.summary payload.initialClauses
  if payload.initialClauses.size != material.justifications.size then
    throw (diagnostic .residualSplit
      "residual CDCL initial clauses and materialized justifications have different sizes")
  pure <|
    DAGCertificate.PropositionalClosurePayload.ofRaw payload.initialClauses payload.proof
      material.atomMap material.justifications payload.summary.resolutionSteps
      "materialized from residual CDCL"
def avatarSplitPayload (state : MaterializationState) (payload : AvatarSplitPayload) :
    Result (DAGCertificate.AvatarSplitPayload SearchSignature) := do
  pure {
    source := (← parentFromProofParent state payload.source)
    partitions := payload.partitions
    selectors := payload.selectors
    note := payload.note
  }
def avatarComponentPayload (state : MaterializationState) (payload : AvatarComponentPayload) :
    Result (DAGCertificate.AvatarComponentPayload SearchSignature) := do
  let split ← requireSome .sourceMaterialization
    s!"AVATAR split id {payload.split.id} has not been materialized before component" <|
      state.newId? payload.split.id
  pure {
    split := split
    componentIndex := payload.componentIndex
    note := payload.note
  }
def theoryConflictPayload (state : MaterializationState) (payload : TheoryConflictPayload) :
    Result (DAGCertificate.TheoryConflictPayload SearchSignature) := do
  pure {
    conflict := (← parentFromProofParent state payload.conflict)
    note := payload.note
  }
def propositionalLearnedClausePayload (state : MaterializationState) (payload : PropositionalLearnedClausePayload) :
    Result DAGCertificate.PropositionalLearnedClausePayload := do
  let conflict ← requireSome .residualSplit
    s!"learned-clause conflict node {payload.conflict} has not been materialized" <|
      state.newId? payload.conflict
  pure {
    conflict := conflict
    learned := PropResolution.canonicalClause payload.learned
    note := payload.note
  }
/-! ## 整图材料化入口 -/
def payload (problem : ClauseProblem) (state : MaterializationState) (info : ClauseInfo) (conclusion : Clause) :
    Result Payload := do
  match info.payload with
  | .source source =>
      if !info.parents.isEmpty then
        throw (diagnostic .sourceMaterialization
          s!"source node {info.id} has nonempty parents")
      let initial ← requireSome .sourceMaterialization
        s!"source node {info.id} references missing initial clause {source.initialIndex}" <|
          problem.initialClauses[source.initialIndex]?
      if conclusion.eq initial then
        pure (.source source.initialIndex)
      else
        throw (diagnostic .sourceMaterialization
          s!"source node {info.id} does not match initial clause {source.initialIndex}")
  | .avatarSplit payload =>
      pure (.avatarSplit (← avatarSplitPayload state payload))
  | .avatarComponent payload =>
      pure (.avatarComponent (← avatarComponentPayload state payload))
  | .localStep witness =>
      if !LocalStepWitness.resultMatches witness info.clause then
        throw (diagnostic .sourceMaterialization
          s!"local witness result does not match clause info at node {info.id}")
      pure (.localRule (← localRulePayload state witness))
  | .theoryConflict payload =>
      pure (.theoryConflict (← theoryConflictPayload state payload))
  | .propositionalLearnedClause payload =>
      pure (.propositionalLearnedClause (← propositionalLearnedClausePayload state payload))
  | .residualCdcl payload =>
      pure (.residualCdcl (← residualPayload state payload))
def node (problem : ClauseProblem) (state : MaterializationState) (info : ClauseInfo) : Result Node := do
  let conclusion ← clause info.clause
  let parentIds ←
    info.parents.mapM (fun parent => parentIdFromProofParent state parent)
  let id := state.nodes.size
  let payload ← payload problem state info conclusion
  pure {
    id := id
    parents := parentIds
    ruleTags := payload.ruleTags
    guards := Guards.canonical info.guards
    conclusion := conclusion
    payload := payload
  }
/--
取得可进入材料化的可信 root 切片。
这里统一执行 canonical initial table 对齐与 SearchDAG 全图检查，避免不同材料化出口
分别维护 source 纪律。
-/
def checkedDependencySlice? (problem : ClauseProblem) (dag : SearchDAG) (root : NodeId) : Result (Array ClauseInfo) := do
  dag.ensureInitialClausesMatchProblem problem
  requireSome .dagCheck
    s!"failed to collect checked dependency slice for root {root}" <|
      dag.collectDependencies? root
structure CheckedArtifact (problem : ClauseProblem) where
  checked : CheckedDAG
  problem_eq : checked.dag.problem = problem
namespace CheckedArtifact
def summary {problem : ClauseProblem} (artifact : CheckedArtifact problem) : String :=
  artifact.checked.dag.summary
end CheckedArtifact
end SearchMaterialization
end Automation
end YesMetaZFC
