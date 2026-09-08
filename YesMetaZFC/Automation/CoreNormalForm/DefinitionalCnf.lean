import YesMetaZFC.Automation.CoreNormalForm.AntiPrenexSoundness
/-!
# Core normal form definitional CNF
本模块建立新语义主线使用的可检查定义性 CNF 数据层。它只处理已经处在 NNF
中的量词自由矩阵，通过 Tseitin 定义避免析取/合取分配爆炸；等词原子始终作为
`Atom.equal` 字面量出现在输出子句中，不会被定义谓词遮蔽。开放矩阵中的 typed
自由变量会显式成为定义谓词参数，定义不会退化成与环境无关的零元命题。
-/
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.DefinitionalCnf
structure Config where
  maxDefinitions : Nat := 4096
  maxClauses : Nat := 16384
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
inductive Ref where
  | truth (value : Bool)
  | lit (literal : Literal)
  deriving Repr, Inhabited, Lean.ToExpr
def literalIsEquality (literal : Literal) : Bool :=
  match literal.atom with
  | Atom.equal .. => true
  | _ => false
def literalArrayEq (left right : Array Literal) : Bool :=
  SyntaxEq.literalListEq left.toList right.toList
namespace Ref
def eq : Ref → Ref → Bool
  | truth left, truth right => left == right
  | lit left, lit right => SyntaxEq.literalEq left right
  | _, _ => false
def negate : Ref → Ref
  | truth value => truth (!value)
  | lit literal => lit literal.negate
def isEquality : Ref → Bool
  | truth _ => false
  | lit literal => literalIsEquality literal
end Ref
structure FreeVarParam where
  sort : CoreSort
  varId : VarId
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr
namespace FreeVarParam
def term (parameter : FreeVarParam) : Term :=
  Term.fvar parameter.sort parameter.varId
def insert (parameter : FreeVarParam) (parameters : List FreeVarParam) : List FreeVarParam :=
  if parameters.contains parameter then parameters else parameters ++ [parameter]
def merge (left right : List FreeVarParam) : List FreeVarParam :=
  right.foldl (fun parameters parameter => insert parameter parameters) left
def distinct (parameters : List FreeVarParam) : Bool :=
  parameters.Pairwise fun left right => left != right
def sorts (parameters : List FreeVarParam) : List CoreSort :=
  parameters.map (fun parameter => parameter.sort)
def terms (parameters : List FreeVarParam) : List Term :=
  parameters.map term
end FreeVarParam
mutual
  def Term.freeVarParams : Term → List FreeVarParam
    | Term.bvar .. => []
    | Term.fvar sort varId => [{ sort := sort, varId := varId }]
    | Term.app _ args => Term.freeVarParamsList args
    | Term.apply fn arg => FreeVarParam.merge (Term.freeVarParams fn) (Term.freeVarParams arg)
    | Term.bool _ => []
    | Term.notE body => Term.freeVarParams body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => FreeVarParam.merge (Term.freeVarParams left) (Term.freeVarParams right)
    | Term.quote formula => Formula.freeVarParams formula
    | Term.lam _ _ body => Term.freeVarParams body
    | Term.ite _ condition thenTerm elseTerm =>
        FreeVarParam.merge (Formula.freeVarParams condition) (FreeVarParam.merge (Term.freeVarParams thenTerm) (Term.freeVarParams elseTerm))
  def Formula.freeVarParams : Formula → List FreeVarParam
    | Formula.trueE => []
    | Formula.falseE => []
    | Formula.atom _ args => Term.freeVarParamsList args
    | Formula.equal _ left right => FreeVarParam.merge (Term.freeVarParams left) (Term.freeVarParams right)
    | Formula.boolTerm term => Term.freeVarParams term
    | Formula.neg body => Formula.freeVarParams body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right => FreeVarParam.merge (Formula.freeVarParams left) (Formula.freeVarParams right)
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.freeVarParams body
  def Term.freeVarParamsList : List Term → List FreeVarParam
    | [] => []
    | term :: rest => FreeVarParam.merge (Term.freeVarParams term) (Term.freeVarParamsList rest)
end
def atomFreeVarParams : Atom → List FreeVarParam
  | Atom.predicate _ args => Term.freeVarParamsList args
  | Atom.equal _ left right => FreeVarParam.merge (Term.freeVarParams left) (Term.freeVarParams right)
  | Atom.boolTerm term => Term.freeVarParams term
def literalFreeVarParams (literal : Literal) : List FreeVarParam :=
  atomFreeVarParams literal.atom
def nnfFreeVarParams : Nnf → List FreeVarParam
  | Nnf.trueE => []
  | Nnf.falseE => []
  | Nnf.lit literal => literalFreeVarParams literal
  | Nnf.conj left right
  | Nnf.disj left right => FreeVarParam.merge (nnfFreeVarParams left) (nnfFreeVarParams right)
  | Nnf.forallE _ body
  | Nnf.existsE _ body => nnfFreeVarParams body
structure Definition where
  index : Nat
  predicate : PredicateSymbol
  contextSorts : List CoreSort
  freeVarParams : List FreeVarParam
  body : Nnf
  deriving Repr, Lean.ToExpr
namespace Definition
def inputSorts (definition : Definition) : List CoreSort :=
  definition.contextSorts ++ FreeVarParam.sorts definition.freeVarParams
def arguments (definition : Definition) : List Term :=
  FirstOrderProjection.contextArgs definition.contextSorts ++
    FreeVarParam.terms definition.freeVarParams
def literal (definition : Definition) (positive : Bool := true) : Literal :=
  {
    positive := positive
    atom := Atom.predicate definition.predicate definition.arguments
  }
def atomNnf (definition : Definition) : Nnf :=
  Nnf.lit (definition.literal true)
def formula (definition : Definition) : Formula :=
  FirstOrderProjection.closeForall definition.contextSorts (Formula.iffE (definition.literal true).toFormula definition.body.toFormula)
def hidesEqualityLiteral (definition : Definition) : Bool :=
  match definition.body with
  | Nnf.lit literal => literalIsEquality literal
  | _ => false
def check (definition : Definition) : Bool :=
  definition.predicate.role == PredicateRole.definition &&
    definition.freeVarParams == nnfFreeVarParams definition.body &&
      FreeVarParam.distinct definition.freeVarParams &&
        definition.predicate.arity == definition.inputSorts.length &&
          definition.predicate.inputSorts == definition.inputSorts &&
            definition.body.quantifierFree &&
              !definition.hidesEqualityLiteral &&
                Formula.checkWith definition.contextSorts definition.body.toFormula &&
                  Formula.checkWith definition.contextSorts (definition.literal true).toFormula &&
                    definition.formula.check?
def eq (left right : Definition) : Bool :=
  left.index == right.index &&
    left.predicate == right.predicate &&
      left.contextSorts == right.contextSorts &&
        left.freeVarParams == right.freeVarParams &&
          SyntaxEq.nnfEq left.body right.body
def listEq : List Definition → List Definition → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => eq left right && listEq leftRest rightRest
  | _, _ => false
def arrayEq (left right : Array Definition) : Bool :=
  listEq left.toList right.toList
end Definition
mutual
  def Term.maxPredicateIdSucc : Term → Nat
    | Term.bvar .. => 0
    | Term.fvar .. => 0
    | Term.app _ args => Term.maxPredicateListIdSucc args
    | Term.apply fn arg => Nat.max (Term.maxPredicateIdSucc fn) (Term.maxPredicateIdSucc arg)
    | Term.bool _ => 0
    | Term.notE body => Term.maxPredicateIdSucc body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => Nat.max (Term.maxPredicateIdSucc left) (Term.maxPredicateIdSucc right)
    | Term.quote formula => Formula.maxPredicateIdSucc formula
    | Term.lam _ _ body => Term.maxPredicateIdSucc body
    | Term.ite _ condition thenTerm elseTerm =>
        Nat.max (Formula.maxPredicateIdSucc condition) (Nat.max (Term.maxPredicateIdSucc thenTerm) (Term.maxPredicateIdSucc elseTerm))
  def Formula.maxPredicateIdSucc : Formula → Nat
    | Formula.trueE => 0
    | Formula.falseE => 0
    | Formula.atom predicate args => Nat.max (predicate.id + 1) (Term.maxPredicateListIdSucc args)
    | Formula.equal _ left right => Nat.max (Term.maxPredicateIdSucc left) (Term.maxPredicateIdSucc right)
    | Formula.boolTerm term => Term.maxPredicateIdSucc term
    | Formula.neg body => Formula.maxPredicateIdSucc body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right => Nat.max (Formula.maxPredicateIdSucc left) (Formula.maxPredicateIdSucc right)
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.maxPredicateIdSucc body
  def Term.maxPredicateListIdSucc : List Term → Nat
    | [] => 0
    | term :: rest => Nat.max (Term.maxPredicateIdSucc term) (Term.maxPredicateListIdSucc rest)
end
def atomMaxPredicateIdSucc : Atom → Nat
  | Atom.predicate predicate args => Nat.max (predicate.id + 1) (Term.maxPredicateListIdSucc args)
  | Atom.equal _ left right => Nat.max (Term.maxPredicateIdSucc left) (Term.maxPredicateIdSucc right)
  | Atom.boolTerm term => Term.maxPredicateIdSucc term
def literalMaxPredicateIdSucc (literal : Literal) : Nat :=
  atomMaxPredicateIdSucc literal.atom
def nnfMaxPredicateIdSucc : Nnf → Nat
  | Nnf.trueE => 0
  | Nnf.falseE => 0
  | Nnf.lit literal => literalMaxPredicateIdSucc literal
  | Nnf.conj left right
  | Nnf.disj left right => Nat.max (nnfMaxPredicateIdSucc left) (nnfMaxPredicateIdSucc right)
  | Nnf.forallE _ body
  | Nnf.existsE _ body => nnfMaxPredicateIdSucc body
def clauseOfRefsAux (acc : List Literal) : List Ref → Option Clause
  | [] => some acc.reverse.toArray
  | Ref.truth true :: _ => none
  | Ref.truth false :: rest => clauseOfRefsAux acc rest
  | Ref.lit literal :: rest => clauseOfRefsAux (literal :: acc) rest
def clauseOfRefs (refs : List Ref) : Option Clause :=
  clauseOfRefsAux [] refs
def clausesOfRefs (refs : List Ref) : ClauseSet :=
  match clauseOfRefs refs with
  | some clause => #[clause]
  | none => #[]
structure BuildState where
  nextPredicate : Nat
  definitions : Array Definition := #[]
  deriving Repr, Lean.ToExpr
abbrev BuildM := StateM BuildState
def freshDefinition (contextSorts : List CoreSort) (body : Nnf) : BuildM Literal := do
  let state ← get
  let freeVarParams := nnfFreeVarParams body
  let inputSorts := contextSorts ++ FreeVarParam.sorts freeVarParams
  let predicate : PredicateSymbol := {
    id := state.nextPredicate
    arity := inputSorts.length
    role := PredicateRole.definition
    inputSorts := inputSorts
  }
  let definition : Definition := {
    index := state.definitions.size
    predicate := predicate
    contextSorts := contextSorts
    freeVarParams := freeVarParams
    body := body
  }
  set ({ nextPredicate := state.nextPredicate + 1, definitions := state.definitions.push definition
  } : BuildState)
  pure (definition.literal true)
structure BuildCore where
  ref : Ref
  clauses : ClauseSet
  deriving Repr, Inhabited, Lean.ToExpr
def conjDefinitionClauses (defLit : Literal) (left right : Ref) : ClauseSet :=
  clausesOfRefs [Ref.lit defLit.negate, left] ++
    clausesOfRefs [Ref.lit defLit.negate, right] ++
      clausesOfRefs [Ref.lit defLit, left.negate, right.negate]
def disjDefinitionClauses (defLit : Literal) (left right : Ref) : ClauseSet :=
  clausesOfRefs [Ref.lit defLit, left.negate] ++
    clausesOfRefs [Ref.lit defLit, right.negate] ++
      clausesOfRefs [Ref.lit defLit.negate, left, right]
def buildCore (contextSorts : List CoreSort) : Nnf → BuildM BuildCore
  | Nnf.trueE => pure { ref := Ref.truth true, clauses := #[] }
  | Nnf.falseE => pure { ref := Ref.truth false, clauses := #[] }
  | Nnf.lit literal => pure { ref := Ref.lit literal, clauses := #[] }
  | Nnf.conj left right => do
      let leftResult ← buildCore contextSorts left
      let rightResult ← buildCore contextSorts right
      let defLit ← freshDefinition contextSorts (Nnf.conj left right)
      let definitionClauses :=
        conjDefinitionClauses defLit leftResult.ref rightResult.ref
      pure {
        ref := Ref.lit defLit
        clauses := leftResult.clauses ++ rightResult.clauses ++ definitionClauses
      }
  | Nnf.disj left right => do
      let leftResult ← buildCore contextSorts left
      let rightResult ← buildCore contextSorts right
      let defLit ← freshDefinition contextSorts (Nnf.disj left right)
      let definitionClauses :=
        disjDefinitionClauses defLit leftResult.ref rightResult.ref
      pure {
        ref := Ref.lit defLit
        clauses := leftResult.clauses ++ rightResult.clauses ++ definitionClauses
      }
  | Nnf.forallE .. => pure { ref := Ref.truth false, clauses := #[#[]] }
  | Nnf.existsE .. => pure { ref := Ref.truth false, clauses := #[#[]] }
structure CoreResult where
  root : Ref
  clauses : ClauseSet
  definitions : Array Definition
  deriving Repr, Lean.ToExpr
def buildCoreResult (contextSorts : List CoreSort) (source : Nnf) : CoreResult :=
  let initial : BuildState := {
    nextPredicate := nnfMaxPredicateIdSucc source
  }
  let (core, state) := (buildCore contextSorts source).run initial
  {
    root := core.ref
    clauses := core.clauses ++ clausesOfRefs [core.ref]
    definitions := state.definitions
  }
partial def sourceEqualityLiterals : Nnf → Array Literal
  | Nnf.trueE => #[]
  | Nnf.falseE => #[]
  | Nnf.lit literal => if literalIsEquality literal then #[literal] else #[]
  | Nnf.conj left right
  | Nnf.disj left right => sourceEqualityLiterals left ++ sourceEqualityLiterals right
  | Nnf.forallE _ body
  | Nnf.existsE _ body => sourceEqualityLiterals body
def visibleEqualityLiterals (clauses : ClauseSet) : Array Literal :=
  Id.run do
    let mut out := #[]
    for clause in clauses do
      for literal in clause do
        if literalIsEquality literal then
          out := out.push literal
    return out
def literalMem (literal : Literal) (literals : Array Literal) : Bool :=
  literals.toList.any (fun candidate => SyntaxEq.literalEq literal candidate)
def equalityVisibilityOk (source : Nnf) (clauses : ClauseSet) : Bool :=
  let visible := visibleEqualityLiterals clauses
  (sourceEqualityLiterals source).toList.all (fun literal => literalMem literal visible)
def budgetOk (config : Config) (definitions : Array Definition) (clauses : ClauseSet) : Bool :=
  definitions.size <= config.maxDefinitions &&
    clauses.size <= config.maxClauses
def statsEq (left right : Certificate.Stats) : Bool :=
  left.steps == right.steps &&
    left.clauses == right.clauses &&
      left.literals == right.literals &&
        left.generated == right.generated &&
          left.retained == right.retained &&
            left.verified == right.verified &&
              left.residuals == right.residuals &&
                left.fuel == right.fuel
def statsOf (config : Config) (source : Nnf) (clauses : ClauseSet) (definitions : Array Definition) : Certificate.Stats :=
  {
    steps := definitions.size
    clauses := clauses.size
    literals := clauses.literalCount
    generated := source.size
    retained := clauses.size
    verified := visibleEqualityLiterals clauses |>.size
    residuals := if budgetOk config definitions clauses then 0 else 1
    fuel := config.maxDefinitions
  }
end DefinitionalCnf
structure DefinitionalCnfPayload where
  config : DefinitionalCnf.Config
  contextSorts : List CoreSort
  source : Nnf
  sourceFreeVarParams : List DefinitionalCnf.FreeVarParam
  root : DefinitionalCnf.Ref
  clauses : ClauseSet
  definitions : Array DefinitionalCnf.Definition
  sourceEqualityLiterals : Array Literal
  visibleEqualityLiterals : Array Literal
  sourceSize : Nat
  definitionCount : Nat
  clauseCount : Nat
  literalCount : Nat
  equalityVisible : Bool
  budgetSatisfied : Bool
  stats : Certificate.Stats
  deriving Repr, Lean.ToExpr
namespace DefinitionalCnfPayload
def build (config : DefinitionalCnf.Config) (contextSorts : List CoreSort) (source : Nnf) : DefinitionalCnfPayload :=
  let core := DefinitionalCnf.buildCoreResult contextSorts source
  let sourceEquality := DefinitionalCnf.sourceEqualityLiterals source
  let visibleEquality := DefinitionalCnf.visibleEqualityLiterals core.clauses
  let equalityVisible := DefinitionalCnf.equalityVisibilityOk source core.clauses
  let budgetSatisfied := DefinitionalCnf.budgetOk config core.definitions core.clauses
  {
    config := config
    contextSorts := contextSorts
    source := source
    sourceFreeVarParams := DefinitionalCnf.nnfFreeVarParams source
    root := core.root
    clauses := core.clauses
    definitions := core.definitions
    sourceEqualityLiterals := sourceEquality
    visibleEqualityLiterals := visibleEquality
    sourceSize := source.size
    definitionCount := core.definitions.size
    clauseCount := core.clauses.size
    literalCount := core.clauses.literalCount
    equalityVisible := equalityVisible
    budgetSatisfied := budgetSatisfied
    stats := DefinitionalCnf.statsOf config source core.clauses core.definitions
  }
def eq (left right : DefinitionalCnfPayload) : Bool :=
  left.config == right.config &&
    left.contextSorts == right.contextSorts &&
      SyntaxEq.nnfEq left.source right.source &&
        left.sourceFreeVarParams == right.sourceFreeVarParams &&
          DefinitionalCnf.Ref.eq left.root right.root &&
            ClauseSet.eq left.clauses right.clauses &&
              DefinitionalCnf.Definition.arrayEq left.definitions right.definitions &&
                DefinitionalCnf.literalArrayEq left.sourceEqualityLiterals
                  right.sourceEqualityLiterals &&
                  DefinitionalCnf.literalArrayEq left.visibleEqualityLiterals
                    right.visibleEqualityLiterals &&
                    left.sourceSize == right.sourceSize &&
                      left.definitionCount == right.definitionCount &&
                        left.clauseCount == right.clauseCount &&
                          left.literalCount == right.literalCount &&
                            left.equalityVisible == right.equalityVisible &&
                              left.budgetSatisfied == right.budgetSatisfied &&
                                DefinitionalCnf.statsEq left.stats right.stats
def semanticEq (left right : DefinitionalCnfPayload) : Bool :=
  DefinitionalCnf.Ref.eq left.root right.root &&
    (ClauseSet.eq left.clauses right.clauses && DefinitionalCnf.Definition.arrayEq left.definitions right.definitions)
def check (payload : DefinitionalCnfPayload) : Bool :=
  let expected := build payload.config payload.contextSorts payload.source
  payload.source.quantifierFree &&
    (Formula.checkWith payload.contextSorts payload.source.toFormula && (payload.definitions.toList.all DefinitionalCnf.Definition.check && semanticEq payload expected))
def auditCheck (payload : DefinitionalCnfPayload) : Bool :=
  let expected := build payload.config payload.contextSorts payload.source
  check payload && (payload.equalityVisible && (payload.budgetSatisfied &&
        (payload.sourceFreeVarParams == DefinitionalCnf.nnfFreeVarParams payload.source && (DefinitionalCnf.FreeVarParam.distinct payload.sourceFreeVarParams &&
            (Formula.checkWith payload.contextSorts payload.clauses.toFormula && (DefinitionalCnf.equalityVisibilityOk payload.source payload.clauses && eq payload expected))))))
def mk? (config : DefinitionalCnf.Config) (contextSorts : List CoreSort) (source : Nnf) : Option (Certificate.Checked DefinitionalCnfPayload DefinitionalCnfPayload.check) :=
  Certificate.Checked.mk? (check := DefinitionalCnfPayload.check) (build config contextSorts source)
end DefinitionalCnfPayload
structure DefinitionalCnfResult where
  payload : DefinitionalCnfPayload
  checked? : Option (Certificate.Checked DefinitionalCnfPayload DefinitionalCnfPayload.check)
namespace DefinitionalCnfResult
def build (config : DefinitionalCnf.Config) (contextSorts : List CoreSort) (source : Nnf) : DefinitionalCnfResult :=
  let payload := DefinitionalCnfPayload.build config contextSorts source
  {
    payload := payload
    checked? := Certificate.Checked.mk? (check := DefinitionalCnfPayload.check) payload
  }
def clauses (result : DefinitionalCnfResult) : ClauseSet :=
  result.payload.clauses
def definitions (result : DefinitionalCnfResult) : Array DefinitionalCnf.Definition :=
  result.payload.definitions
def isChecked (result : DefinitionalCnfResult) : Bool :=
  result.checked?.isSome
def check (result : DefinitionalCnfResult) : Bool :=
  DefinitionalCnfPayload.auditCheck result.payload &&
    match result.checked? with
    | some checked => DefinitionalCnfPayload.eq result.payload checked.payload
    | none => false
end DefinitionalCnfResult
def definitionalCnf (source : Nnf) : DefinitionalCnfResult :=
  DefinitionalCnfResult.build {} [] source
def definitionalCnfWith (config : DefinitionalCnf.Config) (contextSorts : List CoreSort) (source : Nnf) : DefinitionalCnfResult :=
  DefinitionalCnfResult.build config contextSorts source
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
