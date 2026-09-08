import YesMetaZFC.Automation.CoreNormalForm.DefinitionalCnf
/-!
# Core normal form local Skolem trace
本模块给 anti-prenex 之后的非前束 NNF 提供局部 Skolem 化 trace。算法按树形结构
就地处理量词：`∀` 打开成 typed 自由变量，`∃` 替换成只依赖当前局部全称上下文的
Skolem 函数应用。这里只建立可计算 payload/checker，不声明对象层 soundness。
-/
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.LocalSkolem
structure Config where
  maxSteps : Nat := 4096
  maxUniversals : Nat := 4096
  maxSkolems : Nat := 4096
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
inductive PathStep where
  | left
  | right
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
abbrev Path := List PathStep
structure UniversalIntro where
  index : Nat
  sort : CoreSort
  varId : VarId
  term : Term
  contextDepth : Nat
  deriving Repr, Lean.ToExpr
namespace UniversalIntro
def check (intro : UniversalIntro) : Bool :=
  SyntaxEq.termEq intro.term (Term.fvar intro.sort intro.varId)
def eq (left right : UniversalIntro) : Bool :=
  left.index == right.index &&
    left.sort == right.sort &&
      left.varId == right.varId &&
        SyntaxEq.termEq left.term right.term &&
          left.contextDepth == right.contextDepth
def listEq : List UniversalIntro → List UniversalIntro → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => eq left right && listEq leftRest rightRest
  | _, _ => false
def arrayEq (left right : Array UniversalIntro) : Bool :=
  listEq left.toList right.toList
end UniversalIntro
structure SkolemIntro where
  index : Nat
  witnessSort : CoreSort
  symbol : FunctionSymbol
  universalContext : Array UniversalIntro
  universalArgs : List Term
  term : Term
  contextDepth : Nat
  deriving Repr, Lean.ToExpr
namespace SkolemIntro
def inputSorts (intro : SkolemIntro) : List CoreSort :=
  intro.universalContext.toList.map (fun universal => universal.sort)
def contextArgs (intro : SkolemIntro) : List Term :=
  intro.universalContext.toList.map (fun universal => universal.term)
def check (intro : SkolemIntro) : Bool :=
  intro.universalContext.all UniversalIntro.check &&
    intro.symbol.role == FunctionRole.skolem &&
      intro.symbol.arity == intro.universalArgs.length &&
        intro.symbol.inputSorts == intro.inputSorts &&
          intro.symbol.outputSort == intro.witnessSort &&
            intro.universalArgs.length == intro.universalContext.size &&
              intro.contextDepth == intro.universalContext.size &&
                SyntaxEq.termListEq intro.universalArgs intro.contextArgs &&
                  SyntaxEq.termEq intro.term (Term.app intro.symbol intro.universalArgs) && (match Term.inferSortWith [] intro.term with
                    | some sort => sort == intro.witnessSort
                    | none => false)
def eq (left right : SkolemIntro) : Bool :=
  left.index == right.index &&
    left.witnessSort == right.witnessSort &&
      left.symbol == right.symbol &&
        UniversalIntro.arrayEq left.universalContext right.universalContext &&
          SyntaxEq.termListEq left.universalArgs right.universalArgs &&
            SyntaxEq.termEq left.term right.term &&
              left.contextDepth == right.contextDepth
def listEq : List SkolemIntro → List SkolemIntro → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => eq left right && listEq leftRest rightRest
  | _, _ => false
def arrayEq (left right : Array SkolemIntro) : Bool :=
  listEq left.toList right.toList
end SkolemIntro
mutual
  def termMaxFVarSucc : Term → Nat
    | Term.bvar .. => 0
    | Term.fvar _ id => id + 1
    | Term.app _ args => termListMaxFVarSucc args
    | Term.apply fn arg => Nat.max (termMaxFVarSucc fn) (termMaxFVarSucc arg)
    | Term.bool _ => 0
    | Term.notE body => termMaxFVarSucc body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => Nat.max (termMaxFVarSucc left) (termMaxFVarSucc right)
    | Term.quote formula => formulaMaxFVarSucc formula
    | Term.lam _ _ body => termMaxFVarSucc body
    | Term.ite _ condition thenTerm elseTerm =>
        Nat.max (formulaMaxFVarSucc condition) (Nat.max (termMaxFVarSucc thenTerm) (termMaxFVarSucc elseTerm))
  def formulaMaxFVarSucc : Formula → Nat
    | Formula.trueE => 0
    | Formula.falseE => 0
    | Formula.atom _ args => termListMaxFVarSucc args
    | Formula.equal _ left right => Nat.max (termMaxFVarSucc left) (termMaxFVarSucc right)
    | Formula.boolTerm term => termMaxFVarSucc term
    | Formula.neg body => formulaMaxFVarSucc body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right => Nat.max (formulaMaxFVarSucc left) (formulaMaxFVarSucc right)
    | Formula.forallE _ body
    | Formula.existsE _ body => formulaMaxFVarSucc body
  def termListMaxFVarSucc : List Term → Nat
    | [] => 0
    | term :: rest => Nat.max (termMaxFVarSucc term) (termListMaxFVarSucc rest)
end
def atomMaxFVarSucc : Atom → Nat
  | Atom.predicate _ args => termListMaxFVarSucc args
  | Atom.equal _ left right => Nat.max (termMaxFVarSucc left) (termMaxFVarSucc right)
  | Atom.boolTerm term => termMaxFVarSucc term
def literalMaxFVarSucc (literal : Literal) : Nat :=
  atomMaxFVarSucc literal.atom
def nnfMaxFVarSucc : Nnf → Nat
  | Nnf.trueE => 0
  | Nnf.falseE => 0
  | Nnf.lit literal => literalMaxFVarSucc literal
  | Nnf.conj left right
  | Nnf.disj left right => Nat.max (nnfMaxFVarSucc left) (nnfMaxFVarSucc right)
  | Nnf.forallE _ body
  | Nnf.existsE _ body => nnfMaxFVarSucc body
mutual
  def termMaxFunctionIdSucc : Term → Nat
    | Term.bvar .. => 0
    | Term.fvar .. => 0
    | Term.app symbol args => Nat.max (symbol.id + 1) (termListMaxFunctionIdSucc args)
    | Term.apply fn arg => Nat.max (termMaxFunctionIdSucc fn) (termMaxFunctionIdSucc arg)
    | Term.bool _ => 0
    | Term.notE body => termMaxFunctionIdSucc body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => Nat.max (termMaxFunctionIdSucc left) (termMaxFunctionIdSucc right)
    | Term.quote formula => formulaMaxFunctionIdSucc formula
    | Term.lam _ _ body => termMaxFunctionIdSucc body
    | Term.ite _ condition thenTerm elseTerm =>
        Nat.max (formulaMaxFunctionIdSucc condition) (Nat.max (termMaxFunctionIdSucc thenTerm) (termMaxFunctionIdSucc elseTerm))
  def formulaMaxFunctionIdSucc : Formula → Nat
    | Formula.trueE => 0
    | Formula.falseE => 0
    | Formula.atom _ args => termListMaxFunctionIdSucc args
    | Formula.equal _ left right => Nat.max (termMaxFunctionIdSucc left) (termMaxFunctionIdSucc right)
    | Formula.boolTerm term => termMaxFunctionIdSucc term
    | Formula.neg body => formulaMaxFunctionIdSucc body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right => Nat.max (formulaMaxFunctionIdSucc left) (formulaMaxFunctionIdSucc right)
    | Formula.forallE _ body
    | Formula.existsE _ body => formulaMaxFunctionIdSucc body
  def termListMaxFunctionIdSucc : List Term → Nat
    | [] => 0
    | term :: rest => Nat.max (termMaxFunctionIdSucc term) (termListMaxFunctionIdSucc rest)
end
def atomMaxFunctionIdSucc : Atom → Nat
  | Atom.predicate _ args => termListMaxFunctionIdSucc args
  | Atom.equal _ left right => Nat.max (termMaxFunctionIdSucc left) (termMaxFunctionIdSucc right)
  | Atom.boolTerm term => termMaxFunctionIdSucc term
def literalMaxFunctionIdSucc (literal : Literal) : Nat :=
  atomMaxFunctionIdSucc literal.atom
def nnfMaxFunctionIdSucc : Nnf → Nat
  | Nnf.trueE => 0
  | Nnf.falseE => 0
  | Nnf.lit literal => literalMaxFunctionIdSucc literal
  | Nnf.conj left right
  | Nnf.disj left right => Nat.max (nnfMaxFunctionIdSucc left) (nnfMaxFunctionIdSucc right)
  | Nnf.forallE _ body
  | Nnf.existsE _ body => nnfMaxFunctionIdSucc body
def instantiateAtomAt (depth : Nat) (replacement : Term) : Atom → Atom
  | Atom.predicate predicate args => Atom.predicate predicate (Term.instantiateListAt depth replacement args)
  | Atom.equal sort left right =>
      Atom.equal sort (Term.instantiateAt depth replacement left) (Term.instantiateAt depth replacement right)
  | Atom.boolTerm term => Atom.boolTerm (Term.instantiateAt depth replacement term)
def instantiateLiteralAt (depth : Nat) (replacement : Term) (literal : Literal) : Literal :=
  { literal with atom := instantiateAtomAt depth replacement literal.atom }
def instantiateNnfAt (depth : Nat) (replacement : Term) : Nnf → Nnf
  | Nnf.trueE => Nnf.trueE
  | Nnf.falseE => Nnf.falseE
  | Nnf.lit literal => Nnf.lit (instantiateLiteralAt depth replacement literal)
  | Nnf.conj left right =>
      Nnf.conj (instantiateNnfAt depth replacement left) (instantiateNnfAt depth replacement right)
  | Nnf.disj left right =>
      Nnf.disj (instantiateNnfAt depth replacement left) (instantiateNnfAt depth replacement right)
  | Nnf.forallE sort body => Nnf.forallE sort (instantiateNnfAt (depth + 1) replacement body)
  | Nnf.existsE sort body => Nnf.existsE sort (instantiateNnfAt (depth + 1) replacement body)
def instantiateNnf (replacement : Term) (body : Nnf) : Nnf :=
  instantiateNnfAt 0 replacement body
def skolemMeasure : Nnf → Nat
  | Nnf.trueE | Nnf.falseE | Nnf.lit _ => 1
  | Nnf.conj left right | Nnf.disj left right => skolemMeasure left + skolemMeasure right + 1
  | Nnf.forallE _ body | Nnf.existsE _ body => skolemMeasure body + 1
theorem instantiateNnfAt_measure (depth : Nat) (replacement : Term) (nnf : Nnf) : skolemMeasure (instantiateNnfAt depth replacement nnf) = skolemMeasure nnf := by
  induction nnf generalizing depth with
  | trueE | falseE | lit => rfl
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight =>
      simp only [instantiateNnfAt, skolemMeasure]
      rw [ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih =>
      simp only [instantiateNnfAt, skolemMeasure]
      rw [ih]
theorem instantiateNnf_measure (replacement : Term) (nnf : Nnf) : skolemMeasure (instantiateNnf replacement nnf) = skolemMeasure nnf :=
  instantiateNnfAt_measure 0 replacement nnf
theorem instantiateAtomAt_toFormula (depth : Nat) (replacement : Term) (atom : Atom) : (instantiateAtomAt depth replacement atom).toFormula = Formula.instantiateAt depth replacement atom.toFormula := by
  cases atom <;>
    simp [instantiateAtomAt, Atom.toFormula, Formula.instantiateAt]
theorem instantiateLiteralAt_toFormula (depth : Nat) (replacement : Term) (literal : Literal) : (instantiateLiteralAt depth replacement literal).toFormula = Formula.instantiateAt depth replacement literal.toFormula := by
  cases literal with
  | mk positive atom =>
      cases positive <;>
        simp [instantiateLiteralAt, Literal.toFormula, Formula.instantiateAt, instantiateAtomAt_toFormula]
theorem instantiateNnfAt_toFormula (depth : Nat) (replacement : Term) (nnf : Nnf) : (instantiateNnfAt depth replacement nnf).toFormula = Formula.instantiateAt depth replacement nnf.toFormula := by
  induction nnf generalizing depth with
  | trueE => rfl
  | falseE => rfl
  | lit literal => simp [instantiateNnfAt, Nnf.toFormula, instantiateLiteralAt_toFormula]
  | conj left right ihLeft ihRight => simp [instantiateNnfAt, Nnf.toFormula, Formula.instantiateAt, ihLeft, ihRight]
  | disj left right ihLeft ihRight => simp [instantiateNnfAt, Nnf.toFormula, Formula.instantiateAt, ihLeft, ihRight]
  | forallE sort body ih => simp [instantiateNnfAt, Nnf.toFormula, Formula.instantiateAt, ih]
  | existsE sort body ih => simp [instantiateNnfAt, Nnf.toFormula, Formula.instantiateAt, ih]
theorem instantiateNnfAt_satisfies {M : Semantics.Model} (env : Semantics.Env M) (depth : Nat) (replacement : Term) (nnf : Nnf) : Semantics.Nnf.Satisfies env (instantiateNnfAt depth replacement nnf) ↔ Semantics.Nnf.Satisfies (env.insertAt depth (Semantics.Term.eval (env.drop depth) replacement)) nnf := by rw [← Semantics.Nnf.satisfies_toFormula, instantiateNnfAt_toFormula, Semantics.Formula.satisfies_instantiateAt, Semantics.Nnf.satisfies_toFormula]
theorem instantiateNnf_satisfies {M : Semantics.Model} (env : Semantics.Env M) (replacement : Term) (body : Nnf) : Semantics.Nnf.Satisfies env (instantiateNnf replacement body) ↔ Semantics.Nnf.Satisfies (env.insertAt 0 (Semantics.Term.eval env replacement)) body := by
  simpa [instantiateNnf, Semantics.Env.drop] using
    instantiateNnfAt_satisfies env 0 replacement body
structure Context where
  universals : List UniversalIntro := []
  deriving Repr, Lean.ToExpr
namespace Context
def orderedUniversals (context : Context) : Array UniversalIntro :=
  context.universals.reverse.toArray
def skolemArgs (context : Context) : List Term :=
  context.orderedUniversals.toList.map (fun universal => universal.term)
def skolemInputSorts (context : Context) : List CoreSort :=
  context.orderedUniversals.toList.map (fun universal => universal.sort)
def depth (context : Context) : Nat :=
  context.universals.length
end Context
inductive StepKind where
  | openForall
  | skolemizeExists
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
structure Step where
  path : Path
  kind : StepKind
  binderSort : CoreSort
  body : Nnf
  replacement : Term
  instantiatedBody : Nnf
  universalContext : Array UniversalIntro
  universal? : Option UniversalIntro := none
  skolem? : Option SkolemIntro := none
  deriving Repr, Lean.ToExpr
namespace Step
def universalOptionEq : Option UniversalIntro → Option UniversalIntro → Bool
  | none, none => true
  | some left, some right => UniversalIntro.eq left right
  | _, _ => false
def eq (left right : Step) : Bool :=
  left.path == right.path &&
    left.kind == right.kind &&
      left.binderSort == right.binderSort &&
        SyntaxEq.nnfEq left.body right.body &&
          SyntaxEq.termEq left.replacement right.replacement &&
            SyntaxEq.nnfEq left.instantiatedBody right.instantiatedBody &&
              UniversalIntro.arrayEq left.universalContext right.universalContext &&
                universalOptionEq left.universal? right.universal? && (match left.skolem?, right.skolem? with
                  | none, none => true
                  | some leftIntro, some rightIntro => SkolemIntro.eq leftIntro rightIntro
                  | _, _ => false)
def check (step : Step) : Bool :=
  step.universalContext.all UniversalIntro.check &&
    SyntaxEq.nnfEq step.instantiatedBody (instantiateNnf step.replacement step.body) &&
      match step.kind, step.universal?, step.skolem? with
      | StepKind.openForall, some universal, none =>
          universal.check &&
            universal.sort == step.binderSort &&
              SyntaxEq.termEq universal.term step.replacement &&
                universal.contextDepth == step.universalContext.size
      | StepKind.skolemizeExists, none, some intro =>
          intro.check &&
            intro.witnessSort == step.binderSort &&
              UniversalIntro.arrayEq intro.universalContext step.universalContext &&
                SyntaxEq.termEq intro.term step.replacement
      | _, _, _ => false
end Step
abbrev Trace := Array Step
namespace Trace
def listEq : List Step → List Step → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => Step.eq left right && listEq leftRest rightRest
  | _, _ => false
def eq (left right : Trace) : Bool :=
  listEq left.toList right.toList
def check (trace : Trace) : Bool :=
  trace.all Step.check
end Trace
namespace SharedState
def allChecked {α : Type} (check : α → Bool) : List α → Bool
  | [] => true
  | value :: rest => check value && allChecked check rest
theorem checked_of_mem {α : Type} {check : α → Bool} {values : List α} (hAll : allChecked check values = true) {value : α} (hMem : value ∈ values) : check value = true := by
  induction values with
  | nil => simp at hMem
  | cons head tail ih =>
      simp only [allChecked, Bool.and_eq_true_iff] at hAll
      rcases List.mem_cons.mp hMem with rfl | hTail
      · exact hAll.1
      · exact ih hAll.2 hTail
def universalSequenceFrom (base index : Nat) : List UniversalIntro → Bool
  | [] => true
  | intro :: rest =>
      intro.index == index && (intro.varId == base + index && universalSequenceFrom base (index + 1) rest)
theorem universal_fresh_of_sequenceFrom {base index : Nat} {intros : List UniversalIntro} (hSequence : universalSequenceFrom base index intros = true) {intro : UniversalIntro} (hMem : intro ∈ intros) : base ≤ intro.varId := by
  induction intros generalizing index with
  | nil => simp at hMem
  | cons value values ih =>
      simp only [universalSequenceFrom, Bool.and_eq_true_iff] at hSequence
      rcases List.mem_cons.mp hMem with hEq | hTail
      · cases hEq
        have hId : intro.varId = base + index := by simpa using hSequence.2.1
        rw [hId]
        omega
      · exact ih hSequence.2.2 hTail
def skolemSequenceFrom (base index : Nat) : List SkolemIntro → Bool
  | [] => true
  | intro :: rest =>
      intro.index == index && (intro.symbol.id == base + index && skolemSequenceFrom base (index + 1) rest)
theorem skolem_fresh_of_sequenceFrom {base index : Nat} {intros : List SkolemIntro} (hSequence : skolemSequenceFrom base index intros = true) {intro : SkolemIntro} (hMem : intro ∈ intros) : base ≤ intro.symbol.id := by
  induction intros generalizing index with
  | nil => simp at hMem
  | cons value values ih =>
      simp only [skolemSequenceFrom, Bool.and_eq_true_iff] at hSequence
      rcases List.mem_cons.mp hMem with hEq | hTail
      · cases hEq
        have hId : intro.symbol.id = base + index := by simpa using hSequence.2.1
        rw [hId]
        omega
      · exact ih hSequence.2.2 hTail
end SharedState
structure BuildState where
  nextFVar : Nat
  nextSkolem : Nat
  steps : Array Step := #[]
  universalTrace : Array UniversalIntro := #[]
  skolemTrace : Array SkolemIntro := #[]
  deriving Repr, Lean.ToExpr
abbrev BuildM := StateM BuildState
def initialState (source : Nnf) : BuildState where
  nextFVar := nnfMaxFVarSucc source
  nextSkolem := nnfMaxFunctionIdSucc source
def freshUniversal (path : Path) (context : Context) (sort : CoreSort) (body : Nnf) : BuildM UniversalIntro := do
  let state ← get
  let varId := state.nextFVar
  let term := Term.fvar sort varId
  let universal : UniversalIntro := {
    index := state.universalTrace.size
    sort := sort
    varId := varId
    term := term
    contextDepth := context.depth
  }
  let instantiated := instantiateNnf term body
  let step : Step := {
    path := path
    kind := StepKind.openForall
    binderSort := sort
    body := body
    replacement := term
    instantiatedBody := instantiated
    universalContext := context.orderedUniversals
    universal? := some universal
  }
  set {
    state with
    nextFVar := state.nextFVar + 1
    steps := state.steps.push step
    universalTrace := state.universalTrace.push universal
  }
  pure universal
def freshSkolem (path : Path) (context : Context) (sort : CoreSort) (body : Nnf) : BuildM SkolemIntro := do
  let state ← get
  let universalContext := context.orderedUniversals
  let universalArgs := context.skolemArgs
  let symbol : FunctionSymbol := {
    id := state.nextSkolem
    arity := universalArgs.length
    role := FunctionRole.skolem
    inputSorts := context.skolemInputSorts
    outputSort := sort
  }
  let term := Term.app symbol universalArgs
  let intro : SkolemIntro := {
    index := state.skolemTrace.size
    witnessSort := sort
    symbol := symbol
    universalContext := universalContext
    universalArgs := universalArgs
    term := term
    contextDepth := universalContext.size
  }
  let instantiated := instantiateNnf term body
  let step : Step := {
    path := path
    kind := StepKind.skolemizeExists
    binderSort := sort
    body := body
    replacement := term
    instantiatedBody := instantiated
    universalContext := universalContext
    skolem? := some intro
  }
  set {
    state with
    nextSkolem := state.nextSkolem + 1
    steps := state.steps.push step
    skolemTrace := state.skolemTrace.push intro
  }
  pure intro
def skolemizeAt (path : Path) (context : Context) : Nnf → BuildM Nnf
  | Nnf.trueE => pure Nnf.trueE
  | Nnf.falseE => pure Nnf.falseE
  | Nnf.lit literal => pure (Nnf.lit literal)
  | Nnf.conj left right => do
      let left ← skolemizeAt (path ++ [PathStep.left]) context left
      let right ← skolemizeAt (path ++ [PathStep.right]) context right
      pure (Nnf.conj left right)
  | Nnf.disj left right => do
      let left ← skolemizeAt (path ++ [PathStep.left]) context left
      let right ← skolemizeAt (path ++ [PathStep.right]) context right
      pure (Nnf.disj left right)
  | Nnf.forallE sort body => do
      let universal ← freshUniversal path context sort body
      let instantiated := instantiateNnf universal.term body
      skolemizeAt path { universals := universal :: context.universals } instantiated
  | Nnf.existsE sort body => do
      let intro ← freshSkolem path context sort body
      let instantiated := instantiateNnf intro.term body
      skolemizeAt path context instantiated
termination_by nnf => skolemMeasure nnf
decreasing_by
  all_goals simp [skolemMeasure, instantiateNnf_measure] <;> omega
structure CoreResult where
  result : Nnf
  trace : Trace
  universalTrace : Array UniversalIntro
  skolemTrace : Array SkolemIntro
  deriving Repr, Lean.ToExpr
def buildCore (source : Nnf) : CoreResult :=
  let initial := initialState source
  let (result, state) := (skolemizeAt [] {} source).run initial
  {
    result := result
    trace := state.steps
    universalTrace := state.universalTrace
    skolemTrace := state.skolemTrace
  }
def budgetOk (config : Config) (core : CoreResult) : Bool :=
  core.trace.size <= config.maxSteps &&
    core.universalTrace.size <= config.maxUniversals &&
      core.skolemTrace.size <= config.maxSkolems
def statsEq (left right : Certificate.Stats) : Bool :=
  left.steps == right.steps &&
    left.clauses == right.clauses &&
      left.literals == right.literals &&
        left.generated == right.generated &&
          left.retained == right.retained &&
            left.verified == right.verified &&
              left.residuals == right.residuals &&
                left.fuel == right.fuel
def statsOf (config : Config) (source : Nnf) (core : CoreResult) : Certificate.Stats :=
  {
    steps := core.trace.size
    generated := source.size
    retained := core.result.size
    verified := core.trace.size
    residuals := if budgetOk config core then 0 else 1
    fuel := config.maxSteps
  }
end LocalSkolem
structure LocalSkolemPayload where
  config : LocalSkolem.Config
  source : Nnf
  result : Nnf
  trace : LocalSkolem.Trace
  universalTrace : Array LocalSkolem.UniversalIntro
  skolemTrace : Array LocalSkolem.SkolemIntro
  sourceSize : Nat
  resultSize : Nat
  steps : Nat
  universalCount : Nat
  skolemCount : Nat
  budgetSatisfied : Bool
  stats : Certificate.Stats
  deriving Repr, Lean.ToExpr
namespace LocalSkolemPayload
def build (config : LocalSkolem.Config) (source : Nnf) : LocalSkolemPayload :=
  let core := LocalSkolem.buildCore source
  let budgetSatisfied := LocalSkolem.budgetOk config core
  {
    config := config
    source := source
    result := core.result
    trace := core.trace
    universalTrace := core.universalTrace
    skolemTrace := core.skolemTrace
    sourceSize := source.size
    resultSize := core.result.size
    steps := core.trace.size
    universalCount := core.universalTrace.size
    skolemCount := core.skolemTrace.size
    budgetSatisfied := budgetSatisfied
    stats := LocalSkolem.statsOf config source core
  }
def eq (left right : LocalSkolemPayload) : Bool :=
  left.config == right.config &&
    SyntaxEq.nnfEq left.source right.source &&
      SyntaxEq.nnfEq left.result right.result &&
        LocalSkolem.Trace.eq left.trace right.trace &&
          LocalSkolem.UniversalIntro.arrayEq left.universalTrace right.universalTrace &&
            LocalSkolem.SkolemIntro.arrayEq left.skolemTrace right.skolemTrace &&
              left.sourceSize == right.sourceSize &&
                left.resultSize == right.resultSize &&
                  left.steps == right.steps &&
                    left.universalCount == right.universalCount &&
                      left.skolemCount == right.skolemCount &&
                        left.budgetSatisfied == right.budgetSatisfied &&
                          LocalSkolem.statsEq left.stats right.stats
def structuralCheck (payload : LocalSkolemPayload) : Bool :=
  payload.source.toFormula.check? &&
    payload.result.toFormula.check? &&
      payload.result.quantifierFree &&
        payload.budgetSatisfied &&
          LocalSkolem.Trace.check payload.trace
def dependencyCheck (payload : LocalSkolemPayload) : Bool :=
  LocalSkolem.SharedState.allChecked
      LocalSkolem.UniversalIntro.check payload.universalTrace.toList &&
    LocalSkolem.SharedState.allChecked
      LocalSkolem.SkolemIntro.check payload.skolemTrace.toList
def freshnessCheck (payload : LocalSkolemPayload) : Bool :=
  LocalSkolem.SharedState.universalSequenceFrom (LocalSkolem.nnfMaxFVarSucc payload.source) 0
      payload.universalTrace.toList &&
    LocalSkolem.SharedState.skolemSequenceFrom (LocalSkolem.nnfMaxFunctionIdSucc payload.source) 0
      payload.skolemTrace.toList
def check (payload : LocalSkolemPayload) : Bool :=
  let expected := build payload.config payload.source
  structuralCheck payload && (dependencyCheck payload && (freshnessCheck payload && eq payload expected))
structure SharedStateSound (payload : LocalSkolemPayload) : Prop where
  structuralChecked : structuralCheck payload = true
  dependencyChecked : dependencyCheck payload = true
  freshnessChecked : freshnessCheck payload = true
  rebuilt : eq payload (build payload.config payload.source) = true
  universalFresh :
    ∀ intro ∈ payload.universalTrace.toList,
      LocalSkolem.nnfMaxFVarSucc payload.source ≤ intro.varId
  skolemFresh :
    ∀ intro ∈ payload.skolemTrace.toList,
      LocalSkolem.nnfMaxFunctionIdSucc payload.source ≤ intro.symbol.id
  universalParametersChecked :
    ∀ intro ∈ payload.universalTrace.toList,
      LocalSkolem.UniversalIntro.check intro = true
  skolemParametersChecked :
    ∀ intro ∈ payload.skolemTrace.toList,
      LocalSkolem.SkolemIntro.check intro = true
theorem sharedStateSound_of_check {payload : LocalSkolemPayload} (hCheck : check payload = true) : SharedStateSound payload := by
  unfold check at hCheck
  simp only [Bool.and_eq_true_iff] at hCheck
  have hStructural := hCheck.1
  have hDependency := hCheck.2.1
  have hFreshness := hCheck.2.2.1
  have hRebuilt := hCheck.2.2.2
  have hDependencyParts := Bool.and_eq_true_iff.mp hDependency
  have hFreshnessParts := Bool.and_eq_true_iff.mp hFreshness
  exact {
    structuralChecked := hStructural
    dependencyChecked := hDependency
    freshnessChecked := hFreshness
    rebuilt := hRebuilt
    universalFresh := by
      intro intro hMem
      exact LocalSkolem.SharedState.universal_fresh_of_sequenceFrom
        hFreshnessParts.1 hMem
    skolemFresh := by
      intro intro hMem
      exact LocalSkolem.SharedState.skolem_fresh_of_sequenceFrom
        hFreshnessParts.2 hMem
    universalParametersChecked := by
      intro intro hMem
      exact LocalSkolem.SharedState.checked_of_mem hDependencyParts.1 hMem
    skolemParametersChecked := by
      intro intro hMem
      exact LocalSkolem.SharedState.checked_of_mem hDependencyParts.2 hMem
  }
def mk? (config : LocalSkolem.Config) (source : Nnf) : Option (Certificate.Checked LocalSkolemPayload LocalSkolemPayload.check) :=
  Certificate.Checked.mk? (check := LocalSkolemPayload.check) (build config source)
end LocalSkolemPayload
structure LocalSkolemResult where
  payload : LocalSkolemPayload
  checked? : Option (Certificate.Checked LocalSkolemPayload LocalSkolemPayload.check)
namespace LocalSkolemResult
def build (config : LocalSkolem.Config) (source : Nnf) : LocalSkolemResult :=
  let payload := LocalSkolemPayload.build config source
  {
    payload := payload
    checked? := Certificate.Checked.mk? (check := LocalSkolemPayload.check) payload
  }
def result (result : LocalSkolemResult) : Nnf :=
  result.payload.result
def trace (result : LocalSkolemResult) : LocalSkolem.Trace :=
  result.payload.trace
def isChecked (result : LocalSkolemResult) : Bool :=
  result.checked?.isSome
def check (result : LocalSkolemResult) : Bool :=
  LocalSkolemPayload.check result.payload &&
    match result.checked? with
    | some checked => LocalSkolemPayload.eq result.payload checked.payload
    | none => false
end LocalSkolemResult
def localSkolem (source : Nnf) : LocalSkolemResult :=
  LocalSkolemResult.build {} source
def localSkolemWith (config : LocalSkolem.Config) (source : Nnf) : LocalSkolemResult :=
  LocalSkolemResult.build config source
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
