import YesMetaZFC.Automation.Request
/-!
# 普通 Lean `Prop` 的可信语义核

本模块只保存宿主命题骨架、proof-carrying facts 及其到公共一阶搜索语义的桥接。
Lean 元层重化由 `HostRules.Frontend` 负责，AVATAR 证书物化与宿主回放由
`HostRules.Backend` 负责。
-/
namespace YesMetaZFC
namespace Automation
namespace HostProp
universe x
open Lean Meta
open CoreSyntax
open CoreSyntax.NormalForm
structure Atom where
  id : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
inductive Formula where
  | atom (value : Atom)
  | falsum
  | truth
  | neg (body : Formula)
  | conj (left right : Formula)
  | disj (left right : Formula)
  | imp (left right : Formula)
  | iff (left right : Formula)
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace Formula
def eval (atoms : Nat → Prop) : Formula → Prop
  | .atom value => atoms value.id
  | .falsum => False
  | .truth => True
  | .neg body => ¬ eval atoms body
  | .conj left right => eval atoms left ∧ eval atoms right
  | .disj left right => eval atoms left ∨ eval atoms right
  | .imp left right => eval atoms left → eval atoms right
  | .iff left right => eval atoms left ↔ eval atoms right
def predicate (atom : Atom) : CoreSyntax.PredicateSymbol := {
  id := atom.id
  arity := 0
  role := .relation
  inputSorts := []
}
def toCore : Formula → CoreSyntax.Formula
  | .atom value => .atom (predicate value) []
  | .falsum => .falseE
  | .truth => .trueE
  | .neg body => .neg body.toCore
  | .conj left right => .conj left.toCore right.toCore
  | .disj left right => .disj left.toCore right.toCore
  | .imp left right => .imp left.toCore right.toCore
  | .iff left right => .iffE left.toCore right.toCore
def toSearch : Formula →
    Logic.FirstOrder.Formula SearchMaterialization.SearchSignature
  | .atom value => .rel (.predicate (predicate value)) []
  | .falsum => .falsum
  | .truth => .truth
  | .neg body => .neg body.toSearch
  | .conj left right => .conj left.toSearch right.toSearch
  | .disj left right => .disj left.toSearch right.toSearch
  | .imp left right => .imp left.toSearch right.toSearch
  | .iff left right => .iff left.toSearch right.toSearch
/-! ## 宿主命题骨架的良构性证书 -/
theorem toSearch_admissible (formula : Formula) :
    Logic.FirstOrder.Formula.Admissible formula.toSearch := by
  induction formula with
  | atom value =>
      constructor
      · exact Logic.FirstOrder.FormulaWellFormed.rel (σ := SearchMaterialization.SearchSignature)
          (SearchMaterialization.RelSymbol.predicate (predicate value)) .nil
      · exact Logic.FirstOrder.FormulaScoped.rel (σ := SearchMaterialization.SearchSignature)
          (SearchMaterialization.RelSymbol.predicate (predicate value)) [] (by
            intro term hTerm
            cases hTerm)
  | falsum =>
      exact Logic.FirstOrder.Formula.Admissible.falsum
  | truth =>
      exact Logic.FirstOrder.Formula.Admissible.truth
  | neg body ih =>
      exact Logic.FirstOrder.Formula.Admissible.neg ih
  | conj left right ihLeft ihRight =>
      exact Logic.FirstOrder.Formula.Admissible.conj ihLeft ihRight
  | disj left right ihLeft ihRight =>
      exact Logic.FirstOrder.Formula.Admissible.disj ihLeft ihRight
  | imp left right ihLeft ihRight =>
      exact Logic.FirstOrder.Formula.Admissible.imp ihLeft ihRight
  | iff left right ihLeft ihRight =>
      exact Logic.FirstOrder.Formula.Admissible.iff ihLeft ihRight
end Formula
inductive Facts where
  | nil
  | cons (proposition : Prop) (proof : proposition) (tail : Facts)
namespace Facts
@[reducible] def propositions : Facts → List Prop
  | .nil => []
  | .cons proposition _ tail => proposition :: tail.propositions
theorem holds : ∀ (facts : Facts) (proposition : Prop),
    proposition ∈ facts.propositions → proposition
  | .nil, proposition, hMem => by
      simp [propositions] at hMem
  | .cons head proof tail, proposition, hMem => by
      simp only [propositions, List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · simpa [hHead] using proof
      · exact tail.holds proposition hTail
end Facts
/--
元层重化的 proof-carrying 结果。
两个 alignment 字段把纯语法快照钉回原 Lean 命题；后端 closed 计算不读取它们。
-/
structure CheckedInput (goal : Prop) where
  atoms : Nat → Prop
  facts : Facts
  premises : List Formula
  target : Formula
  premisesAligned :
    premises.map (Formula.eval atoms) = facts.propositions
  targetAligned :
    Formula.eval atoms target = goal
namespace CheckedInput
theorem premiseHolds {goal : Prop} (input : CheckedInput goal)
    {formula : Formula} (hFormula : formula ∈ input.premises) :
    Formula.eval input.atoms formula := by
  apply input.facts.holds
  rw [← input.premisesAligned]
  exact List.mem_map.mpr ⟨formula, hFormula, rfl⟩
theorem goalOfTarget {goal : Prop} (input : CheckedInput goal) (hTarget : Formula.eval input.atoms input.target) : goal := by
  rw [← input.targetAligned]
  exact hTarget
def sourceProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.Problem := {
  premises := premises.map Formula.toCore
  target := target.toCore
}
def deepProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.DeepProblem := {
  premises := premises.map Formula.toSearch
  target := target.toSearch
}
theorem deepProblemOfSyntax_admissible (premises : List Formula) (target : Formula) :
    LogicSoundness.SetLevel.DeepProblem.Admissible (deepProblemOfSyntax premises target) := by
  constructor
  · exact target.toSearch_admissible
  · intro premise hPremise
    change premise ∈ premises.map Formula.toSearch at hPremise
    rcases List.mem_map.mp hPremise with ⟨source, hSource, rfl⟩
    exact source.toSearch_admissible
def sourceProblem {goal : Prop} (input : CheckedInput goal) :
    SourcePreprocessing.Problem :=
  sourceProblemOfSyntax input.premises input.target
def deepProblem {goal : Prop} (input : CheckedInput goal) :
    SourcePreprocessing.DeepProblem :=
  deepProblemOfSyntax input.premises input.target
abbrev SearchStructureAt :=
  LogicSoundness.SetLevel.StructureAt.{x}
    SearchMaterialization.SearchSignature
abbrev SearchStructure := SearchStructureAt.{0}
abbrev SearchEnvAt (M : SearchStructureAt.{x}) :=
  LogicSoundness.SetLevel.EnvAt.{x} M
abbrev SearchEnv (M : SearchStructure) := SearchEnvAt.{0} M
@[reducible] noncomputable def coreModelOfSearch (M : SearchStructureAt.{x}) : Semantics.Model.{x} := by
  classical
  exact {
    Carrier := M.Domain
    default := Classical.choice M.nonempty
    sortInterp := M.sortInterp
    sortNonempty := M.sortNonempty
    functionInterp := fun symbol arguments =>
      if hArguments :
          Logic.FirstOrder.ArgsSatisfy M.sortInterp arguments (SearchMaterialization.SearchSignature.funcDomain
              (FirstOrderProjection.functionSymbol symbol)) then
        M.funcInterp (FirstOrderProjection.functionSymbol symbol) arguments
      else
        Classical.choose (M.sortNonempty symbol.outputSort)
    predicateInterp := fun predicate arguments =>
      M.relInterp (.predicate predicate) arguments
    applyInterp := fun _ _ => Classical.choice M.nonempty
    boolValue := fun _ => Classical.choice M.nonempty
    notValue := fun _ => Classical.choice M.nonempty
    andValue := fun _ _ => Classical.choice M.nonempty
    orValue := fun _ _ => Classical.choice M.nonempty
    impValue := fun _ _ => Classical.choice M.nonempty
    iffValue := fun _ _ => Classical.choice M.nonempty
    quoteValue := fun _ => Classical.choice M.nonempty
    lambdaValue := fun _ _ _ => Classical.choice M.nonempty
    iteValue := fun _ _ _ => Classical.choice M.nonempty
    boolHolds := fun _ => False
  }
@[reducible] noncomputable def coreEnvOfSearch
    {M : SearchStructureAt.{x}} (env : SearchEnvAt.{x} M) :
    Semantics.Env (coreModelOfSearch M) where
  boundVal := fun index => env.boundVal .object index
  freeVal := env.freeVal
theorem coreModel_functionSort (M : SearchStructureAt.{x}) :
    ∀ symbol arguments, (coreModelOfSearch M).sortInterp symbol.outputSort ((coreModelOfSearch M).functionInterp symbol arguments) := by
  intro symbol arguments
  classical
  by_cases hArguments :
      Logic.FirstOrder.ArgsSatisfy M.sortInterp arguments (SearchMaterialization.SearchSignature.funcDomain (FirstOrderProjection.functionSymbol symbol))
  · simpa only [coreModelOfSearch, hArguments, ↓reduceDIte] using
      M.funcSort (FirstOrderProjection.functionSymbol symbol)
        arguments hArguments
  · simpa only [coreModelOfSearch, hArguments, ↓reduceDIte] using
      Classical.choose_spec (M.sortNonempty symbol.outputSort)
theorem coreEnv_respectsFree {M : SearchStructureAt.{x}} (env : SearchEnvAt.{x} M) :
    Semantics.Env.RespectsFree (coreEnvOfSearch env) := by
  intro sort id
  exact env.freeSort sort id
theorem satisfies_coreFormula {M : SearchStructureAt.{x}} (env : SearchEnvAt.{x} M) :
    ∀ formula : Formula,
      Semantics.Formula.Satisfies (coreEnvOfSearch env) formula.toCore ↔
        Logic.FirstOrder.Formula.satisfies env formula.toSearch
  | .atom value => by
      simp [Formula.toCore, Formula.toSearch, Formula.predicate,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies, coreModelOfSearch]
  | .falsum => by
      simp [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .truth => by
      simp [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .neg body => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          not_congr (satisfies_coreFormula env body)
  | .conj left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          and_congr (satisfies_coreFormula env left) (satisfies_coreFormula env right)
  | .disj left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          or_congr (satisfies_coreFormula env left) (satisfies_coreFormula env right)
  | .imp left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          imp_congr (satisfies_coreFormula env left) (satisfies_coreFormula env right)
  | .iff left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          iff_congr (satisfies_coreFormula env left) (satisfies_coreFormula env right)
theorem coreSatisfiesConjunctionList {M : Semantics.Model.{x}} (env : Semantics.Env M) (formulas : List CoreSyntax.Formula) (hFormulas :
      ∀ formula ∈ formulas, Semantics.Formula.Satisfies env formula) :
    Semantics.Formula.Satisfies env (CoreSyntax.Formula.conjunctionList formulas) := by
  induction formulas with
  | nil =>
      simp [CoreSyntax.Formula.conjunctionList,
        Semantics.Formula.Satisfies, Semantics.Formula.eval]
  | cons head tail ih =>
      cases tail with
      | nil =>
          simpa [CoreSyntax.Formula.conjunctionList] using
            hFormulas head (by simp)
      | cons next rest =>
          simp only [CoreSyntax.Formula.conjunctionList,
            Semantics.Formula.Satisfies, Semantics.Formula.eval]
          constructor
          · exact hFormulas head (by simp)
          · apply ih
            intro formula hFormula
            exact hFormulas formula (by simp [hFormula])
def firstOrderBridgeAt {goal : Prop} (input : CheckedInput goal) :
    SourcePreprocessing.FirstOrderProblemBridgeAt.{x}
      input.sourceProblem input.deepProblem := by
  constructor
  intro M env hModels hTarget
  refine ⟨{
    model := coreModelOfSearch M
    functionSort := coreModel_functionSort M
    env := coreEnvOfSearch env
    respectsFree := coreEnv_respectsFree env
    satisfies := ?_
  }⟩
  unfold sourceProblem SourcePreprocessing.Problem.refutationSource
  apply coreSatisfiesConjunctionList
  intro formula hFormula
  simp only [List.mem_append, List.mem_singleton] at hFormula
  rcases hFormula with hPremise | hTargetFormula
  · rcases List.mem_map.mp hPremise with
      ⟨source, hSource, rfl⟩
    exact (satisfies_coreFormula env source).mpr <|
        hModels source.toSearch <|
          List.mem_map.mpr ⟨source, hSource, rfl⟩
  · subst formula
    have hCoreTarget :
        ¬ Semantics.Formula.Satisfies (coreEnvOfSearch env) input.target.toCore := by
      intro hCore
      exact hTarget <| (satisfies_coreFormula env input.target).mp hCore
    simpa [Semantics.Formula.Satisfies, Semantics.Formula.eval] using
      hCoreTarget
def firstOrderBridge {goal : Prop} (input : CheckedInput goal) :
    SourcePreprocessing.FirstOrderProblemBridge
      input.sourceProblem input.deepProblem :=
  input.firstOrderBridgeAt
/--
atom 表在任意模型 universe 中的标准宿主模型；所有 sort 共享提升后的 `Unit`，
关系解释回到原 Lean 命题。
-/
def hostStructureAt (atoms : Nat → Prop) : SearchStructureAt.{x} where
  Domain := ULift.{x, 0} Unit
  nonempty := ⟨ULift.up ()⟩
  sortInterp := fun _ _ => True
  sortNonempty := fun _ => ⟨ULift.up (), trivial⟩
  funcInterp := fun _ _ => ULift.up ()
  funcSort := by
    intro symbol arguments hArguments
    trivial
  relInterp := fun relation arguments =>
    match relation with
    | .predicate predicate =>
        if arguments.isEmpty then atoms predicate.id else False
    | _ => False
def hostStructure (atoms : Nat → Prop) : SearchStructure :=
  hostStructureAt.{0} atoms
def hostEnvAt (atoms : Nat → Prop) :
    SearchEnvAt.{x} (hostStructureAt.{x} atoms) where
  boundVal := fun _ _ => ULift.up ()
  freeVal := fun _ _ => ULift.up ()
  boundSort := by simp [hostStructureAt]
  freeSort := by simp [hostStructureAt]
def hostEnv (atoms : Nat → Prop) : SearchEnv (hostStructure atoms) :=
  hostEnvAt.{0} atoms
theorem satisfies_searchFormula_hostAt (atoms : Nat → Prop) :
    ∀ formula : Formula,
      Logic.FirstOrder.Formula.satisfies (hostEnvAt.{x} atoms) formula.toSearch ↔
        formula.eval atoms
  | .atom value => by
      simp [Formula.toSearch, Formula.predicate,
        Logic.FirstOrder.Formula.satisfies, hostStructureAt, hostEnvAt,
        Formula.eval]
  | .falsum => by
      simp [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval]
  | .truth => by
      simp [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval]
  | .neg body => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          not_congr (satisfies_searchFormula_hostAt atoms body)
  | .conj left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          and_congr (satisfies_searchFormula_hostAt atoms left) (satisfies_searchFormula_hostAt atoms right)
  | .disj left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          or_congr (satisfies_searchFormula_hostAt atoms left) (satisfies_searchFormula_hostAt atoms right)
  | .imp left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          imp_congr (satisfies_searchFormula_hostAt atoms left) (satisfies_searchFormula_hostAt atoms right)
  | .iff left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          iff_congr (satisfies_searchFormula_hostAt atoms left) (satisfies_searchFormula_hostAt atoms right)
theorem satisfies_searchFormula_host (atoms : Nat → Prop) :
    ∀ formula : Formula,
      Logic.FirstOrder.Formula.satisfies (hostEnv atoms) formula.toSearch ↔
        formula.eval atoms :=
  satisfies_searchFormula_hostAt.{0} atoms
theorem soundOfSearchAt {goal : Prop} (input : CheckedInput goal) (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
        input.deepProblem.theory input.deepProblem.target) :
    goal := by
  have hTarget :
      Logic.FirstOrder.Formula.satisfies (hostEnvAt.{x} input.atoms) input.target.toSearch :=
    hSearch (hostEnvAt.{x} input.atoms) (by
      intro formula hFormula
      rcases List.mem_map.mp hFormula with
        ⟨source, hSource, rfl⟩
      exact (satisfies_searchFormula_hostAt input.atoms source).mpr (input.premiseHolds hSource))
  exact input.goalOfTarget <| (satisfies_searchFormula_hostAt input.atoms input.target).mp hTarget
theorem soundOfSearch {goal : Prop} (input : CheckedInput goal) (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntails
        input.deepProblem.theory input.deepProblem.target) :
    goal :=
  input.soundOfSearchAt hSearch
end CheckedInput
/-! ## 公共 proof-carrying facts 构造 -/
def proofFactsExprWithTypes (proofs propositions : Array Expr) : MetaM Expr := do
  unless proofs.size == propositions.size do
    throwError
      "internal prove_auto fact proposition snapshot changed length"
  let mut tail := mkConst ``Facts.nil
  let mut index := proofs.size
  while index > 0 do
    index := index - 1
    let proposition := propositions[index]!
    unless ← isProp proposition do
      throwError
        "prove_auto USE expected a proof term, but got{indentExpr proposition}"
    tail ← mkAppM ``Facts.cons #[proposition, proofs[index]!, tail]
  return tail
def proofFactsExpr (proofs : Array Expr) : MetaM Expr := do
  let propositions ← proofs.mapM fun proof => do
    instantiateMVars (← inferType proof)
  proofFactsExprWithTypes proofs propositions
end HostProp
end Automation
end YesMetaZFC
