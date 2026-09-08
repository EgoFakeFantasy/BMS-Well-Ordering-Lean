import YesMetaZFC.Automation.HostFirstOrder.Semantics
import YesMetaZFC.Automation.HostRules.Semantics

/-!
# 索引化宿主一阶的 replay 语义

本模块只负责把索引语法送入 core normal form 的语义。所有绑定变量已经由
`Fin depth` 保证作用域正确；这里不再生成 scope、admissibility 或良构桥接证明。
-/

namespace YesMetaZFC
namespace Automation
namespace HostFirstOrder
namespace ReplaySemantics

universe u x

open CoreSyntax
open CoreSyntax.NormalForm
open SearchMaterialization
open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

abbrev SearchStructureAt :=
  LogicSoundness.SetLevel.StructureAt.{x}
    SearchMaterialization.SearchSignature

abbrev CoreModel := CoreSyntax.NormalForm.Semantics.Model.{x}
abbrev CoreEnv (M : CoreModel) := CoreSyntax.NormalForm.Semantics.Env M

def valuesOfList {M : SearchStructureAt}
    (default : M.Carrier CoreSort.object) :
    (arity : Nat) → List (M.Carrier CoreSort.object) →
      Logic.FirstOrder.Values M.Carrier
        (List.replicate arity CoreSort.object)
  | 0, _ => .nil
  | Nat.succ arity, [] =>
      .cons default (valuesOfList default arity [])
  | Nat.succ arity, value :: tail =>
      .cons value (valuesOfList default arity tail)

def coreFunctionInterp {M : SearchStructureAt}
    (default : M.Carrier CoreSort.object)
    (symbol : CoreSyntax.FunctionSymbol)
    (arguments : List (M.Carrier CoreSort.object)) :
    M.Carrier CoreSort.object :=
  if symbol.role = .parameter ∧ symbol.inputSorts = [] ∧
      symbol.outputSort = CoreSort.object then
    M.funcInterp
      (Term.intrinsicFunctionSymbol symbol.id symbol.arity)
      (valuesOfList default symbol.arity arguments)
  else
    default

@[implicit_reducible]
def coreModel {M : SearchStructureAt}
    (default : M.Carrier CoreSort.object) : CoreModel where
  Carrier := M.Carrier CoreSort.object
  default := default
  sortInterp := fun _ _ => True
  sortNonempty := fun _ => ⟨default, trivial⟩
  functionInterp := coreFunctionInterp default
  predicateInterp := fun symbol arguments =>
    if symbol.role = .relation ∧ symbol.inputSorts = [] then
      M.relInterp
        (Formula.intrinsicPredicateSymbol symbol.id symbol.arity)
        (valuesOfList default symbol.arity arguments)
    else
      False
  applyInterp := fun _ _ => default
  boolValue := fun _ => default
  notValue := fun _ => default
  andValue := fun _ _ => default
  orValue := fun _ _ => default
  impValue := fun _ _ => default
  iffValue := fun _ _ => default
  quoteValue := fun _ => default
  lambdaValue := fun _ _ _ => default
  iteValue := fun _ _ _ => default
  boolHolds := fun _ => False

def coreBoundValue {α : Type x} (default : α) :
    (depth : Nat) → (Fin depth → α) → Nat → α
  | 0, _, _ => default
  | Nat.succ depth, bound, 0 => bound ⟨0, Nat.zero_lt_succ depth⟩
  | Nat.succ depth, bound, index + 1 =>
      coreBoundValue default depth (fun value => bound value.succ) index

def intrinsicBoundValue {M : SearchStructureAt} :
    (depth : Nat) → (Fin depth → M.Carrier CoreSort.object) →
      {sort : SearchMaterialization.SearchSignature.SortSymbol} →
        Logic.FirstOrder.Variable (ObjectContext depth) sort → M.Carrier sort
  | 0, _, _, entry => nomatch entry
  | Nat.succ depth, bound, _, .here =>
      bound ⟨0, Nat.zero_lt_succ depth⟩
  | Nat.succ depth, bound, _, .there previous =>
      intrinsicBoundValue depth (fun index => bound index.succ) previous

def intrinsicEnv {M : SearchStructureAt} {depth : Nat}
    (bound : Fin depth → M.Carrier CoreSort.object) :
    Logic.FirstOrder.Env M (ObjectContext depth) [] where
  boundVal := intrinsicBoundValue depth bound
  freeVal := fun entry => nomatch entry

def coreEnv {M : SearchStructureAt} (default : M.Carrier CoreSort.object)
    {depth : Nat} (bound : Fin depth → M.Carrier CoreSort.object) :
    CoreEnv (coreModel (M := M) default) where
  boundVal := coreBoundValue default depth bound
  freeVal := fun _ _ => default

@[simp] theorem coreBoundValue_bound {α : Type x} (default : α)
    {depth : Nat} (bound : Fin depth → α) (index : Fin depth) :
    coreBoundValue default depth bound index.val = bound index := by
  cases depth with
  | zero => exact Fin.elim0 index
  | succ depth =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · simpa [coreBoundValue] using
          coreBoundValue_bound default (fun value => bound value.succ) tail

@[simp] theorem intrinsicBoundValue_boundVariable {M : SearchStructureAt}
    {depth : Nat} (bound : Fin depth → M.Carrier CoreSort.object)
    (index : Fin depth) :
    intrinsicBoundValue depth bound (boundVariable depth index) = bound index := by
  cases depth with
  | zero => exact Fin.elim0 index
  | succ depth =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · simpa [boundVariable, intrinsicBoundValue] using
          intrinsicBoundValue_boundVariable
            (M := M) (fun value => bound value.succ) tail

theorem intrinsicEnv_push {M : SearchStructureAt}
    {depth : Nat} (bound : Fin depth → M.Carrier CoreSort.object)
    (value : M.Carrier CoreSort.object) :
    intrinsicEnv (M := M) (Formula.pushBound value bound) =
      (intrinsicEnv (M := M) bound).pushBound value := by
  apply Logic.FirstOrder.Env.ext
  · intro sort entry
    cases entry with
    | here => simp [intrinsicEnv, intrinsicBoundValue,
        Logic.FirstOrder.Env.pushBound, Formula.pushBound]
    | there previous =>
        have hBound :
            (fun index : Fin depth => Formula.pushBound value bound index.succ) =
              bound := by
          funext index
          rfl
        change intrinsicBoundValue depth
          (fun index : Fin depth => Formula.pushBound value bound index.succ)
          previous = intrinsicBoundValue depth bound previous
        rw [hBound]
  · intro sort entry
    cases entry

theorem coreEnv_ext {M : CoreModel} {left right : CoreEnv M}
    (hBound : left.boundVal = right.boundVal)
    (hFree : left.freeVal = right.freeVal) : left = right := by
  cases left
  cases right
  cases hBound
  cases hFree
  rfl

theorem coreEnv_push {M : SearchStructureAt}
    (default : M.Carrier CoreSort.object)
    {depth : Nat} (bound : Fin depth → M.Carrier CoreSort.object)
    (value : M.Carrier CoreSort.object) :
    coreEnv (M := M) default (Formula.pushBound value bound) =
      (coreEnv (M := M) default bound).push value := by
  apply coreEnv_ext
  · funext index
    cases index with
    | zero => rfl
    | succ index =>
        have hBound :
            (fun value_1 : Fin depth => Formula.pushBound value bound value_1.succ) =
              bound := by
          funext value_1
          rfl
        change coreBoundValue default depth
          (fun value_1 : Fin depth => Formula.pushBound value bound value_1.succ)
          index = coreBoundValue default depth bound index
        rw [hBound]
  · rfl

@[simp] theorem toCoreList_eq_map {depth : Nat}
    (terms : List (Term depth)) :
    Term.toCoreList terms = terms.map Term.toCore := by
  induction terms with
  | nil => simp [Term.toCoreList]
  | cons head tail ih => simp [Term.toCoreList, ih]

mutual

  theorem term_eval_of_correspondence {M : SearchStructureAt}
      (default : M.Carrier CoreSort.object)
      {depth : Nat} (bound : Fin depth → M.Carrier CoreSort.object) :
      ∀ term : Term depth,
        CoreSyntax.NormalForm.Semantics.Term.eval
            (coreEnv (M := M) default bound) term.toCore =
          Logic.FirstOrder.Term.eval
            (intrinsicEnv (M := M) bound) term.toIntrinsic
    | .bvar index => by
        simp [Term.toCore, Term.toIntrinsic,
          CoreSyntax.NormalForm.Semantics.Term.eval,
          Logic.FirstOrder.Term.eval, coreEnv, intrinsicEnv,
          coreBoundValue_bound, intrinsicBoundValue_boundVariable]
    | .app symbol arguments => by
        simp only [Term.toCore, Term.toIntrinsic,
          CoreSyntax.NormalForm.Semantics.Term.eval,
          Logic.FirstOrder.Term.eval, coreFunctionInterp,
          coreModel]
        have hArguments :
            valuesOfList (M := M) default arguments.length
                (arguments.map (fun term =>
                  CoreSyntax.NormalForm.Semantics.Term.eval
                    (coreEnv (M := M) default bound) term.toCore)) =
              Logic.FirstOrder.Arguments.eval
                (intrinsicEnv (M := M) bound)
                (Term.toIntrinsicList arguments) := by
          simpa [toCoreList_eq_map, Function.comp_def] using
            values_eval_of_correspondence default bound arguments
        rw [if_pos]
        · have hFunction := congrArg
            (M.funcInterp (Term.intrinsicFunctionSymbol symbol arguments.length))
            hArguments
          simpa [Term.functionSymbol] using! hFunction
        · simp [Term.functionSymbol]

  theorem values_eval_of_correspondence {M : SearchStructureAt}
      (default : M.Carrier CoreSort.object)
      {depth : Nat} (bound : Fin depth → M.Carrier CoreSort.object) :
      ∀ terms : List (Term depth),
        valuesOfList (M := M) default terms.length
            (terms.map (fun term =>
              CoreSyntax.NormalForm.Semantics.Term.eval
                (coreEnv (M := M) default bound) term.toCore)) =
          Logic.FirstOrder.Arguments.eval
            (intrinsicEnv (M := M) bound) (Term.toIntrinsicList terms)
    | [] => by simp [valuesOfList, Term.toIntrinsicList,
        Logic.FirstOrder.Arguments.eval]
    | head :: tail => by
        simp only [List.length_cons, List.map_cons,
          Term.toIntrinsicList,
          Logic.FirstOrder.Arguments.eval, valuesOfList]
        rw [term_eval_of_correspondence default bound head]
        rw [values_eval_of_correspondence default bound tail]

end

theorem formula_satisfies_of_correspondence {M : SearchStructureAt}
    (default : M.Carrier CoreSort.object)
    {depth : Nat} (bound : Fin depth → M.Carrier CoreSort.object) :
    ∀ formula : Formula depth,
      CoreSyntax.NormalForm.Semantics.Formula.Satisfies
          (coreEnv (M := M) default bound) formula.toCore ↔
        Logic.FirstOrder.Formula.satisfies
          (intrinsicEnv (M := M) bound) formula.toIntrinsic
  | .atom symbol arguments => by
      simp only [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies, coreModel]
      have hArguments :
          valuesOfList (M := M) default arguments.length
              (List.map (fun term =>
                CoreSyntax.NormalForm.Semantics.Term.eval
                  (coreEnv (M := M) default bound) term.toCore)
                arguments) =
            Logic.FirstOrder.Arguments.eval
              (intrinsicEnv (M := M) bound)
              (Term.toIntrinsicList arguments) := by
        exact values_eval_of_correspondence default bound arguments
      have hPredicate := congrArg
        (M.relInterp (Formula.intrinsicPredicateSymbol symbol arguments.length))
        hArguments
      simpa [Formula.predicateSymbol, Formula.intrinsicPredicateSymbol,
        toCoreList_eq_map, Function.comp_def] using! hPredicate
  | .equal left right => by
      simp only [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      rw [term_eval_of_correspondence default bound left,
        term_eval_of_correspondence default bound right]
  | .falsum => by
      simp [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .truth => by
      simp [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .neg body => by
      simpa [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
        not_congr (formula_satisfies_of_correspondence default bound body)
  | .conj left right => by
      simpa [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
        and_congr
          (formula_satisfies_of_correspondence default bound left)
          (formula_satisfies_of_correspondence default bound right)
  | .disj left right => by
      simpa [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
        or_congr
          (formula_satisfies_of_correspondence default bound left)
          (formula_satisfies_of_correspondence default bound right)
  | .imp left right => by
      simpa [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
        imp_congr
          (formula_satisfies_of_correspondence default bound left)
          (formula_satisfies_of_correspondence default bound right)
  | .iff left right => by
      simpa [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
        iff_congr
          (formula_satisfies_of_correspondence default bound left)
          (formula_satisfies_of_correspondence default bound right)
  | .forallE body => by
      simp [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies, coreModel]
      constructor <;> intro h value
      · have hBody := h value
        have hBody' :
            CoreSyntax.NormalForm.Semantics.Formula.Satisfies
              (coreEnv (M := M) default (Formula.pushBound value bound))
              body.toCore := by
          simpa [CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
            coreEnv_push] using hBody
        have hResult :=
          (formula_satisfies_of_correspondence default
            (Formula.pushBound value bound) body).mp hBody'
        rw [intrinsicEnv_push] at hResult
        exact hResult
      · have hBody := h value
        rw [← intrinsicEnv_push] at hBody
        have hCore :=
          (formula_satisfies_of_correspondence default
            (Formula.pushBound value bound) body).mpr hBody
        simpa [CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
          coreEnv_push] using hCore

  | .existsE body => by
      simp [Formula.toCore, Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies, coreModel]
      constructor
      · rintro ⟨value, hBody⟩
        refine ⟨value, ?_⟩
        have hBody' :
            CoreSyntax.NormalForm.Semantics.Formula.Satisfies
              (coreEnv (M := M) default (Formula.pushBound value bound))
              body.toCore := by
          simpa [CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
            coreEnv_push] using hBody
        have hResult :=
          (formula_satisfies_of_correspondence default
            (Formula.pushBound value bound) body).mp hBody'
        rw [intrinsicEnv_push] at hResult
        exact hResult
      · rintro ⟨value, hBody⟩
        refine ⟨value, ?_⟩
        rw [← intrinsicEnv_push] at hBody
        have hCore :=
          (formula_satisfies_of_correspondence default
            (Formula.pushBound value bound) body).mpr hBody
        simpa [CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
           coreEnv_push] using hCore

theorem intrinsicEnv_empty {M : SearchStructureAt} :
    intrinsicEnv (M := M) (Fin.elim0) =
      (Logic.FirstOrder.Env.empty :
        Logic.FirstOrder.Env M [] []) := by
  apply Logic.FirstOrder.Env.ext
  · intro sort entry
    cases entry
  · intro sort entry
    cases entry

theorem coreFunctionSort {M : SearchStructureAt}
    (default : M.Carrier CoreSort.object) :
    ∀ symbol arguments,
      (coreModel (M := M) default).sortInterp symbol.outputSort
        ((coreModel (M := M) default).functionInterp symbol arguments) := by
  intro symbol arguments
  trivial

theorem coreEnv_respectsFree {M : SearchStructureAt}
    (default : M.Carrier CoreSort.object) :
    CoreSyntax.NormalForm.Semantics.Env.RespectsFree
      (coreEnv (M := M) default (Fin.elim0)) := by
  intro sort id
  trivial

theorem coreConjunction_true {M : CoreModel}
    (env : CoreSyntax.NormalForm.Semantics.Env M)
    (formulas : List CoreSyntax.Formula)
    (hFormulas : ∀ formula ∈ formulas,
      CoreSyntax.NormalForm.Semantics.Formula.Satisfies env formula) :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies env
      (CoreSyntax.Formula.conjunctionList formulas) := by
  induction formulas with
  | nil =>
      simp [CoreSyntax.Formula.conjunctionList,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval]
  | cons head tail ih =>
      cases tail with
      | nil =>
          simpa [CoreSyntax.Formula.conjunctionList] using
            hFormulas head (by simp)
      | cons next rest =>
          simp only [CoreSyntax.Formula.conjunctionList,
            CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
            CoreSyntax.NormalForm.Semantics.Formula.eval]
          constructor
          · exact hFormulas head (by simp)
          · apply ih
            intro formula hFormula
            exact hFormulas formula (by simp [hFormula])

theorem coreRefutation_true_of_syntax
    (premises : List ClosedFormula) (target : ClosedFormula)
    {M : SearchStructureAt}
    (default : M.Carrier CoreSort.object)
    (hModels : Logic.FirstOrder.Theory.Models M
      (intrinsicProblemOfSyntax premises target).theory)
    (hTarget : ¬ target.toIntrinsic.TrueIn M) :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies
      (coreEnv (M := M) default (Fin.elim0))
      (sourceProblemOfSyntax premises target).refutationSource := by
  unfold sourceProblemOfSyntax SourcePreprocessing.Problem.refutationSource
  apply coreConjunction_true
  intro formula hFormula
  simp only [List.mem_append, List.mem_singleton] at hFormula
  rcases hFormula with hPremise | hTargetFormula
  · rcases List.mem_map.mp hPremise with ⟨source, hSource, rfl⟩
    have hIntrinsic :
        Logic.FirstOrder.Formula.satisfies
          (intrinsicEnv (M := M) (Fin.elim0)) source.toIntrinsic := by
      rw [intrinsicEnv_empty]
      exact hModels source.toIntrinsic
        (List.mem_map.mpr ⟨source, hSource, rfl⟩)
    exact (formula_satisfies_of_correspondence default (Fin.elim0) source).mpr
      hIntrinsic
  · subst formula
    have hIntrinsic :
        Logic.FirstOrder.Formula.satisfies
          (intrinsicEnv (M := M) (Fin.elim0))
          (HostFirstOrder.Formula.neg target).toIntrinsic := by
      rw [intrinsicEnv_empty]
      simpa [HostFirstOrder.Formula.toIntrinsic,
        Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies] using hTarget
    exact
      (formula_satisfies_of_correspondence default (Fin.elim0)
        (.neg target)).mpr hIntrinsic

/-- 物化 DAG 的初始子句精确来自 preprocessing payload。 -/
theorem artifact_initialClauses_eq_coreClauseSet
    (payload : SourcePreprocessing.Payload)
    (problem : SourcePreprocessing.DeepProblem)
    (search : SourcePreprocessing.SearchInput) (label : String)
    (artifact : SearchMaterialization.CheckedArtifact
      (SourcePreprocessing.FirstOrderReplay.searchInput
        payload problem search label).clauseProblem) :
    artifact.checked.dag.problem.initialClauses =
      SearchMaterialization.coreClauseSet payload.clauses := by
  have hInitial := congrArg
    (fun problem : SearchMaterialization.ClauseProblem =>
      problem.initialClauses) artifact.problem_eq
  simpa [SourcePreprocessing.FirstOrderReplay.searchInput,
    SourcePreprocessing.FirstOrderReplay.clauseProblemOf,
    SearchMaterialization.ReplayCoreProjection.clauseSet_eq_coreClauseSet]
    using hInitial

theorem coreRefutation_true {α : Type u} {goal : Prop}
    (input : Semantics.CheckedInput (α := α) goal)
    {M : SearchStructureAt}
    (default : M.Carrier CoreSort.object)
    (hModels : Logic.FirstOrder.Theory.Models M
      input.intrinsicProblem.theory)
    (hTarget : ¬ input.target.toIntrinsic.TrueIn M) :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies
      (coreEnv (M := M) default (Fin.elim0))
      input.sourceProblem.refutationSource :=
  coreRefutation_true_of_syntax input.premises input.target default hModels hTarget

theorem guarded_semanticallyEntailsSyntaxAt
    (premises : List ClosedFormula) (target : ClosedFormula)
    {problem : SourcePreprocessing.Problem}
    (replay : SourcePreprocessing.FirstOrderReplay problem)
    (artifact : SearchMaterialization.CheckedArtifact replay.clauseProblem)
    (compiled : DAGCertificate.Compile.CheckedDAGClauses
      artifact.checked.dag)
    (hProblem : artifact.checked.dag.problem.initialClauses =
      SearchMaterialization.coreClauseSet replay.payload.clauses)
    (hSourceProblem : problem = sourceProblemOfSyntax premises target)
    (hSupported : artifact.checked.dag.guardedSoundnessSupported = true) :
    LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
      (intrinsicProblemOfSyntax premises target).theory
      (intrinsicProblemOfSyntax premises target).target := by
  intro M hModels
  by_cases hTarget : target.toIntrinsic.TrueIn M
  · exact hTarget
  · exfalso
    rcases M.nonempty CoreSort.object with ⟨default⟩
    have hSource :
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies
          (coreEnv (M := M) default (Fin.elim0)) replay.payload.source := by
      rw [replay.sourceIsRefutation, hSourceProblem]
      exact coreRefutation_true_of_syntax premises target default hModels hTarget
    rcases CoreSyntax.NormalForm.CheckedPreprocessing.modelExtension
      replay.checkedPayload
      (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
        replay.antiPrenexFreeClosed)
      (coreModel (M := M) default)
      (coreEnv (M := M) default (Fin.elim0)) with ⟨extension⟩
    let functionSort := extension.functionSort_of (coreFunctionSort default)
    let targetModel := extension.target
    let targetBase := extension.rebase
      (coreEnv (M := M) default (Fin.elim0))
    let targetStructure :=
      SearchMaterialization.CoreProjectionSoundness.searchStructure
        targetModel functionSort
    have hTargetFree :
        CoreSyntax.NormalForm.Semantics.Env.RespectsFree targetBase :=
      extension.respectsFree (coreEnv_respectsFree default)
    have hClauses : ∀ env,
        CoreSyntax.NormalForm.Semantics.Env.RespectsFree env →
        CoreSyntax.NormalForm.Semantics.LocalSkolemChoice.SameBoundStack
          env targetBase →
        CoreSyntax.NormalForm.Semantics.ClauseSet.Satisfies env
          replay.payload.clauses := by
      intro env hFree hBound
      exact extension.clausesSatisfiedTarget_of_normalized_eq
        replay.normalizationIdentity hSource env hFree hBound
    have hInitial : ∀ target ∈ compiled.compilation.initialClauses.toList,
        target.TrueIn targetStructure :=
      SearchMaterialization.CoreProjectionSoundness.checkedDAGInitials_trueIn
        functionSort targetBase hTargetFree replay.payload.clauses
        replay.clausesProjectable hClauses artifact.checked.dag hProblem
        compiled
    have hRoot :=
      DAGCertificate.IntrinsicReplay.rootNodeTrueIn_of_supported
        targetStructure (fun _ => False) artifact.checked compiled hInitial
        hSupported
    have hRootEmpty :
        (compiled.nodeAt artifact.checked.dag.root
          artifact.checked.contract.root_exists).raw.isEmpty = true := by
      rw [DAGCertificate.Compile.CheckedDAGClauses.nodeAt_raw]
      exact artifact.checked.contract.root_conclusion_empty
    exact DAGCertificate.IntrinsicReplay.compiledClause_not_trueIn_of_raw_empty
      targetStructure
      (compiled.nodeAt artifact.checked.dag.root
        artifact.checked.contract.root_exists) hRootEmpty hRoot

theorem guarded_semanticallyEntailsAt {α : Type u} {goal : Prop}
    (input : Semantics.CheckedInput (α := α) goal)
    {problem : SourcePreprocessing.Problem}
    (replay : SourcePreprocessing.FirstOrderReplay problem)
    (artifact : SearchMaterialization.CheckedArtifact replay.clauseProblem)
    (compiled : DAGCertificate.Compile.CheckedDAGClauses
      artifact.checked.dag)
    (hProblem : artifact.checked.dag.problem.initialClauses =
      SearchMaterialization.coreClauseSet replay.payload.clauses)
    (hSourceProblem : problem = input.sourceProblem)
    (hSupported : artifact.checked.dag.guardedSoundnessSupported = true) :
    LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
      input.intrinsicProblem.theory input.intrinsicProblem.target :=
  guarded_semanticallyEntailsSyntaxAt input.premises input.target replay artifact
    compiled hProblem hSourceProblem hSupported

theorem avatar_semanticallyEntailsSyntaxAt
    (premises : List ClosedFormula) (target : ClosedFormula)
    {problem : SourcePreprocessing.Problem}
    (replay : SourcePreprocessing.FirstOrderReplay problem)
    (artifact : SearchMaterialization.CheckedArtifact replay.clauseProblem)
    (compiled : DAGCertificate.Compile.CheckedDAGClauses
      artifact.checked.dag)
    (registry : DAGCertificate.AvatarSelectorComponent.Registry
      SearchMaterialization.SearchSignature)
    (hRegistry : DAGCertificate.DAG.avatarRegistryCheckWith
      artifact.checked.dag registry = true)
    (hProblem : artifact.checked.dag.problem.initialClauses =
      SearchMaterialization.coreClauseSet replay.payload.clauses)
    (hSourceProblem : problem = sourceProblemOfSyntax premises target)
    (hSupported : artifact.checked.dag.avatarSoundnessSupported = true) :
    LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
      (intrinsicProblemOfSyntax premises target).theory
      (intrinsicProblemOfSyntax premises target).target := by
  intro M hModels
  by_cases hTarget : target.toIntrinsic.TrueIn M
  · exact hTarget
  · exfalso
    rcases M.nonempty CoreSort.object with ⟨default⟩
    have hSource :
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies
          (coreEnv (M := M) default (Fin.elim0)) replay.payload.source := by
      rw [replay.sourceIsRefutation, hSourceProblem]
      exact coreRefutation_true_of_syntax premises target default hModels hTarget
    rcases CoreSyntax.NormalForm.CheckedPreprocessing.modelExtension
      replay.checkedPayload
      (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
        replay.antiPrenexFreeClosed)
      (coreModel (M := M) default)
      (coreEnv (M := M) default (Fin.elim0)) with ⟨extension⟩
    let functionSort := extension.functionSort_of (coreFunctionSort default)
    let targetModel := extension.target
    let targetBase := extension.rebase
      (coreEnv (M := M) default (Fin.elim0))
    let targetStructure :=
      SearchMaterialization.CoreProjectionSoundness.searchStructure
        targetModel functionSort
    have hTargetFree :
        CoreSyntax.NormalForm.Semantics.Env.RespectsFree targetBase :=
      extension.respectsFree (coreEnv_respectsFree default)
    have hClauses : ∀ env,
        CoreSyntax.NormalForm.Semantics.Env.RespectsFree env →
        CoreSyntax.NormalForm.Semantics.LocalSkolemChoice.SameBoundStack
          env targetBase →
        CoreSyntax.NormalForm.Semantics.ClauseSet.Satisfies env
          replay.payload.clauses := by
      intro env hFree hBound
      exact extension.clausesSatisfiedTarget_of_normalized_eq
        replay.normalizationIdentity hSource env hFree hBound
    have hInitial : ∀ target ∈ compiled.compilation.initialClauses.toList,
        target.TrueIn targetStructure :=
      SearchMaterialization.CoreProjectionSoundness.checkedDAGInitials_trueIn
        functionSort targetBase hTargetFree replay.payload.clauses
        replay.clausesProjectable hClauses artifact.checked.dag hProblem
        compiled
    have hComponentSemantics :
        DAGCertificate.IntrinsicReplay.AvatarComponentSemantics
          targetStructure compiled
          (DAGCertificate.IntrinsicReplay.avatarSelectorValuation
            targetStructure compiled artifact.checked.dag.avatarSelectorRegistry) := by
      intro splitId splitNode splitPayload componentIndex indices selector
        hNode hPayload hIndices hSelector
      exact
        DAGCertificate.IntrinsicReplay.avatarComponentSemantics_of_checked_registry
          targetStructure artifact.checked compiled registry hRegistry
          hNode hPayload hIndices hSelector
    have hSplitSemantics :
        DAGCertificate.IntrinsicReplay.AvatarSplitSemantics
          targetStructure compiled
          (DAGCertificate.IntrinsicReplay.avatarSelectorValuation
            targetStructure compiled artifact.checked.dag.avatarSelectorRegistry) := by
      intro splitId splitNode splitPayload hNode hPayload
      exact
        DAGCertificate.IntrinsicReplay.avatarSplitSemantics_of_checked_registry
          targetStructure artifact.checked compiled registry hRegistry
          hNode hPayload
    have hRoot :=
      DAGCertificate.IntrinsicReplay.rootNodeTrueIn_of_avatar_supported
        targetStructure
          (DAGCertificate.IntrinsicReplay.avatarSelectorValuation
            targetStructure compiled artifact.checked.dag.avatarSelectorRegistry)
          artifact.checked compiled hInitial
        hComponentSemantics hSplitSemantics hSupported
    have hRootEmpty :
        (compiled.nodeAt artifact.checked.dag.root
          artifact.checked.contract.root_exists).raw.isEmpty = true := by
      rw [DAGCertificate.Compile.CheckedDAGClauses.nodeAt_raw]
      exact artifact.checked.contract.root_conclusion_empty
    exact DAGCertificate.IntrinsicReplay.compiledClause_not_trueIn_of_raw_empty
      targetStructure
      (compiled.nodeAt artifact.checked.dag.root
        artifact.checked.contract.root_exists) hRootEmpty hRoot

theorem avatar_semanticallyEntailsAt {α : Type u} {goal : Prop}
    (input : Semantics.CheckedInput (α := α) goal)
    {problem : SourcePreprocessing.Problem}
    (replay : SourcePreprocessing.FirstOrderReplay problem)
    (artifact : SearchMaterialization.CheckedArtifact replay.clauseProblem)
    (compiled : DAGCertificate.Compile.CheckedDAGClauses
      artifact.checked.dag)
    (registry : DAGCertificate.AvatarSelectorComponent.Registry
      SearchMaterialization.SearchSignature)
    (hRegistry : DAGCertificate.DAG.avatarRegistryCheckWith
      artifact.checked.dag registry = true)
    (hProblem : artifact.checked.dag.problem.initialClauses =
      SearchMaterialization.coreClauseSet replay.payload.clauses)
    (hSourceProblem : problem = input.sourceProblem)
    (hSupported : artifact.checked.dag.avatarSoundnessSupported = true) :
    LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
      input.intrinsicProblem.theory input.intrinsicProblem.target :=
  avatar_semanticallyEntailsSyntaxAt input.premises input.target replay artifact
    compiled registry hRegistry hProblem hSourceProblem hSupported

end ReplaySemantics
end HostFirstOrder
end Automation
end YesMetaZFC
