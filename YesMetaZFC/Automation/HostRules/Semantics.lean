import YesMetaZFC.Automation.HostProp
import YesMetaZFC.Automation.SourcePreprocessing
import YesMetaZFC.Automation.CoreNormalForm.FirstOrderProjectionSoundness
import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay

/-!
# HR 内在语义出口

这里把宿主命题反模型送入 checked preprocessing，再由内在 DAG replay 导出矛盾。
接口只携带当前内核能够构造的对象：闭句、检查编译结果和 root 支持证书。
-/

namespace YesMetaZFC
namespace Automation
namespace HostRules
namespace Semantics

open CoreSyntax
open CoreSyntax.NormalForm
open HostProp
open SearchMaterialization
open SourcePreprocessing
open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

universe x

abbrev SearchStructureAt :=
  LogicSoundness.SetLevel.StructureAt.{x} SearchMaterialization.SearchSignature

abbrev CoreModel := CoreSyntax.NormalForm.Semantics.Model.{x}
abbrev CoreEnv (M : CoreModel) := CoreSyntax.NormalForm.Semantics.Env M

def hostCoreModel (M : SearchStructureAt) : CoreModel where
  Carrier := Unit
  default := ()
  sortInterp := fun _ _ => True
  sortNonempty := fun _ => ⟨(), trivial⟩
  functionInterp := fun _ _ => ()
  predicateInterp := fun predicate arguments =>
    if arguments.isEmpty then
      M.relInterp
        (.predicate {
          id := predicate.id
          arity := 0
          role := .relation
          inputSorts := []
        }) .nil
    else
      False
  applyInterp := fun _ _ => ()
  boolValue := fun _ => ()
  notValue := fun _ => ()
  andValue := fun _ _ => ()
  orValue := fun _ _ => ()
  impValue := fun _ _ => ()
  iffValue := fun _ _ => ()
  quoteValue := fun _ => ()
  lambdaValue := fun _ _ _ => ()
  iteValue := fun _ _ _ => ()
  boolHolds := fun _ => False

def hostCoreEnv (M : SearchStructureAt) : CoreEnv (hostCoreModel M) where
  boundVal := fun _ => ()
  freeVal := fun _ _ => ()

theorem hostCore_functionSort (M : SearchStructureAt) :
    ∀ symbol arguments,
      (hostCoreModel M).sortInterp symbol.outputSort
        ((hostCoreModel M).functionInterp symbol arguments) := by
  intro symbol arguments
  trivial

theorem hostCore_respectsFree (M : SearchStructureAt) :
    CoreSyntax.NormalForm.Semantics.Env.RespectsFree
      (hostCoreEnv M) := by
  intro sort id
  trivial

theorem hostCore_formula_trueIn (M : SearchStructureAt) :
    ∀ formula : HostProp.Formula,
      CoreSyntax.NormalForm.Semantics.Formula.Satisfies
          (hostCoreEnv M) formula.toCore ↔
        formula.toIntrinsic.TrueIn M
  | .atom value => by
      simp [HostProp.Formula.toCore, HostProp.Formula.toIntrinsic,
        HostProp.Formula.predicate,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        hostCoreModel, hostCoreEnv, Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies,
        Logic.FirstOrder.Arguments.eval]
  | .falsum => by
      simp [HostProp.Formula.toCore, HostProp.Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies]
  | .truth => by
      simp [HostProp.Formula.toCore, HostProp.Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies]
  | .neg body => by
      simpa [HostProp.Formula.toCore, HostProp.Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies] using
        not_congr (hostCore_formula_trueIn M body)
  | .conj left right => by
      simpa [HostProp.Formula.toCore, HostProp.Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies] using
        and_congr (hostCore_formula_trueIn M left)
          (hostCore_formula_trueIn M right)
  | .disj left right => by
      simpa [HostProp.Formula.toCore, HostProp.Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies] using
        or_congr (hostCore_formula_trueIn M left)
          (hostCore_formula_trueIn M right)
  | .imp left right => by
      simpa [HostProp.Formula.toCore, HostProp.Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies] using
        imp_congr (hostCore_formula_trueIn M left)
          (hostCore_formula_trueIn M right)
  | .iff left right => by
      simpa [HostProp.Formula.toCore, HostProp.Formula.toIntrinsic,
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
        CoreSyntax.NormalForm.Semantics.Formula.eval,
        Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies] using
        iff_congr (hostCore_formula_trueIn M left)
          (hostCore_formula_trueIn M right)

theorem hostCore_conjunction_true
    (M : SearchStructureAt) (formulas : List CoreSyntax.Formula)
    (hFormulas : ∀ formula ∈ formulas,
      CoreSyntax.NormalForm.Semantics.Formula.Satisfies
        (hostCoreEnv M) formula) :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies
      (hostCoreEnv M) (CoreSyntax.Formula.conjunctionList formulas) := by
  induction formulas with
  | nil => simp [CoreSyntax.Formula.conjunctionList,
      CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
      CoreSyntax.NormalForm.Semantics.Formula.eval]
  | cons head tail ih =>
      cases tail with
      | nil => simpa [CoreSyntax.Formula.conjunctionList] using
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

theorem hostCore_refutation_true {goal : Prop}
    (input : HostProp.CheckedInput goal)
    (M : SearchStructureAt)
    (hModels : Logic.FirstOrder.Theory.Models M
      input.intrinsicProblem.theory)
    (hTarget : ¬ input.target.toIntrinsic.TrueIn M) :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies
      (hostCoreEnv M) input.sourceProblem.refutationSource := by
  unfold HostProp.CheckedInput.sourceProblem
    SourcePreprocessing.Problem.refutationSource
  apply hostCore_conjunction_true M
  intro formula hFormula
  simp only [List.mem_append, List.mem_singleton] at hFormula
  rcases hFormula with hPremise | hTargetFormula
  · rcases List.mem_map.mp hPremise with ⟨source, hSource, rfl⟩
    apply (hostCore_formula_trueIn M source).mpr
    apply hModels source.toIntrinsic
    exact List.mem_map.mpr ⟨source, hSource, rfl⟩
  · subst formula
    apply (hostCore_formula_trueIn M (.neg input.target)).mpr
    simpa [HostProp.Formula.toIntrinsic,
      Logic.FirstOrder.Formula.TrueIn,
      Logic.FirstOrder.Formula.satisfies] using hTarget

theorem guarded_semanticallyEntailsAt {goal : Prop}
    (input : HostProp.CheckedInput goal)
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
      input.intrinsicProblem.theory input.intrinsicProblem.target := by
  intro M hModels
  by_cases hTarget : input.target.toIntrinsic.TrueIn M
  · exact hTarget
  · exfalso
    have hSource :
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies
          (hostCoreEnv M) replay.payload.source := by
      rw [replay.sourceIsRefutation, hSourceProblem]
      exact hostCore_refutation_true input M hModels hTarget
    rcases CoreSyntax.NormalForm.CheckedPreprocessing.modelExtension
      replay.checkedPayload
      (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
        replay.antiPrenexFreeClosed)
      (hostCoreModel M) (hostCoreEnv M) with ⟨extension⟩
    let functionSort := extension.functionSort_of (hostCore_functionSort M)
    let targetModel := extension.target
    let targetBase := extension.rebase (hostCoreEnv M)
    let targetStructure :=
      SearchMaterialization.CoreProjectionSoundness.searchStructure
        targetModel functionSort
    have hTargetFree :
        CoreSyntax.NormalForm.Semantics.Env.RespectsFree targetBase :=
      extension.respectsFree (hostCore_respectsFree M)
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

theorem avatar_semanticallyEntailsAt {goal : Prop}
    (input : HostProp.CheckedInput goal)
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
      input.intrinsicProblem.theory input.intrinsicProblem.target := by
  intro M hModels
  by_cases hTarget : input.target.toIntrinsic.TrueIn M
  · exact hTarget
  · exfalso
    have hSource :
        CoreSyntax.NormalForm.Semantics.Formula.Satisfies
          (hostCoreEnv M) replay.payload.source := by
      rw [replay.sourceIsRefutation, hSourceProblem]
      exact hostCore_refutation_true input M hModels hTarget
    rcases CoreSyntax.NormalForm.CheckedPreprocessing.modelExtension
      replay.checkedPayload
      (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
        replay.antiPrenexFreeClosed)
      (hostCoreModel M) (hostCoreEnv M) with ⟨extension⟩
    let functionSort := extension.functionSort_of (hostCore_functionSort M)
    let targetModel := extension.target
    let targetBase := extension.rebase (hostCoreEnv M)
    let targetStructure :=
      SearchMaterialization.CoreProjectionSoundness.searchStructure
        targetModel functionSort
    have hTargetFree :
        CoreSyntax.NormalForm.Semantics.Env.RespectsFree targetBase :=
      extension.respectsFree (hostCore_respectsFree M)
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

end Semantics
end HostRules
end Automation
end YesMetaZFC
