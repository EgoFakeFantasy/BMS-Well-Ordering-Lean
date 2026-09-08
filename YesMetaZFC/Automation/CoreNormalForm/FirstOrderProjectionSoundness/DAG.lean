import YesMetaZFC.Automation.CoreNormalForm.FirstOrderProjectionSoundness.Problem
import YesMetaZFC.Automation.DAGCertificate.CompileDAG

namespace YesMetaZFC
namespace Automation
namespace SearchMaterialization
namespace CoreProjectionSoundness

universe x

open CoreSyntax
open CoreSyntax.NormalForm
open _root_.YesMetaZFC.Logic

/-- 单个全局-registry 编译字句继承 preprocessing 字句真实性。 -/
theorem coreCompiledClause_trueIn
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (base : Semantics.Env M) (hBaseFree : Semantics.Env.RespectsFree base)
    (clause : CoreSyntax.NormalForm.Clause)
    (hProjectable : FirstOrderProjection.Projectable.clause clause = true)
    (compiled : DAGCertificate.Compile.CompiledClause registry)
    (hRaw : compiled.raw = coreClause clause)
    (hSatisfies : ∀ env,
      Semantics.Env.RespectsFree env →
      Semantics.LocalSkolemChoice.SameBoundStack env base →
      Semantics.Clause.Satisfies env clause) :
    compiled.TrueIn (searchStructure M functionSort) := by
  unfold DAGCertificate.Compile.CompiledClause.TrueIn
  refine coreClauseSentence_trueIn functionSort registry base hBaseFree
    clause hProjectable compiled.sentence ?_ hSatisfies
  unfold DAGCertificate.Compile.CompiledClause.sentence
  unfold DAGCertificate.Compile.clauseSentence?
  rw [← hRaw, compiled.compiled]
  rfl

/-- 全局-registry 初始字句数组逐项继承 preprocessing 字句集真实性。 -/
theorem coreCompiledClauseArray_trueIn
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (base : Semantics.Env M) (hBaseFree : Semantics.Env.RespectsFree base)
    (clauses : CoreSyntax.NormalForm.ClauseSet)
    (hProjectable : FirstOrderProjection.Projectable.clauseSet clauses = true)
    (hSatisfies : ∀ env,
      Semantics.Env.RespectsFree env →
      Semantics.LocalSkolemChoice.SameBoundStack env base →
      Semantics.ClauseSet.Satisfies env clauses)
    (compiled : Array (DAGCertificate.Compile.CompiledClause registry))
    (hRaw : compiled.map DAGCertificate.Compile.CompiledClause.raw =
      coreClauseSet clauses) :
    ∀ target ∈ compiled.toList,
      target.TrueIn (searchStructure M functionSort) := by
  intro target hTarget
  have hRawList :
      compiled.toList.map DAGCertificate.Compile.CompiledClause.raw =
        clauses.toList.map coreClause := by
    simpa [coreClauseSet, Array.toList_map] using congrArg Array.toList hRaw
  have hTargetRaw : target.raw ∈ clauses.toList.map coreClause := by
    rw [← hRawList]
    exact List.mem_map.mpr ⟨target, hTarget, rfl⟩
  rcases List.mem_map.mp hTargetRaw with ⟨clause, hClause, hClauseRaw⟩
  have hClauseProjectable :
      FirstOrderProjection.Projectable.clause clause = true := by
    apply DAGCertificate.array_check_of_mem
    · simpa [FirstOrderProjection.Projectable.clauseSet] using hProjectable
    · exact hClause
  apply coreCompiledClause_trueIn functionSort registry base hBaseFree clause
      hClauseProjectable target hClauseRaw.symm
  intro env hFree hBound
  exact hSatisfies env hFree hBound clause hClause

/-- checked DAG 的全部初始 compiled clauses 构成拓扑 replay 的内在语义基例。 -/
theorem checkedDAGInitials_trueIn
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (base : Semantics.Env M) (hBaseFree : Semantics.Env.RespectsFree base)
    (clauses : CoreSyntax.NormalForm.ClauseSet)
    (hProjectable : FirstOrderProjection.Projectable.clauseSet clauses = true)
    (hSatisfies : ∀ env,
      Semantics.Env.RespectsFree env →
      Semantics.LocalSkolemChoice.SameBoundStack env base →
      Semantics.ClauseSet.Satisfies env clauses)
    (dag : DAGCertificate.DAG SearchSignature)
    (hProblem : dag.problem.initialClauses = coreClauseSet clauses)
    (checked : DAGCertificate.Compile.CheckedDAGClauses dag) :
    ∀ target ∈ checked.compilation.initialClauses.toList,
      target.TrueIn (searchStructure M functionSort) := by
  apply coreCompiledClauseArray_trueIn functionSort
    checked.compilation.registry base hBaseFree clauses hProjectable
      hSatisfies checked.compilation.initialClauses
  exact checked.initial_raws.trans hProblem

end CoreProjectionSoundness
end SearchMaterialization
end Automation
end YesMetaZFC
