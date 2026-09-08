import YesMetaZFC.Automation.CoreNormalForm.FirstOrderProjectionSoundness.Closed

namespace YesMetaZFC
namespace Automation

open CoreSyntax
open CoreSyntax.NormalForm
open _root_.YesMetaZFC.Logic

namespace DAGCertificate
namespace Compile
namespace ClauseCompilation

universe x

/-- 编译后的每个初始字句闭句都在指定内在结构中成立。 -/
def TrueIn {σ : Signature}
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (compilation : ClauseCompilation σ) : Prop :=
  ∀ sentence ∈ compilation.clauses, sentence.TrueIn M

end ClauseCompilation
end Compile
end DAGCertificate

namespace SearchMaterialization
namespace CoreProjectionSoundness

universe x

/-- canonical core clause problem 的检查编译结果逐句保持 preprocessing 语义。 -/
theorem coreClauseProblem_trueIn
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
    (compilation : DAGCertificate.Compile.ClauseCompilation SearchSignature)
    (hCompile : DAGCertificate.Compile.compileClauseProblem?
      ({ initialClauses := coreClauseSet clauses } :
        DAGCertificate.ClauseProblem SearchSignature) = some compilation) :
    compilation.TrueIn (searchStructure M functionSort) := by
  have hListProjectable :
      clauses.toList.all FirstOrderProjection.Projectable.clause = true := by
    simpa [FirstOrderProjection.Projectable.clauseSet] using hProjectable
  unfold DAGCertificate.Compile.compileClauseProblem? at hCompile
  simp only [coreClauseSet, Array.toList_map] at hCompile
  let registry := DAGCertificate.Compile.FreeRegistry.ofClauses
    (clauses.toList.map coreClause)
  cases hSentences : DAGCertificate.Compile.compileClauses? registry
      (clauses.toList.map coreClause) with
  | none =>
      simp [registry, hSentences] at hCompile
  | some sentences =>
      have hCompilation :
          ({ registry := registry, clauses := sentences } :
            DAGCertificate.Compile.ClauseCompilation SearchSignature) =
            compilation := by
        simpa [registry, hSentences] using hCompile
      cases hCompilation
      intro sentence hSentence
      refine coreClauseList_trueIn functionSort registry base hBaseFree
        clauses.toList hListProjectable ?_ sentences hSentences sentence hSentence
      intro env hFree hBound clause hClause
      exact hSatisfies env hFree hBound clause hClause

/-- checked compiler 边界直接暴露整组内在闭句的真实性。 -/
theorem checkedCoreClauseProblem_trueIn
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
    (checked : DAGCertificate.Compile.CheckedClauseProblem
      ({ initialClauses := coreClauseSet clauses } :
        DAGCertificate.ClauseProblem SearchSignature)) :
    checked.compilation.TrueIn (searchStructure M functionSort) :=
  coreClauseProblem_trueIn functionSort base hBaseFree clauses hProjectable
    hSatisfies checked.compilation checked.compiled

end CoreProjectionSoundness
end SearchMaterialization
end Automation
end YesMetaZFC
