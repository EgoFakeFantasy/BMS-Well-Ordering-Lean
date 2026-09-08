import YesMetaZFC.Automation.CoreNormalForm.FirstOrderProjectionSoundness.Clause

namespace YesMetaZFC
namespace Automation
namespace SearchMaterialization
namespace CoreProjectionSoundness

universe x

open CoreSyntax
open CoreSyntax.NormalForm
open _root_.YesMetaZFC.Logic

/--
任意 typed assignment 的 preprocessing 环境。未注册变量沿用既有 base，因此不需要
从 `sortNonempty` 选择全局默认元。
-/
def sourceEnvOfAssignment
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (base : Semantics.Env M)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context) :
    Semantics.Env M where
  boundVal := base.boundVal
  freeVal := fun sort id =>
    match registry.find? sort id with
    | none => base.freeVal sort id
    | some entry => (assignment entry).1

/-- 反向环境在所有排序上保持良构。 -/
theorem sourceEnvOfAssignment_respectsFree
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (base : Semantics.Env M) (hBaseFree : Semantics.Env.RespectsFree base)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context) :
    Semantics.Env.RespectsFree
      (sourceEnvOfAssignment functionSort registry base assignment) := by
  intro sort id
  cases hFind : registry.find? sort id with
  | none =>
      simpa [sourceEnvOfAssignment, hFind] using hBaseFree sort id
  | some entry =>
      simpa [sourceEnvOfAssignment, hFind] using (assignment entry).2

/-- 反向环境与原 typed assignment 在注册变量上逐点一致。 -/
theorem sourceEnvOfAssignment_corresponds
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (base : Semantics.Env M)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context) :
    AssignmentCorresponds functionSort registry
      (sourceEnvOfAssignment functionSort registry base assignment)
      assignment := by
  intro sort id entry hFind
  simp [sourceEnvOfAssignment, hFind]

/-- 反向环境保留 base 的 bound 栈。 -/
theorem sourceEnvOfAssignment_sameBound
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (base : Semantics.Env M)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context) :
    Semantics.LocalSkolemChoice.SameBoundStack
      (sourceEnvOfAssignment functionSort registry base assignment) base := by
  intro index
  rfl

/-- projected 字句编译成全称闭句后，在任意 typed assignment 下保持满足。 -/
theorem coreClauseSentence_trueIn
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (base : Semantics.Env M) (hBaseFree : Semantics.Env.RespectsFree base)
    (clause : CoreSyntax.NormalForm.Clause)
    (hProjectable : FirstOrderProjection.Projectable.clause clause = true)
    (sentence : Logic.FirstOrder.Sentence SearchSignature)
    (hCompile : DAGCertificate.Compile.clauseSentence? registry
      (coreClause clause) = some sentence)
    (hSatisfies : ∀ env,
      Semantics.Env.RespectsFree env →
      Semantics.LocalSkolemChoice.SameBoundStack env base →
      Semantics.Clause.Satisfies env clause) :
    sentence.TrueIn (searchStructure M functionSort) := by
  unfold DAGCertificate.Compile.clauseSentence? at hCompile
  cases hFormula : DAGCertificate.Compile.clauseFormula? registry
      (coreClause clause) with
  | none => simp [hFormula] at hCompile
  | some formula =>
      simp [hFormula] at hCompile
      subst sentence
      apply (DAGCertificate.Compile.forallFree_trueIn_iff formula).mpr
      intro assignment
      let env := sourceEnvOfAssignment functionSort registry base assignment
      have hFree : Semantics.Env.RespectsFree env :=
        sourceEnvOfAssignment_respectsFree functionSort registry base
          hBaseFree assignment
      have hBound :
          Semantics.LocalSkolemChoice.SameBoundStack env base :=
        sourceEnvOfAssignment_sameBound functionSort registry base assignment
      exact (coreClause_satisfies_of_corresponds functionSort registry env
        assignment
        (sourceEnvOfAssignment_corresponds functionSort registry base assignment)
        clause hProjectable formula hFormula).mpr
          (hSatisfies env hFree hBound)

/-- 字句列表逐项编译后，每个内在闭句都在 projected 结构中为真。 -/
theorem coreClauseList_trueIn
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (base : Semantics.Env M) (hBaseFree : Semantics.Env.RespectsFree base) :
    ∀ clauses : List CoreSyntax.NormalForm.Clause,
      clauses.all FirstOrderProjection.Projectable.clause = true →
      (∀ env,
        Semantics.Env.RespectsFree env →
        Semantics.LocalSkolemChoice.SameBoundStack env base →
        ∀ clause ∈ clauses, Semantics.Clause.Satisfies env clause) →
      ∀ sentences,
        DAGCertificate.Compile.compileClauses? registry
            (clauses.map coreClause) = some sentences →
          ∀ sentence ∈ sentences,
            sentence.TrueIn (searchStructure M functionSort)
  | [], _hProjectable, _hSatisfies, sentences, hCompile => by
      simp [DAGCertificate.Compile.compileClauses?] at hCompile
      subst sentences
      simp
  | clause :: rest, hProjectable, hSatisfies, sentences, hCompile => by
      rcases Bool.and_eq_true_iff.mp hProjectable with
        ⟨hClauseProjectable, hRestProjectable⟩
      cases hSentence : DAGCertificate.Compile.clauseSentence? registry
          (coreClause clause) with
      | none =>
          simp [DAGCertificate.Compile.compileClauses?, hSentence] at hCompile
      | some sentence =>
          cases hRestCompile : DAGCertificate.Compile.compileClauses? registry
              (rest.map coreClause) with
          | none =>
              simp [DAGCertificate.Compile.compileClauses?, hSentence,
                hRestCompile] at hCompile
          | some restSentences =>
              simp [DAGCertificate.Compile.compileClauses?, hSentence,
                hRestCompile] at hCompile
              subst sentences
              intro target hTarget
              simp only [List.mem_cons] at hTarget
              rcases hTarget with hTarget | hTarget
              · subst target
                refine coreClauseSentence_trueIn functionSort registry base
                  hBaseFree clause hClauseProjectable sentence hSentence ?_
                intro env hFree hBound
                exact hSatisfies env hFree hBound clause (by simp)
              · apply coreClauseList_trueIn functionSort registry base hBaseFree
                  rest hRestProjectable
                · intro env hFree hBound target hTarget
                  exact hSatisfies env hFree hBound target (by simp [hTarget])
                · exact hRestCompile
                · exact hTarget

end CoreProjectionSoundness
end SearchMaterialization
end Automation
end YesMetaZFC
