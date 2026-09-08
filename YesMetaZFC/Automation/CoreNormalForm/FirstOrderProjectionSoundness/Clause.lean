import YesMetaZFC.Automation.CoreNormalForm.FirstOrderProjectionSoundness.Atom

namespace YesMetaZFC
namespace Automation
namespace SearchMaterialization
namespace CoreProjectionSoundness

universe x

open CoreSyntax
open CoreSyntax.NormalForm
open _root_.YesMetaZFC.Logic

/-- 成功编译的 projected 文字保持 preprocessing 满足关系。 -/
theorem coreLiteral_satisfies_of_corresponds
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context)
    (hAssignment : AssignmentCorresponds functionSort registry env assignment)
    (literal : CoreSyntax.NormalForm.Literal)
    (hProjectable : FirstOrderProjection.Projectable.literal literal = true)
    (compiled : Logic.FirstOrder.Formula
      SearchSignature [] registry.context)
    (hCompile : DAGCertificate.Compile.formula? registry []
      (coreLiteral literal).toFormula = some compiled) :
    Logic.FirstOrder.Formula.satisfies
        (DAGCertificate.Compile.openEnv assignment) compiled ↔
      Semantics.Literal.Satisfies env literal := by
  rcases literal with ⟨positive, atom⟩
  simp only [FirstOrderProjection.Projectable.literal] at hProjectable
  cases positive with
  | false =>
      simp only [coreLiteral, DAGCertificate.Literal.toFormula,
        Bool.false_eq_true, ↓reduceIte,
        DAGCertificate.Compile.formula?] at hCompile
      cases hAtomCompile :
          DAGCertificate.Compile.formula? registry [] (coreAtom atom) with
      | none => simp [hAtomCompile] at hCompile
      | some compiledAtom =>
          simp [hAtomCompile] at hCompile
          subst compiled
          exact not_congr <|
            coreAtom_satisfies_of_corresponds functionSort registry env
              assignment hAssignment atom
              hProjectable compiledAtom hAtomCompile
  | true =>
      exact coreAtom_satisfies_of_corresponds functionSort registry env
        assignment hAssignment atom hProjectable compiled hCompile

/-- projected 文字列表的析取编译保持“至少一个文字成立”的语义。 -/
private theorem coreLiteralList_satisfies
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context)
    (hAssignment : AssignmentCorresponds functionSort registry env assignment) :
    ∀ literals : List CoreSyntax.NormalForm.Literal,
      literals.all FirstOrderProjection.Projectable.literal = true →
      ∀ compiled : Logic.FirstOrder.Formula
          SearchSignature [] registry.context,
        DAGCertificate.Compile.formula? registry []
            (DAGCertificate.Formula.disjunctionList
              (literals.map fun literal => (coreLiteral literal).toFormula)) =
              some compiled →
          (Logic.FirstOrder.Formula.satisfies
              (DAGCertificate.Compile.openEnv assignment) compiled ↔
            ∃ literal ∈ literals, Semantics.Literal.Satisfies env literal)
  | [], _hProjectable, compiled, hCompile => by
      simp [DAGCertificate.Formula.disjunctionList,
        DAGCertificate.Compile.formula?] at hCompile
      subst compiled
      simp [Logic.FirstOrder.Formula.satisfies]
  | head :: tail, hProjectable, compiled, hCompile => by
      rcases Bool.and_eq_true_iff.mp hProjectable with
        ⟨hHeadProjectable, hTailProjectable⟩
      cases tail with
      | nil =>
          simp only [List.map_cons, List.map_nil,
            DAGCertificate.Formula.disjunctionList] at hCompile
          simpa using
            coreLiteral_satisfies_of_corresponds functionSort registry env
              assignment hAssignment head hHeadProjectable compiled hCompile
      | cons next rest =>
          cases hHeadCompile :
              DAGCertificate.Compile.formula? registry []
                (coreLiteral head).toFormula with
          | none =>
              simp [DAGCertificate.Formula.disjunctionList,
                DAGCertificate.Compile.formula?, hHeadCompile] at hCompile
          | some compiledHead =>
              cases hTailCompile :
                  DAGCertificate.Compile.formula? registry []
                    (DAGCertificate.Formula.disjunctionList
                      ((next :: rest).map fun literal =>
                        (coreLiteral literal).toFormula)) with
              | none =>
                  have hTailCompile' :
                      DAGCertificate.Compile.formula? registry []
                          (DAGCertificate.Formula.disjunctionList
                            ((coreLiteral next).toFormula ::
                              rest.map fun literal =>
                                (coreLiteral literal).toFormula)) = none := by
                    simpa only [List.map_cons] using hTailCompile
                  simp [DAGCertificate.Formula.disjunctionList,
                    DAGCertificate.Compile.formula?, hHeadCompile,
                    hTailCompile'] at hCompile
              | some compiledTail =>
                  have hTailCompile' :
                      DAGCertificate.Compile.formula? registry []
                          (DAGCertificate.Formula.disjunctionList
                            ((coreLiteral next).toFormula ::
                              rest.map fun literal =>
                                (coreLiteral literal).toFormula)) =
                        some compiledTail := by
                    simpa only [List.map_cons] using hTailCompile
                  have hCompiled :
                      .disj compiledHead compiledTail = compiled := by
                    simpa [DAGCertificate.Formula.disjunctionList,
                      DAGCertificate.Compile.formula?, hHeadCompile,
                      hTailCompile'] using hCompile
                  cases hCompiled
                  rw [show
                    Logic.FirstOrder.Formula.satisfies
                        (DAGCertificate.Compile.openEnv assignment)
                        (.disj compiledHead compiledTail) ↔
                      Logic.FirstOrder.Formula.satisfies
                          (DAGCertificate.Compile.openEnv assignment)
                          compiledHead ∨
                        Logic.FirstOrder.Formula.satisfies
                          (DAGCertificate.Compile.openEnv assignment)
                          compiledTail by rfl]
                  rw [coreLiteral_satisfies_of_corresponds functionSort registry
                    env assignment hAssignment head hHeadProjectable
                    compiledHead hHeadCompile]
                  rw [coreLiteralList_satisfies functionSort registry env
                    assignment hAssignment (next :: rest) hTailProjectable
                    compiledTail hTailCompile]
                  simp

/-- 成功编译的 projected 字句保持 preprocessing 字句满足关系。 -/
theorem coreClause_satisfies_of_corresponds
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context)
    (hAssignment : AssignmentCorresponds functionSort registry env assignment)
    (clause : CoreSyntax.NormalForm.Clause)
    (hProjectable : FirstOrderProjection.Projectable.clause clause = true)
    (compiled : Logic.FirstOrder.OpenFormula
      SearchSignature registry.context)
    (hCompile : DAGCertificate.Compile.clauseFormula? registry
      (coreClause clause) = some compiled) :
    Logic.FirstOrder.Formula.satisfies
        (DAGCertificate.Compile.openEnv assignment) compiled ↔
      Semantics.Clause.Satisfies env clause := by
  have hListProjectable :
      clause.toList.all FirstOrderProjection.Projectable.literal = true := by
    simpa [FirstOrderProjection.Projectable.clause] using hProjectable
  have hCompile' :
      DAGCertificate.Compile.formula? registry []
          (DAGCertificate.Formula.disjunctionList
            (clause.toList.map fun literal =>
              (coreLiteral literal).toFormula)) = some compiled := by
    simpa [DAGCertificate.Compile.clauseFormula?,
      DAGCertificate.Clause.toFormula, coreClause, Array.toList_map,
      List.map_map, Function.comp_def] using hCompile
  simpa [Semantics.Clause.Satisfies] using
    coreLiteralList_satisfies functionSort registry env assignment hAssignment
      clause.toList hListProjectable compiled hCompile'

/-- 完整 preprocessing 环境上的常用文字语义接口。 -/
theorem coreLiteral_satisfies
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (literal : CoreSyntax.NormalForm.Literal)
    (hProjectable : FirstOrderProjection.Projectable.literal literal = true)
    (compiled : Logic.FirstOrder.Formula
      SearchSignature [] registry.context)
    (hCompile : DAGCertificate.Compile.formula? registry []
      (coreLiteral literal).toFormula = some compiled) :
    Logic.FirstOrder.Formula.satisfies
        (searchEnv functionSort registry env hFree) compiled ↔
      Semantics.Literal.Satisfies env literal := by
  exact coreLiteral_satisfies_of_corresponds functionSort registry env
    (searchAssignment functionSort registry env hFree)
    (searchAssignment_corresponds functionSort registry env hFree)
    literal hProjectable compiled hCompile

/-- 完整 preprocessing 环境上的常用字句语义接口。 -/
theorem coreClause_satisfies
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (clause : CoreSyntax.NormalForm.Clause)
    (hProjectable : FirstOrderProjection.Projectable.clause clause = true)
    (compiled : Logic.FirstOrder.OpenFormula
      SearchSignature registry.context)
    (hCompile : DAGCertificate.Compile.clauseFormula? registry
      (coreClause clause) = some compiled) :
    Logic.FirstOrder.Formula.satisfies
        (searchEnv functionSort registry env hFree) compiled ↔
      Semantics.Clause.Satisfies env clause := by
  exact coreClause_satisfies_of_corresponds functionSort registry env
    (searchAssignment functionSort registry env hFree)
    (searchAssignment_corresponds functionSort registry env hFree)
    clause hProjectable compiled hCompile

end CoreProjectionSoundness
end SearchMaterialization
end Automation
end YesMetaZFC
