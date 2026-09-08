import YesMetaZFC.Automation.CoreNormalForm.FirstOrderProjectionSoundness.Core

namespace YesMetaZFC
namespace Automation
namespace SearchMaterialization
namespace CoreProjectionSoundness

universe x

open CoreSyntax
open CoreSyntax.NormalForm
open _root_.YesMetaZFC.Logic

/-- 成功编译的 projected 原子保持 preprocessing 满足关系。 -/
theorem coreAtom_satisfies_of_corresponds
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context)
    (hAssignment : AssignmentCorresponds functionSort registry env assignment)
    (atom : CoreSyntax.NormalForm.Atom)
    (hProjectable : FirstOrderProjection.Projectable.atom atom = true)
    (compiled : Logic.FirstOrder.Formula
      SearchSignature [] registry.context)
    (hCompile : DAGCertificate.Compile.formula? registry []
      (coreAtom atom) = some compiled) :
    Logic.FirstOrder.Formula.satisfies
        (DAGCertificate.Compile.openEnv assignment) compiled ↔
      Semantics.Atom.Satisfies env atom := by
  cases atom with
  | predicate predicate arguments =>
      simp only [FirstOrderProjection.Projectable.atom] at hProjectable
      simp only [coreAtom, DAGCertificate.Compile.formula?] at hCompile
      cases hArguments :
          DAGCertificate.Compile.arguments? registry []
            (SearchSignature.relDomain (.predicate predicate))
            (arguments.map coreTerm) with
      | none => simp [hArguments] at hCompile
      | some compiledArguments =>
          simp [hArguments] at hCompile
          subst compiled
          simp only [Logic.FirstOrder.Formula.satisfies,
            searchStructure, Semantics.Atom.Satisfies]
          exact iff_of_eq <| congrArg (M.predicateInterp predicate) <|
            coreTermList_eval_of_corresponds functionSort registry env
              assignment hAssignment
              arguments hProjectable _ compiledArguments hArguments
  | equal sourceSort left right =>
      rcases Bool.and_eq_true_iff.mp hProjectable with
        ⟨hLeftProjectable, hRightProjectable⟩
      simp only [coreAtom, DAGCertificate.Compile.formula?] at hCompile
      cases hLeft :
          DAGCertificate.Compile.term? registry [] (coreTerm left) with
      | none => simp [hLeft] at hCompile
      | some compiledLeft =>
          cases hRight :
              DAGCertificate.Compile.term? registry [] (coreTerm right) with
          | none => simp [hLeft, hRight] at hCompile
          | some compiledRight =>
              have hLeftEval :=
                coreTerm_eval_of_corresponds functionSort registry env
                  assignment hAssignment
                  left hLeftProjectable compiledLeft hLeft
              have hRightEval :=
                coreTerm_eval_of_corresponds functionSort registry env
                  assignment hAssignment
                  right hRightProjectable compiledRight hRight
              rcases compiledLeft with ⟨leftSort, leftTerm⟩
              rcases compiledRight with ⟨rightSort, rightTerm⟩
              by_cases hSort : leftSort = rightSort
              · cases hSort
                simp [hLeft, hRight] at hCompile
                subst compiled
                simp only [Logic.FirstOrder.Formula.satisfies,
                  Semantics.Atom.Satisfies]
                constructor
                · intro hEqual
                  have hValue := congrArg Subtype.val hEqual
                  simpa [hLeftEval, hRightEval] using hValue
                · intro hEqual
                  apply Subtype.ext
                  simpa [hLeftEval, hRightEval] using hEqual
              · simp [hLeft, hRight, hSort] at hCompile
  | boolTerm term =>
      simp only [FirstOrderProjection.Projectable.atom] at hProjectable
      simp only [coreAtom, DAGCertificate.Compile.formula?] at hCompile
      cases hArguments :
          DAGCertificate.Compile.arguments? registry []
            (SearchSignature.relDomain .boolHolds) [coreTerm term] with
      | none => simp [hArguments] at hCompile
      | some compiledArguments =>
          simp [hArguments] at hCompile
          subst compiled
          have hTermList :
              FirstOrderProjection.Projectable.termList [term] = true := by
            simp [FirstOrderProjection.Projectable.termList, hProjectable]
          have hEval :=
            coreTermList_eval_of_corresponds functionSort registry env
              assignment hAssignment
              [term] hTermList _ compiledArguments hArguments
          let values :
              Logic.FirstOrder.Values (SearchCarrier M) [.bool] :=
            Logic.FirstOrder.Arguments.eval
              (DAGCertificate.Compile.openEnv assignment)
              compiledArguments
          have hValues :
              SearchValues.erase values =
                [Semantics.Term.eval env term] := by
            change SearchValues.erase
                (Logic.FirstOrder.Arguments.eval
                  (DAGCertificate.Compile.openEnv assignment)
                  compiledArguments) =
              [Semantics.Term.eval env term]
            exact hEval
          rw [SearchValues.erase_single] at hValues
          have hValue :
              (SearchValues.single values).1 =
                Semantics.Term.eval env term :=
            (List.cons.inj hValues).1
          change
            M.boolHolds (SearchValues.single values).1 ↔
              M.boolHolds (Semantics.Term.eval env term)
          exact iff_of_eq (congrArg M.boolHolds hValue)

/-- 完整 preprocessing 环境上的常用原子语义接口。 -/
theorem coreAtom_satisfies
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (atom : CoreSyntax.NormalForm.Atom)
    (hProjectable : FirstOrderProjection.Projectable.atom atom = true)
    (compiled : Logic.FirstOrder.Formula
      SearchSignature [] registry.context)
    (hCompile : DAGCertificate.Compile.formula? registry []
      (coreAtom atom) = some compiled) :
    Logic.FirstOrder.Formula.satisfies
        (searchEnv functionSort registry env hFree) compiled ↔
      Semantics.Atom.Satisfies env atom := by
  exact coreAtom_satisfies_of_corresponds functionSort registry env
    (searchAssignment functionSort registry env hFree)
    (searchAssignment_corresponds functionSort registry env hFree)
    atom hProjectable compiled hCompile

end CoreProjectionSoundness
end SearchMaterialization
end Automation
end YesMetaZFC
