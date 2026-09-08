import YesMetaZFC.Automation.SearchMaterialization
import YesMetaZFC.Automation.DAGCertificate.CompileSemantics

/-!
# 一阶投影到内在 DAG 子句的语义保持

preprocessing 仍在紧凑的单载体 `CoreSyntax` 模型中证明算法语义；进入搜索可信层时，
本模块把每个排序解释为旧 carrier 上的 subtype，并把 projected raw syntax 交给统一
检查编译器。整个转换不需要默认元素或 `Classical.choice`。
-/

namespace YesMetaZFC
namespace Automation
namespace SearchMaterialization
namespace CoreProjectionSoundness

universe x

open CoreSyntax
open CoreSyntax.NormalForm
open _root_.YesMetaZFC.Logic

/-- 旧单载体模型中某一排序的真实论域。 -/
abbrev SearchCarrier (M : Semantics.Model.{x}) (sort : CoreSort) :=
  { value : M.Carrier // M.sortInterp sort value }

namespace SearchValues

/-- 擦除 typed 参数列的排序标签，回到 preprocessing 使用的 carrier 列表。 -/
def erase {M : Semantics.Model.{x}} :
    {sorts : List CoreSort} →
      Logic.FirstOrder.Values (SearchCarrier M) sorts → List M.Carrier
  | [], .nil => []
  | _ :: _, .cons value rest => value.1 :: erase rest

@[simp] theorem erase_nil {M : Semantics.Model.{x}} :
    erase (M := M) (.nil :
      Logic.FirstOrder.Values (SearchCarrier M) []) = [] :=
  rfl

@[simp] theorem erase_cons {M : Semantics.Model.{x}}
    {sort : CoreSort} {sorts : List CoreSort}
    (value : SearchCarrier M sort)
    (rest : Logic.FirstOrder.Values (SearchCarrier M) sorts) :
    erase (.cons value rest) = value.1 :: erase rest :=
  rfl

/-- singleton typed 参数列的唯一元素。 -/
def single {M : Semantics.Model.{x}} {sort : CoreSort} :
    Logic.FirstOrder.Values (SearchCarrier M) [sort] → SearchCarrier M sort
  | .cons value .nil => value

@[simp] theorem erase_single {M : Semantics.Model.{x}}
    {sort : CoreSort}
    (values : Logic.FirstOrder.Values (SearchCarrier M) [sort]) :
    erase values = [(single values).1] := by
  cases values with
  | cons value rest =>
      cases rest
      rfl

end SearchValues

/-- projected 搜索签名的真正多排序结构。 -/
def searchStructure (M : Semantics.Model.{x})
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments)) :
    LogicSoundness.SetLevel.StructureAt.{x} SearchSignature where
  Carrier := SearchCarrier M
  nonempty := fun sort => by
    rcases M.sortNonempty sort with ⟨value, hValue⟩
    exact ⟨⟨value, hValue⟩⟩
  funcInterp := fun symbol arguments =>
    ⟨M.functionInterp symbol.toCore (SearchValues.erase arguments),
      functionSort symbol.toCore (SearchValues.erase arguments)⟩
  relInterp := fun symbol arguments =>
    match symbol with
    | .member =>
        M.predicateInterp
          { id := 1, arity := 2, role := PredicateRole.membership,
            inputSorts := [CoreSort.object, CoreSort.object] }
          (SearchValues.erase arguments)
    | .boolHolds =>
        M.boolHolds (SearchValues.single arguments).1
    | .definition id arity =>
        M.predicateInterp
          { id := id, arity := arity, role := PredicateRole.definition }
          (SearchValues.erase arguments)
    | .predicate predicate =>
        M.predicateInterp predicate (SearchValues.erase arguments)

@[simp] theorem functionSymbol_toCore (symbol : CoreSyntax.FunctionSymbol) :
    (FirstOrderProjection.functionSymbol symbol).toCore = symbol := by
  cases symbol with
  | mk id arity role inputSorts outputSort =>
      cases role <;> rfl

/-- 旧 free 环境按稳定 registry 生成内在 typed assignment。 -/
def searchAssignment
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) :
    Logic.FirstOrder.Assignment (searchStructure M functionSort)
      registry.context :=
  registry.assignment fun sort id =>
    ⟨env.freeVal sort id, hFree sort id⟩

/-- projected 子句没有外层 bound 变量；free 上下文完全由 registry 决定。 -/
def searchEnv
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) :
    Logic.FirstOrder.Env (searchStructure M functionSort) []
      registry.context :=
  DAGCertificate.Compile.openEnv
    (searchAssignment functionSort registry env hFree)

/-- typed assignment 与 preprocessing free 环境只在实际注册的变量上对齐。 -/
def AssignmentCorresponds
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context) : Prop :=
  ∀ {sort id entry}, registry.find? sort id = some entry →
    (assignment entry).1 = env.freeVal sort id

/-- 由完整 preprocessing 环境生成的 assignment 满足注册变量对应关系。 -/
theorem searchAssignment_corresponds
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) :
    AssignmentCorresponds functionSort registry env
      (searchAssignment functionSort registry env hFree) := by
  intro sort id entry hFind
  exact congrArg Subtype.val <|
    DAGCertificate.Compile.FreeRegistry.assignment_find?
      registry
      (fun sort id =>
        (⟨env.freeVal sort id, hFree sort id⟩ : SearchCarrier M sort))
      hFind

mutual

/-- 成功编译的 projected 项保持 preprocessing 求值。 -/
theorem coreTerm_eval_of_corresponds
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context)
    (hAssignment : AssignmentCorresponds functionSort registry env assignment) :
    ∀ term,
      FirstOrderProjection.Projectable.term term = true →
      ∀ compiled : DAGCertificate.Compile.SomeTerm
          SearchSignature [] registry.context,
        DAGCertificate.Compile.term? registry [] (coreTerm term) =
            some compiled →
          (Logic.FirstOrder.Term.eval
            (DAGCertificate.Compile.openEnv assignment)
            compiled.term).1 =
            Semantics.Term.eval env term
  | .fvar sort id, _hProjectable, compiled, hCompile => by
      simp only [coreTerm, DAGCertificate.Compile.term?_fvar] at hCompile
      cases hFind : registry.find? sort id with
      | none => simp [hFind] at hCompile
      | some entry =>
          simp [hFind] at hCompile
          subst compiled
          simp only [Logic.FirstOrder.Term.eval,
            DAGCertificate.Compile.openEnv,
            Semantics.Term.eval]
          exact hAssignment hFind
  | .app symbol arguments, hProjectable, compiled, hCompile => by
      simp only [FirstOrderProjection.Projectable.term] at hProjectable
      simp only [coreTerm, DAGCertificate.Compile.term?_app] at hCompile
      cases hArguments :
          DAGCertificate.Compile.arguments? registry []
            (SearchSignature.funcDomain
              (FirstOrderProjection.functionSymbol symbol))
            (arguments.map coreTerm) with
      | none => simp [hArguments] at hCompile
      | some compiledArguments =>
          simp [hArguments] at hCompile
          subst compiled
          simp only [Logic.FirstOrder.Term.eval, searchStructure,
            Semantics.Term.eval]
          rw [functionSymbol_toCore]
          exact congrArg (M.functionInterp symbol)
            (coreTermList_eval_of_corresponds functionSort registry env
              assignment hAssignment
              arguments hProjectable _ compiledArguments hArguments)
  | .bvar .., hProjectable, _, _
  | .apply .., hProjectable, _, _
  | .bool .., hProjectable, _, _
  | .notE .., hProjectable, _, _
  | .andE .., hProjectable, _, _
  | .orE .., hProjectable, _, _
  | .impE .., hProjectable, _, _
  | .iffE .., hProjectable, _, _
  | .quote .., hProjectable, _, _
  | .lam .., hProjectable, _, _
  | .ite .., hProjectable, _, _ => by
      simp [FirstOrderProjection.Projectable.term] at hProjectable

/-- 成功编译的 projected 参数列逐项保持 preprocessing 求值。 -/
theorem coreTermList_eval_of_corresponds
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M)
    (assignment : Logic.FirstOrder.Assignment
      (searchStructure M functionSort) registry.context)
    (hAssignment : AssignmentCorresponds functionSort registry env assignment) :
    ∀ terms,
      FirstOrderProjection.Projectable.termList terms = true →
      ∀ sorts (compiled : Logic.FirstOrder.Arguments
          SearchSignature [] registry.context sorts),
        DAGCertificate.Compile.arguments? registry [] sorts
            (terms.map coreTerm) = some compiled →
          SearchValues.erase
              (Logic.FirstOrder.Arguments.eval
                (DAGCertificate.Compile.openEnv assignment) compiled) =
            terms.map (Semantics.Term.eval env)
  | [], _hProjectable, [], compiled, hCompile => by
      simp only [List.map_nil] at hCompile
      rw [DAGCertificate.Compile.arguments?_nil] at hCompile
      cases hCompile
      rfl
  | [], _hProjectable, _ :: _, _, hCompile => by
      simp at hCompile
  | _ :: _, hProjectable, [], _, hCompile => by
      simp at hCompile
  | head :: tail, hProjectable, sort :: sorts, compiled, hCompile => by
      rcases Bool.and_eq_true_iff.mp hProjectable with
        ⟨hHeadProjectable, hTailProjectable⟩
      simp only [List.map_cons] at hCompile
      rw [DAGCertificate.Compile.arguments?_cons] at hCompile
      cases hHead :
          DAGCertificate.Compile.term? registry [] (coreTerm head) with
      | none => simp [hHead] at hCompile
      | some compiledHead =>
          cases hTail :
              DAGCertificate.Compile.arguments? registry [] sorts
                (tail.map coreTerm) with
          | none => simp [hHead, hTail] at hCompile
          | some compiledTail =>
              by_cases hSort : compiledHead.sort = sort
              · subst sort
                simp [hHead, hTail] at hCompile
                subst compiled
                simp only [Logic.FirstOrder.Arguments.eval, List.map_cons]
                change
                  (Logic.FirstOrder.Term.eval
                      (DAGCertificate.Compile.openEnv assignment)
                      compiledHead.term).1 ::
                      SearchValues.erase
                        (Logic.FirstOrder.Arguments.eval
                          (DAGCertificate.Compile.openEnv assignment)
                          compiledTail) =
                    Semantics.Term.eval env head ::
                      tail.map (Semantics.Term.eval env)
                rw [coreTerm_eval_of_corresponds functionSort registry env
                    assignment hAssignment head hHeadProjectable
                    compiledHead hHead,
                  coreTermList_eval_of_corresponds functionSort registry env
                    assignment hAssignment tail hTailProjectable sorts
                    compiledTail hTail]
              · simp [hHead, hTail, hSort] at hCompile

end

/-- 完整 preprocessing 环境上的常用项语义接口。 -/
theorem coreTerm_eval
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (term : CoreSyntax.Term)
    (hProjectable : FirstOrderProjection.Projectable.term term = true)
    (compiled : DAGCertificate.Compile.SomeTerm
      SearchSignature [] registry.context)
    (hCompile : DAGCertificate.Compile.term? registry [] (coreTerm term) =
      some compiled) :
    (Logic.FirstOrder.Term.eval
      (searchEnv functionSort registry env hFree) compiled.term).1 =
        Semantics.Term.eval env term := by
  exact coreTerm_eval_of_corresponds functionSort registry env
    (searchAssignment functionSort registry env hFree)
    (searchAssignment_corresponds functionSort registry env hFree)
    term hProjectable compiled hCompile

/-- 完整 preprocessing 环境上的常用参数列语义接口。 -/
theorem coreTermList_eval
    {M : Semantics.Model.{x}}
    (functionSort : ∀ symbol arguments,
      M.sortInterp symbol.outputSort
        (M.functionInterp symbol arguments))
    (registry : DAGCertificate.Compile.FreeRegistry SearchSignature)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (terms : List CoreSyntax.Term)
    (hProjectable : FirstOrderProjection.Projectable.termList terms = true)
    (sorts : List CoreSort)
    (compiled : Logic.FirstOrder.Arguments
      SearchSignature [] registry.context sorts)
    (hCompile : DAGCertificate.Compile.arguments? registry [] sorts
      (terms.map coreTerm) = some compiled) :
    SearchValues.erase
        (Logic.FirstOrder.Arguments.eval
          (searchEnv functionSort registry env hFree) compiled) =
      terms.map (Semantics.Term.eval env) := by
  exact coreTermList_eval_of_corresponds functionSort registry env
    (searchAssignment functionSort registry env hFree)
    (searchAssignment_corresponds functionSort registry env hFree)
    terms hProjectable sorts compiled hCompile

end CoreProjectionSoundness
end SearchMaterialization
end Automation
end YesMetaZFC
