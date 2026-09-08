import YesMetaZFC.Automation.SourcePreprocessing

/-!
# 普通 Lean `Prop` 的可信语义核

本模块把宿主命题骨架同时翻译为：

* 供预处理与搜索器消费的原始有限语法；
* 供可信语义边界消费的内在闭句语法。

两种翻译由一次确定性的检查编译等式对齐。排序正确、作用域正确和闭合性不再作为
递归 Prop 证明向下游传播；旧的反模型扩张桥与自由变量环境桥已完全移除。
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

/-- 搜索层使用的原始有限语法。 -/
def toSearch : Formula →
    DAGCertificate.Formula SearchMaterialization.SearchSignature
  | .atom value => .rel (.predicate (predicate value)) []
  | .falsum => .falsum
  | .truth => .truth
  | .neg body => .neg body.toSearch
  | .conj left right => .conj left.toSearch right.toSearch
  | .disj left right => .disj left.toSearch right.toSearch
  | .imp left right => .imp left.toSearch right.toSearch
  | .iff left right => .iff left.toSearch right.toSearch

/-- 可信层使用的内在闭句语法。 -/
def toIntrinsic : Formula →
    Logic.FirstOrder.Sentence SearchMaterialization.SearchSignature
  | .atom value => .rel (.predicate (predicate value)) .nil
  | .falsum => .falsum
  | .truth => .truth
  | .neg body => .neg body.toIntrinsic
  | .conj left right => .conj left.toIntrinsic right.toIntrinsic
  | .disj left right => .disj left.toIntrinsic right.toIntrinsic
  | .imp left right => .imp left.toIntrinsic right.toIntrinsic
  | .iff left right => .iff left.toIntrinsic right.toIntrinsic

/-- 宿主命题原始语法编译后定义上就是对应的内在闭句。 -/
@[simp] theorem compile_toSearch (formula : Formula) :
    DAGCertificate.Compile.sentence? formula.toSearch =
      some formula.toIntrinsic := by
  induction formula with
  | atom value =>
      simp only [toSearch, toIntrinsic,
        DAGCertificate.Compile.sentence?,
        DAGCertificate.Compile.formula?]
      dsimp [predicate, SearchMaterialization.SearchSignature]
      rw [DAGCertificate.Compile.arguments?_nil]
      rfl
  | falsum | truth =>
      rfl
  | neg body ih =>
      change DAGCertificate.Compile.formula?
        DAGCertificate.Compile.FreeRegistry.empty [] body.toSearch =
          some body.toIntrinsic at ih
      change Option.map Logic.FirstOrder.Formula.neg
        (DAGCertificate.Compile.formula?
          DAGCertificate.Compile.FreeRegistry.empty [] body.toSearch) =
        some (Logic.FirstOrder.Formula.neg body.toIntrinsic)
      rw [ih]
      rfl
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      change DAGCertificate.Compile.formula?
        DAGCertificate.Compile.FreeRegistry.empty [] left.toSearch =
          some left.toIntrinsic at ihLeft
      change DAGCertificate.Compile.formula?
        DAGCertificate.Compile.FreeRegistry.empty [] right.toSearch =
          some right.toIntrinsic at ihRight
      simp only [toSearch, toIntrinsic,
        DAGCertificate.Compile.sentence?,
        DAGCertificate.Compile.formula?]
      rw [ihLeft, ihRight]
      rfl

@[simp] theorem compile_toSearchList (formulas : List Formula) :
    DAGCertificate.Compile.sentenceList? (formulas.map toSearch) =
      some (formulas.map toIntrinsic) := by
  induction formulas with
  | nil => rfl
  | cons formula rest ih =>
      simp [DAGCertificate.Compile.sentenceList?, ih]

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

theorem goalOfTarget {goal : Prop} (input : CheckedInput goal)
    (hTarget : Formula.eval input.atoms input.target) : goal := by
  rw [← input.targetAligned]
  exact hTarget

def sourceProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.Problem := {
  premises := premises.map Formula.toCore
  target := target.toCore
}

/-- 预处理与搜索器消费的原始公式问题。 -/
def searchProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.DeepProblem := {
  premises := premises.map Formula.toSearch
  target := target.toSearch
}

/-- 可信语义层消费的内在闭句问题。 -/
def intrinsicProblemOfSyntax (premises : List Formula) (target : Formula) :
    LogicSoundness.SetLevel.DeepProblem
      SearchMaterialization.SearchSignature := {
  premises := premises.map Formula.toIntrinsic
  target := target.toIntrinsic
}

/-- 原始问题的一次检查编译精确命中宿主命题的内在翻译。 -/
@[simp] theorem searchProblem_compilation
    (premises : List Formula) (target : Formula) :
    DAGCertificate.Compile.compileProblem?
        (searchProblemOfSyntax premises target) =
      some (intrinsicProblemOfSyntax premises target) := by
  simp [DAGCertificate.Compile.compileProblem?, searchProblemOfSyntax,
    intrinsicProblemOfSyntax]

def checkedProblemOfSyntax (premises : List Formula) (target : Formula) :
    DAGCertificate.Compile.CheckedProblem
      (searchProblemOfSyntax premises target) :=
  DAGCertificate.Compile.CheckedProblem.of_compilation
    (searchProblem_compilation premises target)

def sourceProblem {goal : Prop} (input : CheckedInput goal) :
    SourcePreprocessing.Problem :=
  sourceProblemOfSyntax input.premises input.target

def searchProblem {goal : Prop} (input : CheckedInput goal) :
    SourcePreprocessing.DeepProblem :=
  searchProblemOfSyntax input.premises input.target

def intrinsicProblem {goal : Prop} (input : CheckedInput goal) :
    LogicSoundness.SetLevel.DeepProblem
      SearchMaterialization.SearchSignature :=
  intrinsicProblemOfSyntax input.premises input.target

def checkedProblem {goal : Prop} (input : CheckedInput goal) :
    DAGCertificate.Compile.CheckedProblem input.searchProblem :=
  checkedProblemOfSyntax input.premises input.target

@[simp] theorem checkedProblem_problem {goal : Prop}
    (input : CheckedInput goal) :
    input.checkedProblem.problem = input.intrinsicProblem :=
  rfl

abbrev SearchStructureAt :=
  LogicSoundness.SetLevel.StructureAt.{x}
    SearchMaterialization.SearchSignature

abbrev SearchStructure := SearchStructureAt.{0}

/--
atom 表的标准宿主结构。所有排序解释为提升后的 `Unit`；宿主命题只由零元 predicate
解释读取，函数和其余关系不会出现在宿主命题翻译中。
-/
def hostStructureAt (atoms : Nat → Prop) : SearchStructureAt.{x} where
  Carrier := fun _ => ULift.{x, 0} Unit
  nonempty := fun _ => ⟨ULift.up ()⟩
  funcInterp := fun _ _ => ULift.up ()
  relInterp := fun relation _ =>
    match relation with
    | .predicate predicate => atoms predicate.id
    | _ => False

def hostStructure (atoms : Nat → Prop) : SearchStructure :=
  hostStructureAt.{0} atoms

/-- 内在闭句在标准宿主结构中的真假定义上回到原 Lean 命题。 -/
theorem satisfies_intrinsic_hostAt (atoms : Nat → Prop) :
    ∀ formula : Formula,
      formula.toIntrinsic.TrueIn (hostStructureAt.{x} atoms) ↔
        formula.eval atoms
  | .atom value => by
      simp [Formula.toIntrinsic, Formula.predicate,
        Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies,
        Logic.FirstOrder.Env.empty, hostStructureAt, Formula.eval]
  | .falsum => by
      simp [Formula.toIntrinsic, Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies, Formula.eval]
  | .truth => by
      simp [Formula.toIntrinsic, Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies, Formula.eval]
  | .neg body => by
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies, Formula.eval] using
          not_congr (satisfies_intrinsic_hostAt atoms body)
  | .conj left right => by
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies, Formula.eval] using
          and_congr (satisfies_intrinsic_hostAt atoms left)
            (satisfies_intrinsic_hostAt atoms right)
  | .disj left right => by
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies, Formula.eval] using
          or_congr (satisfies_intrinsic_hostAt atoms left)
            (satisfies_intrinsic_hostAt atoms right)
  | .imp left right => by
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies, Formula.eval] using
          imp_congr (satisfies_intrinsic_hostAt atoms left)
            (satisfies_intrinsic_hostAt atoms right)
  | .iff left right => by
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.TrueIn,
        Logic.FirstOrder.Formula.satisfies, Formula.eval] using
          iff_congr (satisfies_intrinsic_hostAt atoms left)
            (satisfies_intrinsic_hostAt atoms right)

theorem satisfies_intrinsic_host (atoms : Nat → Prop) :
    ∀ formula : Formula,
      formula.toIntrinsic.TrueIn (hostStructure atoms) ↔
        formula.eval atoms :=
  satisfies_intrinsic_hostAt.{0} atoms

/-- 内在闭句语义证书直接恢复原宿主目标。 -/
theorem soundOfIntrinsicAt {goal : Prop} (input : CheckedInput goal)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
        input.intrinsicProblem.theory input.intrinsicProblem.target) :
    goal := by
  have hTarget :
      input.target.toIntrinsic.TrueIn
        (hostStructureAt.{x} input.atoms) :=
    hSearch (hostStructureAt.{x} input.atoms) (by
      intro sentence hSentence
      change sentence ∈ input.premises.map Formula.toIntrinsic at hSentence
      rcases List.mem_map.mp hSentence with ⟨source, hSource, rfl⟩
      exact (satisfies_intrinsic_hostAt input.atoms source).mpr
        (input.premiseHolds hSource))
  exact input.goalOfTarget <|
    (satisfies_intrinsic_hostAt input.atoms input.target).mp hTarget

theorem soundOfIntrinsic {goal : Prop} (input : CheckedInput goal)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntails
        input.intrinsicProblem.theory input.intrinsicProblem.target) :
    goal :=
  input.soundOfIntrinsicAt hSearch

/-- 任意同源 checked 编译结果都由其编译等式归约到同一个内在问题。 -/
theorem soundOfCheckedAt {goal : Prop} (input : CheckedInput goal)
    (checked : DAGCertificate.Compile.CheckedProblem input.searchProblem)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
        checked.problem.theory checked.problem.target) :
    goal := by
  have hProblem : checked.problem = input.intrinsicProblem :=
    DAGCertificate.Compile.CheckedProblem.problem_eq_of_compilation checked
      (searchProblem_compilation input.premises input.target)
  apply input.soundOfIntrinsicAt
  simpa [hProblem] using! hSearch

theorem soundOfChecked {goal : Prop} (input : CheckedInput goal)
    (checked : DAGCertificate.Compile.CheckedProblem input.searchProblem)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntails
        checked.problem.theory checked.problem.target) :
    goal :=
  input.soundOfCheckedAt checked hSearch

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
