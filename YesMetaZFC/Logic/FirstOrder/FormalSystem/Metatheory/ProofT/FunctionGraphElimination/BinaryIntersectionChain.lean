import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.BinaryIntersection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.UnorderedPair

/-
# 二元交依赖树的证明级消去

二元交的直接图消去先留下“配对函数扩张 + 一元交扩张”。本模块继续沿理论
并的右分支消去无序对，把一致性回传到
`pairing_theory ∪ intersection_operator_theory`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace BinaryIntersectionChain

open Nonlogical.BasicSetTheory

set_option autoImplicit false

private theorem intersection_avoids_pair
    {φ : SetFormula}
    (hφ : intersection_operator_theory φ) :
    FormulaAvoids FunctionSymbol.unorderedPair φ := by
  simp only [intersection_operator_theory,
    intersection_base_theory,
    subset_theory,
    empty_set_symbol_theory,
    empty_set_theory,
    empty_predicate,
    SetPredicate.separation_theory,
    extensionality_theory,
    Theory.insert, Theory.union,
    Theory.singleton] at hφ
  repeat'
    first
    | obtain hφ | hφ := hφ
    | subst φ
  all_goals
    apply checkFormulaAvoids_sound
    native_decide

private def pair_lift :
    TheoryPresentation UnorderedPair.data :=
  UnorderedPair.theory_presentation.union_right
    intersection_operator_theory
    intersection_operator_theory_sentence
    intersection_avoids_pair

/-- 消去二元交与无序对后留下的一元交定义扩张和配对存在理论。 -/
def reduct_theory : SetTheory :=
  Theory.union pairing_theory intersection_operator_theory

/-! ## 任意公式的组合编译 -/

/-- 二元交基理论消去无序对函数后的公式编译。 -/
def base_compile_formula (φ : SetFormula) : SetFormula :=
  formula UnorderedPair.data φ

/-- 二元交基理论中的任意 checked 闭证明可翻译到还原理论。 -/
theorem base_derives
    {φ : SetFormula}
    (h :
      Derives binary_intersection_base_theory [] φ) :
    Derives reduct_theory []
      (base_compile_formula φ) := by
  simpa [base_compile_formula,
      binary_intersection_base_theory,
      reduct_theory, pair_lift] using
    pair_lift.derives SetSort.set h

/-- 二元交的基理论可继续回传到无序对已消去的还原理论。 -/
theorem base_derives_falsum
    (h :
      Derives binary_intersection_base_theory []
        Formula.falsum) :
    Derives reduct_theory []
      Formula.falsum := by
  simpa [base_compile_formula,
    FunctionGraphElimination.formula] using
    base_derives h

/-- 还原理论一致时，二元交基理论保持一致。 -/
theorem base_consistent
    (h :
      Derives.Consistent reduct_theory []) :
    Derives.Consistent binary_intersection_base_theory [] := by
  intro hBase
  exact h <| base_derives_falsum hBase

/-- 二元交与无序对两层消去对闭公式给出的组合编译。 -/
def compile_formula (φ : SetFormula) : SetFormula :=
  formula UnorderedPair.data
    (formula BinaryIntersection.data φ)

/-- 二元交函数扩张中的任意 checked 闭证明可翻译到还原理论。 -/
theorem derives
    {φ : SetFormula}
    (h :
      Derives binary_intersection_operator_theory [] φ) :
    Derives reduct_theory [] (compile_formula φ) := by
  simpa [compile_formula, reduct_theory, pair_lift] using
    BinaryIntersection.theory_presentation.derives_comp
      pair_lift SetSort.set SetSort.set
      (fun _ hφ => hφ) h

/-- 二元交函数扩张中的矛盾回传到无序对已消去的理论。 -/
theorem derives_falsum
    (h :
      Derives binary_intersection_operator_theory []
        Formula.falsum) :
    Derives reduct_theory []
      Formula.falsum := by
  simpa [compile_formula,
    FunctionGraphElimination.formula] using
    derives h

/-- 还原理论一致时，二元交定义扩张保持一致。 -/
theorem consistent
    (h :
      Derives.Consistent reduct_theory []) :
    Derives.Consistent
      binary_intersection_operator_theory [] :=
  BinaryIntersection.consistent (base_consistent h)

end BinaryIntersectionChain
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
