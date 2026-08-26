import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.BinaryUnion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Union
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.UnorderedPair
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.SuccessorChain

/-!
# 二元并依赖树的证明级消去

`binary_union_base_theory` 是
`pairing_operator_theory ∪ union_operator_theory`。本模块分别提升右侧一元并插件与
左侧无序对插件，最终把两棵定义扩张同时压到
`pairing_theory ∪ union_theory`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace BinaryUnionChain

open Nonlogical.BasicSetTheory
open scoped Symbols

/-- 二元并依赖树消去全部描述符函数后的存在公理理论。 -/
def reduct_theory : SetTheory :=
  Theory.union pairing_theory union_theory

private theorem pairing_avoids_union
    {φ : SetFormula}
    (hφ : pairing_operator_theory φ) :
    FormulaAvoids FunctionSymbol.union φ := by
  rcases hφ with rfl | hφ
  · simpa [pair_definition_axiom] using
      formula_avoids_forall_close
        FunctionSymbol.union
        [(SetSort.set, 0), (SetSort.set, 1),
          (SetSort.set, 2)]
        (pair_definition_instance
          (x#0) (x#1) (x#2)) <| by
            simp [pair_definition_instance,
              pair_spec, pair_member_condition,
              unordered_pair_term,
              FormulaAvoids, TermsAvoid, TermAvoids]
  · rcases hφ with rfl | hφ
    · simpa [pairing_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.union
          [(SetSort.set, 0), (SetSort.set, 1)]
          (pair_exists (x#0) (x#1)) <| by
            simp [pair_exists, pair_member_condition,
              FormulaAvoids, TermsAvoid, TermAvoids]
    · change φ = extensionality_axiom at hφ
      subst φ
      simpa [extensionality_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.union
          [(SetSort.set, 0), (SetSort.set, 1)]
          (extensionality_instance
            (x#0) (x#1)) <| by
              simp [extensionality_instance,
                agreement_to_equality,
                membership_agreement,
                FormulaAvoids, TermsAvoid, TermAvoids]

private theorem union_avoids_pair
    {φ : SetFormula}
    (hφ : union_theory φ) :
    FormulaAvoids FunctionSymbol.unorderedPair φ := by
  rcases hφ with rfl | hφ
  · simpa [union_axiom] using
      formula_avoids_forall_close
        FunctionSymbol.unorderedPair
        [(SetSort.set, 0)]
        (union_exists (x#0)) <| by
          simp [union_exists,
            FormulaAvoids, TermsAvoid, TermAvoids]
  · change φ = extensionality_axiom at hφ
    subst φ
    simpa [extensionality_axiom] using
      formula_avoids_forall_close
        FunctionSymbol.unorderedPair
        [(SetSort.set, 0), (SetSort.set, 1)]
        (extensionality_instance
          (x#0) (x#1)) <| by
            simp [extensionality_instance,
              agreement_to_equality,
              membership_agreement,
              FormulaAvoids, TermsAvoid, TermAvoids]

/-- 在左侧保留配对描述符理论的一元并消去表示。 -/
def union_lift :
    TheoryPresentation Union.data :=
  Union.theory_presentation.union_left
    pairing_operator_theory
    pairing_operator_theory_sentence
    pairing_avoids_union

/-- 在右侧保留并集存在理论的无序对消去表示。 -/
def pair_lift :
    TheoryPresentation UnorderedPair.data :=
  UnorderedPair.theory_presentation.union_right
    union_theory
    (by
      intro φ hφ
      exact union_operator_theory_sentence (Or.inr hφ))
    union_avoids_pair

/-! ## 二元并基础依赖树 -/

/-- 二元并基理论消去一元并与无序对后的组合公式编译。 -/
def base_compile_formula (φ : SetFormula) : SetFormula :=
  formula UnorderedPair.data
    (formula Union.data φ)

/-- 二元并基理论中的任意 checked 闭证明可翻译到存在公理理论。 -/
theorem base_derives
    {φ : SetFormula}
    (h :
      Derives binary_union_base_theory [] φ) :
    Derives reduct_theory []
      (base_compile_formula φ) := by
  simpa [base_compile_formula,
      binary_union_base_theory,
      reduct_theory, union_lift, pair_lift] using
    union_lift.derives_comp
      pair_lift SetSort.set SetSort.set
      (fun _ hφ => hφ) h

/-- 二元并基理论中的 checked 矛盾回传到无描述符函数的存在公理理论。 -/
theorem base_derives_falsum
    (h :
      Derives binary_union_base_theory []
        Formula.falsum) :
    Derives reduct_theory [] Formula.falsum := by
  simpa [base_compile_formula,
    FunctionGraphElimination.formula] using
    base_derives h

/-- 还原理论一致时，二元并基理论保持 checked 一致。 -/
theorem base_consistent
    (h : Derives.Consistent reduct_theory []) :
    Derives.Consistent binary_union_base_theory [] := by
  simpa [binary_union_base_theory,
      reduct_theory, union_lift, pair_lift] using
    union_lift.consistent_comp
      pair_lift SetSort.set SetSort.set
      (fun _ hφ => hφ) h

/-! ## 二元并完整定义链 -/

/-- 二元并、一元并与无序对三层消去对闭公式给出的组合编译。 -/
def compile_formula (φ : SetFormula) : SetFormula :=
  base_compile_formula
    (formula BinaryUnion.data φ)

/-- 二元并函数扩张中的任意 checked 闭证明可翻译到还原理论。 -/
theorem derives
    {φ : SetFormula}
    (h :
      Derives binary_union_operator_theory [] φ) :
    Derives reduct_theory [] (compile_formula φ) := by
  simpa [compile_formula] using
    base_derives (BinaryUnion.derives h)

/-- 二元并函数扩张中的 checked 矛盾回传到还原理论。 -/
theorem derives_falsum
    (h :
      Derives binary_union_operator_theory []
        Formula.falsum) :
    Derives reduct_theory [] Formula.falsum := by
  simpa [compile_formula, base_compile_formula,
    FunctionGraphElimination.formula] using
    derives h

/-- 还原理论一致时，二元并函数扩张保持 checked 一致。 -/
theorem consistent
    (h : Derives.Consistent reduct_theory []) :
    Derives.Consistent binary_union_operator_theory [] :=
  BinaryUnion.consistent (base_consistent h)

/-! ## 后继完整依赖树 -/

/-- 后继完整依赖树对闭公式给出的组合编译。 -/
def successor_compile_formula (φ : SetFormula) : SetFormula :=
  base_compile_formula
    (SuccessorChain.compile_formula φ)

/-- 后继函数扩张中的任意 checked 闭证明可沿完整依赖树翻译到还原理论。 -/
theorem successor_derives
    {φ : SetFormula}
    (h :
      Derives successor_operator_theory [] φ) :
    Derives reduct_theory []
      (successor_compile_formula φ) := by
  simpa [successor_compile_formula] using
    base_derives (SuccessorChain.derives h)

/-- 后继函数扩张中的 checked 矛盾沿完整依赖树回传到还原理论。 -/
theorem successor_derives_falsum
    (h :
      Derives successor_operator_theory []
        Formula.falsum) :
    Derives reduct_theory [] Formula.falsum := by
  simpa [successor_compile_formula,
    base_compile_formula,
    SuccessorChain.compile_formula,
    FunctionGraphElimination.formula] using
    successor_derives h

/-- 还原理论一致时，完整后继定义链保持 checked 一致。 -/
theorem successor_consistent
    (h : Derives.Consistent reduct_theory []) :
    Derives.Consistent successor_operator_theory [] :=
  SuccessorChain.consistent (base_consistent h)

end BinaryUnionChain
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
