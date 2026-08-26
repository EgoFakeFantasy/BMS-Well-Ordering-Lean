import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.CartesianProductBaseChain

/-!
# 笛卡尔积分离公理的证明级函数图消去

本模块让笛卡尔积分离公理随基础函数依赖树逐层编译。每一层都把上一层的闭公理
替换为其函数图编译像，并复用对应基础理论的 `TheoryPresentation`：

`orderedPair → binaryUnion → powerSet → singleton → union → unorderedPair`。

最终只保留一个纯关系语言的分离实例，以及幂集、配对、并集三个存在公理理论。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace CartesianProductChain

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-! ## 分离公理的逐层编译像 -/

def sep_ordered : SetFormula :=
  formula OrderedPair.data
    cartesian_product_separation_axiom

def sep_binary : SetFormula :=
  formula BinaryUnion.data sep_ordered

def sep_power : SetFormula :=
  formula PowerSet.data sep_binary

def sep_singleton : SetFormula :=
  formula Singleton.data sep_power

def sep_union : SetFormula :=
  formula Union.data sep_singleton

def sep_pair : SetFormula :=
  formula UnorderedPair.data sep_union

private theorem sep_ordered_sentence :
    Formula.Sentence sep_ordered := by
  exact formula_sentence_of_single_sort
    OrderedPair.data
    (by intro sort; cases sort; rfl)
    (cartesian_product_theory_sentence
      (Or.inl rfl))

private theorem sep_binary_sentence :
    Formula.Sentence sep_binary := by
  exact formula_sentence_of_single_sort
    BinaryUnion.data
    (by intro sort; cases sort; rfl)
    sep_ordered_sentence

private theorem sep_power_sentence :
    Formula.Sentence sep_power := by
  exact formula_sentence_of_single_sort
    PowerSet.data
    (by intro sort; cases sort; rfl)
    sep_binary_sentence

private theorem sep_singleton_sentence :
    Formula.Sentence sep_singleton := by
  exact formula_sentence_of_single_sort
    Singleton.data
    (by intro sort; cases sort; rfl)
    sep_power_sentence

private theorem sep_union_sentence :
    Formula.Sentence sep_union := by
  exact formula_sentence_of_single_sort
    Union.data
    (by intro sort; cases sort; rfl)
    sep_singleton_sentence

private theorem sep_pair_sentence :
    Formula.Sentence sep_pair := by
  exact formula_sentence_of_single_sort
    UnorderedPair.data
    (by intro sort; cases sort; rfl)
    sep_union_sentence

/-! ## 理论级逐层替换 -/

def ordered_lift :
    TheoryPresentation OrderedPair.data :=
  CartesianProductBaseChain.base_lift.insert_compiled
    cartesian_product_separation_axiom
    sep_ordered_sentence

def binary_lift :
    TheoryPresentation BinaryUnion.data :=
  CartesianProductBaseChain.binary_lift.insert_compiled
    sep_ordered sep_binary_sentence

def power_lift :
    TheoryPresentation PowerSet.data :=
  CartesianProductBaseChain.power_lift.insert_compiled
    sep_binary sep_power_sentence

def singleton_lift :
    TheoryPresentation Singleton.data :=
  CartesianProductBaseChain.singleton_lift.insert_compiled
    sep_power sep_singleton_sentence

def union_lift :
    TheoryPresentation Union.data :=
  CartesianProductBaseChain.union_lift.insert_compiled
    sep_singleton sep_union_sentence

def pair_lift :
    TheoryPresentation UnorderedPair.data :=
  CartesianProductBaseChain.pair_lift.insert_compiled
    sep_union sep_pair_sentence

/-- 全部函数图消去后得到的纯关系分离理论。 -/
def reduct_theory : SetTheory :=
  Theory.insert sep_pair
    CartesianProductBaseChain.zf_reduct_theory

/-! ## 任意公式的组合编译 -/

/-- 笛卡尔积分离链对闭公式给出的组合编译。 -/
def compile_formula (φ : SetFormula) : SetFormula :=
  formula UnorderedPair.data
    (formula Union.data
      (formula Singleton.data
        (formula PowerSet.data
          (formula BinaryUnion.data
            (formula OrderedPair.data φ)))))

/-- 笛卡尔积分离理论中的任意 checked 闭证明可翻译到纯关系理论。 -/
theorem derives
    {φ : SetFormula}
    (h : Derives cartesian_product_theory [] φ) :
    Derives reduct_theory [] (compile_formula φ) := by
  change Derives ordered_lift.source [] φ at h
  have hOrdered :=
    ordered_lift.derives SetSort.set h
  change Derives binary_lift.source []
    (formula OrderedPair.data φ) at hOrdered
  have hBinary :=
    binary_lift.derives SetSort.set hOrdered
  change Derives power_lift.source []
    (formula BinaryUnion.data
      (formula OrderedPair.data φ)) at hBinary
  have hPower :=
    power_lift.derives SetSort.set hBinary
  change Derives singleton_lift.source []
    (formula PowerSet.data
      (formula BinaryUnion.data
        (formula OrderedPair.data φ))) at hPower
  have hSingleton :=
    singleton_lift.derives SetSort.set hPower
  change Derives union_lift.source []
    (formula Singleton.data
      (formula PowerSet.data
        (formula BinaryUnion.data
          (formula OrderedPair.data φ)))) at hSingleton
  have hUnion :=
    union_lift.derives SetSort.set hSingleton
  change Derives pair_lift.source []
    (formula Union.data
      (formula Singleton.data
        (formula PowerSet.data
          (formula BinaryUnion.data
            (formula OrderedPair.data φ))))) at hUnion
  have hPair :=
    pair_lift.derives SetSort.set hUnion
  change Derives reduct_theory []
    (formula UnorderedPair.data
      (formula Union.data
        (formula Singleton.data
          (formula PowerSet.data
            (formula BinaryUnion.data
              (formula OrderedPair.data φ)))))) at hPair
  exact hPair

/--
笛卡尔积存在理论中的 checked 矛盾，沿分离公理与基础函数依赖树同步编译，
最终回传到纯关系分离理论。
-/
theorem derives_falsum
    (h :
      Derives cartesian_product_theory []
        Formula.falsum) :
    Derives reduct_theory []
      Formula.falsum := by
  simpa [compile_formula, FunctionGraphElimination.formula] using
    derives h

/-- 纯关系分离理论一致时，笛卡尔积存在理论保持 checked 一致。 -/
theorem consistent
    (h : Derives.Consistent reduct_theory []) :
    Derives.Consistent cartesian_product_theory [] := by
  intro hProduct
  exact h (derives_falsum hProduct)

/-- 笛卡尔积函数符号扩张中的矛盾同样回传到纯关系分离理论。 -/
theorem operator_derives_falsum
    (h :
      Derives cartesian_product_operator_theory []
        Formula.falsum) :
    Derives reduct_theory []
      Formula.falsum :=
  derives_falsum
    (CartesianProduct.derives_falsum h)

/-- 纯关系分离理论一致时，笛卡尔积函数符号扩张保持 checked 一致。 -/
theorem operator_consistent
    (h : Derives.Consistent reduct_theory []) :
    Derives.Consistent
      cartesian_product_operator_theory [] :=
  CartesianProduct.consistent
    (consistent h)

end CartesianProductChain
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
