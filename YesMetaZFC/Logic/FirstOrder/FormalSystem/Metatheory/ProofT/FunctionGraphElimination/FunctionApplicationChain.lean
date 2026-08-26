import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.FunctionApplication
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.CartesianProduct
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.OrderedPair
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.BinaryUnion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.PowerSet
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Singleton
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Union
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.UnorderedPair

/-!
# 函数求值背景的证明级函数图消去

本模块把函数求值理论作为一个整体连续编译，而不逐条复制其关系定义公理。
消去顺序为：

`application → cartesianProduct → orderedPair → binaryUnion → powerSet →
singleton → union → unorderedPair`。

每一步的目标理论都是图理论与上一层全部公理编译像的联合，因此依赖当前函数
符号的任意闭公理都会同步变换。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace FunctionApplicationChain

open Nonlogical.BasicSetTheory

set_option autoImplicit false

private theorem set_sort_unique
    (sort : SetSort) :
    sort = SetSort.set := by
  cases sort
  rfl

/-! ## 整理论逐层编译 -/

/-- 消去求值符号后的映射谓词理论。 -/
def application_lift :
    TheoryPresentation FunctionApplication.data :=
  FunctionApplication.theory_presentation

/-- 对整个映射谓词理论消去笛卡尔积函数。 -/
def cartesian_lift :
    TheoryPresentation CartesianProduct.data :=
  CartesianProduct.graph_presentation.compile_theory
    application_lift.graph.theory
    application_lift.graph.theory_sentence
    set_sort_unique

/-- 对上一层全部编译公理消去有序对函数。 -/
def ordered_lift :
    TheoryPresentation OrderedPair.data :=
  OrderedPair.graph_presentation.compile_theory
    cartesian_lift.graph.theory
    cartesian_lift.graph.theory_sentence
    set_sort_unique

/-- 对上一层全部编译公理消去二元并函数。 -/
def binary_lift :
    TheoryPresentation BinaryUnion.data :=
  BinaryUnion.graph_presentation.compile_theory
    ordered_lift.graph.theory
    ordered_lift.graph.theory_sentence
    set_sort_unique

/-- 对上一层全部编译公理消去幂集函数。 -/
def power_lift :
    TheoryPresentation PowerSet.data :=
  PowerSet.graph_presentation.compile_theory
    binary_lift.graph.theory
    binary_lift.graph.theory_sentence
    set_sort_unique

/-- 对上一层全部编译公理消去单点集函数。 -/
def singleton_lift :
    TheoryPresentation Singleton.data :=
  Singleton.graph_presentation.compile_theory
    power_lift.graph.theory
    power_lift.graph.theory_sentence
    set_sort_unique

/-- 对上一层全部编译公理消去一元并函数。 -/
def union_lift :
    TheoryPresentation Union.data :=
  Union.graph_presentation.compile_theory
    singleton_lift.graph.theory
    singleton_lift.graph.theory_sentence
    set_sort_unique

/-- 对上一层全部编译公理消去无序对函数。 -/
def pair_lift :
    TheoryPresentation UnorderedPair.data :=
  UnorderedPair.graph_presentation.compile_theory
    union_lift.graph.theory
    union_lift.graph.theory_sentence
    set_sort_unique

/-- 八个函数符号全部消去后的关系化函数求值背景。 -/
def reduct_theory : SetTheory :=
  pair_lift.graph.theory

/-! ## 任意公式的组合编译 -/

/-- 八层函数图消去对闭公式给出的组合编译。 -/
def compile_formula (φ : SetFormula) : SetFormula :=
  formula UnorderedPair.data
    (formula Union.data
      (formula Singleton.data
        (formula PowerSet.data
          (formula BinaryUnion.data
            (formula OrderedPair.data
              (formula CartesianProduct.data
                (formula FunctionApplication.data φ)))))))

/-- 函数求值背景中的任意 checked 闭证明可逐层翻译到关系化理论。 -/
theorem derives
    {φ : SetFormula}
    (h : Derives function_application_theory [] φ) :
    Derives reduct_theory [] (compile_formula φ) := by
  have hApplication :=
    application_lift.derives SetSort.set h
  have hCartesian :=
    cartesian_lift.derives SetSort.set hApplication
  have hOrdered :=
    ordered_lift.derives SetSort.set hCartesian
  have hBinary :=
    binary_lift.derives SetSort.set hOrdered
  have hPower :=
    power_lift.derives SetSort.set hBinary
  have hSingleton :=
    singleton_lift.derives SetSort.set hPower
  have hUnion :=
    union_lift.derives SetSort.set hSingleton
  have hPair :=
    pair_lift.derives SetSort.set hUnion
  simpa [compile_formula, reduct_theory] using hPair

/-! ## 证明与一致性回传 -/

/--
函数求值背景中的 checked 矛盾，经八层整理论编译回传到关系化目标理论。
-/
theorem derives_falsum
    (h :
      Derives function_application_theory []
        Formula.falsum) :
    Derives reduct_theory []
      Formula.falsum := by
  simpa [compile_formula, FunctionGraphElimination.formula] using
    derives (φ := Formula.falsum) h

/--
关系化目标理论一致时，原函数求值背景保持 checked 一致。
-/
theorem consistent
    (h :
      Derives.Consistent reduct_theory []) :
    Derives.Consistent
      function_application_theory [] := by
  intro hSource
  exact h (derives_falsum hSource)

end FunctionApplicationChain
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
