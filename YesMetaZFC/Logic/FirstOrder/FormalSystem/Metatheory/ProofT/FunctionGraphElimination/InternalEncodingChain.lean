import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.FunctionApplication
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.RelationDomain
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Omega
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Successor
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.CartesianProduct
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.OrderedPair
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.BinaryIntersection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.BinaryUnion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.PowerSet
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Singleton
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Union
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.UnorderedPair

/-!
# 内部编码理论的证明级函数图消去

本模块参数化于任意闭句基础理论 `base`，直接作用于
`fs_internal_raw_theory base`。它连续消去仓库当前已经具备真实函数图实例的
十二类函数符号：

`application → domain → omega → successor → cartesianProduct → orderedPair →
binaryIntersection → binaryUnion → powerSet → singleton → union →
unorderedPair`。

尚无图实例的自然数递归运算、关系投影、值域等符号继续留在最终理论中；
这里不以抽象假设伪造它们的存在唯一性。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace InternalEncodingChain

open Nonlogical.BasicSetTheory

set_option autoImplicit false

private theorem set_sort_unique
    (sort : SetSort) :
    sort = SetSort.set := by
  cases sort
  rfl

variable
  (base : SetTheory)
  (hBase :
    ∀ {φ}, base φ → Formula.Sentence φ)

/-! ## 通用内部理论的逐层编译 -/

def application_lift :
    TheoryPresentation FunctionApplication.data :=
  FunctionApplication.graph_presentation.compile_theory
    (fs_internal_raw_theory base)
    (fs_internal_raw_theory_sentence
      (fun _ hφ => hBase hφ))
    set_sort_unique

def domain_lift :
    TheoryPresentation RelationDomain.data :=
  RelationDomain.graph_presentation.compile_theory
    (application_lift base hBase).graph.theory
    (application_lift base hBase).graph.theory_sentence
    set_sort_unique

def omega_lift :
    TheoryPresentation Omega.data :=
  Omega.graph_presentation.compile_theory
    (domain_lift base hBase).graph.theory
    (domain_lift base hBase).graph.theory_sentence
    set_sort_unique

def successor_lift :
    TheoryPresentation Successor.data :=
  Successor.graph_presentation.compile_theory
    (omega_lift base hBase).graph.theory
    (omega_lift base hBase).graph.theory_sentence
    set_sort_unique

def cartesian_lift :
    TheoryPresentation CartesianProduct.data :=
  CartesianProduct.graph_presentation.compile_theory
    (successor_lift base hBase).graph.theory
    (successor_lift base hBase).graph.theory_sentence
    set_sort_unique

def ordered_lift :
    TheoryPresentation OrderedPair.data :=
  OrderedPair.graph_presentation.compile_theory
    (cartesian_lift base hBase).graph.theory
    (cartesian_lift base hBase).graph.theory_sentence
    set_sort_unique

def intersection_lift :
    TheoryPresentation BinaryIntersection.data :=
  BinaryIntersection.graph_presentation.compile_theory
    (ordered_lift base hBase).graph.theory
    (ordered_lift base hBase).graph.theory_sentence
    set_sort_unique

def binary_lift :
    TheoryPresentation BinaryUnion.data :=
  BinaryUnion.graph_presentation.compile_theory
    (intersection_lift base hBase).graph.theory
    (intersection_lift base hBase).graph.theory_sentence
    set_sort_unique

def power_lift :
    TheoryPresentation PowerSet.data :=
  PowerSet.graph_presentation.compile_theory
    (binary_lift base hBase).graph.theory
    (binary_lift base hBase).graph.theory_sentence
    set_sort_unique

def singleton_lift :
    TheoryPresentation Singleton.data :=
  Singleton.graph_presentation.compile_theory
    (power_lift base hBase).graph.theory
    (power_lift base hBase).graph.theory_sentence
    set_sort_unique

def union_lift :
    TheoryPresentation Union.data :=
  Union.graph_presentation.compile_theory
    (singleton_lift base hBase).graph.theory
    (singleton_lift base hBase).graph.theory_sentence
    set_sort_unique

def pair_lift :
    TheoryPresentation UnorderedPair.data :=
  UnorderedPair.graph_presentation.compile_theory
    (union_lift base hBase).graph.theory
    (union_lift base hBase).graph.theory_sentence
    set_sort_unique

/-- 当前已有函数图实例全部应用后得到的内部关系化理论。 -/
def reduct_theory : SetTheory :=
  (pair_lift base hBase).graph.theory

/-! ## 任意公式的组合编译 -/

/-- 十二层内部编码函数图消去对闭公式给出的组合编译。 -/
def compile_formula (φ : SetFormula) : SetFormula :=
  formula UnorderedPair.data
    (formula Union.data
      (formula Singleton.data
        (formula PowerSet.data
          (formula BinaryUnion.data
            (formula BinaryIntersection.data
              (formula OrderedPair.data
                (formula CartesianProduct.data
                  (formula Successor.data
                    (formula Omega.data
                      (formula RelationDomain.data
                        (formula FunctionApplication.data φ)))))))))))

/-- 通用内部理论中的任意 checked 闭证明可逐层翻译到关系化理论。 -/
theorem derives
    {φ : SetFormula}
    (h :
      Derives (fs_internal_raw_theory base) [] φ) :
    Derives (reduct_theory base hBase) []
      (compile_formula φ) := by
  have hApplication :=
    (application_lift base hBase).derives
      SetSort.set h
  have hDomain :=
    (domain_lift base hBase).derives
      SetSort.set hApplication
  have hOmega :=
    (omega_lift base hBase).derives
      SetSort.set hDomain
  have hSuccessor :=
    (successor_lift base hBase).derives
      SetSort.set hOmega
  have hCartesian :=
    (cartesian_lift base hBase).derives
      SetSort.set hSuccessor
  have hOrdered :=
    (ordered_lift base hBase).derives
      SetSort.set hCartesian
  have hIntersection :=
    (intersection_lift base hBase).derives
      SetSort.set hOrdered
  have hBinary :=
    (binary_lift base hBase).derives
      SetSort.set hIntersection
  have hPower :=
    (power_lift base hBase).derives
      SetSort.set hBinary
  have hSingleton :=
    (singleton_lift base hBase).derives
      SetSort.set hPower
  have hUnion :=
    (union_lift base hBase).derives
      SetSort.set hSingleton
  have hPair :=
    (pair_lift base hBase).derives
      SetSort.set hUnion
  simpa [compile_formula, reduct_theory] using hPair

/-! ## 证明与一致性回传 -/

/--
通用 raw 内部理论中的 checked 矛盾，经十二层函数图编译回传到关系化理论。
-/
theorem derives_falsum
    (h :
      Derives (fs_internal_raw_theory base) []
        Formula.falsum) :
    Derives (reduct_theory base hBase) []
      Formula.falsum := by
  simpa [compile_formula, FunctionGraphElimination.formula] using
    derives base hBase (φ := Formula.falsum) h

/--
关系化目标理论一致时，原通用 raw 内部理论保持 checked 一致。
-/
theorem consistent
    (h :
      Derives.Consistent
        (reduct_theory base hBase) []) :
    Derives.Consistent
      (fs_internal_raw_theory base) [] := by
  intro hSource
  exact h (derives_falsum base hBase hSource)

end InternalEncodingChain
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
