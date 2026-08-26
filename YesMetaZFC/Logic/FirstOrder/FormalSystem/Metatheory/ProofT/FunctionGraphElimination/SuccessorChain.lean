import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Successor
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.BinaryUnion

/-!
# 后继定义链的证明级消去

本模块组合后继与二元并两个直接定义扩张：

`successor_operator_theory → binary_union_operator_theory → binary_union_base_theory`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace SuccessorChain

open Nonlogical.BasicSetTheory

/-! ## 任意公式的组合编译 -/

/-- 后继与二元并两层消去对闭公式给出的组合编译。 -/
def compile_formula (φ : SetFormula) : SetFormula :=
  formula BinaryUnion.data
    (formula Successor.data φ)

/-- 后继函数扩张中的任意 checked 闭证明可翻译到二元并基理论。 -/
theorem derives
    {φ : SetFormula}
    (h :
      Derives successor_operator_theory [] φ) :
    Derives binary_union_base_theory []
      (compile_formula φ) := by
  simpa [compile_formula] using
    Successor.theory_presentation.derives_comp
      BinaryUnion.theory_presentation
      SetSort.set SetSort.set
      (fun _ hφ => hφ) h

/-- 后继与二元并两个函数定义可连续回传 checked 矛盾。 -/
theorem derives_falsum
    (h :
      Derives successor_operator_theory []
        Formula.falsum) :
    Derives binary_union_base_theory []
      Formula.falsum := by
  simpa [compile_formula,
    FunctionGraphElimination.formula] using
    derives h

/-- 二元并基理论的一致性连续提升到后继函数扩张。 -/
theorem consistent
    (h :
      Derives.Consistent binary_union_base_theory []) :
    Derives.Consistent successor_operator_theory [] :=
  Successor.theory_presentation.consistent_comp
    BinaryUnion.theory_presentation
    SetSort.set SetSort.set
    (fun _ hφ => hφ) h

end SuccessorChain
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
