import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Singleton
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.UnorderedPair
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.OrderedPair

/-!
# 配对函数定义链的证明级消去

本模块首次实际组合两个独立函数图插件：

`singleton_operator_theory → pairing_operator_theory → pairing_theory`。

复合公式编译与任意 checked 闭证明翻译均显式暴露；矛盾与一致性只是其特例。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace PairingChain

open Nonlogical.BasicSetTheory

/-! ## 单点集与无序对组合 -/

/-- 单点集与无序对两层消去对闭公式给出的组合编译。 -/
def compile_formula (φ : SetFormula) : SetFormula :=
  formula UnorderedPair.data
    (formula Singleton.data φ)

/-- 单点集函数扩张中的任意 checked 闭证明可翻译到配对存在理论。 -/
theorem derives
    {φ : SetFormula}
    (h :
      Derives singleton_operator_theory [] φ) :
    Derives pairing_theory [] (compile_formula φ) := by
  simpa [compile_formula] using
    Singleton.theory_presentation.derives_comp
      UnorderedPair.theory_presentation
      SetSort.set SetSort.set
      (fun _ hφ => hφ) h

/-- 单点集与无序对两个函数定义可连续回传 checked 矛盾。 -/
theorem derives_falsum
    (h :
    Derives singleton_operator_theory []
        Formula.falsum) :
    Derives pairing_theory []
      Formula.falsum := by
  simpa [compile_formula,
    FunctionGraphElimination.formula] using
    derives h

/-- 配对存在理论的一致性连续提升到单点集函数扩张。 -/
theorem consistent
    (h :
      Derives.Consistent pairing_theory []) :
    Derives.Consistent
      singleton_operator_theory [] :=
  Singleton.theory_presentation.consistent_comp
    UnorderedPair.theory_presentation
    SetSort.set SetSort.set
    (fun _ hφ => hφ) h

/-! ## 有序对完整依赖链 -/

/-- 有序对、单点集与无序对三层消去对闭公式给出的组合编译。 -/
def ordered_compile_formula (φ : SetFormula) : SetFormula :=
  compile_formula (formula OrderedPair.data φ)

/-- 有序对函数扩张中的任意 checked 闭证明可翻译到配对存在理论。 -/
theorem ordered_derives
    {φ : SetFormula}
    (h :
      Derives ordered_pair_operator_theory [] φ) :
    Derives pairing_theory []
      (ordered_compile_formula φ) := by
  simpa [ordered_compile_formula] using
    derives (OrderedPair.derives h)

/-- 有序对函数扩张中的 checked 矛盾连续回传到配对存在理论。 -/
theorem ordered_derives_falsum
    (h :
      Derives ordered_pair_operator_theory []
        Formula.falsum) :
    Derives pairing_theory [] Formula.falsum := by
  simpa [ordered_compile_formula, compile_formula,
    FunctionGraphElimination.formula] using
    ordered_derives h

/-- 配对存在理论一致时，整条有序对定义链保持 checked 一致。 -/
theorem ordered_consistent
    (h : Derives.Consistent pairing_theory []) :
    Derives.Consistent ordered_pair_operator_theory [] :=
  OrderedPair.consistent (consistent h)

end PairingChain
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
