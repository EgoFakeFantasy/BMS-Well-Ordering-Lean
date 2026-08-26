import YesMetaZFC.Logic.FirstOrder.FormalSystem.FiniteSequenceConcatenation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy

/-!
# `ProofT` 的基础 `Delta0` 条件

本模块只收集不依赖具体 replay 的低层句法事实。函数图谓词本身是关系原子，
有限序列条件则是该原子与定义域自然数条件的合取；二者都不需要额外的对象理论
公理，也不需要把函数求值项改写成对象层存在量词。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 函数图谓词的 `Delta0` 句法证书。 -/
theorem function_formula_delta0
    (function : SetTerm) :
    Formula.IsDelta0 set_levy_bound
      (is_function_formula function) :=
  Formula.IsDelta0.rel
    RelationSymbol.isFunction
    [function]

/-- 有限序列条件的 `Delta0` 句法证书。 -/
theorem finite_sequence_condition_delta0
    (sequence : SetTerm) :
    Formula.IsDelta0 set_levy_bound
      (finite_sequence_condition sequence) := by
  simpa [finite_sequence_condition] using
    Formula.IsDelta0.conj
      (function_formula_delta0 sequence)
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [domₘ(sequence), ωₘ])

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
