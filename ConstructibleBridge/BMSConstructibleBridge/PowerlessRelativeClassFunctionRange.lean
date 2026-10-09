import BMSConstructibleBridge.PowerlessRelativeLimitFunctionRange
import BMSConstructibleBridge.PowerlessRelativeClassLimitParameterBounds

/-! # 实际 Class 函数图的精确 raw 值域

原 raw 陪域无需是 Class。实际 Class 定义域和图进入共同非零极限层，
既有同层值域构造给精确全 raw 值域；不是 Collection 或见证选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionRange

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}

theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (A f : type_l hℳ B) {q : SecondOrderQuotient.type_l hℳ}
    (hf : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val A.val q) :
    ∃ R : type_l hℳ B, ∀ y, mem_l hℳ y R.val ↔
      ∃ a, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val a y := by
  let η : Env (structure_l hℳ B hBase) [] [.set] := Env.empty.pushFree f
  obtain ⟨ξ, C, hLimit, hC, hAC, hParams⟩ :=
    PowerlessRelativeClassLimitParameterBounds.exists_l η A
  obtain ⟨R, hRC, hR⟩ := PowerlessRelativeLimitFunctionRange.exists_l
    hBase hLimit hC hAC (hParams .set .here) hf
  exact ⟨⟨R, ⟨ξ, C, hC, hRC⟩⟩, hR⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionRange
