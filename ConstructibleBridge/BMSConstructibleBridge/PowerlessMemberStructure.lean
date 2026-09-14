import BMSConstructibleBridge.PowerlessEvaluationAtoms

/-!
# 非空集合的实际成员结构

载体直接取原模型中 A 的成员，不要求 A 有数值满呈现。
非空前提仅用于上游一阶结构接口；空域算子已在独立接口处理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberStructure

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def type_l (A : carrier_l ℳ) := {x : carrier_l ℳ // member_l ℳ x A}

def structure_l (A : carrier_l ℳ) (hA : ∃ a, member_l ℳ a A) : FirstOrder.Structure.{0, 0, 0, u} ℒ where
  Carrier _ := type_l A
  nonempty _ := hA.elim fun a ha => ⟨⟨a, ha⟩⟩
  funcInterp f := nomatch f
  relInterp
    | .membership, .cons x (.cons y .nil) => member_l ℳ x.val y.val

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberStructure
