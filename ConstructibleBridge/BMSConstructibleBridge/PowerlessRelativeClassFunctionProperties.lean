import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 类内集合函数的坐标、值唯一性和定义域唯一性

只消费实际原商函数与类绝对性，不要求整类满足源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionProperties

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem value_mem_l {f D A x y : type_l hℳ B} (hf : map_l (ℳ := structure_l hℳ B hBase) f D A)
    (hxy : value_l (ℳ := structure_l hℳ B hBase) f x y) :
    mem_l hℳ x.val D.val ∧ mem_l hℳ y.val A.val :=
  SecondOrderFunctionProperties.value_mem_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f D A).mp hf)
    ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x y).mp hxy)

theorem value_unique_l {f D A x y z : type_l hℳ B} (hf : map_l (ℳ := structure_l hℳ B hBase) f D A)
    (hy : value_l (ℳ := structure_l hℳ B hBase) f x y)
    (hz : value_l (ℳ := structure_l hℳ B hBase) f x z) : y = z :=
  Subtype.ext (SecondOrderFunctionProperties.value_unique_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f D A).mp hf)
    ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x y).mp hy)
    ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x z).mp hz))

theorem domain_unique_l {f D E A C : type_l hℳ B}
    (hf : map_l (ℳ := structure_l hℳ B hBase) f D A)
    (hg : map_l (ℳ := structure_l hℳ B hBase) f E C) : D = E := by
  apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, _⟩ := hf.2 x hx
    exact (value_mem_l hg hy.2).1
  · intro hx
    obtain ⟨y, hy, _⟩ := hg.2 x hx
    exact (value_mem_l hf hy.2).1

#print axioms value_unique_l
#print axioms domain_unique_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionProperties
