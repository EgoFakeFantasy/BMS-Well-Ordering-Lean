import BMSConstructibleBridge.SecondOrderPairObjects

/-!
# 图商中的函数对象规格

函数本身是一个图商对象，其成员必须恰为有序对；定义域上的输出存在唯一。
不能仅给出宿主函数并将其称为模型内的集合函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionObjects

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderQuotient

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def value_l (hℳ : Theory.Models ℳ theory_m) (f x y : type_l hℳ) : Prop :=
  ∃ p, mem_l hℳ p f ∧ SecondOrderPairObjects.ordered_l hℳ x y p

def map_l (hℳ : Theory.Models ℳ theory_m) (f a b : type_l hℳ) : Prop :=
  (∀ p, mem_l hℳ p f → ∃ x y, mem_l hℳ x a ∧ mem_l hℳ y b ∧
    SecondOrderPairObjects.ordered_l hℳ x y p) ∧
  ∀ x, mem_l hℳ x a → ∃! y, mem_l hℳ y b ∧ value_l hℳ f x y

def injective_l (hℳ : Theory.Models ℳ theory_m) (f : type_l hℳ) : Prop :=
  ∀ x z y, value_l hℳ f x y → value_l hℳ f z y → x = z

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionObjects
