import BMSConstructibleBridge.SecondOrderFunctionObjects

/-! # 原图商集合函数的定义域、值域与唯一性

直接使用有序对坐标唯一性及原 map 规格，不要求商满足 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionLaws

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderQuotient
open SecondOrderFunctionObjects

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  (hℳ : Theory.Models ℳ theory_m)

theorem value_mem_l {f a b x y : type_l hℳ} (hf : map_l hℳ f a b)
    (hxy : value_l hℳ f x y) : mem_l hℳ x a ∧ mem_l hℳ y b := by
  obtain ⟨p, hp, hxy⟩ := hxy
  obtain ⟨z, w, hz, hw, hzw⟩ := hf.1 p hp
  obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hzw).mp rfl
  exact ⟨hz, hw⟩

theorem value_unique_l {f a b x y z : type_l hℳ} (hf : map_l hℳ f a b)
    (hy : value_l hℳ f x y) (hz : value_l hℳ f x z) : y = z := by
  have hxy := value_mem_l hℳ hf hy
  have hxz := value_mem_l hℳ hf hz
  obtain ⟨w, _, hw⟩ := hf.2 x hxy.1
  exact (hw y ⟨hxy.2, hy⟩).trans (hw z ⟨hxz.2, hz⟩).symm

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionLaws
