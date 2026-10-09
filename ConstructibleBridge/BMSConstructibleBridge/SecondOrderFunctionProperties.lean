import BMSConstructibleBridge.SecondOrderFunctionObjects

/-! # 原商集合函数的坐标界及无条件值唯一性

先由图中有序对的坐标唯一性获得定义域、陪域成员证据，再调用映射
规格中的局部唯一性。不要求图商满足完整无幂集集合论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionProperties

open Logic FirstOrder SecondOrderQuotient SecondOrderFunctionObjects

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem value_mem_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {f a b x y : type_l hℳ}
    (hf : map_l hℳ f a b) (hxy : value_l hℳ f x y) : mem_l hℳ x a ∧ mem_l hℳ y b := by
  obtain ⟨p, hp, hPair⟩ := hxy
  obtain ⟨x', y', hx', hy', hPair'⟩ := hf.1 p hp
  obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hPair hPair').mp rfl
  exact ⟨hx', hy'⟩

theorem value_unique_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {f a b x y z : type_l hℳ}
    (hf : map_l hℳ f a b) (hy : value_l hℳ f x y) (hz : value_l hℳ f x z) : y = z := by
  have hxy := value_mem_l hℳ hf hy
  have hxz := value_mem_l hℳ hf hz
  obtain ⟨w, _, hUnique⟩ := hf.2 x hxy.1
  exact (hUnique y ⟨hxy.2, hy⟩).trans (hUnique z ⟨hxz.2, hz⟩).symm

#print axioms value_unique_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionProperties
