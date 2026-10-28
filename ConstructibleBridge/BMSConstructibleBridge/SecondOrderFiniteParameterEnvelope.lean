import BMSConstructibleBridge.SecondOrderTransitiveSuperset
import BMSConstructibleBridge.SecondOrderPairObjects

/-! # 原 Z₂ 模型中有限参数的共同传递包

列表只索引一个外部固定的有限参数包，不是模型内部 ω 的外部枚举。
见证逐步在 Prop 中取得；不抽取参数到传递包的 Type 选择函数。
此包可用作临时辅助类的基底，不改变原相对层次的基底。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteParameterEnvelope

open Logic FirstOrder SecondOrderQuotient

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private theorem singleton_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (a : type_l hℳ) :
    ∃ B, mem_l hℳ a B ∧ ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B := by
  obtain ⟨A, rfl⟩ := surj_l hℳ a
  obtain ⟨T, hA, hT⟩ := SecondOrderTransitiveSuperset.exists_l hℳ A
  refine ⟨mk_l hℳ T, hA, ?_⟩
  intro x hx y hy
  obtain ⟨X, rfl⟩ := surj_l hℳ x
  obtain ⟨Y, rfl⟩ := surj_l hℳ y
  exact hT X Y hx hy

/-- 锚点及给定有限列表中的全部对象都是共同传递包的成员。 -/
theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (a : type_l hℳ) (S : List (type_l hℳ)) :
    ∃ B, (∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) ∧
      mem_l hℳ a B ∧ ∀ x ∈ S, mem_l hℳ x B := by
  induction S with
  | nil =>
      obtain ⟨B, ha, hB⟩ := singleton_l hℳ a
      exact ⟨B, hB, ha, by simp⟩
  | cons b S ih =>
      obtain ⟨B, _, ha, hS⟩ := ih
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.pair_exists_l hℳ b B
      obtain ⟨T, hpT, hT⟩ := singleton_l hℳ p
      have hBT : mem_l hℳ B T := hT p hpT B ((hp B).mpr (Or.inr rfl))
      refine ⟨T, hT, hT B hBT a ha, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hT p hpT x ((hp x).mpr (Or.inl rfl))
      · exact hT B hBT x (hS x hx)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteParameterEnvelope
