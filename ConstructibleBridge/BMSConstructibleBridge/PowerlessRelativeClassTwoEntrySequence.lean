import BMSConstructibleBridge.PowerlessRelativeClassFunctionExtension

/-! # 类内两项序列的实际图

先在一元素定义域上形成常值图，再在下一个内部编号延拓。只使用实际
集合后继规格，不假设模型自然数标准，也不调用有限族的 Type 选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTwoEntrySequence

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {e one two X a b : type_l hℳ B}
    (he : PowerlessNatural.zero_l (ℳ := structure_l hℳ B hBase) e)
    (hone : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) e one)
    (htwo : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) one two)
    (ha : mem_l hℳ a.val X.val) (hb : mem_l hℳ b.val X.val) :
    ∃ g : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) g two X ∧
      value_l (ℳ := structure_l hℳ B hBase) g e a ∧ value_l (ℳ := structure_l hℳ B hBase) g one b := by
  have heOne : mem_l hℳ e.val one.val := (hone e).mpr (Or.inr rfl)
  have hOneNe : one ≠ e := by
    intro hEq
    exact he e (hEq ▸ heOne)
  have hOneNot : ¬mem_l hℳ one.val one.val := by
    intro h
    rcases (hone one).mp h with h | h
    · exact he one h
    · exact hOneNe h
  obtain ⟨f, hf, hRead⟩ := PowerlessRelativeClassFunctionExtension.constant_l (hBase := hBase) one X a ha
  obtain ⟨g, hg, hExtend⟩ := PowerlessRelativeClassFunctionExtension.exists_l (hBase := hBase)
    (c := one) (S := two) hf hOneNot hb htwo
  exact ⟨g, hg, (hExtend e a).mpr (Or.inl ((hRead e a).mpr ⟨heOne, rfl⟩)),
    (hExtend one b).mpr (Or.inr ⟨rfl, rfl⟩)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTwoEntrySequence
