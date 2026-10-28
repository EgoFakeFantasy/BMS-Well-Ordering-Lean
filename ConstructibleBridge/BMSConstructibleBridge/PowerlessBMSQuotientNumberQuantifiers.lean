import BMSConstructibleBridge.PowerlessBMSQuotientCoding

/-! # 纯集合内部 ω 量词的逐数回读

使用全部模型数的实际数码双射，不使用宿主 Nat 枚举，也不抽取选择函数。
这些命题接口供纯公式语义的组合证明使用；本身不新增对象理论公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientNumberQuantifiers

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem forall_l (C : source_coding_l hℳ) (P : SecondOrderQuotient.type_l hℳ → Prop) :
    (∀ x, SecondOrderQuotient.mem_l hℳ x C.omega → P x) ↔
      ∀ n : SecondOrderModel.num_l ℳ, P (numberCode_l C n).val := by
  constructor
  · intro h n
    exact h (numberCode_l C n).val (numberCode_l C n).property
  · intro h x hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨x, hx⟩
    have hn' : (numberCode_l C n).val = x := congrArg Subtype.val hn
    exact hn' ▸ h n

theorem exists_l (C : source_coding_l hℳ) (P : SecondOrderQuotient.type_l hℳ → Prop) :
    (∃ x, SecondOrderQuotient.mem_l hℳ x C.omega ∧ P x) ↔
      ∃ n : SecondOrderModel.num_l ℳ, P (numberCode_l C n).val := by
  constructor
  · rintro ⟨x, hx, hP⟩
    obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨x, hx⟩
    have hn' : (numberCode_l C n).val = x := congrArg Subtype.val hn
    exact ⟨n, hn'.symm ▸ hP⟩
  · rintro ⟨n, hP⟩
    exact ⟨(numberCode_l C n).val, (numberCode_l C n).property, hP⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientNumberQuantifiers
