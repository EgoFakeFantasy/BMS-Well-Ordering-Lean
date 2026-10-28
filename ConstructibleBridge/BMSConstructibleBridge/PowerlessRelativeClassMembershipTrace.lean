import BMSConstructibleBridge.SecondOrderMembershipBoolean
import BMSConstructibleBridge.PowerlessRelativeClassNumericTrace

/-! # 任意实数的内部有限数字成员表属于相对类

实数 V 及其无限零一总图均可在类外。给定任意内部数 n，其有限限制
由实际 Seq(ω) 规格落入类；结论不收集所有前段，不声称无限总图已类化，
也不将此直接成员表冒充旧二维合法性检查器。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassMembershipTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l (K : source_coding_l hℳ) {ω : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)
    (V : SecondOrderModel.set_l ℳ) (n : SecondOrderModel.num_l ℳ) :
    ∃ f : type_l hℳ B,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        f.val (numberCode_l K n).val K.omega ∧
      ∀ i j, value_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        f.val (numberCode_l K i).val (numberCode_l K j).val ↔
          SecondOrderOrder.lt_l i n ∧
            ((SecondOrderModel.mem_l i V ∧
                j = SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)) ∨
              (¬SecondOrderModel.mem_l i V ∧ j = SecondOrderModel.zero_l ℳ)) := by
  obtain ⟨E, hE, hSpec⟩ := SecondOrderMembershipBoolean.exists_l hℳ V
  obtain ⟨f, hf, hRead⟩ := PowerlessRelativeClassNumericTrace.exists_l K hω hωEq hE n
  exact ⟨f, hf, fun i j => (hRead i j).trans (and_congr Iff.rfl (hSpec i j))⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassMembershipTrace
