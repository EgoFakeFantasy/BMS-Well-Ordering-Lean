import BMSConstructibleBridge.PowerlessArithmetic
import BMSConstructibleBridge.PowerlessBMSQuotientCoding
import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor
import BMSConstructibleBridge.SecondOrderPureTransfer

/-!
# 从根码 quotient 到 Z₂ 候选实数的纯矩阵迁移接口

目标模型的每个二阶对象已有 quotient 子集代表。这里把该代表关系接到原有
`correspondence_l`，并用明确的零、后继、加法、乘法保运算等式填充算术字段。
本文件只组装已给出的证书，不构造加法/乘法，也不推出任何源模型存在性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientPureTransfer

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hM

/-- 把 quotient 的 ω、指定零对象及运算证书解释成二阶算术签名。 -/
def arithmeticStructure_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (F : PowerlessArithmetic.operations_l (ℳ := quotient_l) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val) :
    FirstOrder.Structure.{0, 0, 0, u} signature_m :=
  PowerlessArithmetic.structure_l
    (PowerlessBMSQuotientSuccessor.zero_l C)
    (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).property
    F

/-- 每个目标二阶对象有一个关系对应的 quotient 子集代表。 -/
theorem setRel_total_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (X : SecondOrderModel.set_l M) :
    ∃ A : PowerlessArithmetic.set_l (ℳ := quotient_l) C.omega,
      PowerlessBMSQuotientCoding.setRel_l C A X :=
  PowerlessBMSQuotientCoding.representative_exists_l C X

/-- 已给出算术运算保对应等式时，构造真实的纯矩阵迁移记录。

加法和乘法保对应仍是显式前提；本定理不把这些缺失证明包装成已构造运算。 -/
noncomputable def correspondence_of_operations_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (F : PowerlessArithmetic.operations_l (ℳ := quotient_l) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val)
    (hSucc : ∀ a,
      PowerlessBMSQuotientCoding.numberEquiv_l C (F.succ_l a) =
        SecondOrderModel.succ_l (PowerlessBMSQuotientCoding.numberEquiv_l C a))
    (hAdd : ∀ a b,
      PowerlessBMSQuotientCoding.numberEquiv_l C (F.add_l a b) =
        SecondOrderModel.add_l (PowerlessBMSQuotientCoding.numberEquiv_l C a)
          (PowerlessBMSQuotientCoding.numberEquiv_l C b))
    (hMul : ∀ a b,
      PowerlessBMSQuotientCoding.numberEquiv_l C (F.mul_l a b) =
        SecondOrderModel.mul_l (PowerlessBMSQuotientCoding.numberEquiv_l C a)
          (PowerlessBMSQuotientCoding.numberEquiv_l C b)) :
    SecondOrderPureTransfer.correspondence_l
      (M := arithmeticStructure_l C F) (N := M) where
  numberEquiv_l := PowerlessBMSQuotientCoding.numberEquiv_l C
  setRel_l := fun A X => PowerlessBMSQuotientCoding.setRel_l C A X
  zero_l := by
    change PowerlessBMSQuotientCoding.numberEquiv_l C
        (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)) =
      SecondOrderModel.zero_l M
    exact Equiv.apply_symm_apply (PowerlessBMSQuotientCoding.numberEquiv_l C)
      (SecondOrderModel.zero_l M)
  succ_l := hSucc
  add_l := hAdd
  mul_l := hMul
  member_iff_l := by
    intro a A X hAX
    change ThirdOrderSemantics.member_l (ℳ := quotient_l) a.val A.val ↔
      SecondOrderModel.mem_l (PowerlessBMSQuotientCoding.numberEquiv_l C a) X
    have hCode : PowerlessBMSQuotientCoding.numberCode_l C
        (PowerlessBMSQuotientCoding.numberEquiv_l C a) = a :=
      Equiv.symm_apply_apply (PowerlessBMSQuotientCoding.numberEquiv_l C) a
    have h := hAX (PowerlessBMSQuotientCoding.numberEquiv_l C a)
    rw [hCode] at h
    exact h

#print axioms arithmeticStructure_l
#print axioms setRel_total_l
#print axioms correspondence_of_operations_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientPureTransfer
