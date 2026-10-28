import BMSConstructibleBridge.SecondOrderLegacyAssignmentUpdate
import BMSConstructibleBridge.PowerlessLegacyAssignmentSyntax
import BMSConstructibleBridge.SecondOrderFunctionUpdate

/-! # 原商更新图与前插赋值的完整连接

只消费给定更新图的实际取值方程。全部内部数字槽和全部原商输出
均被覆盖，不预供图的 Class 成员资格。环境枚举的函数性识别新槽
输出；数码单射性识别原槽，不假定内部自然数外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentRawUpdateReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open PowerlessLegacyAssignmentSyntax (link_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem point_l (K : source_coding_l hℳ) {f g x : type_l hℳ}
    (l : SecondOrderModel.num_l ℳ)
    (hUpdate : PowerlessAssignmentUpdate.update_l (ℳ := 𝒱) f (numberCode_l K l).val x g)
    (i : SecondOrderModel.num_l ℳ) (y : type_l hℳ) :
    value_l (ℳ := 𝒱) g (numberCode_l K i).val y ↔
      (i = l ∧ y = x) ∨ i ≠ l ∧ value_l (ℳ := 𝒱) f (numberCode_l K i).val y := by
  have hNum : (numberCode_l K i).val = (numberCode_l K l).val ↔ i = l :=
    ⟨fun h => numberCode_injective_l K (Subtype.ext h), fun h => h ▸ rfl⟩
  exact (hUpdate _ y).trans
    (or_congr (and_congr hNum Iff.rfl) (and_congr (not_congr hNum) Iff.rfl))

theorem prepend_l (K : source_coding_l hℳ) {A f g x U : type_l hℳ}
    {E : SecondOrderModel.set_l ℳ} {c l d v L z : SecondOrderModel.num_l ℳ}
    (hd : SecondOrderAssignmentSyntax.extension_l E c l d v) (hLength : SecondOrderOrder.lt_l l L)
    (hUpdate : PowerlessAssignmentUpdate.update_l (ℳ := 𝒱) f (numberCode_l K l).val x g)
    (hLink : link_l K E c l L z U f)
    (hU : map_l (ℳ := 𝒱) U K.omega A)
    (hx : value_l (ℳ := 𝒱) U (numberCode_l K v).val x) :
    link_l K E d (SecondOrderModel.succ_l l) L z U g := by
  intro i y
  rw [point_l K l hUpdate i y]
  classical
  by_cases hi : i = l
  · subst i
    have hPad (j : SecondOrderModel.num_l ℳ) :
        SecondOrderLegacyAssignmentPadding.padded_l E d (SecondOrderModel.succ_l l) L z l j ↔ j = v := by
      simp only [SecondOrderLegacyAssignmentPadding.prepend_l hℳ hd hLength,
        eq_self, true_and, ne_eq, not_true_eq_false, false_and, or_false]
    simp only [eq_self, true_and, ne_eq, not_true_eq_false, false_and, or_false, hPad, exists_eq_left]
    exact ⟨fun h => h ▸ hx, fun h => SecondOrderFunctionProperties.value_unique_l hℳ hU h hx⟩
  · have hPad (j : SecondOrderModel.num_l ℳ) :
        SecondOrderLegacyAssignmentPadding.padded_l E d (SecondOrderModel.succ_l l) L z i j ↔
          SecondOrderLegacyAssignmentPadding.padded_l E c l L z i j := by
      simp only [SecondOrderLegacyAssignmentPadding.prepend_l hℳ hd hLength,
        hi, false_and, ne_eq, not_false_eq_true, true_and, false_or]
    simp only [hi, false_and, ne_eq, not_false_eq_true, true_and, false_or, hPad]
    exact hLink i y

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentRawUpdateReading
