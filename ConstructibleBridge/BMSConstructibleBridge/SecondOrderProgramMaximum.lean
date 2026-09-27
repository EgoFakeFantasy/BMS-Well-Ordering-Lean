import BMSConstructibleBridge.SecondOrderProgramSubtraction
import BMSConstructibleBridge.SecondOrderProgramConditional

/-!
# 内部最大值的原程序

以已验截断减法判别两数的大小，再使用原条件选择器读取相应输入坐标。
比较不调用宿主类型的可判定性；标准求值和全部内部输入的原图规格分别证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMaximum

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramSubtraction
open SecondOrderProgramConditional
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 差值为零时选右值，否则选左值；测试也是显式原程序。 -/
def max_m : code_m := branch_m sub_m .left .right

/-- 标准配对码上的精确最大值。 -/
theorem max_eval_l (a b : Nat) : eval_l max_m (Nat.pair a b) = max a b := by
  rw [max_m, branch_eval_l, sub_eval_l]
  simp only [eval_l, Nat.unpair_pair, Nat.sub_eq_zero_iff_le]
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

/-- 原最大值程序在任意模型内部线序中的完整规格。 -/
theorem max_rel_l (hℳ : Theory.Models ℳ theory_m) {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m max_m) M) (a b y : num_l ℳ) :
    letI := order_l hℳ
    relation_l M (value_l a b) y ↔ max a b = y := by
  letI := order_l hℳ
  obtain ⟨D, hDf, hD⟩ := graph_total_l hℳ sub_m
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  rw [branch_rel_l hℳ sub_m .left .right hD hL hR hM]
  simp only [left_rel_l hℳ hL, right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l]
  constructor
  · rintro (⟨h, rfl⟩ | ⟨k, hk, h, rfl⟩)
    · exact max_eq_right ((sub_zero_iff_l hℳ hD a b).mp h)
    · have hab : ¬a ≤ b := fun hab => hk (function_value_unique_l hDf h
          ((sub_zero_iff_l hℳ hD a b).mpr hab))
      exact max_eq_left (le_of_not_ge hab)
  · intro hy
    by_cases hab : a ≤ b
    · exact Or.inl ⟨(sub_zero_iff_l hℳ hD a b).mpr hab, (max_eq_right hab).symm.trans hy⟩
    · obtain ⟨k, hk, _⟩ := hDf (value_l a b)
      have hk0 : k ≠ zero_l ℳ := fun h => hab ((sub_zero_iff_l hℳ hD a b).mp (h ▸ hk))
      exact Or.inr ⟨k, hk0, hk, (max_eq_left (le_of_not_ge hab)).symm.trans hy⟩

#print axioms max_m
#print axioms max_eval_l
#print axioms max_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMaximum
