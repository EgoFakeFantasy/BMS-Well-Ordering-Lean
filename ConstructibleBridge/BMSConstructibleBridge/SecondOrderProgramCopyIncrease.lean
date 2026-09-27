import BMSConstructibleBridge.SecondOrderProgramCallbackValue
import BMSConstructibleBridge.SecondOrderProgramSubtraction

/-!
# 原 copyBlock 的数值增量程序

原复制项的数值为 value + copyNumber * (lastValue - firstValue)，减法为截断减法。
输入 pair value (pair copyNumber (pair firstValue lastValue))，这里先处理两个可选项
都存在且 ascending 成功后的数值分支；Option 检查和上升谓词不能由本模块省略。
标准身份与全部内部数值上的真实编译图规格分别证明，不依赖数组高度或外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyIncrease

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramArithmetic
open SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramSubtraction (sub_m sub_eval_l)
open PrimitiveProgram (code_m eval_l graph_m add_m mul_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原末值减首值，方向不可交换。 -/
def difference_input_m : code_m := .comp (.pair .right .left) (.comp .right .right)

/-- 真实截断差值。 -/
def difference_m : code_m := .comp sub_m difference_input_m

/-- 同一复制次数乘原差值，不把复制次数误取为列号。 -/
def product_m : code_m := .comp mul_m (.pair (.comp .left .right) difference_m)

/-- 原值加复制增量。 -/
def increase_m : code_m := .comp add_m (.pair .left product_m)

/-- 标准端逐数值与原 copyBlock 数值正文相同。 -/
theorem increase_eval_l (v k f l : Nat) :
    eval_l increase_m (Nat.pair v (Nat.pair k (Nat.pair f l))) = v + k * (l - f) := by
  have hd : eval_l difference_m (Nat.pair v (Nat.pair k (Nat.pair f l))) = l - f := by
    change eval_l sub_m (eval_l difference_input_m (Nat.pair v (Nat.pair k (Nat.pair f l)))) = _
    simp only [difference_input_m, eval_l, Nat.unpair_pair, sub_eval_l]
  have hp : eval_l product_m (Nat.pair v (Nat.pair k (Nat.pair f l))) = k * (l - f) := by
    change eval_l mul_m (Nat.pair (Nat.pair v (Nat.pair k (Nat.pair f l))).unpair.2.unpair.1
      (eval_l difference_m (Nat.pair v (Nat.pair k (Nat.pair f l))))) = _
    rw [Nat.unpair_pair, Nat.unpair_pair, hd, PrimitiveProgram.mul_l]
  change eval_l add_m (Nat.pair (Nat.pair v (Nat.pair k (Nat.pair f l))).unpair.1
    (eval_l product_m (Nat.pair v (Nat.pair k (Nat.pair f l))))) = _
  rw [Nat.unpair_pair, hp, PrimitiveProgram.add_l]

private theorem add_value_l (hℳ : Theory.Models ℳ theory_m) :
    value_spec_l add_m (fun q : num_l ℳ =>
      add_l (SecondOrderUnpairing.value_l hℳ q).1 (SecondOrderUnpairing.value_l hℳ q).2) := by
  intro A hA q y
  obtain ⟨a, b, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ q
  simpa only [SecondOrderUnpairing.unpair_l] using add_spec_l hℳ hA a b y

private theorem mul_value_l (hℳ : Theory.Models ℳ theory_m) :
    value_spec_l mul_m (fun q : num_l ℳ =>
      mul_l (SecondOrderUnpairing.value_l hℳ q).1 (SecondOrderUnpairing.value_l hℳ q).2) := by
  intro A hA q y
  obtain ⟨a, b, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ q
  simpa only [SecondOrderUnpairing.unpair_l] using mul_spec_l hℳ hA a b y

/-- 内部规格保留同一截断减法图；加乘仍是模型原加乘解释。 -/
theorem increase_rel_l (hℳ : Theory.Models ℳ theory_m) {I D : set_l ℳ}
    (hI : graph_semantics_l (graph_m increase_m) I)
    (hD : graph_semantics_l (graph_m sub_m) D) (v k f l y : num_l ℳ) :
    relation_l I (value_l v (value_l k (value_l f l))) y ↔
      ∃ d, relation_l D (value_l l f) d ∧ add_l v (mul_l k d) = y := by
  obtain ⟨d, hd, _⟩ := value_exists_l hℳ sub_m hD
  have hv := (comp_value_l hℳ (add_value_l hℳ)
    (pair_value_l hℳ (left_value_l hℳ)
      (comp_value_l hℳ (mul_value_l hℳ)
        (pair_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ))
          (comp_value_l hℳ hd (comp_value_l hℳ
            (pair_value_l hℳ (right_value_l hℳ) (left_value_l hℳ))
            (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ))))))))
    hI (value_l v (value_l k (value_l f l))) y
  simp only [SecondOrderUnpairing.unpair_l] at hv
  rw [hv]
  simp only [hd hD, exists_eq_left']

#print axioms difference_input_m
#print axioms difference_m
#print axioms product_m
#print axioms increase_m
#print axioms increase_eval_l
#print axioms increase_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyIncrease
