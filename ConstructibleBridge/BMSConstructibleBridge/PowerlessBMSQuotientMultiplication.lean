import BMSConstructibleBridge.PowerlessBMSQuotientRecursion
import BMSConstructibleBridge.PowerlessBMSQuotientPureTransfer

/-!
# Z₂ 图商中的实际乘法与纯算术对应

用加法输出唯一性补齐右加算子的双向规格，将原模型的乘法图验证为该算子的
内部迭代。所得运算证书及对应记录只有原 Z₂ 模型与根码编码参数，不要求
商满足 Collection。源模型覆盖和 BMS 最终对象推导仍是独立义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientMultiplication

open Logic FirstOrder ThirdOrderSemantics
open PowerlessBMSQuotientCoding PowerlessBMSQuotientArithmetic
open PowerlessBMSQuotientRecursion

set_option autoImplicit false

attribute [local implicit_reducible] SecondOrderQuotient.structure_l

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hM

private theorem numberCode_exists_l (C : source_coding_l hM)
    (x : SecondOrderQuotient.type_l hM) (hx : member_l quotient_l x C.omega) :
    ∃ n : SecondOrderModel.num_l M, (numberCode_l C n).val = x := by
  obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨x, hx⟩
  exact ⟨n, congrArg Subtype.val hn⟩

/-- 右加法图满足原乘法定义要求的完整双向算子规格。 -/
theorem operator_exists_l (C : source_coding_l hM) (a : SecondOrderModel.num_l M) :
    ∃ H, PowerlessMultiplication.operator_l (ℳ := quotient_l) C.omega
      (numberCode_l C (SecondOrderModel.zero_l M)).val (numberCode_l C a).val H := by
  obtain ⟨H, hMap, hGraph⟩ := rightAdditionGraph_l C a
  refine ⟨H, hMap, fun x y => ?_⟩
  constructor
  · intro h
    have hxy := value_mem_l hMap h
    exact ⟨hxy.1, rightAdditionValue_addition_l C a H hGraph
      ⟨x, hxy.1⟩ ⟨y, hxy.2⟩ h⟩
  · rintro ⟨hx, h⟩
    obtain ⟨n, rfl⟩ := numberCode_exists_l C x hx
    have hy := (addition_iff_l C n a y).mp h
    subst y
    apply (hGraph (numberCode_l C n) (numberCode_l C (SecondOrderModel.add_l n a))).mpr
    simp only [numberEquiv_numberCode_l]

/-- 目标模型乘法图实际满足纯集合乘法迭代的初值与每个内部后继步。 -/
theorem iteration_l (C : source_coding_l hM) (a : SecondOrderModel.num_l M)
    (H f : SecondOrderQuotient.type_l hM)
    (hH : PowerlessMultiplication.operator_l (ℳ := quotient_l) C.omega
      (numberCode_l C (SecondOrderModel.zero_l M)).val (numberCode_l C a).val H)
    (hf : map_l (ℳ := quotient_l) f C.omega C.omega)
    (hGraph : ∀ x y : qnum_l C, value_l (ℳ := quotient_l) f x.val y.val ↔
      numberEquiv_l C y = SecondOrderModel.mul_l a (numberEquiv_l C x)) :
    PowerlessFunctionIteration.iteration_l (ℳ := quotient_l) C.omega
      (numberCode_l C (SecondOrderModel.zero_l M)).val C.omega H
      (numberCode_l C (SecondOrderModel.zero_l M)).val f := by
  refine ⟨hf, ?_, ?_⟩
  · apply (hGraph (numberCode_l C (SecondOrderModel.zero_l M))
      (numberCode_l C (SecondOrderModel.zero_l M))).mpr
    simp only [numberEquiv_numberCode_l, SecondOrderModel.mul_zero_l hM]
  · intro n m x y hn hnm hx hy
    have hnx := value_mem_l hf hx
    have hmy := value_mem_l hf hy
    obtain ⟨p, rfl⟩ := numberCode_exists_l C n hn
    obtain ⟨q, rfl⟩ := numberCode_exists_l C m hmy.1
    obtain ⟨r, rfl⟩ := numberCode_exists_l C x hnx.2
    obtain ⟨s, rfl⟩ := numberCode_exists_l C y hmy.2
    have hq : q = SecondOrderModel.succ_l p :=
      numberCode_injective_l C (Subtype.ext
        (successor_unique_l hnm (PowerlessBMSQuotientSuccessor.successor_l C p)))
    have hr := (hGraph (numberCode_l C p) (numberCode_l C r)).mp hx
    have hs := (hGraph (numberCode_l C q) (numberCode_l C s)).mp hy
    simp only [numberEquiv_numberCode_l] at hr hs
    apply (hH.2 _ _).mpr
    refine ⟨(numberCode_l C r).property, ?_⟩
    apply (addition_iff_l C r a _).mpr
    rw [hs, hq, SecondOrderModel.mul_succ_l hM, hr]

/-- 每对目标内部数的积满足实际纯集合乘法关系。 -/
theorem multiplicationInstance_l (C : source_coding_l hM)
    (a b : SecondOrderModel.num_l M) :
    PowerlessMultiplication.multiplication_l (ℳ := quotient_l) C.omega
      (numberCode_l C (SecondOrderModel.zero_l M)).val
      (numberCode_l C a).val (numberCode_l C b).val
      (numberCode_l C (SecondOrderModel.mul_l a b)).val := by
  obtain ⟨H, hH⟩ := operator_exists_l C a
  obtain ⟨f, hf, hGraph⟩ := multiplicationMapGraph_l C a
  refine ⟨H, f, hH, iteration_l C a H f hH hf hGraph, ?_⟩
  apply (hGraph (numberCode_l C b) (numberCode_l C (SecondOrderModel.mul_l a b))).mpr
  simp only [numberEquiv_numberCode_l]

/-- 数码双射搬运的乘法函数。 -/
noncomputable def mulNumbers_l (C : source_coding_l hM) (x y : qnum_l C) : qnum_l C :=
  numberCode_l C (SecondOrderModel.mul_l (numberEquiv_l C x) (numberEquiv_l C y))

/-- 原乘法关系没有额外输出；不增加源集合论模型假设。 -/
theorem multiplication_unique_l (C : source_coding_l hM)
    {a b c d : SecondOrderQuotient.type_l hM} (hb : member_l quotient_l b C.omega)
    (hc : PowerlessMultiplication.multiplication_l (ℳ := quotient_l) C.omega
      (numberCode_l C (SecondOrderModel.zero_l M)).val a b c)
    (hd : PowerlessMultiplication.multiplication_l (ℳ := quotient_l) C.omega
      (numberCode_l C (SecondOrderModel.zero_l M)).val a b d) : c = d := by
  obtain ⟨H, f, hH, hf, hc⟩ := hc
  obtain ⟨K, g, hK, hg, hd⟩ := hd
  have hHK : H = K := map_ext_l hH.1 hK.1
    (fun x y => (hH.2 x y).trans (hK.2 x y).symm)
  subst K
  obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨b, hb⟩
  have hn' : (numberCode_l C n).val = b := congrArg Subtype.val hn
  rw [← hn'] at hc hd
  exact function_agreement_l C hH.1 hf hg n c d hc hd

/-- 乘法图逐点精确等于原模型的积，包括任意商对象作为输出的情形。 -/
theorem multiplication_iff_l (C : source_coding_l hM)
    (a b : SecondOrderModel.num_l M) (c : SecondOrderQuotient.type_l hM) :
    PowerlessMultiplication.multiplication_l (ℳ := quotient_l) C.omega
      (numberCode_l C (SecondOrderModel.zero_l M)).val
      (numberCode_l C a).val (numberCode_l C b).val c ↔
      c = (numberCode_l C (SecondOrderModel.mul_l a b)).val := by
  constructor
  · intro h
    exact multiplication_unique_l C (numberCode_l C b).property h (multiplicationInstance_l C a b)
  · rintro rfl
    exact multiplicationInstance_l C a b

theorem multiplicationGraph_l (C : source_coding_l hM) (x y : qnum_l C) :
    PowerlessMultiplication.multiplication_l (ℳ := quotient_l) C.omega
      (numberCode_l C (SecondOrderModel.zero_l M)).val x.val y.val (mulNumbers_l C x y).val := by
  have h := multiplicationInstance_l C (numberEquiv_l C x) (numberEquiv_l C y)
  have hx : numberCode_l C (numberEquiv_l C x) = x :=
    Equiv.symm_apply_apply (numberEquiv_l C) x
  have hy : numberCode_l C (numberEquiv_l C y) = y :=
    Equiv.symm_apply_apply (numberEquiv_l C) y
  rw [hx, hy] at h
  exact h

theorem numberEquiv_mulNumbers_l (C : source_coding_l hM) (x y : qnum_l C) :
    numberEquiv_l C (mulNumbers_l C x y) =
      SecondOrderModel.mul_l (numberEquiv_l C x) (numberEquiv_l C y) :=
  numberEquiv_numberCode_l C _

/-- 商侧后继、加法、乘法全部具有原纯集合图规格。 -/
noncomputable def operations_l (C : source_coding_l hM) :
    PowerlessArithmetic.operations_l (ℳ := quotient_l) C.omega
      (numberCode_l C (SecondOrderModel.zero_l M)).val where
  succ_l := PowerlessBMSQuotientSuccessor.successorFunction_l C
  add_l := addNumbers_l C
  mul_l := mulNumbers_l C
  succ_graph_l := PowerlessBMSQuotientSuccessor.successorFunction_graph_l C
  add_graph_l := additionGraph_l C
  mul_graph_l := multiplicationGraph_l C

/-- 实际运算填满纯矩阵迁移记录；加乘对应不再是调用者的前提。 -/
noncomputable def correspondence_l (C : source_coding_l hM) :
    SecondOrderPureTransfer.correspondence_l
      (M := PowerlessBMSQuotientPureTransfer.arithmeticStructure_l C (operations_l C))
      (N := M) :=
  PowerlessBMSQuotientPureTransfer.correspondence_of_operations_l C (operations_l C)
    (fun x => numberEquiv_numberCode_l C (SecondOrderModel.succ_l (numberEquiv_l C x)))
    (numberEquiv_addNumbers_l C) (numberEquiv_mulNumbers_l C)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientMultiplication
