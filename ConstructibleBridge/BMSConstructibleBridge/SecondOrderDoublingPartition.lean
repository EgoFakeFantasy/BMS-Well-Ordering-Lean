import BMSConstructibleBridge.PowerlessRelativeClassDoublingDerives
import BMSConstructibleBridge.SecondOrderParity

/-! # 实际倍数图的奇偶索引性质

集合图的值与原模型数精确对应，再用原内部奇偶分解取得覆盖、单射和分支
不相交性。没有把商对象直接当作宿主自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDoublingPartition

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private theorem code_injective_l (K : source_coding_l hℳ) {i j : SecondOrderModel.num_l ℳ}
    (h : (numberCode_l K i).val = (numberCode_l K j).val) : i = j :=
  numberCode_injective_l K (Subtype.ext h)

variable (K : source_coding_l hℳ) {D : type_l hℳ}
  (hD : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) D K.omega K.omega)
  (hPoint : ∀ i : SecondOrderModel.num_l ℳ,
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D (numberCode_l K i).val
      (numberCode_l K (SecondOrderModel.add_l i i)).val)

include hD hPoint

theorem even_coordinate_l {i n : type_l hℳ} {q : SecondOrderModel.num_l ℳ}
    (hi : i = (numberCode_l K q).val)
    (hValue : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D i n) :
    n = (numberCode_l K (SecondOrderModel.add_l q q)).val := by
  rw [hi] at hValue
  exact SecondOrderFunctionProperties.value_unique_l hℳ hD hValue (hPoint q)

theorem odd_coordinate_l {i t n : type_l hℳ} {q : SecondOrderModel.num_l ℳ}
    (hi : i = (numberCode_l K q).val)
    (hValue : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D i t)
    (hSucc : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) t n) :
    n = (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.add_l q q))).val := by
  have ht := even_coordinate_l K hD hPoint hi hValue
  rw [ht] at hSucc
  exact PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ)
    (a := (numberCode_l K (SecondOrderModel.add_l q q)).val)
    (b := n) (c := (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.add_l q q))).val)
    hSucc (PowerlessBMSQuotientSuccessor.successor_l K _)

theorem even_unique_l {i j n : type_l hℳ} (hi : mem_l hℳ i K.omega) (hj : mem_l hℳ j K.omega)
    (hin : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D i n)
    (hjn : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D j n) : i = j := by
  obtain ⟨q, hq⟩ := numberCode_surjective_l K ⟨i, hi⟩
  obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨j, hj⟩
  have hq' := (congrArg Subtype.val hq).symm
  have hr' := (congrArg Subtype.val hr).symm
  have hEq := code_injective_l K ((even_coordinate_l K hD hPoint hq' hin).symm.trans
    (even_coordinate_l K hD hPoint hr' hjn))
  have hqr := SecondOrderParity.even_injective_l hℳ hEq
  exact hq'.trans ((congrArg (fun s => (numberCode_l K s).val) hqr).trans hr'.symm)

theorem odd_unique_l {i j t v n : type_l hℳ} (hi : mem_l hℳ i K.omega) (hj : mem_l hℳ j K.omega)
    (hit : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D i t)
    (hjv : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D j v)
    (ht : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) t n)
    (hv : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) v n) : i = j := by
  obtain ⟨q, hq⟩ := numberCode_surjective_l K ⟨i, hi⟩
  obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨j, hj⟩
  have hq' := (congrArg Subtype.val hq).symm
  have hr' := (congrArg Subtype.val hr).symm
  have hEq := code_injective_l K ((odd_coordinate_l K hD hPoint hq' hit ht).symm.trans
    (odd_coordinate_l K hD hPoint hr' hjv hv))
  have hqr := SecondOrderParity.odd_injective_l hℳ hEq
  exact hq'.trans ((congrArg (fun s => (numberCode_l K s).val) hqr).trans hr'.symm)

theorem disjoint_l {i j t n : type_l hℳ} (hi : mem_l hℳ i K.omega) (hj : mem_l hℳ j K.omega)
    (hin : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D i n)
    (hjt : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D j t)
    (ht : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) t n) : False := by
  obtain ⟨q, hq⟩ := numberCode_surjective_l K ⟨i, hi⟩
  obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨j, hj⟩
  have hEq := code_injective_l K
    ((even_coordinate_l K hD hPoint (congrArg Subtype.val hq).symm hin).symm.trans
      (odd_coordinate_l K hD hPoint (congrArg Subtype.val hr).symm hjt ht))
  exact SecondOrderParity.disjoint_l hℳ q r hEq

omit hD in
theorem cover_l (n : type_l hℳ) (hn : mem_l hℳ n K.omega) :
    (∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D i n) ∨
      ∃ i t, mem_l hℳ i K.omega ∧ mem_l hℳ t K.omega ∧
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D i t ∧
          PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) t n := by
  obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have ha' : n = (numberCode_l K a).val := (congrArg Subtype.val ha).symm
  obtain ⟨q, hq | hq⟩ := SecondOrderParity.exists_l hℳ a
  · refine Or.inl ⟨(numberCode_l K q).val, (numberCode_l K q).property, ?_⟩
    rw [ha', hq]
    exact hPoint q
  · refine Or.inr ⟨(numberCode_l K q).val, (numberCode_l K (SecondOrderModel.add_l q q)).val,
      (numberCode_l K q).property, (numberCode_l K (SecondOrderModel.add_l q q)).property, hPoint q, ?_⟩
    rw [ha', hq]
    exact PowerlessBMSQuotientSuccessor.successor_l K _

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDoublingPartition
