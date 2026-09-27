import BMSConstructibleBridge.PowerlessBMSQuotientCoding
import BMSConstructibleBridge.PowerlessNatural
import BMSConstructibleBridge.SecondOrderAlgebra

/-!
# Z₂ 根码图商中的零与后继

根码成员规格给出纯集合意义下的空对象和后继：模型 `<` 中的初段正好在后继处
增加当前数。证明对任意二阶算术模型成立，未把内部自然数域换成宿主 `Nat`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientSuccessor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

/-- 任意 quotient 对象属于根码 n，当且仅当它等于某个更小自然数根码。 -/
theorem mem_numberCode_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (A : SecondOrderGraph.code_l M) (n : SecondOrderModel.num_l M) :
    SecondOrderQuotient.mem_l hM (SecondOrderQuotient.mk_l hM A)
        (PowerlessBMSQuotientCoding.numberCode_l C n).val ↔
      ∃ k, SecondOrderOrder.lt_l k n ∧
        SecondOrderQuotient.mk_l hM A =
          (PowerlessBMSQuotientCoding.numberCode_l C k).val := by
  change SecondOrderQuotient.mem_l hM (SecondOrderQuotient.mk_l hM A)
      (SecondOrderQuotient.mk_l hM
        (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n)) ↔
    ∃ k, SecondOrderOrder.lt_l k n ∧
      SecondOrderQuotient.mk_l hM A =
        SecondOrderQuotient.mk_l hM
          (SecondOrderNaturalGraph.code_l hM C.less C.less_spec k)
  rw [SecondOrderQuotient.mem_iff_l hM A
    (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n)]
  unfold SecondOrderGraph.mem_l
  constructor
  · rintro ⟨k, hk, hEq⟩
    refine ⟨k, (C.less_spec k n).mp hk, ?_⟩
    exact (SecondOrderQuotient.eq_iff_l hM A
      (SecondOrderNaturalGraph.code_l hM C.less C.less_spec k)).mpr hEq
  · rintro ⟨k, hk, hEq⟩
    refine ⟨k, (C.less_spec k n).mpr hk, ?_⟩
    exact (SecondOrderQuotient.eq_iff_l hM A
      (SecondOrderNaturalGraph.code_l hM C.less C.less_spec k)).mp hEq

/-- 目标模型的零数根码在 quotient 中是空对象。 -/
theorem zero_l (C : PowerlessBMSQuotientCoding.source_coding_l hM) :
    PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hM)
      (PowerlessBMSQuotientCoding.numberCode_l C
        (SecondOrderModel.zero_l M)).val := by
  intro p hp
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hM p
  obtain ⟨k, hk, _⟩ := (mem_numberCode_l C A (SecondOrderModel.zero_l M)).mp hp
  letI := SecondOrderAlgebra.semiring_l hM
  letI := SecondOrderAlgebra.order_l hM
  exact (not_lt_of_ge (SecondOrderAlgebra.zero_le_l hM k)) hk

/-- 后继根码的成员恰为前一根码的成员，加上前一根码自身。 -/
theorem successor_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (n : SecondOrderModel.num_l M) :
    PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hM)
      (PowerlessBMSQuotientCoding.numberCode_l C n).val
      (PowerlessBMSQuotientCoding.numberCode_l C
        (SecondOrderModel.succ_l n)).val := by
  intro p
  change SecondOrderQuotient.mem_l hM p
      (PowerlessBMSQuotientCoding.numberCode_l C
        (SecondOrderModel.succ_l n)).val ↔
    SecondOrderQuotient.mem_l hM p
      (PowerlessBMSQuotientCoding.numberCode_l C n).val ∨
        p = (PowerlessBMSQuotientCoding.numberCode_l C n).val
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hM p
  have hSplit (k : SecondOrderModel.num_l M) :
      SecondOrderOrder.lt_l k (SecondOrderModel.succ_l n) ↔
        SecondOrderOrder.lt_l k n ∨ k = n := by
    letI := SecondOrderAlgebra.semiring_l hM
    letI := SecondOrderAlgebra.order_l hM
    have hSucc : SecondOrderOrder.lt_l k (SecondOrderModel.succ_l n) ↔ k ≤ n :=
      SecondOrderNaturalGraph.lt_succ_l hM k n
    rw [hSucc]
    constructor
    · intro hk
      rcases eq_or_lt_of_le hk with hEq | hlt
      · exact Or.inr hEq
      · exact Or.inl hlt
    · rintro (hlt | rfl)
      · exact le_of_lt hlt
      · exact le_rfl
  rw [mem_numberCode_l C A (SecondOrderModel.succ_l n),
    mem_numberCode_l C A n]
  constructor
  · rintro ⟨k, hk, hEq⟩
    rcases (hSplit k).mp hk with hlt | rfl
    · exact Or.inl ⟨k, hlt, hEq⟩
    · exact Or.inr hEq
  · rintro (⟨k, hk, hEq⟩ | hEq)
    · exact ⟨k, (hSplit k).mpr (Or.inl hk), hEq⟩
    · exact ⟨n, (hSplit n).mpr (Or.inr rfl), hEq⟩

/-- 将目标模型的后继函数经双射送回 quotient 的内部自然数域。 -/
noncomputable def successorFunction_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM) :
    PowerlessArithmetic.num_l
        (ℳ := SecondOrderQuotient.structure_l hM) C.omega →
      PowerlessArithmetic.num_l
        (ℳ := SecondOrderQuotient.structure_l hM) C.omega :=
  fun a => PowerlessBMSQuotientCoding.numberCode_l C
    (SecondOrderModel.succ_l (PowerlessBMSQuotientCoding.numberEquiv_l C a))

/-- 上述函数实际满足 quotient 上的集合论后继关系。 -/
theorem successorFunction_graph_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a : PowerlessArithmetic.num_l
      (ℳ := SecondOrderQuotient.structure_l hM) C.omega) :
    PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hM)
      a.val (successorFunction_l C a).val := by
  have hInv : PowerlessBMSQuotientCoding.numberCode_l C
      (PowerlessBMSQuotientCoding.numberEquiv_l C a) = a := by
    exact Equiv.apply_symm_apply
      (Equiv.ofBijective (PowerlessBMSQuotientCoding.numberCode_l C)
        ⟨PowerlessBMSQuotientCoding.numberCode_injective_l C,
          PowerlessBMSQuotientCoding.numberCode_surjective_l C⟩) a
  simpa only [successorFunction_l, hInv] using
    successor_l C (PowerlessBMSQuotientCoding.numberEquiv_l C a)

#print axioms mem_numberCode_l
#print axioms zero_l
#print axioms successor_l
#print axioms successorFunction_graph_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientSuccessor
