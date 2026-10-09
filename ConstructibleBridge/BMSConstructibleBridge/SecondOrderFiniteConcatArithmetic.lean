import BMSConstructibleBridge.PowerlessBMSQuotientRecursion
import BMSConstructibleBridge.SecondOrderAlgebra
import BMSConstructibleBridge.SecondOrderOmegaTransitive
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 原 Z₂ 商中的内部加法分段

给定实际加法迭代图，将其读数精确接回同一模型的加法，再证明两段
下标的覆盖、分离和单射性。模型数允许非标准；不借用含完整 Collection
的弱集合论模型，也不由选择抽取数码的全局逆函数。
这些语义接口由实际有限拼接图的原对象推导消费。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteConcatArithmetic

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderModel (num_l add_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 图值回读，反向由同一实际图的总定义性给出，而非另选一张图。 -/
theorem read_l (K : source_coding_l hℳ) (a : num_l ℳ) {e F : type_l hℳ}
    (he : ∀ x, ¬mem_l hℳ x e)
    (hF : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e (numberCode_l K a).val F)
    (hMap : map_l (ℳ := 𝒱) F K.omega K.omega) (b : num_l ℳ) (y : type_l hℳ) :
    value_l (ℳ := 𝒱) F (numberCode_l K b).val y ↔
      y = (numberCode_l K (add_l a b)).val := by
  have heEq : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false (he x)
      (PowerlessBMSQuotientSuccessor.zero_l K x))
  have hF' := hF
  rw [heEq] at hF'
  constructor
  · intro hy
    exact (PowerlessBMSQuotientRecursion.addition_iff_l K a b y).mp ⟨F, hF', hy⟩
  · intro hy
    obtain ⟨z, hz, _⟩ := hMap.2 _ (numberCode_l K b).property
    have hzEq := (PowerlessBMSQuotientRecursion.addition_iff_l K a b z).mp ⟨F, hF', hz.2⟩
    exact (hzEq.trans hy.symm) ▸ hz.2

theorem segment_l (K : source_coding_l hℳ) (a b : num_l ℳ) {e F : type_l hℳ}
    (he : ∀ x, ¬mem_l hℳ x e)
    (hF : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e (numberCode_l K a).val F)
    (hMap : map_l (ℳ := 𝒱) F K.omega K.omega) {i : type_l hℳ}
    (hi : mem_l hℳ i (numberCode_l K (add_l a b)).val) :
    mem_l hℳ i (numberCode_l K a).val ∨
      ∃ j, mem_l hℳ j (numberCode_l K b).val ∧ value_l (ℳ := 𝒱) F j i := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  have hcω : mem_l hℳ (numberCode_l K (add_l a b)).val K.omega :=
    (numberCode_l K (add_l a b)).property
  have hiω := SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hcω hi
  obtain ⟨k, hk⟩ := numberCode_surjective_l K ⟨i, hiω⟩
  have hkEq : (numberCode_l K k).val = i := congrArg Subtype.val hk
  have hi' := hi
  rw [← hkEq] at hi'
  have hlt : k < a + b := (numberCode_mem_iff_lt_l K k (a + b)).mp hi'
  by_cases hka : k < a
  · exact Or.inl (hkEq ▸ (numberCode_mem_iff_lt_l K k a).mpr hka)
  · obtain ⟨j, hj⟩ := (SecondOrderAlgebra.le_iff_l hℳ a k).mp (le_of_not_gt hka)
    have hjb : j < b := (add_lt_add_iff_left a).mp (by simpa only [hj] using hlt)
    refine Or.inr ⟨(numberCode_l K j).val, (numberCode_mem_iff_lt_l K j b).mpr hjb, ?_⟩
    apply (read_l K a he hF hMap j i).mpr
    exact hkEq.symm.trans (congrArg (fun n => (numberCode_l K n).val) hj.symm)

theorem lower_l (K : source_coding_l hℳ) (a : num_l ℳ) {e F j i : type_l hℳ}
    (he : ∀ x, ¬mem_l hℳ x e)
    (hF : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e (numberCode_l K a).val F)
    (hMap : map_l (ℳ := 𝒱) F K.omega K.omega)
    (hji : value_l (ℳ := 𝒱) F j i) : ¬mem_l hℳ i (numberCode_l K a).val := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  obtain ⟨k, hk⟩ := numberCode_surjective_l K
    ⟨j, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hji).1⟩
  have hkEq : (numberCode_l K k).val = j := congrArg Subtype.val hk
  have hiEq := (read_l K a he hF hMap k i).mp (hkEq.symm ▸ hji)
  intro hi
  rw [hiEq] at hi
  exact (not_lt_of_ge (le_add_of_nonneg_right (SecondOrderAlgebra.zero_le_l hℳ k)))
    ((numberCode_mem_iff_lt_l K (a + k) a).mp hi)

theorem cancel_l (K : source_coding_l hℳ) (a : num_l ℳ) {e F j k i : type_l hℳ}
    (he : ∀ x, ¬mem_l hℳ x e)
    (hF : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e (numberCode_l K a).val F)
    (hMap : map_l (ℳ := 𝒱) F K.omega K.omega)
    (hj : value_l (ℳ := 𝒱) F j i) (hk : value_l (ℳ := 𝒱) F k i) : j = k := by
  obtain ⟨s, hs⟩ := numberCode_surjective_l K
    ⟨j, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hj).1⟩
  obtain ⟨t, ht⟩ := numberCode_surjective_l K
    ⟨k, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hk).1⟩
  have hsEq : (numberCode_l K s).val = j := congrArg Subtype.val hs
  have htEq : (numberCode_l K t).val = k := congrArg Subtype.val ht
  have hiS := (read_l K a he hF hMap s i).mp (hsEq.symm ▸ hj)
  have hiT := (read_l K a he hF hMap t i).mp (htEq.symm ▸ hk)
  have hst : add_l a s = add_l a t := numberCode_injective_l K
    (Subtype.ext (hiS.symm.trans hiT))
  have hEq := (SecondOrderNumbers.add_cancel_l hℳ a s t).mp hst
  exact hsEq.symm.trans ((congrArg (fun n => (numberCode_l K n).val) hEq).trans htEq)

theorem prefix_l (K : source_coding_l hℳ) (a b : num_l ℳ) {i : type_l hℳ}
    (hi : mem_l hℳ i (numberCode_l K a).val) :
    mem_l hℳ i (numberCode_l K (add_l a b)).val := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  have haω : mem_l hℳ (numberCode_l K a).val K.omega := (numberCode_l K a).property
  obtain ⟨k, hk⟩ := numberCode_surjective_l K
    ⟨i, SecondOrderOmegaTransitive.member_l hℳ K.omega_spec haω hi⟩
  have hkEq : (numberCode_l K k).val = i := congrArg Subtype.val hk
  rw [← hkEq] at hi ⊢
  exact (numberCode_mem_iff_lt_l K k (a + b)).mpr
    (lt_of_lt_of_le ((numberCode_mem_iff_lt_l K k a).mp hi)
      (le_add_of_nonneg_right (SecondOrderAlgebra.zero_le_l hℳ b)))

theorem shifted_l (K : source_coding_l hℳ) (a b : num_l ℳ) {e F j : type_l hℳ}
    (he : ∀ x, ¬mem_l hℳ x e)
    (hF : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e (numberCode_l K a).val F)
    (hMap : map_l (ℳ := 𝒱) F K.omega K.omega)
    (hj : mem_l hℳ j (numberCode_l K b).val) :
    ∃ i, mem_l hℳ i (numberCode_l K (add_l a b)).val ∧ value_l (ℳ := 𝒱) F j i := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  have hbω : mem_l hℳ (numberCode_l K b).val K.omega := (numberCode_l K b).property
  obtain ⟨k, hk⟩ := numberCode_surjective_l K
    ⟨j, SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hbω hj⟩
  have hkEq : (numberCode_l K k).val = j := congrArg Subtype.val hk
  have hj' := hj
  rw [← hkEq] at hj'
  refine ⟨(numberCode_l K (a + k)).val,
    (numberCode_mem_iff_lt_l K (a + k) (a + b)).mpr
      ((add_lt_add_iff_left a).mpr ((numberCode_mem_iff_lt_l K k b).mp hj')), ?_⟩
  exact hkEq ▸ (read_l K a he hF hMap k _).mpr rfl

/-- 加法平移精确保留父坐标先后关系，故未来父坐标不会变成已执行坐标。 -/
theorem order_l (K : source_coding_l hℳ) (a : num_l ℳ) {e F j k i l : type_l hℳ}
    (he : ∀ x, ¬mem_l hℳ x e)
    (hF : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e (numberCode_l K a).val F)
    (hMap : map_l (ℳ := 𝒱) F K.omega K.omega)
    (hj : value_l (ℳ := 𝒱) F j i) (hk : value_l (ℳ := 𝒱) F k l) :
    mem_l hℳ j k ↔ mem_l hℳ i l := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  obtain ⟨s, hs⟩ := numberCode_surjective_l K
    ⟨j, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hj).1⟩
  obtain ⟨t, ht⟩ := numberCode_surjective_l K
    ⟨k, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hk).1⟩
  have hsEq : (numberCode_l K s).val = j := congrArg Subtype.val hs
  have htEq : (numberCode_l K t).val = k := congrArg Subtype.val ht
  have hiEq := (read_l K a he hF hMap s i).mp (hsEq.symm ▸ hj)
  have hlEq := (read_l K a he hF hMap t l).mp (htEq.symm ▸ hk)
  rw [← hsEq, ← htEq, hiEq, hlEq, numberCode_mem_iff_lt_l, numberCode_mem_iff_lt_l]
  exact (add_lt_add_iff_left a).symm

#print axioms read_l
#print axioms segment_l
#print axioms lower_l
#print axioms cancel_l
#print axioms prefix_l
#print axioms shifted_l
#print axioms order_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteConcatArithmetic
