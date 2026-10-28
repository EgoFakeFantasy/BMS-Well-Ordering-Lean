import BMSConstructibleBridge.PowerlessLegacyAssignmentSyntax
import BMSConstructibleBridge.PowerlessEvaluationClause

/-! # 反转填充赋值的槽读数与两个原子分支

母集枚举 U 只在环境商中取值。先沿实际反转索引把填充图的原槽读数
还原，再用 U 对原相等图及成员图的逐点解释证明两个原子真值保持。
本文件不假设 U 属于相对类，也不假设整个商满足无幂集集合论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessLegacyAssignmentSyntax (link_l)
open SecondOrderLegacyAssignmentReversal (index_l)
open SecondOrderSequenceSyntax (read_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem point_l (K : source_coding_l hℳ) {E : SecondOrderModel.set_l ℳ}
    {c l L z i r : SecondOrderModel.num_l ℳ} {U f : SecondOrderQuotient.type_l hℳ}
    (hLength : l = L ∨ SecondOrderOrder.lt_l l L) (hIndex : index_l l i r)
    (hLink : link_l K E c l L z U f) (y : SecondOrderQuotient.type_l hℳ) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (numberCode_l K r).val y ↔
      ∃ x, read_l E c i x ∧ value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U
        (numberCode_l K x).val y := by
  refine (hLink r y).trans ?_
  apply exists_congr
  intro x
  apply and_congr _ Iff.rfl
  refine (SecondOrderLegacyAssignmentPadding.prefix_l hℳ hLength
    (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hIndex).2).trans ?_
  constructor
  · rintro ⟨j, hj, hRead⟩
    have hji := SecondOrderLegacyAssignmentReversal.unique_l hℳ
      ((SecondOrderLegacyAssignmentReversal.symmetric_l hℳ l j r).mp hj)
      ((SecondOrderLegacyAssignmentReversal.symmetric_l hℳ l i r).mp hIndex)
    subst j
    exact hRead
  · exact fun hRead => ⟨i, hIndex, hRead⟩

variable (K : source_coding_l hℳ) {E Q R : SecondOrderModel.set_l ℳ}
  {c l L z i j r s : SecondOrderModel.num_l ℳ} {A U f : SecondOrderQuotient.type_l hℳ}
  (hLength : l = L ∨ SecondOrderOrder.lt_l l L) (hi : index_l l i r) (hj : index_l l j s)
  (hLink : link_l K E c l L z U f)
  (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A)

include hLength hi hj hLink hU

/-- 原相等图与枚举值的相等关系对应时，目标相等原子读数保持真值。 -/
theorem equality_l
    (hQ : ∀ a b x y,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K a).val x →
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K b).val y →
      (SecondOrderPairing.relation_l Q a b ↔ x = y)) :
    (∃ a b, read_l E c i a ∧ read_l E c j b ∧ SecondOrderPairing.relation_l Q a b) ↔
      PowerlessEvaluationClause.equal_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        f (numberCode_l K r).val (numberCode_l K s).val := by
  constructor
  · rintro ⟨a, b, ha, hb, hEq⟩
    obtain ⟨x, hx, _⟩ := hU.2 _ (numberCode_l K a).property
    obtain ⟨y, hy, _⟩ := hU.2 _ (numberCode_l K b).property
    have hxy := (hQ a b x y hx.2 hy.2).mp hEq
    subst y
    exact ⟨x, (point_l K hLength hi hLink x).mpr ⟨a, ha, hx.2⟩,
      (point_l K hLength hj hLink x).mpr ⟨b, hb, hy.2⟩⟩
  · rintro ⟨x, hx, hy⟩
    obtain ⟨a, ha, hax⟩ := (point_l K hLength hi hLink x).mp hx
    obtain ⟨b, hb, hbx⟩ := (point_l K hLength hj hLink x).mp hy
    exact ⟨a, b, ha, hb, (hQ a b x x hax hbx).mpr rfl⟩

/-- 原成员图与枚举值的隶属关系对应时，目标隶属原子读数保持真值。 -/
theorem membership_l
    (hR : ∀ a b x y,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K a).val x →
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K b).val y →
      (SecondOrderPairing.relation_l R a b ↔ member_l (SecondOrderQuotient.structure_l hℳ) x y)) :
    (∃ a b, read_l E c i a ∧ read_l E c j b ∧ SecondOrderPairing.relation_l R a b) ↔
      PowerlessEvaluationClause.member_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        f (numberCode_l K r).val (numberCode_l K s).val := by
  constructor
  · rintro ⟨a, b, ha, hb, hMem⟩
    obtain ⟨x, hx, _⟩ := hU.2 _ (numberCode_l K a).property
    obtain ⟨y, hy, _⟩ := hU.2 _ (numberCode_l K b).property
    exact ⟨x, y, (point_l K hLength hi hLink x).mpr ⟨a, ha, hx.2⟩,
      (point_l K hLength hj hLink y).mpr ⟨b, hb, hy.2⟩,
      (hR a b x y hx.2 hy.2).mp hMem⟩
  · rintro ⟨x, y, hx, hy, hMem⟩
    obtain ⟨a, ha, hax⟩ := (point_l K hLength hi hLink x).mp hx
    obtain ⟨b, hb, hby⟩ := (point_l K hLength hj hLink y).mp hy
    exact ⟨a, b, ha, hb, (hR a b x y hax hby).mpr hMem⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentReading
