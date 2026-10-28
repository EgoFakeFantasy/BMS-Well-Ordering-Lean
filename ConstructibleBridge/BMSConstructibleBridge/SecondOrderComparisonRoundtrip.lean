import BMSConstructibleBridge.SecondOrderComparisonDecode

/-! # 固定枚举的比较实数与完整集合图双向对应

重复枚举坐标的相容性是显式前提，而不是隐含的单射或选择假设。
解码对任意输入总有定义；本模块证明相容输入的重新编码，以及有界
完整图的重新解码。所有自然数均为原模型内部的数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonRoundtrip

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 比较位只取决于实际枚举值，不取决于重复项的编号。 -/
def compatible_l (K : source_coding_l hℳ) (f : type_l hℳ)
    (R : SecondOrderModel.set_l ℳ) : Prop :=
  ∀ i j k l x y,
    value_l (ℳ := 𝒱) f (numberCode_l K i).val x →
    value_l (ℳ := 𝒱) f (numberCode_l K j).val y →
    value_l (ℳ := 𝒱) f (numberCode_l K k).val x →
    value_l (ℳ := 𝒱) f (numberCode_l K l).val y →
    (SecondOrderPairing.relation_l R i j ↔ SecondOrderPairing.relation_l R k l)

private theorem coordinate_l (K : source_coding_l hℳ) {C f P : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C) {R : SecondOrderModel.set_l ℳ}
    (hR : SecondOrderComparisonReal.spec_l K f P R) {i j : SecondOrderModel.num_l ℳ}
    {x y : type_l hℳ}
    (hix : value_l (ℳ := 𝒱) f (numberCode_l K i).val x)
    (hjy : value_l (ℳ := 𝒱) f (numberCode_l K j).val y) :
    SecondOrderPairing.relation_l R i j ↔ value_l (ℳ := 𝒱) P x y := by
  refine (hR i j).trans ⟨?_, fun h => ⟨x, y, hix, hjy, h⟩⟩
  rintro ⟨a, b, ha, hb, hab⟩
  have hA := SecondOrderFunctionLaws.value_unique_l hℳ hf ha hix
  have hB := SecondOrderFunctionLaws.value_unique_l hℳ hf hb hjy
  exact hA ▸ hB ▸ hab

theorem compatible_spec_l (K : source_coding_l hℳ) {C f P : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C) {R : SecondOrderModel.set_l ℳ}
    (hR : SecondOrderComparisonReal.spec_l K f P R) : compatible_l K f R := by
  intro i j k l x y hix hjy hkx hly
  exact (coordinate_l K hf hR hix hjy).trans (coordinate_l K hf hR hkx hly).symm

/-- 相容性足够；重新编码这一方向不要求满射。 -/
theorem encode_decode_l (K : source_coding_l hℳ) {C f P : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C) {R : SecondOrderModel.set_l ℳ}
    (hCompat : compatible_l K f R) (hP : SecondOrderComparisonDecode.graph_l K C f R P) :
    SecondOrderComparisonReal.spec_l K f P R := by
  intro i j
  constructor
  · intro hij
    obtain ⟨x, ⟨hx, hix⟩, _⟩ := hf.2 (numberCode_l K i).val (numberCode_l K i).property
    obtain ⟨y, ⟨hy, hjy⟩, _⟩ := hf.2 (numberCode_l K j).val (numberCode_l K j).property
    exact ⟨x, y, hix, hjy, (SecondOrderComparisonDecode.values_l K hP x y).mpr
      ⟨hx, hy, i, j, hij, hix, hjy⟩⟩
  · rintro ⟨x, y, hix, hjy, hxy⟩
    obtain ⟨_, _, k, l, hkl, hkx, hly⟩ :=
      (SecondOrderComparisonDecode.values_l K hP x y).mp hxy
    exact (hCompat i j k l x y hix hjy hkx hly).mpr hkl

theorem read_spec_l (K : source_coding_l hℳ) {C f P : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C)
    (hOnto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x)
    {R : SecondOrderModel.set_l ℳ} (hR : SecondOrderComparisonReal.spec_l K f P R)
    (x y : type_l hℳ) :
    SecondOrderComparisonDecode.read_l K C f R x y ↔
      mem_l hℳ x C ∧ mem_l hℳ y C ∧ value_l (ℳ := 𝒱) P x y := by
  constructor
  · rintro ⟨hx, hy, i, j, hij, hix, hjy⟩
    exact ⟨hx, hy, (coordinate_l K hf hR hix hjy).mp hij⟩
  · rintro ⟨hx, hy, hxy⟩
    obtain ⟨i, hi, hix⟩ := hOnto x hx
    obtain ⟨j, hj, hjy⟩ := hOnto y hy
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨i, hi⟩
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨j, hj⟩
    have hn' : (numberCode_l K n).val = i := congrArg Subtype.val hn
    have hm' : (numberCode_l K m).val = j := congrArg Subtype.val hm
    rw [← hn'] at hix
    rw [← hm'] at hjy
    exact ⟨hx, hy, n, m, (hR n m).mpr ⟨x, y, hix, hjy, hxy⟩, hix, hjy⟩

/-- 完整有界图才能由比较值恢复；不忽略关系对象中可能存在的垃圾元素。 -/
theorem decode_encode_l (K : source_coding_l hℳ) {C f P Q : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C)
    (hOnto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x)
    (hBound : ∀ p, mem_l hℳ p P → ∃ x y,
      mem_l hℳ x C ∧ mem_l hℳ y C ∧ SecondOrderPairObjects.ordered_l hℳ x y p)
    {R : SecondOrderModel.set_l ℳ} (hR : SecondOrderComparisonReal.spec_l K f P R)
    (hQ : SecondOrderComparisonDecode.graph_l K C f R Q) : Q = P := by
  apply SecondOrderQuotient.ext_l hℳ
  intro p
  rw [hQ p]
  constructor
  · rintro ⟨x, y, hxy, hp⟩
    obtain ⟨_, _, q, hq, hqxy⟩ := (read_spec_l K hf hOnto hR x y).mp hxy
    have hpq := SecondOrderPairObjects.ordered_unique_l hℳ hp hqxy
    exact hpq.symm ▸ hq
  · intro hp
    obtain ⟨x, y, hx, hy, hxy⟩ := hBound p hp
    exact ⟨x, y, (read_spec_l K hf hOnto hR x y).mpr ⟨hx, hy, p, hp, hxy⟩, hxy⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonRoundtrip
