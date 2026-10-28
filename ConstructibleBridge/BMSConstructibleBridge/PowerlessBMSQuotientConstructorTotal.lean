import BMSConstructibleBridge.PowerlessBMSQuotientConstructorInjective

/-! # 实际原商三角构造子的全域性与正向唯一性

内部数码覆盖和实际三角图规格给出全部合法输入的输出，不调用完整源理论。
与坐标单射性不同，这里证明同一输入只有一个输出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientConstructorTotal

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientPairingBounds (spec_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem pairing_exists_l (K : source_coding_l hℳ) {T a b : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega) :
    ∃ c, mem_l hℳ c K.omega ∧
      PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T a b c := by
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a, ha⟩
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hb⟩
  have haEq : a = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  have hbEq : b = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
  obtain ⟨v, hv⟩ := SecondOrderTriangularArithmetic.exists_l hℳ (SecondOrderModel.add_l i j)
  refine ⟨(numberCode_l K (SecondOrderModel.add_l v i)).val, (numberCode_l K (SecondOrderModel.add_l v i)).property, ?_⟩
  rw [haEq, hbEq]
  exact (PowerlessBMSQuotientPairingBounds.instance_l K hT hSpec i j _).mpr ⟨v, hv, rfl⟩

theorem pairing_unique_l (K : source_coding_l hℳ) {T a b c d : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega)
    (hc : PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T a b c)
    (hd : PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T a b d) : c = d := by
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a, ha⟩
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hb⟩
  have haEq : a = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  have hbEq : b = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
  rw [haEq, hbEq] at hc hd
  obtain ⟨v, hv, rfl⟩ := (PowerlessBMSQuotientPairingBounds.instance_l K hT hSpec i j c).mp hc
  obtain ⟨w, hw, rfl⟩ := (PowerlessBMSQuotientPairingBounds.instance_l K hT hSpec i j d).mp hd
  rw [SecondOrderTriangularArithmetic.unique_l hℳ hv hw]

theorem node_exists_l (K : source_coding_l hℳ) {T t p : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (ht : mem_l hℳ t K.omega) (hp : mem_l hℳ p K.omega) :
    ∃ n, mem_l hℳ n K.omega ∧
      PowerlessFormulaNode.node_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T t p n := by
  obtain ⟨c, hcω, hc⟩ := pairing_exists_l K hT hSpec ht hp
  obtain ⟨n, hnω, hn⟩ := K.omega_spec.1.2 c hcω
  exact ⟨n, hnω, ht, hp, c, hc, hn⟩

theorem node_unique_l (K : source_coding_l hℳ) {T t p n m : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (hn : PowerlessFormulaNode.node_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T t p n)
    (hm : PowerlessFormulaNode.node_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T t p m) : n = m := by
  obtain ⟨ht, hp, c, hc, hn⟩ := hn
  obtain ⟨_, _, d, hd, hm⟩ := hm
  have hcd := pairing_unique_l K hT hSpec ht hp hc hd
  subst d
  exact PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) hn hm

theorem exists_l (K : source_coding_l hℳ) {T t a b : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (ht : mem_l hℳ t K.omega) (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega) :
    ∃ n, mem_l hℳ n K.omega ∧
      PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T t a b n := by
  obtain ⟨p, hpω, hp⟩ := pairing_exists_l K hT hSpec ha hb
  obtain ⟨n, hnω, hn⟩ := node_exists_l K hT hSpec ht hpω
  exact ⟨n, hnω, ha, hb, p, hp, hn⟩

theorem unique_l (K : source_coding_l hℳ) {T t a b n m : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (hn : PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (zero_l K) T t a b n)
    (hm : PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (zero_l K) T t a b m) : n = m := by
  obtain ⟨ha, hb, p, hp, hn⟩ := hn
  obtain ⟨_, _, q, hq, hm⟩ := hm
  have hpq := pairing_unique_l K hT hSpec ha hb hp hq
  subst q
  exact node_unique_l K hT hSpec hn hm

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientConstructorTotal
