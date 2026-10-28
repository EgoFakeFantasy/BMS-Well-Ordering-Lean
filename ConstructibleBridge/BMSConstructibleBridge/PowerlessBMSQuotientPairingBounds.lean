import BMSConstructibleBridge.SecondOrderTriangularPairing
import BMSConstructibleBridge.PowerlessFormulaConstructorBounded
import BMSConstructibleBridge.SecondOrderOmegaOrdinal

/-! # 原 Z₂ 商中的三角配数及严格子码界

只要求实际 ω 自映射与逐内部根码的三角关系规格，不调用源理论模型。
类内实际图构造已提供这两个证书；本模块保留原配数及构造子签名。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientPairingBounds

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def spec_l (K : source_coding_l hℳ) (T : type_l hℳ) : Prop :=
  ∀ i j : SecondOrderModel.num_l ℳ,
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) T (numberCode_l K i).val (numberCode_l K j).val ↔
      SecondOrderTriangularArithmetic.relation_l i j

private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem instance_l (K : source_coding_l hℳ) {T : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (i j : SecondOrderModel.num_l ℳ) (c : type_l hℳ) :
    PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T
      (numberCode_l K i).val (numberCode_l K j).val c ↔
        ∃ v, SecondOrderTriangularArithmetic.relation_l (SecondOrderModel.add_l i j) v ∧
          c = (numberCode_l K (SecondOrderModel.add_l v i)).val := by
  constructor
  · rintro ⟨s, t, hSum, hValue, hOut⟩
    have hs := (PowerlessBMSQuotientRecursion.addition_iff_l K i j s).mp hSum
    obtain ⟨v, hv⟩ := numberCode_surjective_l K
      ⟨t, (SecondOrderFunctionProperties.value_mem_l hℳ hT hValue).2⟩
    have ht : t = (numberCode_l K v).val := (congrArg Subtype.val hv).symm
    rw [hs, ht] at hValue
    rw [ht] at hOut
    exact ⟨v, (hSpec _ _).mp hValue, (PowerlessBMSQuotientRecursion.addition_iff_l K v i c).mp hOut⟩
  · rintro ⟨v, hv, hc⟩
    exact ⟨(numberCode_l K (SecondOrderModel.add_l i j)).val, (numberCode_l K v).val,
      (PowerlessBMSQuotientRecursion.addition_iff_l K i j _).mpr rfl,
      (hSpec _ _).mpr hv, (PowerlessBMSQuotientRecursion.addition_iff_l K v i c).mpr hc⟩

theorem coordinates_l (K : source_coding_l hℳ) {T a b c : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega)
    (hCode : PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (zero_l K) T a b c) : (mem_l hℳ a c ∨ a = c) ∧ (mem_l hℳ b c ∨ b = c) := by
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a, ha⟩
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hb⟩
  have haEq : a = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  have hbEq : b = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
  rw [haEq, hbEq] at hCode ⊢
  obtain ⟨v, hv, rfl⟩ := (instance_l K hT hSpec i j c).mp hCode
  have hNative : SecondOrderTriangularPairing.code_l i j (SecondOrderModel.add_l v i) := ⟨v, hv, rfl⟩
  obtain ⟨h₀, h₁⟩ := SecondOrderTriangularPairing.coordinates_l hℳ hNative
  have hRead (x y : SecondOrderModel.num_l ℳ) (h : x = y ∨ SecondOrderOrder.lt_l x y) :
      mem_l hℳ (numberCode_l K x).val (numberCode_l K y).val ∨
        (numberCode_l K x).val = (numberCode_l K y).val := by
    rcases h with rfl | h
    · exact Or.inr rfl
    · exact Or.inl ((numberCode_mem_iff_lt_l K x y).mpr h)
  exact ⟨hRead _ _ h₀, hRead _ _ h₁⟩

theorem node_bounds_l (K : source_coding_l hℳ) {T t p n : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (hNode : PowerlessFormulaNode.node_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (zero_l K) T t p n) : mem_l hℳ t n ∧ mem_l hℳ p n := by
  obtain ⟨ht, hp, c, hc, hn⟩ := hNode
  obtain ⟨h₀, h₁⟩ := coordinates_l K hT hSpec ht hp hc
  exact ⟨(hn t).mpr h₀, (hn p).mpr h₁⟩

theorem node_natural_l (K : source_coding_l hℳ) {T t p n : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hNode : PowerlessFormulaNode.node_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (zero_l K) T t p n) : mem_l hℳ n K.omega := by
  obtain ⟨ht, _, c, hc, hn⟩ := hNode
  have hcω := PowerlessFormulaConstructorBounded.code_natural_l K hT ht hc
  obtain ⟨m, hmω, hm⟩ := K.omega_spec.1.2 c hcω
  have hEq := PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) (a := c) (b := n) (c := m) hn hm
  exact hEq.symm ▸ hmω

theorem constructor_bounds_l (K : source_coding_l hℳ) {T t a b n : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (hConstructor : PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (zero_l K) T t a b n) : mem_l hℳ a n ∧ mem_l hℳ b n := by
  obtain ⟨ha, hb, p, hp, hn⟩ := hConstructor
  have hpn := (node_bounds_l K hT hSpec hn).2
  have hnω := node_natural_l K hT hn
  have hnOrdinal : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) n :=
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec).mem hnω
  obtain ⟨h₀, h₁⟩ := coordinates_l K hT hSpec ha hb hp
  exact ⟨h₀.elim (fun h => hnOrdinal.transitive p hpn a h) (fun h => h.symm ▸ hpn),
    h₁.elim (fun h => hnOrdinal.transitive p hpn b h) (fun h => h.symm ▸ hpn)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientPairingBounds
