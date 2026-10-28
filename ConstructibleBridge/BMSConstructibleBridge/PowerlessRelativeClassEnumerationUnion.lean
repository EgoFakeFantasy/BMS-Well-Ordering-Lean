import BMSConstructibleBridge.PowerlessRelativeClassInterleave
import BMSConstructibleBridge.SecondOrderDoublingPartition

/-! # 两份类内满射枚举的并集枚举

由实际内部倍数图填满交错接口的全部索引条件；得到的满射图仍属于同一类。
不以环境满射替代类内满射，也不在 Type 中选择两个枚举的值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationUnion

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {ω G H U V W : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hG : map_l (ℳ := structure_l hℳ B hBase) G ω U)
    (hH : map_l (ℳ := structure_l hℳ B hBase) H ω V)
    (hGOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val U.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) G i y)
    (hHOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val V.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) H i y)
    (hW : ∀ y : type_l hℳ B, mem_l hℳ y.val W.val ↔ mem_l hℳ y.val U.val ∨ mem_l hℳ y.val V.val) :
    ∃ F : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) F ω W ∧
      ∀ y : type_l hℳ B, mem_l hℳ y.val W.val → ∃ n : type_l hℳ B,
        mem_l hℳ n.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) F n y := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  obtain ⟨α, C₀, hC₀, hωC₀⟩ := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  obtain ⟨β, hβ, hαβ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ α
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hC₀)
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  have hωC := PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC₀ hC K.omega hωC₀
  obtain ⟨D, ω', hω', hD, hPoint⟩ := PowerlessRelativeClassDoubling.exists_l K hBase hC
    ⟨⟨α, hαβ⟩, hNoMax⟩ hωC
  have hEq : ω' = ω := Subtype.ext (hω'.trans hωEq.symm)
  subst ω'
  have hD' : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) D.val K.omega K.omega := by
    have h := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) D ω ω).mp hD
    change map_l (ℳ := SecondOrderQuotient.structure_l hℳ) D.val ω.val ω.val at h
    simpa only [hωEq] using h
  have hEven (i j n : type_l hℳ B) (hi : mem_l hℳ i.val ω.val) (hj : mem_l hℳ j.val ω.val)
      (hin : value_l (ℳ := structure_l hℳ B hBase) D i n)
      (hjn : value_l (ℳ := structure_l hℳ B hBase) D j n) : i = j := by
    apply Subtype.ext
    exact SecondOrderDoublingPartition.even_unique_l K hD' hPoint (hωEq ▸ hi) (hωEq ▸ hj)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) D i n).mp hin)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) D j n).mp hjn)
  have hOdd (i j t v n : type_l hℳ B) (hi : mem_l hℳ i.val ω.val) (hj : mem_l hℳ j.val ω.val)
      (hit : value_l (ℳ := structure_l hℳ B hBase) D i t)
      (hjv : value_l (ℳ := structure_l hℳ B hBase) D j v)
      (ht : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) t n)
      (hv : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) v n) : i = j := by
    apply Subtype.ext
    exact SecondOrderDoublingPartition.odd_unique_l K hD' hPoint
      (i := i.val) (j := j.val) (t := t.val) (v := v.val) (n := n.val) (hωEq ▸ hi) (hωEq ▸ hj)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) D i t).mp hit)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) D j v).mp hjv)
      ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t n).mp ht)
      ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) v n).mp hv)
  have hDisjoint (i j t n : type_l hℳ B) (hi : mem_l hℳ i.val ω.val) (hj : mem_l hℳ j.val ω.val)
      (hin : value_l (ℳ := structure_l hℳ B hBase) D i n)
      (hjt : value_l (ℳ := structure_l hℳ B hBase) D j t)
      (ht : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) t n) : False :=
    SecondOrderDoublingPartition.disjoint_l K hD' hPoint (hωEq ▸ hi) (hωEq ▸ hj)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) D i n).mp hin)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) D j t).mp hjt)
      ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t n).mp ht)
  have hCover (n : type_l hℳ B) (hn : mem_l hℳ n.val ω.val) :
      (∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) D i n) ∨
        ∃ i t : type_l hℳ B, mem_l hℳ i.val ω.val ∧ mem_l hℳ t.val ω.val ∧
          value_l (ℳ := structure_l hℳ B hBase) D i t ∧ PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) t n := by
    have h := SecondOrderDoublingPartition.cover_l K (D := D.val) hPoint n.val (hωEq ▸ hn)
    rw [← hωEq] at h
    rcases h with ⟨i, hi, hin⟩ | ⟨i, t, hi, ht, hit, htn⟩
    · let i' : type_l hℳ B := ⟨i, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hi⟩
      exact Or.inl ⟨i', hi, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) D i' n).mpr hin⟩
    · let i' : type_l hℳ B := ⟨i, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hi⟩
      let t' : type_l hℳ B := ⟨t, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property ht⟩
      exact Or.inr ⟨i', t', hi, ht,
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) D i' t').mpr hit,
        (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t' n).mpr htn⟩
  obtain ⟨F, hF, hValue⟩ := PowerlessRelativeClassInterleave.exists_l hG hH hW hEven hOdd hDisjoint hCover
  refine ⟨F, hF, fun y hy => ?_⟩
  rcases (hW y).mp hy with hy | hy
  · obtain ⟨i, hi, hiy⟩ := hGOnto y hy
    obtain ⟨n, hn, _⟩ := hD.2 i hi
    exact ⟨n, hn.1, (hValue n y).mpr ⟨hn.1, Or.inl ⟨i, hi, hn.2, hiy⟩⟩⟩
  · obtain ⟨i, hi, hiy⟩ := hHOnto y hy
    obtain ⟨t, ht, _⟩ := hD.2 i hi
    obtain ⟨n, hn, htn⟩ := ((PowerlessNatural.inductive_iff_l
      (ℳ := structure_l hℳ B hBase) ω).mp hω.1).2 t ht.1
    exact ⟨n, hn, (hValue n y).mpr ⟨hn, Or.inr ⟨i, t, hi, ht.1, ht.2, htn, hiy⟩⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationUnion
