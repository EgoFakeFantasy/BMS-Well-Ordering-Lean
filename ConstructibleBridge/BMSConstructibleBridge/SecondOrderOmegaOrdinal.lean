import BMSConstructibleBridge.SecondOrderOrdinalBounded
import BMSConstructibleBridge.SecondOrderOmegaTransitive

/-! # 无 Collection 的原商 ω 序数证书

使用原模型全部内部自然数的精确根码覆盖，并从内部小于的传递性和三歧性
取得序数判据；没有把内部数域识别成标准 Nat，也没有借用完整源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmegaOrdinal

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem ordinal_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {ω : type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) : SetTheory.Structure.IsOrdinal
    (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) ω := by
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  rw [SecondOrderOmega.unique_l hℳ hω C.omega_spec]
  apply SecondOrderOrdinalBounded.of_transitive_l hℳ
  · exact fun x hx y hy => SecondOrderOmegaTransitive.member_l hℳ C.omega_spec hx hy
  · intro k hk y hy z hz
    obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨k, hk⟩
    have hnk : (numberCode_l C n).val = k := congrArg Subtype.val hn
    rw [← hnk] at hy
    obtain ⟨i, hin, hiy⟩ := SecondOrderFiniteEnumerationRoots.member_number_l C n y hy
    rw [← hiy] at hz
    obtain ⟨j, hji, hjz⟩ := SecondOrderFiniteEnumerationRoots.member_number_l C i z hz
    rw [← hjz, ← hnk]
    exact (numberCode_mem_iff_lt_l C j n).mpr (SecondOrderOrder.trans_l hℳ hji hin)
  · intro x y hx hy
    obtain ⟨i, hi⟩ := numberCode_surjective_l C ⟨x, hx⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l C ⟨y, hy⟩
    have hix : (numberCode_l C i).val = x := congrArg Subtype.val hi
    have hjy : (numberCode_l C j).val = y := congrArg Subtype.val hj
    rw [← hix, ← hjy]
    rcases SecondOrderOrder.trichotomy_l hℳ i j with h | rfl | h
    · exact Or.inl ((numberCode_mem_iff_lt_l C i j).mpr h)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ((numberCode_mem_iff_lt_l C j i).mpr h))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmegaOrdinal
