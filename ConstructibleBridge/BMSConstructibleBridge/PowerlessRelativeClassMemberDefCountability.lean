import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionIndexEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalOrderStep
import BMSConstructibleBridge.PowerlessRelativeClassOntoCountability

/-! # 已有原 Def 候选的实际类内可数性

已有候选提供 Def 包含于同一全槽行族的证明。本文件只枚举其实际指标、
复合统一行映射，再把最小编号逆图限制到 Def；空 Def 不需要另取默认成员。
不重证明代码覆盖，不假定完整类模型，也不构造超限枚举历史。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassMemberDefCountability

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 已有实际类枚举的任意类子集可数，包括空子集；无需子集的 ω 满射。 -/
theorem subset_l {ω Y D H : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω) (hH : map_l (ℳ := 𝒩) H ω Y)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val Y.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) H i y)
    (hSubset : subset_l (ℳ := 𝒱) D.val Y.val) :
    PowerlessRelativeOrdinalCutoff.countable_l B ω.val D.val := by
  have hOntoD : ∀ d : type_l hℳ B, mem_l hℳ d.val D.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) H i d :=
    fun d hd => hOnto d (hSubset d.val hd)
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassEnumerationSection.exists_l hω hOntoD
  have hHRaw := (PowerlessRelativeClassFunctionAbsolute.map_l H ω Y).mp hH
  refine ⟨R.val, R.property, (PowerlessRelativeClassFunctionAbsolute.map_l R D ω).mp hR, ?_⟩
  intro x z i hxi hzi
  obtain ⟨hx, hi⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase R hxi
  obtain ⟨hz, _⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase R hzi
  let x' : type_l hℳ B := ⟨x, hx⟩
  let z' : type_l hℳ B := ⟨z, hz⟩
  let i' : type_l hℳ B := ⟨i, hi⟩
  have hix := ((hRead x' i').mp
    ((PowerlessRelativeClassFunctionAbsolute.value_l R x' i').mpr hxi)).2.2.1
  have hiz := ((hRead z' i').mp
    ((PowerlessRelativeClassFunctionAbsolute.value_l R z' i').mpr hzi)).2.2.1
  exact SecondOrderFunctionProperties.value_unique_l hℳ hHRaw
    ((PowerlessRelativeClassFunctionAbsolute.value_l H i' x').mp hix)
    ((PowerlessRelativeClassFunctionAbsolute.value_l H i' z').mp hiz)

/-- 消费已经证明的候选包含，不另加母集良序或 Sat 正确性前提。 -/
theorem of_candidate_l {ω A P Sat D L E : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω) (hE : map_l (ℳ := 𝒩) E ω A)
    (hOnto : ∀ a : type_l hℳ B, mem_l hℳ a.val A.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) E i a)
    (hCandidate : PowerlessRelativeClassCanonicalOrderStep.candidate_l
      (hBase := hBase) ω A P Sat D L) :
    PowerlessRelativeOrdinalCutoff.countable_l B ω.val D.val := by
  obtain ⟨S, I, J, U, Q, Y, hIndex, _, hRows, _, hSubset, _⟩ := hCandidate
  obtain ⟨G, hG, hGOnto⟩ := PowerlessRelativeClassSatisfactionIndexEnumeration.of_spec_l
    hω hE hOnto hIndex.1 hIndex.2.1 hIndex.2.2.1
  obtain ⟨Y₀, F, hF, hFOnto, _, hRange⟩ := PowerlessRelativeClassRowFamily.exists_l J A Q
  have hYEq : Y₀ = Y := by
    apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    exact fun y => (hRange y).trans (hRows y).symm
  subst Y₀
  obtain ⟨H, hH, hRead⟩ := PowerlessRelativeClassFunctionComposition.exists_l hG hF
  have hHOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val Y.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) H i y := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := hFOnto y hy
    obtain ⟨i, hi, hit⟩ := hGOnto t ht
    exact ⟨i, hi, (hRead i y).mpr ⟨hi, hy, t, ht, hit, hty⟩⟩
  exact subset_l hω hH hHOnto hSubset

#print axioms subset_l
#print axioms of_candidate_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassMemberDefCountability
