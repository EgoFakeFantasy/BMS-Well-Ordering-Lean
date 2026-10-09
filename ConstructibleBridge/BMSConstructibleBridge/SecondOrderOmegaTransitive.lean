import BMSConstructibleBridge.SecondOrderFiniteEnumerationRoots
import BMSConstructibleBridge.PowerlessFiniteClosureProperties

/-! # 原图商内 ω 的传递性

按模型内部数域的根码精确覆盖证明，不对内部自然数作宿主归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmegaTransitive

open Logic FirstOrder PowerlessBMSQuotientCoding SecondOrderQuotient

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {ω k x : type_l hℳ} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hk : mem_l hℳ k ω) (hx : mem_l hℳ x k) : mem_l hℳ x ω := by
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hEq := SecondOrderOmega.unique_l hℳ hω C.omega_spec
  rw [hEq] at hk ⊢
  obtain ⟨i, hi⟩ := numberCode_surjective_l C ⟨k, hk⟩
  have hik : (numberCode_l C i).val = k := congrArg Subtype.val hi
  rw [← hik] at hx
  obtain ⟨j, _, hj⟩ := SecondOrderFiniteEnumerationRoots.member_number_l C i x hx
  rw [← hj]
  exact (numberCode_l C j).property

theorem closure_transitive_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {ω c : type_l hℳ} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hc : PowerlessFiniteClosureSyntax.closure_l (ℳ := structure_l hℳ) ω ω c) :
    PowerlessFiniteClosureProperties.transitive_l (ℳ := structure_l hℳ) c :=
  PowerlessFiniteClosureProperties.transitive_of_l (x := ω) (SecondOrderWeakSetTheory.models_l hℳ)
    (fun _ hk _ hx => member_l hℳ hω hk hx) hc

#print axioms member_l
#print axioms closure_transitive_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmegaTransitive
