import BMSConstructibleBridge.SecondOrderMemberStructure
import BMSConstructibleBridge.SecondOrderMixedImage
import BMSConstructibleBridge.SecondOrderFunctionLaws
import BMSConstructibleBridge.PowerlessBMSQuotientCoding

/-!
# 非空成员结构的实际集合函数呈现

将已有的全内部数域正规化关系变成商中的集合函数，定义域为商的实际 ω。
逐数函数值与原成员结构呈现严格相同，并满射到母集。这一等式供纯集合
公式读取既有求值器使用；没有把宿主函数当作集合函数，也不要求 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberEnumeration

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open PowerlessBMSQuotientCoding SecondOrderFunctionObjects SecondOrderQuotient

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ theory_m}

theorem exists_l (C : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) :
    ∃ f : type_l hℳ, map_l hℳ f C.omega (mk_l hℳ A) ∧
      (∀ n y, value_l hℳ f (numberCode_l C n).val y ↔
        y = (SecondOrderMemberStructure.value_l hℳ A a ha n).val) ∧
      ∀ y, mem_l hℳ y (mk_l hℳ A) → ∃ x, mem_l hℳ x C.omega ∧ value_l hℳ f x y := by
  obtain ⟨N, hN⟩ := SecondOrderMemberNormalizer.exists_l hℳ A.real A.root a
  have hRoots n b (h : relation_l N n b) :
      SecondOrderDomain.wf_l C.less n ∧ SecondOrderDomain.wf_l A.real b := by
    rw [hN n b] at h
    subst b
    exact ⟨SecondOrderNaturalGraph.wf_l hℳ C.less C.less_spec n,
      SecondOrderDomain.child_l hℳ A.real A.root _ A.wf
        (SecondOrderMemberNormalizer.member_l A.real A.root a ha n)⟩
  obtain ⟨f, hf⟩ := SecondOrderMixedImage.exists_l hℳ C.less A.real N hRoots
  let y (n : num_l ℳ) := (SecondOrderMemberStructure.value_l hℳ A a ha n).val
  have hRead p : mem_l hℳ p f ↔ ∃ n,
      SecondOrderPairObjects.ordered_l hℳ (numberCode_l C n).val (y n) p := by
    refine (hf p).trans ?_
    constructor
    · rintro ⟨n, b, h, hp⟩
      have hb := (hN n b).mp h
      subst b
      exact ⟨n, hp⟩
    · rintro ⟨n, hp⟩
      exact ⟨n, _, (hN n _).mpr rfl, hp⟩
  have hValue x z : value_l hℳ f x z ↔ ∃ n, x = (numberCode_l C n).val ∧ z = y n := by
    constructor
    · rintro ⟨p, hp, hxz⟩
      obtain ⟨n, hn⟩ := (hRead p).mp hp
      exact ⟨n, (SecondOrderPairObjects.ordered_eq_l hℳ hxz hn).mp rfl⟩
    · rintro ⟨n, rfl, rfl⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (numberCode_l C n).val (y n)
      exact ⟨p, (hRead p).mpr ⟨n, hp⟩, hp⟩
  have hNumber n z : value_l hℳ f (numberCode_l C n).val z ↔ z = y n := by
    refine (hValue (numberCode_l C n).val z).trans ?_
    constructor
    · rintro ⟨m, hnm, hz⟩
      have h : n = m := numberCode_injective_l C (Subtype.ext hnm)
      exact h ▸ hz
    · intro hz
      exact ⟨n, rfl, hz⟩
  refine ⟨f, ⟨?_, ?_⟩, hNumber, ?_⟩
  · intro p hp
    obtain ⟨n, hn⟩ := (hRead p).mp hp
    exact ⟨(numberCode_l C n).val, y n, (numberCode_l C n).property,
      (SecondOrderMemberStructure.value_l hℳ A a ha n).property, hn⟩
  · intro x hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨x, hx⟩
    have hn' : (numberCode_l C n).val = x := congrArg Subtype.val hn
    refine ⟨y n, ⟨(SecondOrderMemberStructure.value_l hℳ A a ha n).property,
      (hValue x (y n)).mpr ⟨n, hn'.symm, rfl⟩⟩, ?_⟩
    rintro z ⟨_, hz⟩
    rw [← hn'] at hz
    exact (hNumber n z).mp hz
  · intro z hz
    obtain ⟨n, hn⟩ := SecondOrderMemberStructure.surjective_l hℳ A a ha ⟨z, hz⟩
    have hn' : y n = z := congrArg Subtype.val hn
    exact ⟨(numberCode_l C n).val, (numberCode_l C n).property, (hNumber n z).mpr hn'.symm⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberEnumeration
