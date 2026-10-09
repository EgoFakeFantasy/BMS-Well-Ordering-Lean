import BMSConstructibleBridge.SecondOrderMixedImage
import BMSConstructibleBridge.PowerlessBMSQuotientCoding
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.SecondOrderFunctions

/-! # 从内部数函数到固定根图的实际集合函数

两端通过混合有序对像连接。值域只要求各输出根表示的对象属于给定集合，
无需 Collection，也不对内部数作外部归纳或抽取根代表选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootedNumericFunction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) (R : SecondOrderModel.set_l ℳ)
    (hR : ∀ m, SecondOrderDomain.wf_l R m) {E : SecondOrderModel.set_l ℳ}
    (hE : SecondOrderFunctions.function_l E) (Y : type_l hℳ)
    (hRange : ∀ n m, SecondOrderPairing.relation_l E n m →
      mem_l hℳ (SecondOrderQuotient.mk_l hℳ ⟨R, m, hR m⟩) Y) :
    ∃ F : type_l hℳ, map_l (ℳ := 𝒱) F K.omega Y ∧
      ∀ x y, value_l (ℳ := 𝒱) F x y ↔ ∃ n m,
        SecondOrderPairing.relation_l E n m ∧ x = (numberCode_l K n).val ∧
          y = SecondOrderQuotient.mk_l hℳ ⟨R, m, hR m⟩ := by
  have hRoots (n m : SecondOrderModel.num_l ℳ) (_ : SecondOrderPairing.relation_l E n m) :
      SecondOrderDomain.wf_l K.less n ∧ SecondOrderDomain.wf_l R m :=
    ⟨SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec n, hR m⟩
  obtain ⟨F, hF⟩ := SecondOrderMixedImage.exists_l hℳ K.less R E hRoots
  have hGraph (p : type_l hℳ) : mem_l hℳ p F ↔ ∃ n m,
      SecondOrderPairing.relation_l E n m ∧ SecondOrderPairObjects.ordered_l hℳ
        (numberCode_l K n).val (SecondOrderQuotient.mk_l hℳ ⟨R, m, hR m⟩) p := by
    refine (hF p).trans ⟨?_, ?_⟩
    · rintro ⟨n, m, hnm, hp⟩
      exact ⟨n, m, hnm, hp⟩
    · rintro ⟨n, m, hnm, hp⟩
      exact ⟨n, m, hnm, hp⟩
  have hValue (x y : type_l hℳ) : value_l (ℳ := 𝒱) F x y ↔ ∃ n m,
      SecondOrderPairing.relation_l E n m ∧ x = (numberCode_l K n).val ∧
        y = SecondOrderQuotient.mk_l hℳ ⟨R, m, hR m⟩ := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨n, m, hnm, hp'⟩ := (hGraph p).mp hp
      exact ⟨n, m, hnm, (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp').mp rfl⟩
    · rintro ⟨n, m, hnm, rfl, rfl⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (numberCode_l K n).val
        (SecondOrderQuotient.mk_l hℳ ⟨R, m, hR m⟩)
      exact ⟨p, (hGraph p).mpr ⟨n, m, hnm, hp⟩, hp⟩
  refine ⟨F, ⟨?_, ?_⟩, hValue⟩
  · intro p hp
    obtain ⟨n, m, hnm, hPair⟩ := (hGraph p).mp hp
    exact ⟨(numberCode_l K n).val, SecondOrderQuotient.mk_l hℳ ⟨R, m, hR m⟩,
      (numberCode_l K n).property, hRange n m hnm, hPair⟩
  · intro x hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hnx : (numberCode_l K n).val = x := congrArg Subtype.val hn
    obtain ⟨m, hnm, _⟩ := hE n
    refine ⟨SecondOrderQuotient.mk_l hℳ ⟨R, m, hR m⟩,
      ⟨hRange n m hnm, (hValue x _).mpr ⟨n, m, hnm, hnx.symm, rfl⟩⟩, ?_⟩
    rintro y ⟨_, hy⟩
    obtain ⟨i, j, hij, hxi, hyj⟩ := (hValue x y).mp hy
    have hin : i = n := numberCode_injective_l K (Subtype.ext (hxi.symm.trans hnx.symm))
    subst i
    have hjm : j = m := (hE n).unique hij hnm
    subst j
    exact hyj

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootedNumericFunction
