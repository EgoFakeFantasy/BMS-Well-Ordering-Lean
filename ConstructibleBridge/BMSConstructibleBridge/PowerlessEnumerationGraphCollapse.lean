import BMSConstructibleBridge.PowerlessHereditaryGraphPresentation

/-! # 传递包络枚举的任意精确成员图

图只需精确读取同一枚举，不必是某次构造产生的指定实数。
内部良基性由边等价传输；坍缩正确性消费实际纯求值正文和成员封闭。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEnumerationGraphCollapse

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {T f : SecondOrderQuotient.type_l hℳ}
    (hTrans : ∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T)
    (hMap : SecondOrderFunctionObjects.map_l hℳ f K.omega T)
    (hOnto : ∀ y, mem_l hℳ y T → ∃ x, mem_l hℳ x K.omega ∧ SecondOrderFunctionObjects.value_l hℳ f x y)
    (R : SecondOrderModel.set_l ℳ)
    (hEdge : ∀ n m, SecondOrderPairing.relation_l R n m ↔
      PowerlessHereditaryGraphPresentation.edge_l (ℳ₀ := 𝒱) T f (numberCode_l K n).val (numberCode_l K m).val) :
    ∃ hWf : ∀ n, SecondOrderDomain.wf_l R n, ∀ r X,
      ThirdOrderSemantics.value_l (ℳ := 𝒱) f (numberCode_l K r).val X → mk_l hℳ ⟨R, r, hWf r⟩ = X := by
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  let η : Env 𝒱 [] [.set] := Env.empty.pushFree f
  have hRead (a y : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies ((η.pushFree a).pushFree y) ↔ ThirdOrderSemantics.value_l (ℳ := 𝒱) f a y :=
    PowerlessValueBounded.formula_l ((η.pushFree a).pushFree y)
      (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have hTotal n : ∃ y, φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y) := by
    obtain ⟨y, ⟨_, hy⟩, _⟩ := hMap.2 (numberCode_l K n).val (numberCode_l K n).property
    exact ⟨y, (hRead _ y).mpr hy⟩
  have hUnique n y z (hy : φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y))
      (hz : φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree z)) : y = z :=
    SecondOrderFunctionProperties.value_unique_l hℳ hMap ((hRead _ y).mp hy) ((hRead _ z).mp hz)
  have hSem n m : PowerlessHereditaryGraphPresentation.edge_l (ℳ₀ := 𝒱) T f
      (numberCode_l K n).val (numberCode_l K m).val ↔ ∃ y z,
        φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y) ∧
        φ.satisfies ((η.pushFree (numberCode_l K m).val).pushFree z) ∧ mem_l hℳ y z := by
    constructor
    · rintro ⟨y, z, _, _, hy, hz, hyz⟩
      exact ⟨y, z, (hRead _ y).mpr hy, (hRead _ z).mpr hz, hyz⟩
    · rintro ⟨y, z, hy, hz, hyz⟩
      have hy' := (hRead _ y).mp hy
      have hz' := (hRead _ z).mp hz
      exact ⟨y, z, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hy').2,
        (SecondOrderFunctionProperties.value_mem_l hℳ hMap hz').2, hy', hz', hyz⟩
  obtain ⟨R₀, hEdge₀, hWf₀⟩ := PowerlessBMSClassRelation.exists_l K φ η hTotal hUnique
  have hEdge' n m := (hEdge n m).trans (hSem n m)
  have hWf n : SecondOrderDomain.wf_l R n := SecondOrderDomain.mono_l R₀ R n
    (fun a b hab => (hEdge₀ a b).mpr ((hEdge' a b).mp hab)) (hWf₀ n)
  have hClosed n y (hy : φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y))
      z (hzy : mem_l hℳ z y) : ∃ m,
        φ.satisfies ((η.pushFree (numberCode_l K m).val).pushFree z) := by
    have hyT := (SecondOrderFunctionProperties.value_mem_l hℳ hMap ((hRead _ y).mp hy)).2
    obtain ⟨a, ha, haz⟩ := hOnto z (hTrans y hyT z hzy)
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨a, ha⟩
    have hm' : (numberCode_l K m).val = a := congrArg Subtype.val hm
    exact ⟨m, (hRead _ z).mpr (hm'.symm ▸ haz)⟩
  exact ⟨hWf, fun r X hX => PowerlessBMSClassCollapse.agrees_l K φ η R hWf hUnique hEdge'
    hClosed r X ((hRead _ X).mpr hX)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEnumerationGraphCollapse
