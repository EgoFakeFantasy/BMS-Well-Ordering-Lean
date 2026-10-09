import BMSConstructibleBridge.PowerlessRelativeLimitFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassTriangular
import BMSConstructibleBridge.PowerlessBMSQuotientPairingBounds

/-! # 指定极限层中的同编码三角递推图

全有限 ω 序列集已经在给定层中时，多项式检查是该层参数上的 Δ₀ 关系。
实际类内三角图由全坐标规格放回同一层；保留原 K，不放大层界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitTriangular

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase

include hBase in
theorem member_l (K : source_coding_l hℳ) (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {ω e N T : type_l hℳ B} (hωC : mem_l hℳ ω.val C) (heC : mem_l hℳ e.val C)
    (hNC : mem_l hℳ N.val C) (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val)
    (hMap : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val) : mem_l hℳ T.val C := by
  let η : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree N.val).pushFree e.val).pushFree ω.val
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := PowerlessBoundedTriangular.formula_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  have hParams : ∀ s (v : Variable [SetTheory.SetSort.set, .set, .set] s),
      mem_l hℳ (η.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hωC
    | there v => cases v with
      | here => exact heC
      | there v => cases v with
        | here => exact hNC
        | there v => nomatch v
  have hRead (x y : SecondOrderQuotient.type_l hℳ) (hx : mem_l hℳ x K.omega)
      (hy : mem_l hℳ y K.omega) : value_l (ℳ := 𝒱) T.val x y ↔
      PowerlessBoundedTriangular.holds_l («𝒩» := 𝒱) K.omega
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N.val x y := by
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨x, hx⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨y, hy⟩
    have hi' : (numberCode_l K i).val = x := congrArg Subtype.val hi
    have hj' : (numberCode_l K j).val = y := congrArg Subtype.val hj
    simpa only [hi', hj'] using (hSpec i j).trans (PowerlessBoundedTriangular.instance_l K hN i j).symm
  have hValue (x y : SecondOrderQuotient.type_l hℳ) : value_l (ℳ := 𝒱) T.val x y ↔
      mem_l hℳ x ω.val ∧ mem_l hℳ y ω.val ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
    have hφ := PowerlessBoundedTriangular.formula_l ((η.pushFree y).pushFree x)
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
    change φ.satisfies ((η.pushFree y).pushFree x) ↔
      PowerlessBoundedTriangular.holds_l («𝒩» := 𝒱) ω.val e.val N.val x y at hφ
    rw [hω, he] at hφ
    rw [hω]
    constructor
    · intro hxy
      have hMem := SecondOrderFunctionProperties.value_mem_l hℳ hMap hxy
      exact ⟨hMem.1, hMem.2, hφ.mpr ((hRead x y hMem.1 hMem.2).mp hxy)⟩
    · rintro ⟨hx, hy, hxy⟩
      exact (hRead x y hx hy).mpr (hφ.mp hxy)
  exact PowerlessRelativeLimitFunctionRelation.member_l hBase hLimit hC
    (PowerlessBoundedTriangular.delta_l _ _ _ _ _) η hωC hωC hParams
    (hω.symm ▸ hMap) hValue

theorem exists_l (K : source_coding_l hℳ) (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (ω e N : type_l hℳ B) (hωC : mem_l hℳ ω.val C) (heC : mem_l hℳ e.val C)
    (hNC : mem_l hℳ N.val C) (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val) :
    ∃ T : type_l hℳ B, mem_l hℳ T.val C ∧ PowerlessTriangular.triangular_l (ℳ := 𝒩) ω e T ∧
      map_l (ℳ := 𝒱) T.val K.omega K.omega ∧ PowerlessBMSQuotientPairingBounds.spec_l K T.val := by
  obtain ⟨T, hT, hSpec⟩ := PowerlessRelativeClassTriangular.exists_spec_l K ω e N hω he hN
  have hMap := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) T ω ω).mp hT.1
  rw [hω] at hMap
  exact ⟨T, member_l (hBase := hBase) K hLimit hC hωC heC hNC hω he hN hMap hSpec, hT, hMap, hSpec⟩

#print axioms member_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitTriangular
