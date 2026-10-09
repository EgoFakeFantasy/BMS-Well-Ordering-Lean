import BMSConstructibleBridge.PowerlessRelativeClassOmegaAmbientOrder

/-! # 环境良序向类子模型的安全限制

本方向只减少子集量词范围。类内子集的全部环境成员由传递性
提升入类，再使用环境最小元条款。逆方向不能仅由此接口取得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAmbientWellOrder

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

/-- 良序谓词只读取载体上的比较；子集使用同一图即可，无须收集新图。 -/
theorem of_subset_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {A D R : carrier_l 𝒱} (hR : wellOrder_l (ℳ := 𝒱) A R)
    (hD : subset_l (ℳ := 𝒱) D A) : wellOrder_l (ℳ := 𝒱) D R := by
  refine ⟨fun x hx => hR.1 x (hD x hx), ?_, ?_, ?_⟩
  · intro x y z hxyz
    exact hR.2.1 x y z ⟨hD x hxyz.1, hD y hxyz.2.1, hD z hxyz.2.2⟩
  · intro x y hxy
    exact hR.2.2.1 x y ⟨hD x hxy.1, hD y hxy.2⟩
  · intro U hU
    exact hR.2.2.2 U ⟨fun x hx => hD x (hU.1 x hx), hU.2⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

theorem restrict_l {A R : type_l hℳ B}
    (hR : wellOrder_l (ℳ := SecondOrderQuotient.structure_l hℳ) A.val R.val) :
    wellOrder_l (ℳ := structure_l hℳ B hBase) A R := by
  have hValue := PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hxx
    exact hR.1 x.val hx ((hValue x x).mp hxx)
  · intro x y z hxyz hxy hyz
    exact (hValue x z).mpr (hR.2.1 x.val y.val z.val hxyz
      ((hValue x y).mp hxy) ((hValue y z).mp hyz))
  · intro x y hxy
    rcases hR.2.2.1 x.val y.val hxy with hlt | hEq | hgt
    · exact Or.inl ((hValue x y).mpr hlt)
    · exact Or.inr (Or.inl (Subtype.ext hEq))
    · exact Or.inr (Or.inr ((hValue y x).mpr hgt))
  · intro U hU
    have hSubset : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) U.val A.val := by
      intro y hy
      let y' : type_l hℳ B := ⟨y,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase U.property hy⟩
      exact hU.1 y' hy
    obtain ⟨x, hx⟩ := hU.2
    obtain ⟨y, hy, hMin⟩ := hR.2.2.2 U.val ⟨hSubset, x.val, hx⟩
    let y' : type_l hℳ B := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase U.property hy⟩
    exact ⟨y', hy, fun z hz hlt => hMin z.val hz ((hValue z y').mp hlt)⟩

#print axioms restrict_l

/-- 三个线序条款可沿成员提升传输；环境最小元条款必须另证。 -/
theorem of_minimum_l {A R : type_l hℳ B}
    (hR : wellOrder_l (ℳ := structure_l hℳ B hBase) A R)
    (hMinimum : ∀ U : SecondOrderQuotient.type_l hℳ,
      subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) U A.val ∧
        (∃ x, SecondOrderQuotient.mem_l hℳ x U) →
          ∃ x, SecondOrderQuotient.mem_l hℳ x U ∧ ∀ y,
            SecondOrderQuotient.mem_l hℳ y U →
              ¬value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val y x) :
    wellOrder_l (ℳ := SecondOrderQuotient.structure_l hℳ) A.val R.val := by
  let lift (x : SecondOrderQuotient.type_l hℳ) (hx : SecondOrderQuotient.mem_l hℳ x A.val) :
      type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hx⟩
  have hValue := PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R
  refine ⟨?_, ?_, ?_, hMinimum⟩
  · intro x hx hxx
    exact hR.1 (lift x hx) hx ((hValue _ _).mpr hxx)
  · intro x y z hxyz hxy hyz
    exact (hValue _ _).mp (hR.2.1 (lift x hxyz.1) (lift y hxyz.2.1) (lift z hxyz.2.2)
      hxyz ((hValue _ _).mpr hxy) ((hValue _ _).mpr hyz))
  · intro x y hxy
    rcases hR.2.2.1 (lift x hxy.1) (lift y hxy.2) hxy with hlt | hEq | hgt
    · exact Or.inl ((hValue _ _).mp hlt)
    · exact Or.inr (Or.inl (congrArg Subtype.val hEq))
    · exact Or.inr (Or.inr ((hValue _ _).mp hgt))

#print axioms of_minimum_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAmbientWellOrder
