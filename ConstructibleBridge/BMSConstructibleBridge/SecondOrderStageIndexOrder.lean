import BMSConstructibleBridge.SecondOrderOrdinalAmbientOrder
import BMSConstructibleBridge.SecondOrderComparisonNativeConfiguration
import BMSConstructibleBridge.PowerlessRelativeClassWellOrderPullbackAmbient
import BMSConstructibleBridge.SecondOrderFiniteParameterEnvelope

/-! # 实际阶段指标的环境集合良序

沿实际单射 J 拉回序数隶属序。临时类只用于造图；良序结论及比较读数
都回到原商模型，最小元覆盖任意环境子集。J 是指标函数，N 才是序图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderStageIndexOrder

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 不需要指标满射；只有比较配置本身另外要求覆盖全部阶段。 -/
theorem exists_l {I J A : type_l hℳ}
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A)
    (hJ : map_l (ℳ := 𝒱) J I A) (hInject : injective_l (ℳ := 𝒱) J) :
    ∃ N, wellOrder_l (ℳ := 𝒱) I N ∧ ∀ i j,
      mem_l hℳ i I → mem_l hℳ j I →
      (value_l (ℳ := 𝒱) N i j ↔ ∃ a b,
        value_l (ℳ := 𝒱) J i a ∧ value_l (ℳ := 𝒱) J j b ∧ mem_l hℳ a b) := by
  obtain ⟨R, hR, hRRead⟩ := SecondOrderOrdinalAmbientOrder.exists_l (hℳ := hℳ) hα
  obtain ⟨B, hBase, hIB, hParameters⟩ := SecondOrderFiniteParameterEnvelope.exists_l hℳ I [J, A, R]
  let 𝒩 := PowerlessRelativeClassStructure.structure_l hℳ B hBase
  let I' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨I, PowerlessRelativeClassCorrespondence.base_l hℳ hBase hIB⟩
  let J' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨J, PowerlessRelativeClassCorrespondence.base_l hℳ hBase (hParameters J (by simp))⟩
  let A' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨A, PowerlessRelativeClassCorrespondence.base_l hℳ hBase (hParameters A (by simp))⟩
  let R' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨R, PowerlessRelativeClassCorrespondence.base_l hℳ hBase (hParameters R (by simp))⟩
  have hMap : map_l (ℳ := 𝒩) J' I' A' :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) J' I' A').mpr hJ
  have hInjection : injective_l (ℳ := 𝒩) J' := by
    intro x y a hxa hya
    exact Subtype.ext (hInject x.val y.val a.val
      ((PowerlessRelativeClassFunctionAbsolute.value_l J' x a).mp hxa)
      ((PowerlessRelativeClassFunctionAbsolute.value_l J' y a).mp hya))
  obtain ⟨N, hN, hRead⟩ := PowerlessRelativeClassWellOrderPullbackAmbient.exists_l
    (X := I') (Y := A') (F := J') (R := R') hMap hInjection hR
  let lift (Z : PowerlessRelativeClassStructure.type_l hℳ B) (x : type_l hℳ)
      (hx : mem_l hℳ x Z.val) : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Z.property hx⟩
  have hCompare (x y : PowerlessRelativeClassStructure.type_l hℳ B) :
      PowerlessRelativeClassWellOrderPullback.comparison_l (ℳ₀ := 𝒩) A' J' R' x y ↔
        ∃ a b, value_l (ℳ := 𝒱) J x.val a ∧ value_l (ℳ := 𝒱) J y.val b ∧ mem_l hℳ a b := by
    constructor
    · rintro ⟨a, b, _, _, hxa, hyb, hab⟩
      exact ⟨a.val, b.val,
        (PowerlessRelativeClassFunctionAbsolute.value_l J' x a).mp hxa,
        (PowerlessRelativeClassFunctionAbsolute.value_l J' y b).mp hyb,
        ((hRRead a.val b.val).mp
          ((PowerlessRelativeClassFunctionAbsolute.value_l R' a b).mp hab)).2.2⟩
    · rintro ⟨a, b, hxa, hyb, hab⟩
      have ha := (SecondOrderFunctionLaws.value_mem_l hℳ hJ hxa).2
      have hb := (SecondOrderFunctionLaws.value_mem_l hℳ hJ hyb).2
      exact ⟨lift A' a ha, lift A' b hb, ha, hb,
        (PowerlessRelativeClassFunctionAbsolute.value_l J' x (lift A' a ha)).mpr hxa,
        (PowerlessRelativeClassFunctionAbsolute.value_l J' y (lift A' b hb)).mpr hyb,
        (PowerlessRelativeClassFunctionAbsolute.value_l R' (lift A' a ha) (lift A' b hb)).mpr
          ((hRRead a b).mpr ⟨ha, hb, hab⟩)⟩
  refine ⟨N.val, hN, ?_⟩
  intro i j hi hj
  exact (PowerlessRelativeClassFunctionAbsolute.value_l N (lift I' i hi) (lift I' j hj)).symm.trans
    ((hRead (lift I' i hi) (lift I' j hj)).trans
      ((and_iff_right hi).trans ((and_iff_right hj).trans (hCompare _ _))))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderStageIndexOrder
