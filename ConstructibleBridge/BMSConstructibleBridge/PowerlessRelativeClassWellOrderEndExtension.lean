import BMSConstructibleBridge.SecondOrderWellOrderEndExtension
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeClassRelationAmbientMembers
import BMSConstructibleBridge.SecondOrderWellOrderEndExtensionUnique

/-! # 同一相对类内的环境良序初段扩张图

全部参数及新载体属于同一相对类，旧、新良序均覆盖环境子集。
有界正文取得类内图及全环境逐值规格，再调用环境最小元证明。
本步骤保持旧比较并排除新成员先于旧成员，不声称跨层递归已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderEndExtension

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderWellOrderEndExtension (body_l body_m body_delta_l body_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

include hBase

theorem exists_l {C D R S : type_l hℳ B}
    (hR : wellOrder_l (ℳ := 𝒱) C.val R.val) (hS : wellOrder_l (ℳ := 𝒱) D.val S.val) :
    ∃ L : type_l hℳ B, wellOrder_l (ℳ := 𝒱) D.val L.val ∧
      ∀ x y : SecondOrderQuotient.type_l hℳ, value_l (ℳ := 𝒱) L.val x y ↔
        SecondOrderQuotient.mem_l hℳ x D.val ∧ SecondOrderQuotient.mem_l hℳ y D.val ∧
          body_l (ℳ₀ := 𝒱) C.val R.val S.val x y := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := body_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒩 [] [.set, .set, .set] := ((Env.empty.pushFree S).pushFree R).pushFree C
  obtain ⟨L, hL⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (φ := φ) (body_delta_l _ _ _ _ _) η D D
  have hRead x y : value_l (ℳ := 𝒱) L.val x y ↔
      SecondOrderQuotient.mem_l hℳ x D.val ∧ SecondOrderQuotient.mem_l hℳ y D.val ∧
        body_l (ℳ₀ := 𝒱) C.val R.val S.val x y :=
    (hL x y).trans (and_congr Iff.rfl (and_congr Iff.rfl (body_formula_l _ _ _ _ _ _)))
  exact ⟨L, SecondOrderWellOrderEndExtension.of_graph_l hR hS hRead, hRead⟩

/-- 完整成员规格固定扩张对象，避免只比较读值的伪唯一性。 -/
theorem exists_unique_l {C D R S : type_l hℳ B}
    (hR : wellOrder_l (ℳ := 𝒱) C.val R.val) (hS : wellOrder_l (ℳ := 𝒱) D.val S.val) :
    ∃! L : type_l hℳ B,
      SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒱) C.val D.val R.val S.val L.val ∧
        wellOrder_l (ℳ := 𝒱) D.val L.val := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := body_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒩 [] [.set, .set, .set] := ((Env.empty.pushFree S).pushFree R).pushFree C
  obtain ⟨L, hMembers⟩ := PowerlessRelativeClassRelationAmbientMembers.exists_l
    (φ := φ) (body_delta_l _ _ _ _ _) η D D
  have hφ x y : φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) ↔
      body_l (ℳ₀ := 𝒱) C.val R.val S.val x y := body_formula_l _ _ _ _ _ _
  have hGraph : SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒱) C.val D.val R.val S.val L.val := by
    intro p
    refine (hMembers p).trans ?_
    constructor
    · rintro ⟨x, y, hx, hy, hxy, hBody⟩
      exact ⟨x, y, hx, hy, (hφ x y).mp hBody, hxy⟩
    · rintro ⟨x, y, hx, hy, hBody, hxy⟩
      exact ⟨x, y, hx, hy, hxy, (hφ x y).mpr hBody⟩
  have hOrder := SecondOrderWellOrderEndExtension.of_graph_l hR hS
    (SecondOrderWellOrderEndExtensionUnique.reading_l hGraph)
  exact ⟨L, ⟨hGraph, hOrder⟩, fun T hT =>
    Subtype.ext (SecondOrderWellOrderEndExtensionUnique.unique_l hT.1 hGraph)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderEndExtension
