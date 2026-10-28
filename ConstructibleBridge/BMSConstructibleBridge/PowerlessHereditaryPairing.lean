import BMSConstructibleBridge.PowerlessHereditaryPairEnvelope
import BMSConstructibleBridge.PowerlessHereditaryRelativization

/-! # 遗传子模型的配对公理

实际配对集合先进入相对类，再由合并后的可数传递包络获得遗传性。
原 Z₂ 出口相对化到遗传域，不把相对类的配对公理冒充遗传域的配对公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryPairing

open Logic FirstOrder
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    SecondOrderPairSet.formula_m.TrueIn (structure_l hℳ B hBase) := by
  change ∀ x y : type_l hℳ B, ∃ p : type_l hℳ B, ∀ z : type_l hℳ B,
    mem_l hℳ z.val p.val ↔ z = x ∨ z = y
  intro x y
  have hxClass := PowerlessHereditaryClass.contained_l hℳ hBase x.property
  have hyClass := PowerlessHereditaryClass.contained_l hℳ hBase y.property
  let X : PowerlessRelativeClassStructure.type_l hℳ B := ⟨x.val, hxClass⟩
  let Y : PowerlessRelativeClassStructure.type_l hℳ B := ⟨y.val, hyClass⟩
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.pair_exists_l hℳ x.val y.val
  let P : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨p, PowerlessRelativeClassPair.pair_l hℳ hBase hxClass hyClass hp⟩
  have hPair (z : PowerlessRelativeClassStructure.type_l hℳ B) :
      mem_l hℳ z.val P.val ↔ z = X ∨ z = Y :=
    (hp z.val).trans (or_congr
      ⟨fun h => Subtype.ext (show z.val = X.val from h), fun h => congrArg Subtype.val h⟩
      ⟨fun h => Subtype.ext (show z.val = Y.val from h), fun h => congrArg Subtype.val h⟩)
  have hX := (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) X).mp x.property
  have hY := (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) Y).mp y.property
  have hP := PowerlessHereditaryPairEnvelope.exists_l hX hY hPair
  have hpHH := (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) P).mpr hP
  refine ⟨⟨p, hpHH⟩, fun z => ?_⟩
  exact (hp z.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessHereditaryRelativization.guarded_m SecondOrderPairSet.formula_m)) :=
  PowerlessHereditaryRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryPairing
