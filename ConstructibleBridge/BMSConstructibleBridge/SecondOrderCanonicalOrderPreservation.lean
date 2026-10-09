import BMSConstructibleBridge.SecondOrderCanonicalOrderUniform
import BMSConstructibleBridge.SecondOrderWellOrderCoherentUnionDerives

/-! # 规范 Def 后继保留相容历史的初段关系

直接消费实际完整步骤图，Sat 只作存在见证。旧载体包含性来自原 Def
和母集传递性；读值保持及初段性复用完整扩张图接口，不另设相容公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderPreservation

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem extension_l {ω A P e t₁ t₂ t₃ Pair Valid D E : SecondOrderQuotient.type_l hℳ}
    (h : SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱) ω A P e t₁ t₂ t₃ Pair Valid D E)
    (hTrans : ∀ x y, SecondOrderQuotient.mem_l hℳ x A → SecondOrderQuotient.mem_l hℳ y x →
      SecondOrderQuotient.mem_l hℳ y A) (hDef : SecondOrderMemberDef.spec_l hℳ A D) :
    SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) A P D E := by
  obtain ⟨R, hSat, L, hCandidate, hGraph⟩ := h
  have hAD : subset_l (ℳ := 𝒱) A D := SecondOrderMemberDefProperties.contains_l hℳ hDef hTrans
  have hRead := SecondOrderWellOrderEndExtensionUnique.reading_l (hℳ := hℳ) hGraph
  exact ⟨hAD, fun x y hx hy => SecondOrderWellOrderEndExtension.old_l
      (hℳ := hℳ) (C := A) (D := D) (R := P) (S := L) (L := E) hAD hRead hx hy,
    fun x y hx _ hyx => SecondOrderWellOrderEndExtension.initial_l
      (hℳ := hℳ) (C := A) (D := D) (R := P) (S := L) (L := E) hRead hx hyx⟩

#print axioms extension_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderPreservation
