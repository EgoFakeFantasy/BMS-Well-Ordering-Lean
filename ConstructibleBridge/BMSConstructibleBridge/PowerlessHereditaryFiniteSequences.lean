import BMSConstructibleBridge.PowerlessHereditaryFiniteSequenceEnvelope
import BMSConstructibleBridge.PowerlessHereditaryOmega

/-! # 遗传参数的全部内部有限序列集仍遗传

将 X 的包络与 ω 的包络取二元并，取得同时含 X、ω 的统一可数传递包络。
之后形成有限序列图码的两层对闭包并作单点扩张，不增加 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFiniteSequences

open Logic FirstOrder ThirdOrderSemantics PowerlessHereditaryClassInternals
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {ω X : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hX : envelope_l (𝒩 := structure_l hℳ B hBase) X) :
    ∃ S : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω X S ∧
      envelope_l (𝒩 := structure_l hℳ B hBase) S := by
  obtain ⟨U, G, ω', hXU, hUTrans, hω', hG, hGOnto⟩ := hX
  have hEq : ω' = ω := Subtype.ext (SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mp hω')
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω))
  subst ω'
  have hOmegaEnvelope := (correspondence_l (hBase := hBase) ω).mp
    (PowerlessHereditaryOmega.member_l hℳ hBase
      ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω))
  obtain ⟨V, H, ω', hωV, hVTrans, hω', hH, hHOnto⟩ := hOmegaEnvelope
  have hEq : ω' = ω := Subtype.ext (SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mp hω')
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω))
  subst ω'
  obtain ⟨T, hT, F, hF, hOnto⟩ := PowerlessRelativeClassBinaryUnion.enumeration_l hω hG hH hGOnto hHOnto
  have hTTrans (x : type_l hℳ B) (hx : mem_l hℳ x.val T.val)
      (y : type_l hℳ B) (hy : mem_l hℳ y.val x.val) : mem_l hℳ y.val T.val :=
    (hT y).mpr (((hT x).mp hx).elim
      (fun hxU => Or.inl (hUTrans x hxU y hy)) (fun hxV => Or.inr (hVTrans x hxV y hy)))
  exact PowerlessHereditaryFiniteSequenceEnvelope.exists_l hω
    ((hT X).mpr (Or.inl hXU)) ((hT ω).mpr (Or.inr hωV)) hTTrans hF hOnto

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFiniteSequences
