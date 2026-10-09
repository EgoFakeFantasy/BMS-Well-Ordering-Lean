import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives

/-! # 任意类内全有限序列集的原商规格

已构造的规范序列集具有全原商规格。类内外延性将任意满足同一类内规格的
集合识别为该见证，因此不必重选求值系统中的 S，也不漏掉类外候选赋值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceAbsolute

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

theorem spec_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    {ω A S : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω A S) :
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A.val S.val := by
  obtain ⟨R, hRaw, hClass⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (X := A) hω
  have hEq : S = R := by
    apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    intro f
    exact (hS f).trans (hClass f).symm
  rw [hEq]
  exact hRaw

#print axioms spec_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceAbsolute
