import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderGraph
import BMSConstructibleBridge.PowerlessRelativeClassSequenceZeroOrder

/-! # 统一序列关系在定长切片上的读数

用函数定义域唯一性消去关系正文内再次存在量化的长度；这里只要求给定
长度的反自反性。零长度基例使用同一实际关系 L，不另换一个未经对应的序。
这些是随后对象归纳证明的语义辅助接口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderSlices

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceLexicographic (lex_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

/-- 只需要载体上的逐值对应，关系载体外的值无需相等。 -/
theorem wellOrder_congr_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {P R S : carrier_l ℳ₀} (hR : wellOrder_l P R)
    (hEq : ∀ f, member_l ℳ₀ f P → ∀ g, member_l ℳ₀ g P → (value_l R f g ↔ value_l S f g)) :
    wellOrder_l P S := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun f hf hff => hR.1 f hf ((hEq f hf f hf).mpr hff)
  · intro f g k hfgk hfg hgk
    exact (hEq f hfgk.1 k hfgk.2.2).mp (hR.2.1 f g k hfgk
      ((hEq f hfgk.1 g hfgk.2.1).mpr hfg) ((hEq g hfgk.2.1 k hfgk.2.2).mpr hgk))
  · intro f g hfg
    rcases hR.2.2.1 f g hfg with h | h | h
    · exact Or.inl ((hEq f hfg.1 g hfg.2).mp h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((hEq g hfg.2 f hfg.1).mp h))
  · intro U hU
    obtain ⟨f, hf, hMin⟩ := hR.2.2.2 U hU
    exact ⟨f, hf, fun g hg hgf => hMin g hg ((hEq g (hU.1 g hg) f (hU.1 f hf)).mpr hgf)⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem same_length_l {ω n X R f g : type_l hℳ B}
    (hn : member_l ClassModel n ω) (hIrr : ¬member_l ClassModel n n)
    (hf : map_l (ℳ := ClassModel) f n X) (hg : map_l (ℳ := ClassModel) g n X) :
    shortlex_l (ℳ₀ := ClassModel) ω X R f g ↔ lex_l (ℳ₀ := ClassModel) n X R f g := by
  constructor
  · rintro ⟨k, j, _, _, hfk, hgj, hCompare⟩
    have hkn := PowerlessRelativeClassFunctionProperties.domain_unique_l hfk hf
    have hjn := PowerlessRelativeClassFunctionProperties.domain_unique_l hgj hg
    subst k
    subst j
    exact hCompare.elim (fun h => (hIrr h).elim) (fun h => h.2)
  · exact fun h => ⟨n, n, hn, hn, hf, hg, Or.inr ⟨rfl, h⟩⟩

theorem at_length_l {ω n X R L P : type_l hℳ B}
    (hn : member_l ClassModel n ω) (hIrr : ¬member_l ClassModel n n)
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) n X P)
    (hRead : ∀ f g, value_l (ℳ := ClassModel) L f g ↔ shortlex_l (ℳ₀ := ClassModel) ω X R f g) :
    ∀ f, member_l ClassModel f P → ∀ g, member_l ClassModel g P →
      (value_l (ℳ := ClassModel) L f g ↔ lex_l (ℳ₀ := ClassModel) n X R f g) := by
  intro f hf g hg
  exact (hRead f g).trans (same_length_l hn hIrr ((hP f).mp hf) ((hP g).mp hg))

theorem zero_l {ω n X R L P : type_l hℳ B}
    (hn : member_l ClassModel n ω) (hEmpty : ∀ i, ¬member_l ClassModel i n)
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) n X P)
    (hRead : ∀ f g, value_l (ℳ := ClassModel) L f g ↔ shortlex_l (ℳ₀ := ClassModel) ω X R f g) :
    wellOrder_l (ℳ := ClassModel) P L := by
  apply wellOrder_congr_l (PowerlessRelativeClassSequenceZeroOrder.wellOrder_l hEmpty hP)
  intro f hf g hg
  apply iff_of_false
  · rintro ⟨p, hp, _⟩
    exact hEmpty p hp
  · intro hfg
    obtain ⟨i, _, _, hi, _⟩ := (at_length_l hn (hEmpty n) hP hRead f hf g hg).mp hfg
    exact hEmpty i hi

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderSlices
