import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderInduction

/-! # 统一序列关系的严格线序性质

不同长度由内部 ω 的隶属序比较；相同长度直接复用已证的同一关系图
上的切片良序。此处不选择长度函数，也不将长度识别成外部自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderLinear

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l)
open PowerlessRelativeClassSequenceLexicographic (lex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem comparison_l {ω n m X R L f g : type_l hℳ B}
    (hn : member_l ClassModel n ω) (hm : member_l ClassModel m ω)
    (hf : map_l (ℳ := ClassModel) f n X) (hg : map_l (ℳ := ClassModel) g m X)
    (hRead : ∀ f g, value_l (ℳ := ClassModel) L f g ↔ shortlex_l (ℳ₀ := ClassModel) ω X R f g) :
    value_l (ℳ := ClassModel) L f g ↔ member_l ClassModel n m ∨ n = m ∧ lex_l (ℳ₀ := ClassModel) n X R f g := by
  refine (hRead f g).trans ⟨?_, ?_⟩
  · rintro ⟨i, j, _, _, hfi, hgj, hCompare⟩
    have hin := PowerlessRelativeClassFunctionProperties.domain_unique_l hfi hf
    have hjm := PowerlessRelativeClassFunctionProperties.domain_unique_l hgj hg
    subst i
    subst j
    exact hCompare
  · exact fun h => ⟨n, m, hn, hm, hf, hg, h⟩

theorem linear_l {ω X R L S : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω) (hR : wellOrder_l (ℳ := ClassModel) X R)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω X S)
    (hRead : ∀ f g, value_l (ℳ := ClassModel) L f g ↔ shortlex_l (ℳ₀ := ClassModel) ω X R f g) :
    (∀ f, member_l ClassModel f S → ¬value_l (ℳ := ClassModel) L f f) ∧
    (∀ f g h, member_l ClassModel f S ∧ member_l ClassModel g S ∧ member_l ClassModel h S →
      value_l (ℳ := ClassModel) L f g → value_l (ℳ := ClassModel) L g h → value_l (ℳ := ClassModel) L f h) ∧
    (∀ f g, member_l ClassModel f S ∧ member_l ClassModel g S →
      value_l (ℳ := ClassModel) L f g ∨ f = g ∨ value_l (ℳ := ClassModel) L g f) := by
  have hAll := PowerlessRelativeClassSequenceOrderInduction.all_l hω hR hRead
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω)
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨n, hn, hfn⟩ := (hS f).mp hf
    obtain ⟨P, hP⟩ := PowerlessRelativeClassSequenceSlices.of_omega_l (hBase := hBase) (X := X) hω hn
    exact (hAll n hn P hP).1 f ((hP f).mpr hfn)
  · intro f g h hMembers hfg hgh
    obtain ⟨n, hn, hfn⟩ := (hS f).mp hMembers.1
    obtain ⟨m, hm, hgm⟩ := (hS g).mp hMembers.2.1
    obtain ⟨k, hk, hhk⟩ := (hS h).mp hMembers.2.2
    have hnm := (comparison_l hn hm hfn hgm hRead).mp hfg
    have hmk := (comparison_l hm hk hgm hhk hRead).mp hgh
    rcases hnm with hnm | ⟨hnm, _⟩
    · apply (comparison_l hn hk hfn hhk hRead).mpr
      rcases hmk with hmk | ⟨hmk, _⟩
      · exact Or.inl (hOrd.wellOrder.linear.trans n.val hn m.val hm k.val hk hnm hmk)
      · subst k
        exact Or.inl hnm
    · subst m
      rcases hmk with hnk | ⟨hnk, _⟩
      · exact (comparison_l hn hk hfn hhk hRead).mpr (Or.inl hnk)
      · subst k
        obtain ⟨P, hP⟩ := PowerlessRelativeClassSequenceSlices.of_omega_l (hBase := hBase) (X := X) hω hn
        exact (hAll n hn P hP).2.1 f g h
          ⟨(hP f).mpr hfn, (hP g).mpr hgm, (hP h).mpr hhk⟩ hfg hgh
  · intro f g hMembers
    obtain ⟨n, hn, hfn⟩ := (hS f).mp hMembers.1
    obtain ⟨m, hm, hgm⟩ := (hS g).mp hMembers.2
    rcases hOrd.wellOrder.linear.compare n.val hn m.val hm with hSame | hnm | hmn
    · have hEq : n = m := Subtype.ext (SecondOrderQuotient.ext_l hℳ n.val m.val hSame)
      subst m
      obtain ⟨P, hP⟩ := PowerlessRelativeClassSequenceSlices.of_omega_l (hBase := hBase) (X := X) hω hn
      exact (hAll n hn P hP).2.2.1 f g ⟨(hP f).mpr hfn, (hP g).mpr hgm⟩
    · exact Or.inl ((comparison_l hn hm hfn hgm hRead).mpr (Or.inl hnm))
    · exact Or.inr (Or.inr ((comparison_l hm hn hgm hfn hRead).mpr (Or.inl hmn)))

#print axioms linear_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderLinear
