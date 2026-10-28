import BMSConstructibleBridge.PowerlessRelativeClassSequenceSplit

/-! # 内部序列字典序的后继分解

比较点之前的所有坐标具有相同值；后继长度的比较分解为前缀比较，
或者前缀相等后的末项比较。不要求比较关系已经良序，也不使用
内部 ω 的外部标准性、Collection 或宿主选择函数。
本模块仅提供语义辅助接口，对象公式与原 Z₂ 推导由调用方封装。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceLexicographic

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceSplit (prefix_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

def lex_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (n X R f g : carrier_l ℳ₀) : Prop :=
  ∃ i a b, member_l ℳ₀ i n ∧ member_l ℳ₀ a X ∧ member_l ℳ₀ b X ∧
    value_l f i a ∧ value_l g i b ∧ value_l R a b ∧ prefix_l i X f g

/-- 在共同前缀内，逐值相等可以双向搬运到较短前缀。 -/
private theorem prefix_congr_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {n i X f f' g g' : carrier_l ℳ₀}
    (hSub : ∀ j, member_l ℳ₀ j i → member_l ℳ₀ j n)
    (hp : prefix_l (ℳ₀ := ℳ₀) n X f g) (hp' : prefix_l (ℳ₀ := ℳ₀) n X f' g') :
    prefix_l (ℳ₀ := ℳ₀) i X f f' ↔ prefix_l (ℳ₀ := ℳ₀) i X g g' := by
  constructor
  · intro h j hj x hx
    exact (hp' j (hSub j hj) x hx).trans
      ((h j hj x hx).trans (hp j (hSub j hj) x hx).symm)
  · intro h j hj x hx
    exact (hp' j (hSub j hj) x hx).symm.trans
      ((h j hj x hx).trans (hp j (hSub j hj) x hx))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem successor_l {n m X R f f' g g' a b : type_l hℳ B}
    (hf : map_l (ℳ := ClassModel) f m X) (hf' : map_l (ℳ := ClassModel) f' m X)
    (hg : map_l (ℳ := ClassModel) g n X) (hg' : map_l (ℳ := ClassModel) g' n X)
    (hSucc : ∀ i : type_l hℳ B, member_l ClassModel i m ↔ member_l ClassModel i n ∨ i = n)
    (hTrans : ∀ i : type_l hℳ B, member_l ClassModel i n →
      ∀ j : type_l hℳ B, member_l ClassModel j i → member_l ClassModel j n)
    (hPrefix : prefix_l (ℳ₀ := ClassModel) n X f g)
    (hPrefix' : prefix_l (ℳ₀ := ClassModel) n X f' g')
    (hLast : value_l (ℳ := ClassModel) f n a) (hLast' : value_l (ℳ := ClassModel) f' n b) :
    lex_l (ℳ₀ := ClassModel) m X R f f' ↔
      lex_l (ℳ₀ := ClassModel) n X R g g' ∨ g = g' ∧ value_l (ℳ := ClassModel) R a b := by
  constructor
  · rintro ⟨i, c, d, hi, hc, hd, hfi, hfi', hR, hBefore⟩
    rcases (hSucc i).mp hi with hin | hin
    · exact Or.inl ⟨i, c, d, hin, hc, hd,
        (hPrefix i hin c hc).mpr hfi, (hPrefix' i hin d hd).mpr hfi', hR,
        (prefix_congr_l (hTrans i hin) hPrefix hPrefix').mp hBefore⟩
    · subst i
      have hca : c = a := PowerlessRelativeClassFunctionProperties.value_unique_l hf hfi hLast
      have hdb : d = b := PowerlessRelativeClassFunctionProperties.value_unique_l hf' hfi' hLast'
      subst c
      subst d
      refine Or.inr ⟨?_, hR⟩
      have hSame : prefix_l (ℳ₀ := ClassModel) n X g g' :=
        (prefix_congr_l (fun _ hj => hj) hPrefix hPrefix').mp hBefore
      apply PowerlessRelativeClassFunctionRestriction.ext_l hg hg'
      intro i x
      constructor
      · intro hix
        have hmem := PowerlessRelativeClassFunctionProperties.value_mem_l hg hix
        exact (hSame i hmem.1 x hmem.2).mpr hix
      · intro hix
        have hmem := PowerlessRelativeClassFunctionProperties.value_mem_l hg' hix
        exact (hSame i hmem.1 x hmem.2).mp hix
  · rintro (hLex | ⟨hgg, hR⟩)
    · obtain ⟨i, c, d, hi, hc, hd, hgi, hgi', hR, hBefore⟩ := hLex
      exact ⟨i, c, d, (hSucc i).mpr (Or.inl hi), hc, hd,
        (hPrefix i hi c hc).mp hgi, (hPrefix' i hi d hd).mp hgi', hR,
        (prefix_congr_l (hTrans i hi) hPrefix hPrefix').mpr hBefore⟩
    · subst g'
      refine ⟨n, a, b, (hSucc n).mpr (Or.inr rfl),
        (PowerlessRelativeClassFunctionProperties.value_mem_l hf hLast).2,
        (PowerlessRelativeClassFunctionProperties.value_mem_l hf' hLast').2, hLast, hLast', hR, ?_⟩
      intro i hi x hx
      exact (hPrefix' i hi x hx).symm.trans (hPrefix i hi x hx)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceLexicographic
