import BMSConstructibleBridge.PowerlessRelativeHierarchySemantics

/-! # 纯历史方程在前驱值一致时的确定性

后继前驱唯一性只用当前序数的隶属线序；极限值由两函数在所有前驱的值
一致及商外延性确定。本引理没有模型外良基性或 Collection 前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchyStep

open Logic FirstOrder
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem successor_member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {a b : type_l hℳ} (h : successor_l hℳ a b) : mem_l hℳ a b :=
  (h a).mpr (Or.inr rfl)

theorem successor_unique_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {a b c : type_l hℳ} (hc : SetTheory.Structure.IsOrdinal (quotient_l hℳ) c)
    (ha : successor_l hℳ a c) (hb : successor_l hℳ b c) : a = b := by
  have hac := successor_member_l hℳ ha
  have hbc := successor_member_l hℳ hb
  rcases (hb a).mp hac with hab | hab
  · rcases (ha b).mp hbc with hba | hba
    · exact False.elim (hc.wellOrder.linear.irrefl a hac
        (hc.wellOrder.linear.trans a hac b hbc a hac hab hba))
    · exact hba.symm
  · exact hab

theorem successor_not_limit_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {a b : type_l hℳ} (hb : SetTheory.Structure.IsOrdinal (quotient_l hℳ) b)
    (ha : successor_l hℳ a b) (hLimit : limit_l hℳ b) : False := by
  have hab := successor_member_l hℳ ha
  obtain ⟨c, hcb, hac⟩ := hLimit.2 a hab
  rcases (ha c).mp hcb with hca | hca
  · exact hb.wellOrder.linear.irrefl a hab
      (hb.wellOrder.linear.trans a hab c hcb a hab hac hca)
  · subst c
    exact hb.wellOrder.linear.irrefl a hab hac

theorem unique_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B a f g y z : type_l hℳ} (ha : SetTheory.Structure.IsOrdinal (quotient_l hℳ) a)
    (hTotalF : ∀ b, mem_l hℳ b a → ∃ d, SecondOrderFunctionObjects.value_l hℳ f b d)
    (hTotalG : ∀ b, mem_l hℳ b a → ∃ d, SecondOrderFunctionObjects.value_l hℳ g b d)
    (hPast : ∀ b, mem_l hℳ b a → ∀ d e,
      SecondOrderFunctionObjects.value_l hℳ f b d → SecondOrderFunctionObjects.value_l hℳ g b e → d = e)
    (hy : step_l hℳ B f a y) (hz : step_l hℳ B g a z) : y = z := by
  rcases hy with ⟨hEmpty, hy⟩ | ⟨b, d, hb, hd, hDef⟩ | ⟨hLimit, hUnion⟩
  · rcases hz with ⟨_, hz⟩ | ⟨b, _, hb, _, _⟩ | ⟨hLimit, _⟩
    · exact hy.trans hz.symm
    · exact False.elim (hEmpty b (successor_member_l hℳ hb))
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
  · rcases hz with ⟨hEmpty, _⟩ | ⟨c, e, hc, he, hDef'⟩ | ⟨hLimit, _⟩
    · exact False.elim (hEmpty b (successor_member_l hℳ hb))
    · have hbc := successor_unique_l hℳ ha hb hc
      subst c
      have hde := hPast b (successor_member_l hℳ hb) d e hd he
      subst e
      exact SecondOrderMemberDef.unique_l hℳ hDef hDef'
    · exact False.elim (successor_not_limit_l hℳ ha hb hLimit)
  · rcases hz with ⟨hEmpty, _⟩ | ⟨b, _, hb, _, _⟩ | ⟨_, hUnion'⟩
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
    · exact False.elim (successor_not_limit_l hℳ ha hb hLimit)
    · apply SecondOrderQuotient.ext_l hℳ
      intro x
      constructor
      · intro hx
        obtain ⟨b, d, hb, hd, hxd⟩ := (hUnion x).mp hx
        obtain ⟨e, he⟩ := hTotalG b hb
        have hde := hPast b hb d e hd he
        exact (hUnion' x).mpr ⟨b, e, hb, he, hde ▸ hxd⟩
      · intro hx
        obtain ⟨b, e, hb, he, hxe⟩ := (hUnion' x).mp hx
        obtain ⟨d, hd⟩ := hTotalF b hb
        have hde := hPast b hb d e hd he
        exact (hUnion x).mpr ⟨b, d, hb, hd, hde.symm ▸ hxe⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchyStep
