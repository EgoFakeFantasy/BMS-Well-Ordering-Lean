import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute
import BMSConstructibleBridge.PowerlessEvaluationTags

/-! # 弱相对类中的自然数闭包与共同界

后继闭包来自实际 ω 的归纳集性质，两个内部自然数的共同界来自原商 ω
的序数证书。不要求类满足完整源理论，也不把内部自然数当作外部 Nat。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNaturalProperties

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  {ω : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)

include hω

theorem zero_mem_l {e : type_l hℳ B} (he : PowerlessNatural.zero_l (ℳ := structure_l hℳ B hBase) e) :
    mem_l hℳ e.val ω.val := by
  obtain ⟨z, hz, hzω⟩ := ((PowerlessNatural.inductive_iff_l (ℳ := structure_l hℳ B hBase) ω).mp hω.1).1
  have hEq : z = e := (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    z e (fun x => ⟨fun h => (hz x h).elim, fun h => (he x h).elim⟩)
  change member_l (structure_l hℳ B hBase) e ω
  exact hEq ▸ hzω

theorem successor_exists_l {a : type_l hℳ B} (ha : mem_l hℳ a.val ω.val) :
    ∃ b : type_l hℳ B, mem_l hℳ b.val ω.val ∧
      PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) a b :=
  ((PowerlessNatural.inductive_iff_l (ℳ := structure_l hℳ B hBase) ω).mp hω.1).2 a ha

theorem successor_mem_l {a b : type_l hℳ B} (ha : mem_l hℳ a.val ω.val)
    (hab : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) a b) : mem_l hℳ b.val ω.val := by
  obtain ⟨c, hc, hsucc⟩ := successor_exists_l hω ha
  have hEq : c = b := (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    c b (fun x => (hsucc x).trans (hab x).symm)
  have hVal : c.val = b.val := congrArg Subtype.val hEq
  exact hVal ▸ hc

theorem tags_natural_l {e t₁ t₂ t₃ : type_l hℳ B}
    (ht : PowerlessEvaluationTags.tags_l (ℳ := structure_l hℳ B hBase) e t₁ t₂ t₃) :
    mem_l hℳ e.val ω.val ∧ mem_l hℳ t₁.val ω.val ∧
      mem_l hℳ t₂.val ω.val ∧ mem_l hℳ t₃.val ω.val := by
  have he := zero_mem_l hω ht.1
  have h₁ := successor_mem_l hω he ht.2.1
  have h₂ := successor_mem_l hω h₁ ht.2.2.1
  exact ⟨he, h₁, h₂, successor_mem_l hω h₂ ht.2.2.2⟩

theorem upper_l {a b : type_l hℳ B} (ha : mem_l hℳ a.val ω.val) (hb : mem_l hℳ b.val ω.val) :
    ∃ c : type_l hℳ B, mem_l hℳ c.val ω.val ∧
      subset_l (ℳ := structure_l hℳ B hBase) a c ∧ subset_l (ℳ := structure_l hℳ B hBase) b c := by
  have ho := SecondOrderOmegaOrdinal.ordinal_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω)
  rcases ho.wellOrder.linear.compare a.val ha b.val hb with hEq | hab | hba
  · exact ⟨a, ha, fun _ h => h, fun x hx => (hEq x.val).mpr hx⟩
  · exact ⟨b, hb, fun x hx => ho.wellOrder.linear.trans x.val (ho.transitive a.val ha x.val hx)
      a.val ha b.val hb hx hab, fun _ h => h⟩
  · exact ⟨a, ha, fun _ h => h, fun x hx => ho.wellOrder.linear.trans x.val (ho.transitive b.val hb x.val hx)
      b.val hb a.val ha hx hba⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNaturalProperties
