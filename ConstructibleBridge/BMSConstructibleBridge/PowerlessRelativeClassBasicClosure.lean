import BMSConstructibleBridge.PowerlessRelativeClassPair
import BMSConstructibleBridge.SecondOrderMemberDefBasicClosure

/-! # 相对并类中的空对象与并集闭包

每个构造落在一个实际后继层的 Def 中；所有见证仍留在 Prop。源模型的
公理及原 Z₂ 回传由相对化模块验收，不以环境商中的公理替代类内公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBasicClosure

open Logic FirstOrder
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem empty_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B e : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (he : ∀ z, ¬mem_l hℳ z e) : PowerlessRelativeClassCorrespondence.member_l hℳ B e := by
  obtain ⟨a, c, hc, _⟩ := PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase
  obtain ⟨b, d, _, hd, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hc
  exact ⟨b, d, hd, SecondOrderMemberDefBasicClosure.empty_l hℳ hDef he⟩

theorem union_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B X U : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hU : ∀ w, mem_l hℳ w U ↔ ∃ y, mem_l hℳ y X ∧ mem_l hℳ w y) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B U := by
  obtain ⟨a, c, hc, hXc⟩ := hX
  obtain ⟨b, d, _, hd, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hc
  exact ⟨b, d, hd, SecondOrderMemberDefBasicClosure.union_l hℳ hDef hXc
    (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc) hU⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBasicClosure
