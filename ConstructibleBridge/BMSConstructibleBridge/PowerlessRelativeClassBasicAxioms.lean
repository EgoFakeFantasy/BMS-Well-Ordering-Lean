import BMSConstructibleBridge.PowerlessRelativeClassRelativization
import BMSConstructibleBridge.PowerlessRelativeClassBasicClosure

/-! # 相对类子模型的空集与并集公理

不仅在环境中取得对象：同时证明见证属于指定类、内层存在量词与实际类域
一致，再将公理的纯相对化句回传原 Z₂。完整分离和 Collection 尚待另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBasicAxioms

open Logic FirstOrder
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
  (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)

theorem empty_l : SecondOrderAxioms.empty_m.TrueIn (structure_l hℳ B hBase) := by
  change ∃ e : type_l hℳ B, ∀ z : type_l hℳ B, ¬mem_l hℳ z.val e.val
  obtain ⟨e, he⟩ := SecondOrderQuotient.empty_l hℳ
  exact ⟨⟨e, PowerlessRelativeClassBasicClosure.empty_l hℳ hBase he⟩, fun z => he z.val⟩

theorem union_l : SecondOrderUnion.formula_m.TrueIn (structure_l hℳ B hBase) := by
  change ∀ a : type_l hℳ B, ∃ u : type_l hℳ B, ∀ z : type_l hℳ B,
    mem_l hℳ z.val u.val ↔ ∃ y : type_l hℳ B, mem_l hℳ y.val a.val ∧ mem_l hℳ z.val y.val
  intro a
  have h := SecondOrderUnion.models_l hℳ
  change ∀ a : SecondOrderQuotient.type_l hℳ, ∃ u, ∀ z,
    mem_l hℳ z u ↔ ∃ y, mem_l hℳ y a ∧ mem_l hℳ z y at h
  obtain ⟨u, hu⟩ := h a.val
  refine ⟨⟨u, PowerlessRelativeClassBasicClosure.union_l hℳ hBase a.property hu⟩, fun z => ?_⟩
  refine (hu z.val).trans ⟨?_, ?_⟩
  · rintro ⟨y, hya, hzy⟩
    exact ⟨⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase a.property hya⟩, hya, hzy⟩
  · rintro ⟨y, hya, hzy⟩
    exact ⟨y.val, hya, hzy⟩

theorem empty_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m SecondOrderAxioms.empty_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => empty_l h𝒩 B hBase)

theorem union_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m SecondOrderUnion.formula_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => union_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBasicAxioms
