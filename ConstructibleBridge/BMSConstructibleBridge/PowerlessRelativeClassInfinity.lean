import BMSConstructibleBridge.PowerlessRelativeClassBasicAxioms
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage
import BMSConstructibleBridge.SecondOrderOmegaOrdinal

/-! # 实际相对类子模型的无穷公理

原商的最小归纳对象是实际序数，故由序数覆盖进入相对类。其全部成员及
后继见证因类传递性也进入类，纯相对化无穷句因而在原 Z₂ 中可推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassInfinity

open Logic FirstOrder
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    SecondOrderInfinityAxiom.formula_m.TrueIn (structure_l hℳ B hBase) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  change ∃ w : type_l hℳ B, (∃ e : type_l hℳ B, (∀ x : type_l hℳ B, ¬mem_l hℳ x.val e.val) ∧ mem_l hℳ e.val w.val) ∧
    ∀ a : type_l hℳ B, mem_l hℳ a.val w.val → ∃ b : type_l hℳ B, mem_l hℳ b.val w.val ∧
      ∀ z : type_l hℳ B, mem_l hℳ z.val b.val ↔ mem_l hℳ z.val a.val ∨ z = a
  refine ⟨⟨K.omega, hωClass⟩, ?_, ?_⟩
  · obtain ⟨e, he, heω⟩ := K.omega_spec.1.1
    exact ⟨⟨e, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωClass heω⟩, fun z => he z.val, heω⟩
  · intro a ha
    obtain ⟨b, hb, hSucc⟩ := K.omega_spec.1.2 a.val ha
    refine ⟨⟨b, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωClass hb⟩, hb, fun z => ?_⟩
    exact (hSucc z.val).trans (or_congr Iff.rfl ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m SecondOrderInfinityAxiom.formula_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassInfinity
