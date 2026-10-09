import BMSConstructibleBridge.PowerlessHereditaryRelativization
import BMSConstructibleBridge.PowerlessHereditarySubset
import BMSConstructibleBridge.PowerlessRelativeClassBasicClosure

/-! # 遗传子模型的空集与并集公理

空对象属于 ω。并集在相对类中构造后，利用遗传传递超集和子集封闭
获得遗传性。这不需要两个包络的共同枚举，也不证明配对或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryBasicAxioms

open Logic FirstOrder
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
  (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)

theorem empty_l : SecondOrderAxioms.empty_m.TrueIn (structure_l hℳ B hBase) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  obtain ⟨e, he, heω⟩ := K.omega_spec.1.1
  change ∃ e : type_l hℳ B, ∀ z : type_l hℳ B, ¬mem_l hℳ z.val e.val
  exact ⟨⟨e, PowerlessHereditaryClass.transitive_l hℳ
    (PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec) heω⟩, fun z => he z.val⟩

theorem union_l : SecondOrderUnion.formula_m.TrueIn (structure_l hℳ B hBase) := by
  change ∀ a : type_l hℳ B, ∃ u : type_l hℳ B, ∀ z : type_l hℳ B,
    mem_l hℳ z.val u.val ↔ ∃ y : type_l hℳ B, mem_l hℳ y.val a.val ∧ mem_l hℳ z.val y.val
  intro a
  have h := SecondOrderUnion.models_l hℳ
  change ∀ a : SecondOrderQuotient.type_l hℳ, ∃ u, ∀ z,
    mem_l hℳ z u ↔ ∃ y, mem_l hℳ y a ∧ mem_l hℳ z y at h
  obtain ⟨u, hu⟩ := h a.val
  have huClass := PowerlessRelativeClassBasicClosure.union_l hℳ hBase
    (PowerlessHereditaryClass.contained_l hℳ hBase a.property) hu
  obtain ⟨T, hT, haT, hTrans⟩ := PowerlessHereditaryTransitiveSuperset.exists_l hℳ hBase a.property
  have huT : ∀ z, mem_l hℳ z u → mem_l hℳ z T := by
    intro z hz
    obtain ⟨y, hya, hzy⟩ := (hu z).mp hz
    exact hTrans y (hTrans a.val haT y hya) z hzy
  refine ⟨⟨u, PowerlessHereditarySubset.member_l hℳ hBase hT huClass huT⟩, fun z => ?_⟩
  refine (hu z.val).trans ⟨?_, ?_⟩
  · rintro ⟨y, hya, hzy⟩
    exact ⟨⟨y, PowerlessHereditaryClass.transitive_l hℳ a.property hya⟩, hya, hzy⟩
  · rintro ⟨y, hya, hzy⟩
    exact ⟨y.val, hya, hzy⟩

theorem empty_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessHereditaryRelativization.guarded_m SecondOrderAxioms.empty_m)) :=
  PowerlessHereditaryRelativization.derives_m _ (fun _ h𝒩 B hBase => empty_l h𝒩 B hBase)

theorem union_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessHereditaryRelativization.guarded_m SecondOrderUnion.formula_m)) :=
  PowerlessHereditaryRelativization.derives_m _ (fun _ h𝒩 B hBase => union_l h𝒩 B hBase)

#print axioms union_l
#print axioms empty_derives_m
#print axioms union_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryBasicAxioms
