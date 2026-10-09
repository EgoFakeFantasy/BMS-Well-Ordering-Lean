import BMSConstructibleBridge.PowerlessHereditaryOmega
import BMSConstructibleBridge.PowerlessHereditaryTransitiveSuperset

/-! # 遗传类的实际纯隶属子模型

非空证书来自已经证明属于遗传类的 ω，不抽取 Type 见证。这里验证
外延、正则、无穷和传递超集的语义；逐公式相对化及对象推导另行接线。
没有把此结构宣称为完整 PowerlessTheory 模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryStructure

open Logic FirstOrder
open SecondOrderQuotient (mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

def type_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ) :=
  {x : SecondOrderQuotient.type_l hℳ // PowerlessHereditaryClass.member_l hℳ B x}

def structure_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) : FirstOrder.Structure.{0, 0, 0, u} ℒ where
  Carrier _ := type_l hℳ B
  nonempty _ := by
    obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
    exact ⟨⟨K.omega, PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec⟩⟩
  funcInterp f := nomatch f
  relInterp
    | .membership, .cons x (.cons y .nil) => mem_l hℳ x.val y.val

attribute [local implicit_reducible] structure_l

variable (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
  (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)

theorem ext_l : SetTheory.Extensional
    (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (structure_l hℳ B hBase)) := by
  constructor
  intro a b hab
  apply Subtype.ext
  apply SecondOrderQuotient.ext_l hℳ
  intro z
  constructor
  · intro hz
    exact (hab ⟨z, PowerlessHereditaryClass.transitive_l hℳ a.property hz⟩).mp hz
  · intro hz
    exact (hab ⟨z, PowerlessHereditaryClass.transitive_l hℳ b.property hz⟩).mpr hz

theorem extensionality_l : SecondOrderAxioms.extensionality_m.TrueIn (structure_l hℳ B hBase) := by
  change ∀ a b : type_l hℳ B, (∀ z : type_l hℳ B, mem_l hℳ z.val a.val ↔ mem_l hℳ z.val b.val) → a = b
  exact (ext_l hℳ B hBase).eq_of_same_members

theorem foundation_l : SecondOrderFoundation.formula_m.TrueIn (structure_l hℳ B hBase) := by
  change ∀ a : type_l hℳ B, (∃ b : type_l hℳ B, mem_l hℳ b.val a.val) →
    ∃ b : type_l hℳ B, mem_l hℳ b.val a.val ∧ ∀ z : type_l hℳ B,
      mem_l hℳ z.val b.val → ¬mem_l hℳ z.val a.val
  intro a ⟨b, hba⟩
  have h := SecondOrderFoundation.models_l hℳ
  change ∀ a : SecondOrderQuotient.type_l hℳ, (∃ b, mem_l hℳ b a) →
    ∃ b, mem_l hℳ b a ∧ ∀ z, mem_l hℳ z b → ¬mem_l hℳ z a at h
  obtain ⟨q, hqa, hMin⟩ := h a.val ⟨b.val, hba⟩
  exact ⟨⟨q, PowerlessHereditaryClass.transitive_l hℳ a.property hqa⟩, hqa, fun z hz => hMin z.val hz⟩

theorem infinity_l : SecondOrderInfinityAxiom.formula_m.TrueIn (structure_l hℳ B hBase) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hω := PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec
  change ∃ w : type_l hℳ B, (∃ e : type_l hℳ B,
    (∀ x : type_l hℳ B, ¬mem_l hℳ x.val e.val) ∧ mem_l hℳ e.val w.val) ∧
    ∀ a : type_l hℳ B, mem_l hℳ a.val w.val → ∃ b : type_l hℳ B, mem_l hℳ b.val w.val ∧
      ∀ z : type_l hℳ B, mem_l hℳ z.val b.val ↔ mem_l hℳ z.val a.val ∨ z = a
  refine ⟨⟨K.omega, hω⟩, ?_, ?_⟩
  · obtain ⟨e, he, heω⟩ := K.omega_spec.1.1
    exact ⟨⟨e, PowerlessHereditaryClass.transitive_l hℳ hω heω⟩, fun z => he z.val, heω⟩
  · intro a ha
    obtain ⟨b, hb, hSucc⟩ := K.omega_spec.1.2 a.val ha
    refine ⟨⟨b, PowerlessHereditaryClass.transitive_l hℳ hω hb⟩, hb, fun z => ?_⟩
    exact (hSucc z.val).trans (or_congr Iff.rfl ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem transitive_superset_l : SecondOrderTransitiveSuperset.formula_m.TrueIn (structure_l hℳ B hBase) := by
  change ∀ a : type_l hℳ B, ∃ t : type_l hℳ B,
    (∀ z : type_l hℳ B, mem_l hℳ z.val a.val → mem_l hℳ z.val t.val) ∧
      ∀ x y : type_l hℳ B, mem_l hℳ x.val t.val → mem_l hℳ y.val x.val → mem_l hℳ y.val t.val
  intro a
  obtain ⟨t, ht, hat, hTrans⟩ := PowerlessHereditaryTransitiveSuperset.exists_l hℳ hBase a.property
  exact ⟨⟨t, ht⟩, fun z hz => hTrans a.val hat z.val hz, fun x y hx hy => hTrans x.val hx y.val hy⟩

#print axioms structure_l
#print axioms infinity_l
#print axioms transitive_superset_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryStructure
