import BMSConstructibleBridge.PowerlessRelativeClassPair

/-! # 相对并类的实际纯隶属子模型

载体是原商中满足纯类定义的对象，不是新的任意源模型。非空性由显式基对象
提供，不抽取 Type 见证。这里核验外延、配对、正则；完整源理论及 Collection
仍未成立，量词相对化与原 Z₂ 推导在后续模块完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassStructure

open Logic FirstOrder
open SecondOrderQuotient (mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

def type_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ) :=
  {x : SecondOrderQuotient.type_l hℳ // PowerlessRelativeClassCorrespondence.member_l hℳ B x}

def structure_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) : FirstOrder.Structure.{0, 0, 0, u} ℒ where
  Carrier _ := type_l hℳ B
  nonempty _ := ⟨⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩⟩
  funcInterp f := nomatch f
  relInterp
    | .membership, .cons x (.cons y .nil) => mem_l hℳ x.val y.val

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
  · intro hza
    let z' : type_l hℳ B := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase a.property hza⟩
    exact (hab z').mp hza
  · intro hzb
    let z' : type_l hℳ B := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase b.property hzb⟩
    exact (hab z').mpr hzb

theorem extensionality_l : SecondOrderAxioms.extensionality_m.TrueIn (structure_l hℳ B hBase) := by
  change ∀ a b : type_l hℳ B, (∀ z : type_l hℳ B, mem_l hℳ z.val a.val ↔ mem_l hℳ z.val b.val) → a = b
  exact (ext_l hℳ B hBase).eq_of_same_members

theorem pairing_l : SecondOrderPairSet.formula_m.TrueIn (structure_l hℳ B hBase) := by
  change ∀ a b : type_l hℳ B, ∃ p : type_l hℳ B, ∀ z : type_l hℳ B,
    mem_l hℳ z.val p.val ↔ z = a ∨ z = b
  intro a b
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.pair_exists_l hℳ a.val b.val
  refine ⟨⟨p, PowerlessRelativeClassPair.pair_l hℳ hBase a.property b.property hp⟩, fun z => ?_⟩
  exact (hp z.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem foundation_l : SecondOrderFoundation.formula_m.TrueIn (structure_l hℳ B hBase) := by
  change ∀ a : type_l hℳ B, (∃ b : type_l hℳ B, mem_l hℳ b.val a.val) →
    ∃ b : type_l hℳ B, mem_l hℳ b.val a.val ∧ ∀ z : type_l hℳ B, mem_l hℳ z.val b.val → ¬mem_l hℳ z.val a.val
  intro a ⟨b, hba⟩
  have h := SecondOrderFoundation.models_l hℳ
  change ∀ a : SecondOrderQuotient.type_l hℳ, (∃ b, mem_l hℳ b a) →
    ∃ b, mem_l hℳ b a ∧ ∀ z, mem_l hℳ z b → ¬mem_l hℳ z a at h
  obtain ⟨q, hqa, hMin⟩ := h a.val ⟨b.val, hba⟩
  exact ⟨⟨q, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase a.property hqa⟩, hqa,
    fun z hz => hMin z.val hz⟩

#print axioms structure_l
#print axioms pairing_l
#print axioms foundation_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassStructure
