import BMSConstructibleBridge.PowerlessRelativeClassInfinity

/-! # 相对类子模型与原商共享同一个 ω

先核验空集、后继及归纳性的双向绝对性。最小性不能仅限制量词：反向利用
已经证明属于类的原商 ω，比较两个归纳对象后以外延性对齐。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOmegaAbsolute

open Logic FirstOrder
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase in
theorem empty_l (e : type_l hℳ B) :
    (∀ z : type_l hℳ B, ¬mem_l hℳ z.val e.val) ↔ ∀ z, ¬mem_l hℳ z e.val := by
  constructor
  · intro h z hz
    exact h ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase e.property hz⟩ hz
  · exact fun h z => h z.val

include hBase in
theorem successor_l (a b : type_l hℳ B) :
    (∀ z : type_l hℳ B, mem_l hℳ z.val b.val ↔ mem_l hℳ z.val a.val ∨ z = a) ↔
      PowerlessRelativeHierarchySemantics.successor_l hℳ a.val b.val := by
  constructor
  · intro h z
    constructor
    · intro hz
      let z' : type_l hℳ B := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase b.property hz⟩
      rcases (h z').mp hz with hza | he
      · exact Or.inl hza
      · exact Or.inr (congrArg Subtype.val he)
    · rintro (hza | rfl)
      · let z' : type_l hℳ B := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase a.property hza⟩
        exact (h z').mpr (Or.inl hza)
      · exact (h a).mpr (Or.inr rfl)
  · intro h z
    exact (h z.val).trans (or_congr Iff.rfl ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem inductive_l (i : type_l hℳ B) :
    ThirdOrderSemantics.inductive_l (ℳ := structure_l hℳ B hBase) i ↔ SecondOrderOmega.inductive_l hℳ i.val := by
  change ((∃ e : type_l hℳ B, (∀ z : type_l hℳ B, ¬mem_l hℳ z.val e.val) ∧ mem_l hℳ e.val i.val) ∧
    ∀ a : type_l hℳ B, mem_l hℳ a.val i.val → ∃ b : type_l hℳ B, mem_l hℳ b.val i.val ∧
      ∀ z : type_l hℳ B, mem_l hℳ z.val b.val ↔ mem_l hℳ z.val a.val ∨ z = a) ↔ _
  constructor
  · rintro ⟨⟨e, he, hei⟩, h⟩
    refine ⟨⟨e.val, (empty_l (hBase := hBase) e).mp he, hei⟩, ?_⟩
    intro a hai
    let a' : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase i.property hai⟩
    obtain ⟨b, hbi, hSucc⟩ := h a' hai
    exact ⟨b.val, hbi, (successor_l (hBase := hBase) a' b).mp hSucc⟩
  · rintro ⟨⟨e, he, hei⟩, h⟩
    let e' : type_l hℳ B := ⟨e, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase i.property hei⟩
    refine ⟨⟨e', (empty_l (hBase := hBase) e').mpr he, hei⟩, ?_⟩
    intro a hai
    obtain ⟨b, hbi, hSucc⟩ := h a.val hai
    let b' : type_l hℳ B := ⟨b, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase i.property hbi⟩
    exact ⟨b', hbi, (successor_l (hBase := hBase) a b').mpr hSucc⟩

theorem omega_l (w : type_l hℳ B) :
    ThirdOrderSemantics.omega_l (ℳ := structure_l hℳ B hBase) w ↔ SecondOrderOmega.omega_l hℳ w.val := by
  constructor
  · rintro ⟨hInd, hLeast⟩
    obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
    have hωClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
    let o : type_l hℳ B := ⟨K.omega, hωClass⟩
    have ho := (inductive_l (hBase := hBase) o).mpr K.omega_spec.1
    have hw := (inductive_l (hBase := hBase) w).mp hInd
    have hEq : w.val = K.omega := by
      apply SecondOrderQuotient.ext_l hℳ
      intro z
      constructor
      · intro hz
        let z' : type_l hℳ B := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase w.property hz⟩
        exact hLeast o ho z' hz
      · exact K.omega_spec.2 w.val hw z
    rw [hEq]
    exact K.omega_spec
  · intro hw
    refine ⟨(inductive_l (hBase := hBase) w).mpr hw.1, ?_⟩
    intro i hi z hz
    exact hw.2 i.val ((inductive_l (hBase := hBase) i).mp hi) z.val hz

#print axioms omega_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOmegaAbsolute
