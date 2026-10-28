import BMSConstructibleBridge.PowerlessRelativeClassSequenceIndex
import BMSConstructibleBridge.PowerlessRelativeClassInjectionEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationSection
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives

/-! # 全体内部有限自然数序列的类内满射

精确编码给出单值覆盖关系，最小编号给出集合单射，再填空编号得到实际
ω 满射。长度包括全部内部自然数，不把模型有限序列换成宿主 List。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteNumericEnumeration

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {ω : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ S : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω ω S ∧
      ∃ F : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) F ω S ∧
        ∀ f : type_l hℳ B, mem_l hℳ f.val S.val → ∃ i : type_l hℳ B,
          mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) F i f := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  have hNum (i : SecondOrderModel.num_l ℳ) :
      PowerlessRelativeClassCorrespondence.member_l hℳ B (numberCode_l K i).val :=
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
      (hωEq.symm ▸ (numberCode_l K i).property)
  let e : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val, hNum _⟩
  let one : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val, hNum _⟩
  let two : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.succ_l
    (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).val, hNum _⟩
  obtain ⟨S, hS₀, hSClass⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l
    (hBase := hBase) (ω := ω) (X := ω) hω
  have hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega S.val := by
    simpa only [hωEq] using hS₀
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  obtain ⟨G, hRead⟩ := PowerlessRelativeClassSequenceIndex.graph_l (hBase := hBase) ω e S one two
  have hOnto : ∀ f : type_l hℳ B, mem_l hℳ f.val S.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) G i f := by
    intro f hf
    obtain ⟨i, hi, hCode⟩ := PowerlessRelativeClassSequenceIndex.exists_l (hBase := hBase) K
      (ω := ω) (e := e) (S := S) (one := one) (two := two) (f := f)
      hS hE hωEq rfl rfl rfl hf
    exact ⟨i, hi, (hRead i f).mpr ⟨hi, hf, hCode⟩⟩
  have hUnique (f g i : type_l hℳ B)
      (hf : value_l (ℳ := structure_l hℳ B hBase) G i f)
      (hg : value_l (ℳ := structure_l hℳ B hBase) G i g) : f = g :=
    PowerlessRelativeClassSequenceIndex.unique_l (hBase := hBase) K hS hωEq rfl
      ((hRead i f).mp hf).2.2 ((hRead i g).mp hg).2.2
  obtain ⟨R, hR, hRRead⟩ := PowerlessRelativeClassEnumerationSection.exists_l (hBase := hBase) hω hOnto
  have hInjective (f g i : type_l hℳ B)
      (hf : value_l (ℳ := structure_l hℳ B hBase) R f i)
      (hg : value_l (ℳ := structure_l hℳ B hBase) R g i) : f = g :=
    hUnique f g i ((hRRead f i).mp hf).2.2.1 ((hRRead g i).mp hg).2.2.1
  have heS : mem_l hℳ e.val S.val := (hS e.val).mpr
    ⟨e.val, (numberCode_l K (SecondOrderModel.zero_l ℳ)).property, ⟨
      fun p hp => False.elim (PowerlessBMSQuotientSuccessor.zero_l K p hp),
      fun x hx => False.elim (PowerlessBMSQuotientSuccessor.zero_l K x hx)⟩⟩
  obtain ⟨F, hF, hFOnto, _⟩ := PowerlessRelativeClassInjectionEnumeration.exists_l
    (hBase := hBase) hR hInjective heS
  exact ⟨S, hSClass, F, hF, hFOnto⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteNumericEnumeration
