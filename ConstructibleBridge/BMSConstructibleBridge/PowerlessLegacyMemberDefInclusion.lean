import BMSConstructibleBridge.PowerlessLegacyDefinableSlice
import BMSConstructibleBridge.SecondOrderMemberDefRowImage

/-! # 原五标签 Def 成员在全槽 Sat 族中的实际包含

原 Def 使用实际合法索引收集的集合对象。对其任意环境成员，取内部
翻译码和共同长度界，构造类内 Sat 切片，并以环境商外延性证明它
就是原成员。结论量化原 Def 的所有环境成员，不预设它们属于类。
这里未证明整个原 Def 对象属于类，亦未传输环境子集上的良序最小元。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyMemberDefInclusion

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderFiniteAssignmentLift (number_l)
open SecondOrderModel

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

theorem members_l (K : source_coding_l hℳ) {ω A Seq Sat I Y : type_l hℳ B}
    (hΩ : omega_l (ℳ := 𝒩) ω) (hω : ω.val = K.omega)
    {A₀ H : SecondOrderGraph.code_l ℳ} {a : num_l ℳ}
    {ha : SecondOrderPairing.relation_l A₀.real a A₀.root} {V E D Q R T F C : set_l ℳ}
    (h : SecondOrderLegalMemberCollection.presentation_l hℳ A₀ a ha V E D Q R T F H)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C)
    {U : SecondOrderQuotient.type_l hℳ}
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val)
    (hNumber : ∀ n y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      U (numberCode_l K n).val y ↔ y = (SecondOrderMemberStructure.value_l hℳ A₀ a ha n).val)
    (hOnto : ∀ y, member_l (SecondOrderQuotient.structure_l hℳ) y A.val →
      ∃ v, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val y)
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRow.row_l K B A.val U Sat.val E C T n)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A Seq)
    (hI : ∀ t, SecondOrderQuotient.mem_l hℳ t.val I.val ↔ ∃ c f : type_l hℳ B,
      SecondOrderQuotient.mem_l hℳ c.val ω.val ∧
      SecondOrderQuotient.mem_l hℳ f.val Seq.val ∧ ordered_l (ℳ := 𝒩) c f t)
    (hFamily : PowerlessRelativeClassSatisfactionAllSlots.family_l (ℳ₀ := 𝒩) ω A Seq I Sat Y) :
    ∀ z : SecondOrderQuotient.type_l hℳ,
      SecondOrderQuotient.mem_l hℳ z (SecondOrderQuotient.mk_l hℳ H) →
        PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
          SecondOrderQuotient.mem_l hℳ z Y.val := by
  intro z hz
  obtain ⟨Z₀, rfl⟩ := SecondOrderQuotient.surj_l hℳ z
  obtain ⟨i, hi, hOldSlice⟩ := (h.collection Z₀).mp hz
  obtain ⟨p, l, c, rfl, hc, hp⟩ := hi
  obtain ⟨q, hQuery⟩ :=
    (SecondOrderLegacyFormulaTranslationDomain.domain_l hℳ h.formula_codes hC p (succ_l l)).mp hp
  let L := add_l (succ_l l) p
  have hBound : SecondOrderLegacyFormulaTranslationLength.bound_l (succ_l l) p L :=
    Or.inl rfl
  obtain ⟨f, t, Z, hf, ht, hSlice, hRead⟩ := PowerlessLegacyDefinableSlice.exists_l
    (hBase := hBase) K hΩ hω h.powers h.domain h.family hc hQuery hBound hPreservation hU hOnto hSeq
  have hOldRead := SecondOrderMemberDefRowImage.image_l K h hNumber
    (SecondOrderDefinableFamily.index_l p l c) hOldSlice
  have hEq : SecondOrderQuotient.mk_l hℳ Z₀ = Z.val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun y => (hOldRead y).trans (hRead y).symm)
  have hNumberMem (n : num_l ℳ) :
      SecondOrderQuotient.mem_l hℳ (number_l hBase K ω hω n).val ω.val := by
    change SecondOrderQuotient.mem_l hℳ (numberCode_l K n).val ω.val
    rw [hω]
    exact (numberCode_l K n).property
  have htI := (hI t).mpr ⟨number_l hBase K ω hω q, f, hNumberMem q,
    (hSeq f).mpr ⟨number_l hBase K ω hω L, hNumberMem L, hf⟩, ht⟩
  have hZY := (hFamily Z).mpr ⟨number_l hBase K ω hω l, t, hNumberMem l, htI, hSlice⟩
  exact ⟨hEq.symm ▸ Z.property, hEq.symm ▸ hZY⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyMemberDefInclusion
