import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderStep
import BMSConstructibleBridge.PowerlessRelativeClassLexicographicAmbient

/-! # 同一 shortlex 图的环境后继切片良序步

前缀切片和母集的良序前提覆盖所有环境子集。实际拆分图沿环境
字典序积拉回，逐值读数与已有同一 shortlex 图相等，再以环境关系
相容传输结论。不从类内良序最小元条款推断环境良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderStepAmbient

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem step_l {ω n m X R L P Q : type_l hℳ B}
    (hn : member_l 𝒩 n ω) (hm : member_l 𝒩 m ω)
    (hnIrr : ¬member_l 𝒩 n n) (hmIrr : ¬member_l 𝒩 m m)
    (hSucc : ∀ i : type_l hℳ B, member_l 𝒩 i m ↔ member_l 𝒩 i n ∨ i = n)
    (hTrans : ∀ i : type_l hℳ B, member_l 𝒩 i n →
      ∀ j : type_l hℳ B, member_l 𝒩 j i → member_l 𝒩 j n)
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := 𝒩) n X P)
    (hQ : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := 𝒩) m X Q)
    (hRead : ∀ f g : type_l hℳ B, value_l (ℳ := 𝒩) L f g ↔ shortlex_l (ℳ₀ := 𝒩) ω X R f g)
    (hR : wellOrder_l (ℳ := 𝒱) X.val R.val) (hOld : wellOrder_l (ℳ := 𝒱) P.val L.val) :
    wellOrder_l (ℳ := 𝒱) Q.val L.val := by
  obtain ⟨D, H, hD, hH, hInject, hHRead⟩ :=
    PowerlessRelativeClassSequenceSplitDerives.exists_l (hBase := hBase) hSucc hP hQ
  obtain ⟨D', K, hD', hK, hKRead⟩ := PowerlessRelativeClassLexicographicAmbient.exists_l hOld hR
  have hDD : D = D' := by
    apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    exact fun p => (hD p).trans (hD' p).symm
  subst D'
  obtain ⟨T, hT, hTRead⟩ := PowerlessRelativeClassWellOrderPullbackAmbient.exists_l hH hInject hK
  have hCompare {f g p q : type_l hℳ B}
      (hf : member_l 𝒩 f Q) (hg : member_l 𝒩 g Q)
      (hfp : value_l (ℳ := 𝒩) H f p) (hgq : value_l (ℳ := 𝒩) H g q) :
      value_l (ℳ := 𝒩) K p q ↔ value_l (ℳ := 𝒩) L f g := by
    obtain ⟨u, a, hu, ha, hp, hPrefix, hLast⟩ := ((hHRead f p).mp hfp).2
    obtain ⟨v, b, hv, hb, hq, hPrefix', hLast'⟩ := ((hHRead g q).mp hgq).2
    have hPairRead := (hKRead p q).trans
      (PowerlessRelativeClassSequenceOrderStep.pair_lex_l hu ha hv hb hp hq)
    have hSmall := PowerlessRelativeClassSequenceOrderSlices.at_length_l hn hnIrr hP hRead u hu v hv
    have hSuccessor := PowerlessRelativeClassSequenceLexicographic.successor_l (R := R)
      ((hQ f).mp hf) ((hQ g).mp hg) ((hP u).mp hu) ((hP v).mp hv)
      hSucc hTrans hPrefix hPrefix' hLast hLast'
    have hBig := PowerlessRelativeClassSequenceOrderSlices.at_length_l hm hmIrr hQ hRead f hf g hg
    exact hPairRead.trans ((or_congr hSmall Iff.rfl).trans (hSuccessor.symm.trans hBig.symm))
  have hEquality (f : type_l hℳ B) (hf : member_l 𝒩 f Q)
      (g : type_l hℳ B) (hg : member_l 𝒩 g Q) :
      value_l (ℳ := 𝒩) T f g ↔ value_l (ℳ := 𝒩) L f g := by
    constructor
    · intro hfg
      obtain ⟨_, _, p, q, _, _, hfp, hgq, hpq⟩ := (hTRead f g).mp hfg
      exact (hCompare hf hg hfp hgq).mp hpq
    · intro hfg
      obtain ⟨p, ⟨hpD, hfp⟩, _⟩ := hH.2 f hf
      obtain ⟨q, ⟨hqD, hgq⟩, _⟩ := hH.2 g hg
      exact (hTRead f g).mpr ⟨hf, hg, p, q, hpD, hqD, hfp, hgq, (hCompare hf hg hfp hgq).mpr hfg⟩
  apply PowerlessRelativeClassSequenceOrderSlices.wellOrder_congr_l hT
  intro f hf g hg
  let f' : type_l hℳ B := ⟨f, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Q.property hf⟩
  let g' : type_l hℳ B := ⟨g, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Q.property hg⟩
  exact (PowerlessRelativeClassFunctionAbsolute.value_l T f' g').symm.trans
    ((hEquality f' hf g' hg).trans (PowerlessRelativeClassFunctionAbsolute.value_l L f' g'))

#print axioms step_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderStepAmbient
