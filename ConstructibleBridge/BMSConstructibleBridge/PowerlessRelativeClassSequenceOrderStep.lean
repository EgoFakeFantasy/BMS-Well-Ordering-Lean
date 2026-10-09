import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderSlices
import BMSConstructibleBridge.PowerlessRelativeClassSequenceSplitDerives
import BMSConstructibleBridge.PowerlessRelativeClassLexicographicWellOrder
import BMSConstructibleBridge.PowerlessRelativeClassWellOrderPullback

/-! # 同一序列关系的后继切片良序步

将后继长度切片实际单射到前缀切片与母集的字典序积，再将所得拉回序
逐值识别为给定的同一个关系 L。结论不是另一个任意良序的存在。
本模块仅为对象内部归纳提供语义步骤，不使用外部长度归纳或 Type 选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderStep

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

private theorem coordinates_l {x y a b p : type_l hℳ B}
    (hp : ordered_l (ℳ := ClassModel) x y p) (hq : ordered_l (ℳ := ClassModel) a b p) :
    x = a ∧ y = b := by
  have h := (SecondOrderPairObjects.ordered_eq_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p).mp hp)
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) a b p).mp hq)).mp rfl
  exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

/-- 已知有序对坐标时，消去字典序规格中的再次存在量化。 -/
theorem pair_lex_l {P X L R u v a b p q : type_l hℳ B}
    (hu : member_l ClassModel u P) (ha : member_l ClassModel a X)
    (hv : member_l ClassModel v P) (hb : member_l ClassModel b X)
    (hp : ordered_l (ℳ := ClassModel) u a p) (hq : ordered_l (ℳ := ClassModel) v b q) :
    PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := ClassModel) P X L R p q ↔
      value_l (ℳ := ClassModel) L u v ∨ u = v ∧ value_l (ℳ := ClassModel) R a b := by
  constructor
  · rintro ⟨u', a', v', b', _, _, _, _, hp', hq', hCompare⟩
    obtain ⟨huu, haa⟩ := coordinates_l hp hp'
    obtain ⟨hvv, hbb⟩ := coordinates_l hq hq'
    subst u'
    subst a'
    subst v'
    subst b'
    exact hCompare
  · exact fun h => ⟨u, a, v, b, hu, ha, hv, hb, hp, hq, h⟩

theorem step_l {ω n m X R L P Q : type_l hℳ B}
    (hn : member_l ClassModel n ω) (hm : member_l ClassModel m ω)
    (hnIrr : ¬member_l ClassModel n n) (hmIrr : ¬member_l ClassModel m m)
    (hSucc : ∀ i : type_l hℳ B, member_l ClassModel i m ↔ member_l ClassModel i n ∨ i = n)
    (hTrans : ∀ i : type_l hℳ B, member_l ClassModel i n →
      ∀ j : type_l hℳ B, member_l ClassModel j i → member_l ClassModel j n)
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) n X P)
    (hQ : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) m X Q)
    (hRead : ∀ f g : type_l hℳ B, value_l (ℳ := ClassModel) L f g ↔
      shortlex_l (ℳ₀ := ClassModel) ω X R f g)
    (hR : wellOrder_l (ℳ := ClassModel) X R) (hOld : wellOrder_l (ℳ := ClassModel) P L) :
    wellOrder_l (ℳ := ClassModel) Q L := by
  obtain ⟨D, H, hD, hH, hInject, hHRead⟩ :=
    PowerlessRelativeClassSequenceSplitDerives.exists_l (hBase := hBase) hSucc hP hQ
  obtain ⟨D', K, hD', hK, hKRead⟩ :=
    PowerlessRelativeClassLexicographicWellOrder.exists_l hOld hR
  have hDD : D = D' := by
    apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    exact fun p => (hD p).trans (hD' p).symm
  subst D'
  obtain ⟨T, hT, hTRead⟩ := PowerlessRelativeClassWellOrderPullback.exists_l hH hInject hK
  have hCompare {f g p q : type_l hℳ B}
      (hf : member_l ClassModel f Q) (hg : member_l ClassModel g Q)
      (hfp : value_l (ℳ := ClassModel) H f p) (hgq : value_l (ℳ := ClassModel) H g q) :
      value_l (ℳ := ClassModel) K p q ↔ value_l (ℳ := ClassModel) L f g := by
    obtain ⟨u, a, hu, ha, hp, hPrefix, hLast⟩ := ((hHRead f p).mp hfp).2
    obtain ⟨v, b, hv, hb, hq, hPrefix', hLast'⟩ := ((hHRead g q).mp hgq).2
    have hPairRead := (hKRead p q).trans (pair_lex_l hu ha hv hb hp hq)
    have hSmall := PowerlessRelativeClassSequenceOrderSlices.at_length_l
      hn hnIrr hP hRead u hu v hv
    have hSuccessor := PowerlessRelativeClassSequenceLexicographic.successor_l (R := R)
      ((hQ f).mp hf) ((hQ g).mp hg) ((hP u).mp hu) ((hP v).mp hv)
      hSucc hTrans hPrefix hPrefix' hLast hLast'
    have hBig := PowerlessRelativeClassSequenceOrderSlices.at_length_l
      hm hmIrr hQ hRead f hf g hg
    exact hPairRead.trans ((or_congr hSmall Iff.rfl).trans (hSuccessor.symm.trans hBig.symm))
  apply PowerlessRelativeClassSequenceOrderSlices.wellOrder_congr_l hT
  intro f hf g hg
  constructor
  · intro hfg
    obtain ⟨_, _, p, q, _, _, hfp, hgq, hpq⟩ := (hTRead f g).mp hfg
    exact (hCompare hf hg hfp hgq).mp hpq
  · intro hfg
    obtain ⟨p, ⟨hpD, hfp⟩, _⟩ := hH.2 f hf
    obtain ⟨q, ⟨hqD, hgq⟩, _⟩ := hH.2 g hg
    exact (hTRead f g).mpr ⟨hf, hg, p, q, hpD, hqD, hfp, hgq,
      (hCompare hf hg hfp hgq).mpr hfg⟩

#print axioms step_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderStep
