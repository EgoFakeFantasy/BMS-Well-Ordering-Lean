import BMSConstructibleBridge.PowerlessLegacyImageIndicesBounded
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots
import BMSConstructibleBridge.PowerlessLegacyDefinableRawRowImage
import BMSConstructibleBridge.PowerlessLegacyLinkInverse
import BMSConstructibleBridge.PowerlessLegacyAssignmentRawRealization
import BMSConstructibleBridge.SecondOrderEnumeratedMemberDef

/-! # 原非空 Def 与完整原商旧翻译行像的认同

保留原实际非空呈现、合法索引、原求值图和规范枚举；完整 Seq、
全原商求值保持及全部指标覆盖提供双向精确行像。全部候选 Z 和
元素 x 均量化原商，不要求任何对象属于 Class 或某个可构造层。
这是原 Def 行族认同，不证明指定母域成员界或完整源 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyImageDefRawIdentification

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open SecondOrderQuotient (mem_l mk_l)
open SecondOrderModel (num_l set_l succ_l zero_l add_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 外层有序对的两个 raw 坐标唯一，统一查询准确恢复原指定槽查询。 -/
private theorem query_read_l {ω A Seq Idx Sat l t j : SecondOrderQuotient.type_l hℳ}
    (hl : mem_l hℳ l ω) (ht : mem_l hℳ t Idx)
    (hj : ordered_l (ℳ := RawModel) l t j) (x : SecondOrderQuotient.type_l hℳ) :
    PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := RawModel) ω A Seq Idx Sat j x ↔
      PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := RawModel) ω A Seq l Sat t x := by
  constructor
  · rintro ⟨l', t', _, _, hj', hQuery⟩
    obtain ⟨hL, hT⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hj' hj).mp rfl
    subst l'
    subst t'
    exact hQuery
  · exact fun h => ⟨l, t, hl, ht, hj, h⟩

/-- 正向填充的整个预算尾部从槽 l 起恒取同一个实际 A 成员。 -/
private theorem link_tail_l (K : source_coding_l hℳ) {E : set_l ℳ}
    {c l L z : num_l ℳ} {A U f : SecondOrderQuotient.type_l hℳ}
    (hU : map_l (ℳ := RawModel) U K.omega A)
    (hLink : PowerlessLegacyAssignmentSyntax.link_l K E c l L z U f) :
    ∃ b, mem_l hℳ b A ∧ ∀ i, SecondOrderOrder.lt_l i L → ¬SecondOrderOrder.lt_l i l →
      value_l (ℳ := RawModel) f (code_l K i) b := by
  obtain ⟨b, ⟨hb, hUb⟩, _⟩ := hU.2 (code_l K z) (numberCode_l K z).property
  exact ⟨b, hb, fun i hi hNot =>
    (hLink i b).mpr ⟨z, ⟨hi, Or.inr ⟨hNot, rfl⟩⟩, hUb⟩⟩

include hℳ in
/-- 原预算保证内部待更新槽 l 仍严格位于赋值长度 L 内。 -/
private theorem slot_lt_l {l p L : num_l ℳ}
    (hBound : SecondOrderLegacyFormulaTranslationLength.bound_l (succ_l l) p L) :
    SecondOrderOrder.lt_l l L := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  have hBoundLe : succ_l l + p ≤ L := hBound
  exact lt_of_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ l l).mpr le_rfl)
    ((le_add_of_nonneg_right (SecondOrderAlgebra.zero_le_l hℳ p)).trans hBoundLe)

/-- 给定实际对象及真实读数证书后，原非空 Def 的全 raw 成员就是受限行像。 -/
theorem image_iff_l
    (K : source_coding_l hℳ) {ω A Seq Sat : type_l hℳ}
    {e N₂ F Idx I U : SecondOrderQuotient.type_l hℳ}
    {A₀ H₀ : SecondOrderGraph.code_l ℳ} {a : num_l ℳ}
    {ha : SecondOrderPairing.relation_l A₀.real a A₀.root}
    {V E D Q₀ R₀ T₀ F₀ C : set_l ℳ}
    (hAcode : A = mk_l hℳ A₀)
    (hPresentation : SecondOrderLegalMemberCollection.presentation_l hℳ A₀ a ha V E D Q₀ R₀ T₀ F₀ H₀)
    (hωEq : ω = K.omega) (he : e = code_l K (zero_l ℳ))
    (hN₂ : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) K.omega K.omega N₂)
    (hFnumeric : ∀ n s, value_l (ℳ := RawModel) F (code_l K n) (code_l K s) ↔
      SecondOrderPairing.relation_l C n s)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C)
    (hU : map_l (ℳ := RawModel) U K.omega A)
    (hNumber : ∀ n x, value_l (ℳ := RawModel) U (code_l K n) x ↔
      x = (SecondOrderMemberStructure.value_l hℳ A₀ a ha n).val)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω A Seq)
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRawRow.row_l K A U Sat E C T₀ n)
    (hIdx : ∀ q f t : type_l hℳ, mem_l hℳ q ω → mem_l hℳ f Seq →
      ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) q f t → mem_l hℳ t Idx)
    (hI : ∀ j : SecondOrderQuotient.type_l hℳ, mem_l hℳ j I ↔
      PowerlessLegacyImageIndicesBounded.select_l (𝒩 := RawModel)
        ω e N₂ F A Seq Idx j) :
    ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z (mk_l hℳ H₀) ↔
      ∃ j : SecondOrderQuotient.type_l hℳ, mem_l hℳ j I ∧
        ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x Z ↔
          mem_l hℳ x A ∧ PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := RawModel)
            ω A Seq Idx Sat j x := by
  have hNumberω (n : num_l ℳ) : mem_l hℳ (code_l K n) ω := by
    rw [hωEq]
    exact (numberCode_l K n).property
  have hOnto : ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x A →
      ∃ v, value_l (ℳ := RawModel) U (code_l K v) x := by
    intro x hx
    have hxA₀ : mem_l hℳ x (mk_l hℳ A₀) := hAcode ▸ hx
    obtain ⟨v, hv⟩ := SecondOrderMemberStructure.surjective_l hℳ A₀ a ha ⟨x, hxA₀⟩
    exact ⟨v, (hNumber v x).mpr (congrArg Subtype.val hv).symm⟩
  have hOldCollection (Z : SecondOrderQuotient.type_l hℳ) :
      mem_l hℳ Z (mk_l hℳ H₀) ↔ ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧
        ∀ x, mem_l hℳ x Z ↔ ∃ v, SecondOrderPairing.relation_l F₀ i v ∧
          value_l (ℳ := RawModel) U (code_l K v) x := by
    refine (SecondOrderEnumeratedMemberDef.original_collection_l A₀ a ha hPresentation Z).trans ?_
    apply exists_congr
    intro i
    apply and_congr Iff.rfl
    apply forall_congr'
    intro x
    apply iff_congr Iff.rfl
    exact exists_congr (fun v => and_congr Iff.rfl (hNumber v x).symm)
  intro Z
  rw [hOldCollection Z]
  constructor
  · rintro ⟨i, hi, hRow⟩
    obtain ⟨p, l, c, rfl, hc, hLegal⟩ := hi
    obtain ⟨q, hQuery⟩ :=
      (SecondOrderLegacyFormulaTranslationDomain.domain_l hℳ hPresentation.formula_codes hC p (succ_l l)).mp hLegal
    let L : num_l ℳ := add_l (succ_l l) p
    have hBound : SecondOrderLegacyFormulaTranslationLength.bound_l (succ_l l) p L := Or.inl rfl
    obtain ⟨f, hfRaw, hLink⟩ := PowerlessLegacyAssignmentRawRealization.exists_l
      K hPresentation.powers hc L (zero_l ℳ) hU
    obtain ⟨b, hbA, hTail⟩ := link_tail_l K hU hLink
    have hfSeq : mem_l hℳ f Seq :=
      (hSeq f).mpr ⟨code_l K L, hNumberω L, hfRaw⟩
    obtain ⟨t, htPair⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (code_l K q) f
    have htIdx : mem_l hℳ t Idx :=
      hIdx (code_l K q) f t (hNumberω q) hfSeq htPair
    obtain ⟨j, hjPair⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (code_l K l) t
    have hBodyK : PowerlessLegacyImageIndicesBounded.body_l (𝒩 := RawModel)
        K.omega (code_l K (zero_l ℳ)) N₂ F A (code_l K l) (code_l K q) f :=
      (PowerlessLegacyImageIndicesBounded.body_numeric_l K hN₂ hFnumeric l q).mpr
        ⟨p, succ_l l, L, b, hbA, rfl, hQuery, hBound, hfRaw, hTail⟩
    have hBody : PowerlessLegacyImageIndicesBounded.body_l (𝒩 := RawModel)
        ω e N₂ F A (code_l K l) (code_l K q) f := by
      simpa only [hωEq, he] using hBodyK
    have hjI : mem_l hℳ j I := (hI j).mpr
      ⟨code_l K l, hNumberω l, t, htIdx, code_l K q, hNumberω q,
        f, hfSeq, hjPair, htPair, hBody⟩
    have hRowImage := PowerlessLegacyDefinableRawRowImage.read_l (hℳ := hℳ) (t := t)
      K hωEq hPresentation.powers hPresentation.domain hPresentation.family hc hQuery hBound
        hPreservation hU hOnto hfRaw hLink hSeq htPair
    refine ⟨j, hjI, fun x => ?_⟩
    exact (hRow x).trans ((hRowImage x).symm.trans
      (and_congr Iff.rfl (query_read_l (hℳ := hℳ) (ω := ω) (A := A) (Seq := Seq)
        (Idx := Idx) (Sat := Sat) (l := code_l K l) (t := t) (j := j)
        (hNumberω l) htIdx hjPair x).symm))
  · rintro ⟨j, hjI, hRow⟩
    obtain ⟨lRaw, hlω, tRaw, htIdx, qRaw, hqω, fRaw, hfSeq, hjPair, htPair, hBody⟩ := (hI j).mp hjI
    obtain ⟨l, hl⟩ := numberCode_surjective_l K ⟨lRaw, hωEq ▸ hlω⟩
    obtain ⟨q, hq⟩ := numberCode_surjective_l K ⟨qRaw, hωEq ▸ hqω⟩
    have hLCode : lRaw = code_l K l := (congrArg Subtype.val hl).symm
    have hQCode : qRaw = code_l K q := (congrArg Subtype.val hq).symm
    rw [hLCode] at hlω hjPair hBody
    rw [hQCode] at hqω htPair hBody
    have hBodyK : PowerlessLegacyImageIndicesBounded.body_l (𝒩 := RawModel)
        K.omega (code_l K (zero_l ℳ)) N₂ F A (code_l K l) (code_l K q) fRaw := by
      simpa only [hωEq, he] using hBody
    obtain ⟨p, m, L, b, hbA, hm, hQuery, hBound, hfRaw, hTail⟩ :=
      (PowerlessLegacyImageIndicesBounded.body_numeric_l K hN₂ hFnumeric l q).mp hBodyK
    subst m
    have hfOld : map_l (ℳ := RawModel) fRaw (code_l K L) (mk_l hℳ A₀) := hAcode ▸ hfRaw
    have hbOld : mem_l hℳ b (mk_l hℳ A₀) := hAcode ▸ hbA
    obtain ⟨c, z, hc, hLink⟩ := PowerlessLegacyLinkInverse.inverse_l K A₀ a ha hPresentation.powers
      hNumber hfOld (Or.inr (slot_lt_l (hℳ := hℳ) hBound)) ⟨b, hbOld, hTail⟩
    have hRowImage := PowerlessLegacyDefinableRawRowImage.read_l (hℳ := hℳ) (t := tRaw)
      K hωEq hPresentation.powers hPresentation.domain hPresentation.family hc hQuery hBound
        hPreservation hU hOnto hfRaw hLink hSeq htPair
    have hLegal : SecondOrderPairing.relation_l V p (succ_l l) :=
      (SecondOrderLegacyFormulaTranslationDomain.domain_l hℳ hPresentation.formula_codes hC p (succ_l l)).mpr
        ⟨q, hQuery⟩
    refine ⟨SecondOrderDefinableFamily.index_l p l c,
      (SecondOrderLegalFormulaIndex.index_l hℳ V E p l c).mpr ⟨hc, hLegal⟩, ?_⟩
    intro x
    exact (hRow x).trans ((and_congr Iff.rfl
      (query_read_l (hℳ := hℳ) (ω := ω) (A := A) (Seq := Seq)
        (Idx := Idx) (Sat := Sat) (l := code_l K l) (t := tRaw) (j := j)
        hlω htIdx hjPair x)).trans (hRowImage x))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyImageDefRawIdentification
