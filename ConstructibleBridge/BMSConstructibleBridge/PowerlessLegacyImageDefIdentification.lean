import BMSConstructibleBridge.PowerlessLegacyImageIndicesBounded
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots
import BMSConstructibleBridge.PowerlessLegacyDefinableRowImage
import BMSConstructibleBridge.PowerlessLegacyLinkInverse
import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute
import BMSConstructibleBridge.SecondOrderEnumeratedMemberDef

/-! # 原非空 Def 与受限旧翻译像的全 raw 认同

背景为原 num/set 的 SecondOrderArithmetic.theory_m，行查询及 selector
仍使用已有纯隶属 ℒ 的 AST。给定同一 K 下实际 Seq、Sat、完整数字
序列、旧翻译读数及原求值保持证书，直接认同原呈现 H₀ 的全部 raw
成员与 selector 指标上的精确行像，不先要求行族对象 Y 或 Class Y。

只有 ω、A、Seq、Sat 要求是实际 Class 对象。e、N₂、F、Idx、I 及
规范枚举 U 均可留在原商；Idx 仅需包含实际内层配对指标。反向的内层
有序对由两个实际 Class 坐标的闭包提升，不用 Idx 的 Class 身份。
ω 证书与 U 的数字满射在证明内恢复，不附加 Class U 或 A 可数前提。

原呈现的合法索引、幂图、求值图及精确行族保持固定；全部内部长度和
坐标由同一 K 读取，所有行与元素量化全部 raw 商。这里仅处理带原成员
证书 a、ha 的非空呈现，不能把空域原 Def={∅} 误认作空 selector 行像。
实际行族的 Class 或指定层成员界及对象 Derives 由调用端另行消费。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyImageDefIdentification

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderQuotient (mem_l mk_l)
open SecondOrderModel (num_l set_l succ_l zero_l add_l)
open SecondOrderFiniteAssignmentLift (number_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

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
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {ω A Seq Sat : type_l hℳ B}
    {e N₂ F Idx I U : SecondOrderQuotient.type_l hℳ}
    {A₀ H₀ : SecondOrderGraph.code_l ℳ} {a : num_l ℳ}
    {ha : SecondOrderPairing.relation_l A₀.real a A₀.root}
    {V E D Q₀ R₀ T₀ F₀ C : set_l ℳ}
    (hAcode : A.val = mk_l hℳ A₀)
    (hPresentation : SecondOrderLegalMemberCollection.presentation_l hℳ A₀ a ha V E D Q₀ R₀ T₀ F₀ H₀)
    (hωEq : ω.val = K.omega) (he : e = code_l K (zero_l ℳ))
    (hN₂ : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) K.omega K.omega N₂)
    (hFnumeric : ∀ n s, value_l (ℳ := RawModel) F (code_l K n) (code_l K s) ↔
      SecondOrderPairing.relation_l C n s)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C)
    (hU : map_l (ℳ := RawModel) U K.omega A.val)
    (hNumber : ∀ n x, value_l (ℳ := RawModel) U (code_l K n) x ↔
      x = (SecondOrderMemberStructure.value_l hℳ A₀ a ha n).val)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω A Seq)
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRow.row_l K B A.val U Sat.val E C T₀ n)
    (hIdx : ∀ q f t : type_l hℳ B, mem_l hℳ q.val ω.val → mem_l hℳ f.val Seq.val →
      ordered_l (ℳ := structure_l hℳ B hBase) q f t → mem_l hℳ t.val Idx)
    (hI : ∀ j : SecondOrderQuotient.type_l hℳ, mem_l hℳ j I ↔
      PowerlessLegacyImageIndicesBounded.select_l (𝒩 := RawModel)
        ω.val e N₂ F A.val Seq.val Idx j) :
    ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z (mk_l hℳ H₀) ↔
      ∃ j : SecondOrderQuotient.type_l hℳ, mem_l hℳ j I ∧
        ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x Z ↔
          mem_l hℳ x A.val ∧ PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := RawModel)
            ω.val A.val Seq.val Idx Sat.val j x := by
  have hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr (hωEq.symm ▸ K.omega_spec)
  have hNumberω (n : num_l ℳ) : mem_l hℳ (code_l K n) ω.val := by
    rw [hωEq]
    exact (numberCode_l K n).property
  have hOnto : ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x A.val →
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
    obtain ⟨f, hf, hLink⟩ := PowerlessLegacyAssignmentRealization.exists_l
      (hBase := hBase) K hΩ hωEq hPresentation.powers hc L (zero_l ℳ) hU
    obtain ⟨b, hbA, hTail⟩ := link_tail_l K hU hLink
    have hfRaw := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f _ A).mp hf
    have hfSeq : mem_l hℳ f.val Seq.val :=
      (hSeq f).mpr ⟨number_l hBase K ω hωEq L, hNumberω L, hf⟩
    obtain ⟨tRaw, htPair⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (code_l K q) f.val
    let t : type_l hℳ B := ⟨tRaw, PowerlessRelativeClassPair.ordered_l hℳ hBase
      (number_l hBase K ω hωEq q).property f.property htPair⟩
    have ht : ordered_l (ℳ := structure_l hℳ B hBase) (number_l hBase K ω hωEq q) f t :=
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) _ f t).mpr htPair
    have htIdx : mem_l hℳ t.val Idx :=
      hIdx (number_l hBase K ω hωEq q) f t (hNumberω q) hfSeq ht
    obtain ⟨j, hjPair⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (code_l K l) t.val
    have hBodyK : PowerlessLegacyImageIndicesBounded.body_l (𝒩 := RawModel)
        K.omega (code_l K (zero_l ℳ)) N₂ F A.val (code_l K l) (code_l K q) f.val :=
      (PowerlessLegacyImageIndicesBounded.body_numeric_l K hN₂ hFnumeric l q).mpr
        ⟨p, succ_l l, L, b, hbA, rfl, hQuery, hBound, hfRaw, hTail⟩
    have hBody : PowerlessLegacyImageIndicesBounded.body_l (𝒩 := RawModel)
        ω.val e N₂ F A.val (code_l K l) (code_l K q) f.val := by
      simpa only [hωEq, he] using hBodyK
    have hjI : mem_l hℳ j I := (hI j).mpr
      ⟨code_l K l, hNumberω l, t.val, htIdx, code_l K q, hNumberω q,
        f.val, hfSeq, hjPair, htPair, hBody⟩
    have hRowImage := PowerlessLegacyDefinableRowImage.read_l (hBase := hBase)
      K hΩ hωEq hPresentation.powers hPresentation.domain hPresentation.family hc hQuery hBound
        hPreservation hU hOnto hf hLink hSeq ht
    refine ⟨j, hjI, fun x => ?_⟩
    exact (hRow x).trans ((hRowImage x).symm.trans
      (and_congr Iff.rfl (query_read_l (hℳ := hℳ) (ω := ω.val) (A := A.val) (Seq := Seq.val)
        (Idx := Idx) (Sat := Sat.val) (l := code_l K l) (t := t.val) (j := j)
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
        K.omega (code_l K (zero_l ℳ)) N₂ F A.val (code_l K l) (code_l K q) fRaw := by
      simpa only [hωEq, he] using hBody
    obtain ⟨p, m, L, b, hbA, hm, hQuery, hBound, hfRaw, hTail⟩ :=
      (PowerlessLegacyImageIndicesBounded.body_numeric_l K hN₂ hFnumeric l q).mp hBodyK
    subst m
    have hfOld : map_l (ℳ := RawModel) fRaw (code_l K L) (mk_l hℳ A₀) := hAcode ▸ hfRaw
    have hbOld : mem_l hℳ b (mk_l hℳ A₀) := hAcode ▸ hbA
    obtain ⟨c, z, hc, hLink⟩ := PowerlessLegacyLinkInverse.inverse_l K A₀ a ha hPresentation.powers
      hNumber hfOld (Or.inr (slot_lt_l (hℳ := hℳ) hBound)) ⟨b, hbOld, hTail⟩
    let f : type_l hℳ B := ⟨fRaw,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Seq.property hfSeq⟩
    let t : type_l hℳ B := ⟨tRaw, PowerlessRelativeClassPair.ordered_l hℳ hBase
      (number_l hBase K ω hωEq q).property f.property htPair⟩
    have hf : map_l (ℳ := structure_l hℳ B hBase) f (number_l hBase K ω hωEq L) A :=
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f _ A).mpr hfRaw
    have ht : ordered_l (ℳ := structure_l hℳ B hBase) (number_l hBase K ω hωEq q) f t :=
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) _ f t).mpr htPair
    have hRowImage := PowerlessLegacyDefinableRowImage.read_l (hBase := hBase)
      K hΩ hωEq hPresentation.powers hPresentation.domain hPresentation.family hc hQuery hBound
        hPreservation hU hOnto hf hLink hSeq ht
    have hLegal : SecondOrderPairing.relation_l V p (succ_l l) :=
      (SecondOrderLegacyFormulaTranslationDomain.domain_l hℳ hPresentation.formula_codes hC p (succ_l l)).mpr
        ⟨q, hQuery⟩
    refine ⟨SecondOrderDefinableFamily.index_l p l c,
      (SecondOrderLegalFormulaIndex.index_l hℳ V E p l c).mpr ⟨hc, hLegal⟩, ?_⟩
    intro x
    exact (hRow x).trans ((and_congr Iff.rfl
      (query_read_l (hℳ := hℳ) (ω := ω.val) (A := A.val) (Seq := Seq.val)
        (Idx := Idx) (Sat := Sat.val) (l := code_l K l) (t := tRaw) (j := j)
        hlω htIdx hjPair x)).trans (hRowImage x))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyImageDefIdentification
