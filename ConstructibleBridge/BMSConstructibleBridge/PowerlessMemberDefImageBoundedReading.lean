import BMSConstructibleBridge.PowerlessMemberDefImageBounded
import BMSConstructibleBridge.PowerlessRelativeCofinalDefCoding
import BMSConstructibleBridge.PowerlessLegacyImageDefIdentification
import BMSConstructibleBridge.PowerlessLegacyMemberEnumeration
import BMSConstructibleBridge.PowerlessLegacyEvaluationPreservation
import BMSConstructibleBridge.SecondOrderMemberDef
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments

/-! # 有界旧翻译像检查器与原完整 Def 的双向对应

固定同一内部编码 K 的实际整包。候选 H 完全任意；反向先使用原 Z₂
的 Def 存在性，再以精确全部 raw 行像及原商外延性识别 H。正向使用
整包已经真正构造的层内 Seq、Idx、I、Q。两方向都不要求原枚举 U
属于 Class 或 W，不把最终 image iff、ClassH 或原 Def 列为反向前提。

层 W 的真实极限闭包将 select 中任意有序对指标送回 W，因此指标
检查器的有界反向覆盖恢复全部 raw 范围。此结果是原 Def 步的检查器
桥梁，不是 member-W 的原 global_m、完整超限历史或最终 BMS 良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefImageBoundedReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderModel (zero_l)
open PowerlessMemberDefImageBounded

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β W : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 两个有界覆盖方向在原商中给出完整积规格；逆向使用有序对唯一性。 -/
theorem product_spec_l {X Y P : SecondOrderQuotient.type_l hℳ}
    (h : product_holds_l (𝒩 := RawModel) X Y P) :
    ∀ p, mem_l hℳ p P ↔ ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧
      ordered_l (ℳ := RawModel) x y p := by
  intro p
  constructor
  · intro hp
    obtain ⟨x, hx, y, hy, hPair⟩ := h.1 p hp
    exact ⟨x, y, hx, hy, hPair⟩
  · rintro ⟨x, y, hx, hy, hPair⟩
    obtain ⟨q, hq, hPairQ⟩ := h.2 x hx y hy
    have hEq : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPairQ hPair
    exact hEq ▸ hq

/-- 完整 raw 积规格直接提供 AST 所检查的两个有界覆盖方向。 -/
theorem product_of_spec_l {X Y P : SecondOrderQuotient.type_l hℳ}
    (h : ∀ p, mem_l hℳ p P ↔ ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧
      ordered_l (ℳ := RawModel) x y p) : product_holds_l (𝒩 := RawModel) X Y P := by
  constructor
  · intro p hp
    obtain ⟨x, y, hx, hy, hPair⟩ := (h p).mp hp
    exact ⟨x, hx, y, hy, hPair⟩
  · intro x hx y hy
    obtain ⟨p, hPair⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
    exact ⟨p, (h p).mpr ⟨x, y, hx, hy, hPair⟩, hPair⟩

/-- 从整包提供的完整 raw 数据取得 checker 的局部数据条件。 -/
theorem data_of_spec_l {ω e N F A Sat Seq Idx I Q : SecondOrderQuotient.type_l hℳ}
    (hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := RawModel) ω A f → mem_l hℳ f W)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω A Seq)
    (hIdx : ∀ p, mem_l hℳ p Idx ↔ ∃ q f, mem_l hℳ q ω ∧ mem_l hℳ f Seq ∧
      ordered_l (ℳ := RawModel) q f p)
    (hI : ∀ j, mem_l hℳ j I ↔
      PowerlessLegacyImageIndicesBounded.select_l (𝒩 := RawModel) ω e N F A Seq Idx j)
    (hQ : ∀ j x, value_l (ℳ := RawModel) Q j x ↔ mem_l hℳ j I ∧ mem_l hℳ x A ∧
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := RawModel) ω A Seq Idx Sat j x) :
    data_l (𝒩 := RawModel) ω e N F W A Sat Seq Idx I Q := by
  refine ⟨(PowerlessFiniteSequencesBounded.spec_iff_of_coverage_l hCoverage).mpr hSeq,
    product_of_spec_l hIdx, ⟨fun j hj => (hI j).mp hj, fun j _ hj => (hI j).mpr hj⟩, ?_⟩
  intro j hj x hx
  exact (hQ j x).trans ⟨fun h => h.2.2, fun h => ⟨hj, hx, h⟩⟩

/-- select 的坐标确在 ω 与 Idx 中；真实传递性和配对闭包给出全部 raw 覆盖。 -/
theorem indices_spec_l
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := RawModel) W)
    (hPair : ∀ a b p, mem_l hℳ a W → mem_l hℳ b W →
      SecondOrderPairObjects.pair_l hℳ a b p → mem_l hℳ p W)
    {ω e N F A Seq Idx I : SecondOrderQuotient.type_l hℳ}
    (hωW : mem_l hℳ ω W) (hIdxW : mem_l hℳ Idx W)
    (hI : indices_holds_l (𝒩 := RawModel) ω e N F A Seq Idx W I) :
    ∀ j, mem_l hℳ j I ↔
      PowerlessLegacyImageIndicesBounded.select_l (𝒩 := RawModel) ω e N F A Seq Idx j := by
  intro j
  refine ⟨hI.1 j, fun hj => hI.2 j ?_ hj⟩
  obtain ⟨l, hl, t, ht, _q, _hq, _f, _hf, hOrdered, _⟩ := hj
  exact PowerlessRelativeFiniteHullAssignments.ordered_l (hℳ := hℳ)
    hPair (hTrans ω l hωW hl) (hTrans Idx t hIdxW ht) hOrdered

private theorem sequence_class_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {ω A Seq : type_l hℳ B}
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val A.val Seq.val) :
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω A Seq := by
  intro f
  constructor
  · intro hf
    obtain ⟨n, hn, hMap⟩ := (hSeq f.val).mp hf
    let n' : type_l hℳ B := ⟨n,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hn⟩
    exact ⟨n', hn, (PowerlessRelativeClassFunctionAbsolute.map_l
      (hBase := hBase) f n' A).mpr hMap⟩
  · rintro ⟨n, hn, hMap⟩
    exact (hSeq f.val).mpr ⟨n.val, hn,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f n A).mp hMap⟩

/-- 候选 Q 只需 I×A 的读数，即已确定全部 raw 候选行。 -/
private theorem row_iff_l
    {ω A Seq Idx Sat I Q j Z : SecondOrderQuotient.type_l hℳ}
    (hQ : queries_holds_l (𝒩 := RawModel) ω A Seq Idx Sat I Q) (hj : mem_l hℳ j I) :
    PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) A Q j Z ↔
      ∀ x, mem_l hℳ x Z ↔ mem_l hℳ x A ∧
        PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := RawModel) ω A Seq Idx Sat j x := by
  have hPoint (x : SecondOrderQuotient.type_l hℳ) :
      (mem_l hℳ x A ∧ value_l (ℳ := RawModel) Q j x) ↔
        (mem_l hℳ x A ∧ PowerlessRelativeClassSatisfactionAllSlots.query_l
          (ℳ₀ := RawModel) ω A Seq Idx Sat j x) := by
    apply and_congr_right
    intro hx
    exact hQ j hj x hx
  exact ⟨fun h x => (h x).trans (hPoint x), fun h x => (h x).trans (hPoint x).symm⟩

private theorem family_iff_l
    {ω A Seq Idx Sat I Q H : SecondOrderQuotient.type_l hℳ}
    (hQ : queries_holds_l (𝒩 := RawModel) ω A Seq Idx Sat I Q) :
    SecondOrderRowFamilyBounded.holds_l (𝒩 := RawModel) I A Q H ↔
      ∀ Z, mem_l hℳ Z H ↔ ∃ j, mem_l hℳ j I ∧
        ∀ x, mem_l hℳ x Z ↔ mem_l hℳ x A ∧
          PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := RawModel) ω A Seq Idx Sat j x := by
  rw [SecondOrderRowFamilyBounded.family_iff_l hℳ]
  constructor
  · intro h Z
    exact (h Z).trans ⟨fun ⟨j, hj, hRow⟩ => ⟨j, hj, (row_iff_l hQ hj).mp hRow⟩,
      fun ⟨j, hj, hRow⟩ => ⟨j, hj, (row_iff_l hQ hj).mpr hRow⟩⟩
  · intro h Z
    exact (h Z).trans ⟨fun ⟨j, hj, hRow⟩ => ⟨j, hj, (row_iff_l hQ hj).mpr hRow⟩,
      fun ⟨j, hj, hRow⟩ => ⟨j, hj, (row_iff_l hQ hj).mp hRow⟩⟩

/-- 原非空呈现与任意通过局部数据检查的见证具有同一精确全 raw 行像。 -/
private theorem original_image_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    {ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B}
    {C : SecondOrderModel.set_l ℳ}
    (hωW : mem_l hℳ ω.val W)
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G C)
    {A H Sat Seq Idx I Q : SecondOrderQuotient.type_l hℳ}
    (hAW : mem_l hℳ A W) (hSatW : mem_l hℳ Sat W)
    (hSeqW : mem_l hℳ Seq W) (hIdxW : mem_l hℳ Idx W)
    (hG : value_l (ℳ := RawModel) G.val A Sat)
    (hData : data_l (𝒩 := RawModel) ω.val e.val N.val Translation.val W A Sat Seq Idx I Q)
    (hOriginal : SecondOrderMemberDef.nonempty_l hℳ A H) :
    ∀ Z, mem_l hℳ Z H ↔ ∃ j, mem_l hℳ j I ∧
      ∀ x, mem_l hℳ x Z ↔ mem_l hℳ x A ∧
        PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := RawModel)
          ω.val A Seq Idx Sat j x := by
  obtain ⟨A₀, a, ha, V₅, E, D, Q₀, R₀, T₀, F₀, H₀, hAeq, h, hHeq⟩ := hOriginal
  let AClass : type_l hℳ B := ⟨A, ⟨β, W, hW, hAW⟩⟩
  let SeqClass : type_l hℳ B := ⟨Seq, ⟨β, W, hW, hSeqW⟩⟩
  let SatClass : type_l hℳ B := ⟨Sat, ⟨β, W, hW, hSatW⟩⟩
  have hSeqRaw : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val A Seq :=
    (PowerlessFiniteSequencesBounded.spec_iff_of_coverage_l (hCoding.coverage A hAW)).mp hData.1
  have hSeqClass := sequence_class_l hBase (ω := ω) (A := AClass) (Seq := SeqClass) hSeqRaw
  have hSatClass := hCoding.sat_class AClass SeqClass SatClass hAW hSeqRaw hG
  have hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr
      (hCoding.omega_eq.symm ▸ K.omega_spec)
  obtain ⟨he, ht₁, ht₂, ht₃, hN, hPairMap, hPair, hValidReading⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l (hBase := hBase)
      K hCoding.omega_eq hCoding.static
  have heZero : e.val = code_l K (zero_l ℳ) := he
  obtain ⟨V₄, hV₄, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  obtain ⟨U, hU, hNumber, hOnto, hEquality, hMembership⟩ :=
    PowerlessLegacyMemberEnumeration.exists_l K h (A := AClass) hAeq.symm
  have hPreservation := PowerlessLegacyEvaluationPreservation.preservation_l
    (hBase := hBase) K hΩ hCoding.omega_eq heZero hPairMap hPair
      (hValidReading V₄ hV₄) hSatClass ht₁ ht₂ ht₃ hV₄ hCoding.legacy_translation
      h.powers h.domain h.evaluation hU hOnto hEquality hMembership
  have hIdxIncludes (q f t : type_l hℳ B)
      (hq : mem_l hℳ q.val ω.val) (hf : mem_l hℳ f.val SeqClass.val)
      (ht : ordered_l (ℳ := structure_l hℳ B hBase) q f t) : mem_l hℳ t.val Idx := by
    obtain ⟨p, hp, hPairP⟩ := hData.2.1.2 q.val hq f.val hf
    have hEq : p = t.val := SecondOrderPairObjects.ordered_unique_l hℳ hPairP
      ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) q f t).mp ht)
    exact hEq ▸ hp
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := RawModel) W :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW x hx y hy
  have hI := indices_spec_l hTrans
    (fun _ _ _ hx hy hp => PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hW hx hy hp)
    hωW hIdxW hData.2.2.1
  have hImage := PowerlessLegacyImageDefIdentification.image_iff_l
    hBase K (ω := ω) (A := AClass) (Seq := SeqClass) (Sat := SatClass)
      (e := e.val) (N₂ := N.val) (F := Translation.val) (Idx := Idx) (I := I) (U := U)
      hAeq.symm h hCoding.omega_eq heZero hN hCoding.translation_numeric
        hCoding.legacy_translation hU hNumber hSeqClass hPreservation hIdxIncludes hI
  simpa only [AClass, SeqClass, SatClass, hHeq] using hImage

/-- 固定真实编码整包下，任意 raw 候选 H 通过检查当且仅当满足原完整 Def。 -/
theorem checkeriff_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    {ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B}
    {C : SecondOrderModel.set_l ℳ}
    (hωW : mem_l hℳ ω.val W)
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G C)
    {A H : SecondOrderQuotient.type_l hℳ} (hAW : mem_l hℳ A W) :
    holds_l (𝒩 := RawModel) ω.val e.val N.val Translation.val W G.val A H ↔
      SecondOrderMemberDef.spec_l hℳ A H := by
  classical
  constructor
  · rintro (⟨hEmpty, hPair⟩ | ⟨hNonempty, Sat, hSatW, Seq, hSeqW, Idx, hIdxW,
      I, _hIW, Q, _hQW, hG, hData, hFamily⟩)
    · exact Or.inl ⟨hEmpty, hPair⟩
    · obtain ⟨H₀, hOriginal, _⟩ := SecondOrderMemberDef.exists_l hℳ A
      rcases hOriginal with ⟨hEmpty, _⟩ | hOriginal
      · exact False.elim (hNonempty hEmpty)
      · have hImage := original_image_l hBase K hLimit hW hωW hCoding hAW hSatW
          hSeqW hIdxW hG hData hOriginal
        have hRows := (family_iff_l hData.2.2.2).mp hFamily
        have hEq : H = H₀ := SecondOrderQuotient.ext_l hℳ H H₀
          (fun Z => (hRows Z).trans (hImage Z).symm)
        exact hEq.symm ▸ Or.inr hOriginal
  · rintro (⟨hEmpty, hPair⟩ | hOriginal)
    · exact Or.inl ⟨hEmpty, hPair⟩
    · obtain ⟨b, hb⟩ := SecondOrderMemberDef.nonempty_member_l hℳ hOriginal
      obtain ⟨Sat, ⟨hSatW, hG⟩, _⟩ := hCoding.sat_map.2 A hAW
      obtain ⟨_hSatW, Seq, Idx, I, Q, hSeqW, hIdxW, hIW, hQW, hSeq, hIdx, hI, hQ⟩ :=
        hCoding.witnesses A Sat hAW hG
      have hData := data_of_spec_l (hCoding.coverage A hAW) hSeq hIdx hI hQ
      have hImage := original_image_l hBase K hLimit hW hωW hCoding hAW hSatW
        hSeqW hIdxW hG hData hOriginal
      have hFamily := (family_iff_l hData.2.2.2).mpr hImage
      exact Or.inr ⟨fun hEmpty => hEmpty b hb, Sat, hSatW, Seq.val, hSeqW, Idx.val, hIdxW,
        I.val, hIW, Q.val, hQW, hG, hData, hFamily⟩

#print axioms product_spec_l
#print axioms data_of_spec_l
#print axioms indices_spec_l
#print axioms checkeriff_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefImageBoundedReading
