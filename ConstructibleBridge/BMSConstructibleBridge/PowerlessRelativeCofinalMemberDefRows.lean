import BMSConstructibleBridge.PowerlessRelativeLimitSatisfactionRowOperator
import BMSConstructibleBridge.PowerlessLegacyImageDefIdentification
import BMSConstructibleBridge.PowerlessLegacyEvaluationPreservation
import BMSConstructibleBridge.PowerlessLegacyMemberEnumeration
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments

/-! # 原 Def 的全部实际成员由同一 Sat 行算子覆盖

原 Z₂ 背景、纯隶属查询。固定同一个共尾编码包和实际母集 A∈W，
其原 Def 的每个 raw 成员都是同一 Sat 输出的一个真实行，行码确实在 W。
非空支使用原五标签呈现及全部内部公式翻译，空支单独处理 Def(∅)={∅}。
不要求 A 有 Class 枚举，不重新选择 Sat 包，不把全部 Sat 行认同为原 Def。

内部有限赋值闭包把实际行码收回壳，行调用闭包因而将 A⊆I 传到 Def(A)⊆I。
这是层级覆盖的语义中间引理；实际可数程序像的装配、W 内枚举及最终
原 Derives 的无条件闭句仍须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalMemberDefRows

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeLimitSatisfactionRowOperator (row_l query_bound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 数字缺省码，或两个内部数码加实际有限参数函数的嵌套对。 -/
def input_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A t : carrier_l 𝒩) : Prop :=
  member_l 𝒩 t ω ∨ ∃ l q n f p,
    member_l 𝒩 l ω ∧ member_l 𝒩 q ω ∧ member_l 𝒩 n ω ∧ map_l f n A ∧
      ordered_l q f p ∧ ordered_l l p t

/-- 母集的全部成员已覆盖时，原内部赋值归纳使真实行码也被覆盖。 -/
theorem input_member_l (K : source_coding_l hℳ) {ω A I t : Raw}
    (hω : ω = K.omega) (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hI : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (hAI : ∀ x, mem_l hℳ x A → mem_l hℳ x I) (ht : input_l (𝒩 := 𝒱) ω A t) :
    mem_l hℳ t I := by
  rcases ht with ht | ⟨l, q, n, f, p, hl, hq, hn, hf, hqf, hlp⟩
  · exact hωI t (hω ▸ ht)
  · have hfI := PowerlessRelativeFiniteHullAssignments.subset_member_l K hωI hI (hω ▸ hn) hf hAI
    have hpI := PowerlessRelativeFiniteHullAssignments.ordered_l hI.1 (hωI q (hω ▸ hq)) hfI hqf
    exact PowerlessRelativeFiniteHullAssignments.ordered_l hI.1 (hωI l (hω ▸ hl)) hpI hlp

theorem rows_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {β W A D : Raw}
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hAW : mem_l hℳ A W) (hDef : SecondOrderMemberDef.spec_l hℳ A D) :
    ∃ R : Raw, mem_l hℳ R W ∧ value_l (ℳ := 𝒱) G.val A R ∧
      ∀ Z : Raw, mem_l hℳ Z D → ∃ t : Raw, mem_l hℳ t W ∧
        input_l (𝒩 := 𝒱) ω.val A t ∧ row_l (𝒩 := 𝒱) ω.val W A R t Z := by
  obtain ⟨he, ht₁, ht₂, ht₃, hN, hPairMap, hPair, hValidReading⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hCode.omega_eq hCode.static
  obtain ⟨R, ⟨hRW, hAR⟩, _⟩ := hCode.sat_map.2 A hAW
  refine ⟨R, hRW, hAR, ?_⟩
  rcases hDef with ⟨hEmpty, hPair⟩ | hDef
  · intro Z hZ
    have hEq : Z = A := ((hPair Z).mp hZ).elim id id
    subst Z
    have heω : mem_l hℳ e.val ω.val := by
      rw [hCode.omega_eq, he]
      exact (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
    exact ⟨e.val, hCode.e_mem, Or.inl heω, fun x =>
      iff_of_false (hEmpty x) (fun h => hEmpty x h.1)⟩
  · obtain ⟨A₀, a, ha, V, E, Domain, Q₀, R₀, T₀, F₀, H₀, rfl, h, rfl⟩ := hDef
    let A' : type_l hℳ B := ⟨mk_l hℳ A₀, ⟨β, W, hW, hAW⟩⟩
    let Sat : type_l hℳ B := ⟨R, ⟨β, W, hW, hRW⟩⟩
    obtain ⟨_hRW, Seq, Idx, I, _Q, hSeqW, hIdxW, hIW, _hQW, hSeqRaw, hIdx, hI, _hQ⟩ :=
      hCode.witnesses A'.val Sat.val hAW hAR
    have hSeq : PowerlessFiniteSequencesSyntax.spec_l
        (ℳ := structure_l hℳ B hBase) ω A' Seq := fun f =>
      (hSeqRaw f.val).trans
        (PowerlessRelativeClassFiniteSequencesDerives.sequence_absolute_l
          (hBase := hBase) ω A' f).symm
    have hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω :=
      (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr
        (hCode.omega_eq.symm ▸ K.omega_spec)
    obtain ⟨V₄, hV₄, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
    obtain ⟨U, hU, hNumber, hOnto, hEquality, hMembership⟩ :=
      PowerlessLegacyMemberEnumeration.exists_l K h (A := A') rfl
    have hSat := hCode.sat_class A' Seq Sat hAW hSeqRaw hAR
    have hPreservation := PowerlessLegacyEvaluationPreservation.preservation_l
      (hBase := hBase) K hΩ hCode.omega_eq he hPairMap hPair (hValidReading V₄ hV₄)
        hSat ht₁ ht₂ ht₃ hV₄ hCode.legacy_translation
        h.powers h.domain h.evaluation hU hOnto hEquality hMembership
    have hIdxIncludes (q f t : type_l hℳ B) (hq : mem_l hℳ q.val ω.val)
        (hf : mem_l hℳ f.val Seq.val) (ht : ordered_l (ℳ := structure_l hℳ B hBase) q f t) :
        mem_l hℳ t.val Idx.val := (hIdx t.val).mpr ⟨q.val, f.val, hq, hf,
          (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) q f t).mp ht⟩
    have hImage := PowerlessLegacyImageDefIdentification.image_iff_l
      hBase K (ω := ω) (A := A') (Seq := Seq) (Sat := Sat) (e := e.val)
        (N₂ := N.val) (F := Translation.val) (Idx := Idx.val) (I := I.val) (U := U)
        rfl h hCode.omega_eq he hN hCode.translation_numeric hCode.legacy_translation
        hU hNumber hSeq hPreservation hIdxIncludes hI
    intro Z hZ
    obtain ⟨t, ht, hRow⟩ := (hImage Z).mp hZ
    obtain ⟨l, hl, p, _hp, q, hq, f, hf, hlp, hqf, _hBody⟩ := (hI t).mp ht
    obtain ⟨n, hn, hfMap⟩ := (hSeqRaw f).mp hf
    refine ⟨t, PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW I.val hIW t ht,
      Or.inr ⟨l, q, n, f, p, hl, hq, hn, hfMap, hqf, hlp⟩, ?_⟩
    intro x
    exact (hRow x).trans (and_congr Iff.rfl
      (query_bound_l (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW)
        hSeqW hIdxW hSeqRaw hIdx).symm)

/-- 实际基础闭包及行调用闭包把母集覆盖传到其原 Def，不预供 Def 覆盖。 -/
theorem subset_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {β W A D I F : Raw}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hωW : mem_l hℳ ω.val W) (hAW : mem_l hℳ A W)
    (hDef : SecondOrderMemberDef.spec_l hℳ A D)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hI : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (hAI : ∀ x, mem_l hℳ x A → mem_l hℳ x I) (hA : mem_l hℳ A I)
    (hF : ∀ s Z : Raw, value_l (ℳ := 𝒱) F s Z ↔ mem_l hℳ s W ∧ mem_l hℳ Z W ∧
      PowerlessRelativeLimitSatisfactionRowOperator.total_l (𝒩 := 𝒱) ω.val W G.val e.val s Z)
    (hCall : ∀ s Z : Raw, mem_l hℳ s I → value_l (ℳ := 𝒱) F s Z → mem_l hℳ Z I) :
    ∀ Z, mem_l hℳ Z D → mem_l hℳ Z I := by
  obtain ⟨R, hRW, hAR, hRows⟩ := rows_l hBase K hW ω e t₁ t₂ t₃ Pair N Valid Translation G hCode hAW hDef
  obtain ⟨_hRW, S, J, _U, _Q, hSW, hJW, _hUW, _hQW, hS, hJ, _hU, _hQ⟩ :=
    hCode.witnesses A R hAW hAR
  intro Z hZD
  obtain ⟨t, htW, ht, hZ⟩ := hRows Z hZD
  have htI := input_member_l K hCode.omega_eq hωI hI hAI ht
  obtain ⟨s, hs⟩ := SecondOrderPairObjects.ordered_exists_l hℳ A t
  have hsI := PowerlessRelativeFiniteHullAssignments.ordered_l hI.1 hA htI hs
  have hsW := PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hW hAW htW hs
  obtain ⟨Y, hYW, hY⟩ := PowerlessRelativeLimitSatisfactionRowOperator.row_exists_l
    hBase hLimit hW hωW hAW hRW htW ⟨S.val, J.val, hSW, hJW, hS, hJ⟩
  have hEq : Z = Y := SecondOrderQuotient.ext_l hℳ _ _ (fun x => (hZ x).trans (hY x).symm)
  have hZW : mem_l hℳ Z W := hEq.symm ▸ hYW
  exact hCall s Z hsI ((hF s Z).mpr ⟨hsW, hZW,
    Or.inl ⟨A, t, R, hAW, htW, hRW, hs, hAR, hZ⟩⟩)

#print axioms input_member_l
#print axioms rows_l
#print axioms subset_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalMemberDefRows
