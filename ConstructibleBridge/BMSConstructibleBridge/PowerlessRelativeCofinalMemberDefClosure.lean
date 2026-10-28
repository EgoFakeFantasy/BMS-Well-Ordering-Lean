import BMSConstructibleBridge.PowerlessRelativeCofinalSatisfactionForDomain
import BMSConstructibleBridge.PowerlessRelativeLimitFiniteSequencesDirect
import BMSConstructibleBridge.PowerlessRelativeClassStaticCodingReading
import BMSConstructibleBridge.PowerlessRelativeLimitLegacySyntaxGraphs
import BMSConstructibleBridge.PowerlessRelativeLimitLegacyImageIndices
import BMSConstructibleBridge.PowerlessRelativeLimitSelectedSatisfactionRows
import BMSConstructibleBridge.PowerlessLegacyImageDefIdentification
import BMSConstructibleBridge.PowerlessLegacyMemberEnumeration
import BMSConstructibleBridge.PowerlessLegacyEvaluationPreservation

/-! # 给定共尾极限层内的实际原 Def 闭包

背景为原 num/set 语言的 SecondOrderArithmetic.theory_m，层、行查询和
翻译像筛选沿用纯隶属语言 ℒ 的实际规格。本文件从指定真实层 W 的
共尾条件、K.omega∈W 及 A∈W，证明给定原 MemberDef 对象 H 真正属于 W。

非空分支实际构造同一 K 的静态编码包、该 A 的 Sat、完整有限序列及旧
翻译图，并由原呈现的求值图证明全内部数的保持性。规范枚举 U 只留在
原商，既不要求它是 Class，也不把 A 的类内可数性加入前提。精确行像
量化全部 raw 指标、行和元素；层内行族闭包消费该 iff，非仅包含关系。

全部见证保留 Prop，不使用外部标准有限性、外部良基性、Collection 或
Type 层选择。这仍是对象公式及正式 Derives 所需的任意模型语义装配；
不宣称 member-W 的原 global_m 已有类内 ω 枚举或 BMS 终局已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalMemberDefClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderQuotient (mem_l mk_l)
open SecondOrderModel (zero_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β W A H : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 全 raw 序列规格提升到实际类；长度由 ω 的传递性证书提升，而非外部列表。 -/
private theorem sequence_spec_class_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {ω A S : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val A.val S.val) :
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω A S := by
  intro f
  constructor
  · intro hf
    obtain ⟨n, hn, hMap⟩ := (hS f.val).mp hf
    let n' : type_l hℳ B := ⟨n,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hn⟩
    have hMapRaw : SecondOrderFunctionObjects.map_l hℳ f.val n A.val := hMap
    exact ⟨n', hn, (PowerlessRelativeClassFunctionAbsolute.map_l
      (hBase := hBase) f n' A).mpr hMapRaw⟩
  · rintro ⟨n, hn, hMap⟩
    exact (hS f.val).mpr ⟨n.val, hn,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f n A).mp hMap⟩

/-- 共尾极限层含内部 ω 和 A 时，给定实际原 Def(A) 对象仍属于该层。 -/
theorem member_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    (hωW : mem_l hℳ K.omega W) (hAW : mem_l hℳ A W)
    (hDef : SecondOrderMemberDef.spec_l hℳ A H) : mem_l hℳ H W := by
  rcases hDef with ⟨_hEmpty, hPair⟩ | hNonempty
  · exact PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hW hAW hAW hPair
  · obtain ⟨A₀, a, ha, V₅, E, D, Q₀, R₀, T₀, F₀, H₀, rfl, h, rfl⟩ := hNonempty
    let AClass : type_l hℳ B := ⟨mk_l hℳ A₀, ⟨β, W, hW, hAW⟩⟩
    let ω : type_l hℳ B := ⟨K.omega, ⟨β, W, hW, hωW⟩⟩
    have hωEq : ω.val = K.omega := rfl
    have hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω :=
      (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr K.omega_spec
    obtain ⟨e, t₁, t₂, t₃, Pair, N, Valid, heW, _ht₁W, _ht₂W, _ht₃W,
      hPairW, hNW, _hValidW, hStatic, hDomain⟩ :=
      PowerlessRelativeCofinalSatisfactionForDomain.exists_l (hBase := hBase)
        K hLimit hW hCofinal ω hωW hωEq
    obtain ⟨Sat, hSatW, hSat⟩ := hDomain AClass hAW
    obtain ⟨SeqRaw, hSeqW, hSeqRaw⟩ := PowerlessRelativeLimitFiniteSequencesDirect.exists_l
      hBase hLimit hW K.omega_spec hωW hAW
    let Seq : type_l hℳ B := ⟨SeqRaw, ⟨β, W, hW, hSeqW⟩⟩
    have hSeq : PowerlessFiniteSequencesSyntax.spec_l
        (ℳ := structure_l hℳ B hBase) ω AClass Seq :=
      sequence_spec_class_l hBase hSeqRaw
    obtain ⟨he, ht₁, ht₂, ht₃, hN, hPairMap, hPair, hValidReading⟩ :=
      PowerlessRelativeClassStaticCodingReading.reading_l (hBase := hBase) K hωEq hStatic
    have heZero : e.val = code_l K (zero_l ℳ) := he
    obtain ⟨V₄, hV₄, _hV₄Unique⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
    have hValid := hValidReading V₄ hV₄
    obtain ⟨U, hU, hNumber, hOnto, hEquality, hMembership⟩ :=
      PowerlessLegacyMemberEnumeration.exists_l K h (A := AClass) rfl
    obtain ⟨C, hC, _hCUnique⟩ := SecondOrderLegacyFormulaTranslation.exists_l hℳ
    obtain ⟨_OldValid, Translation, _hOldValidW, hTranslationW,
      _hOldValidRaw, _hOldValidNumeric, _hTranslationRaw, hTranslationNumeric⟩ :=
      PowerlessRelativeLimitLegacySyntaxGraphs.exists_l (hBase := hBase)
        K hLimit hW hΩ hωEq hωW hNW hPairW hN hPairMap hPair h.formula_codes hC
    have hPreservation := PowerlessLegacyEvaluationPreservation.preservation_l
      (hBase := hBase) K hΩ hωEq heZero hPairMap hPair hValid hSat ht₁ ht₂ ht₃
        hV₄ hC h.powers h.domain h.evaluation hU hOnto hEquality hMembership
    obtain ⟨Idx, I, hIdxW, hIW, hIdxRaw, hI⟩ :=
      PowerlessRelativeLimitLegacyImageIndices.exists_l hBase hLimit hW
        ω e N Translation AClass Seq hωW heW hNW hTranslationW hAW hSeqW
    have hIdxIncludes (q f t : type_l hℳ B)
        (hq : mem_l hℳ q.val ω.val) (hf : mem_l hℳ f.val Seq.val)
        (ht : ordered_l (ℳ := structure_l hℳ B hBase) q f t) : mem_l hℳ t.val Idx.val :=
      (hIdxRaw t.val).mpr ⟨q.val, f.val, hq, hf,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) q f t).mp ht⟩
    have hImage := PowerlessLegacyImageDefIdentification.image_iff_l
      hBase K (ω := ω) (A := AClass) (Seq := Seq) (Sat := Sat)
        (e := e.val) (N₂ := N.val) (F := Translation.val) (Idx := Idx.val) (I := I.val) (U := U)
        rfl h hωEq heZero hN hTranslationNumeric hC hU hNumber hSeq hPreservation hIdxIncludes hI
    exact PowerlessRelativeLimitSelectedSatisfactionRows.member_l
      hBase hLimit hW ω AClass Seq Idx Sat I hωW hAW hSeqW hIdxW hSatW hIW hImage

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalMemberDefClosure
