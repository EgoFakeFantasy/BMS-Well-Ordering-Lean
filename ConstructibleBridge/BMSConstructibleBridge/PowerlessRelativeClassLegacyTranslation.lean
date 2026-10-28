import BMSConstructibleBridge.PowerlessLegacyTranslationGraph
import BMSConstructibleBridge.PowerlessLegacyTranslationTrace
import BMSConstructibleBridge.PowerlessRelativeClassLegacyValidity
import BMSConstructibleBridge.PowerlessRelativeClassTriangular

/-! # 全部原内部部分翻译的实际 Class 图

完整规格量化全部原商坐标，不要求原翻译实数 C 属于 Class。原合法性
图 G 是实际类参数；无限翻译图由内部有限证书的 Δ₀ 分离构造，不能
由有限表存在直接断言。N、G 可在包装证明内实际取得；T 使用同一 K。

本模块交付语义识别及实际图。通用构图对象推导在 TranslationGraph，
最终源模型解释仍需原 Def 认同、统一历史界和完整 Separation/Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyTranslation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 原实数二元图的数字根码表示；非法和非数字坐标都没有边。 -/
def relation_l (K : source_coding_l hℳ) (C : SecondOrderModel.set_l ℳ)
    (c s : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∃ n m, c = code_l K n ∧ s = code_l K m ∧ SecondOrderPairing.relation_l C n m

theorem numeric_l (K : source_coding_l hℳ) (C : SecondOrderModel.set_l ℳ)
    (n m : SecondOrderModel.num_l ℳ) :
    relation_l K C (code_l K n) (code_l K m) ↔ SecondOrderPairing.relation_l C n m := by
  constructor
  · rintro ⟨i, j, hi, hj, h⟩
    have hI := (PowerlessLegacyNumericReading.code_eq_l K n i).mp hi
    have hJ := (PowerlessLegacyNumericReading.code_eq_l K m j).mp hj
    subst i
    subst j
    exact h
  · intro h
    exact ⟨n, m, rfl, rfl, h⟩

variable {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  (K : source_coding_l hℳ) {ω : type_l hℳ B}
  (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

include hω hωEq

theorem holds_iff_l {N T G : type_l hℳ B}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val)
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {V C : SecondOrderModel.set_l ℳ}
    (hG : ∀ n l, value_l (ℳ := 𝒱) G.val (code_l K n) (code_l K l) ↔
      SecondOrderPairing.relation_l V n l)
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (c s : SecondOrderQuotient.type_l hℳ) :
    PowerlessLegacyTranslationGraph.holds_l («𝒩» := 𝒱)
      ω.val (code_l K (numeral_l ℳ 0)) N.val T.val (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4))
          G.val c s ↔ relation_l K C c s := by
  rw [hωEq]
  have hCertificate (n l q : SecondOrderModel.num_l ℳ) :=
    PowerlessLegacyTranslationTrace.certificate_iff_l K hN hT hSpec hω hωEq hG hV hC n l q
  constructor
  · rintro ⟨hc, _, l, hl, q, hq, hPair, hCertificateRaw⟩
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨c, hc⟩
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨l, hl⟩
    obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨q, hq⟩
    have hcEq : c = code_l K n := (congrArg Subtype.val hn).symm
    have hlEq : l = code_l K m := (congrArg Subtype.val hm).symm
    have hqEq : q = code_l K r := (congrArg Subtype.val hr).symm
    rw [hlEq, hqEq] at hPair
    rw [hcEq, hlEq, hqEq] at hCertificateRaw
    exact ⟨n, SecondOrderPairing.value_l m r, hcEq,
      (PowerlessBoundedNumericPairing.instance_l K hN m r s).mp hPair,
        (hCertificate n m r).mp hCertificateRaw⟩
  · rintro ⟨n, m, rfl, rfl, hEdge⟩
    obtain ⟨l, q, hPair⟩ := SecondOrderUnpairing.surjective_l hℳ m
    have hQuery : SecondOrderLegacyFormulaTranslation.query_l C n l q := by
      unfold SecondOrderLegacyFormulaTranslation.query_l
      rw [hPair]
      exact hEdge
    exact ⟨(numberCode_l K n).property, (numberCode_l K m).property,
      code_l K l, (numberCode_l K l).property, code_l K q, (numberCode_l K q).property,
        (PowerlessBoundedNumericPairing.instance_l K hN l q _).mpr (congrArg (code_l K) hPair.symm),
          (hCertificate n l q).mpr hQuery⟩

theorem exists_l {N T G : type_l hℳ B}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val)
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {V C : SecondOrderModel.set_l ℳ}
    (hG : ∀ n l, value_l (ℳ := 𝒱) G.val (code_l K n) (code_l K l) ↔
      SecondOrderPairing.relation_l V n l)
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) : ∃ F : type_l hℳ B,
      ∀ c s : SecondOrderQuotient.type_l hℳ, value_l (ℳ := 𝒱) F.val c s ↔ relation_l K C c s := by
  have hCode (n : SecondOrderModel.num_l ℳ) :
      PowerlessRelativeClassCorrespondence.member_l hℳ B (code_l K n) := by
    apply PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
    simpa only [hωEq, code_l, member_l, SecondOrderQuotient.structure_l]
      using (numberCode_l K n).property
  let e : type_l hℳ B := ⟨code_l K (numeral_l ℳ 0), hCode (numeral_l ℳ 0)⟩
  let t₁ : type_l hℳ B := ⟨code_l K (numeral_l ℳ 1), hCode (numeral_l ℳ 1)⟩
  let t₂ : type_l hℳ B := ⟨code_l K (numeral_l ℳ 2), hCode (numeral_l ℳ 2)⟩
  let t₃ : type_l hℳ B := ⟨code_l K (numeral_l ℳ 3), hCode (numeral_l ℳ 3)⟩
  let t₄ : type_l hℳ B := ⟨code_l K (numeral_l ℳ 4), hCode (numeral_l ℳ 4)⟩
  obtain ⟨F, hF⟩ := PowerlessLegacyTranslationGraph.exists_l (hBase := hBase) ω e N T t₁ t₂ t₃ t₄ G
  exact ⟨F, fun c s => (hF c s).trans (holds_iff_l K hω hωEq hN hT hSpec hG hV hC c s)⟩

theorem exists_for_coding_l {T : type_l hℳ B}
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {V C : SecondOrderModel.set_l ℳ} (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) : ∃ N G F : type_l hℳ B,
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val ∧
        (∀ n l, value_l (ℳ := 𝒱) G.val (code_l K n) (code_l K l) ↔ SecondOrderPairing.relation_l V n l) ∧
          ∀ c s : SecondOrderQuotient.type_l hℳ, value_l (ℳ := 𝒱) F.val c s ↔ relation_l K C c s := by
  obtain ⟨N, G, hN, hG⟩ := PowerlessRelativeClassLegacyValidity.exists_for_coding_l K hω hωEq hV
  have hRead (n l : SecondOrderModel.num_l ℳ) :
      value_l (ℳ := 𝒱) G.val (code_l K n) (code_l K l) ↔ SecondOrderPairing.relation_l V n l := by
    refine (hG _ _).trans ?_
    change relation_l K V (code_l K n) (code_l K l) ↔ _
    exact numeric_l K V n l
  obtain ⟨F, hF⟩ := exists_l K hω hωEq hN hT hSpec hRead hV hC
  exact ⟨N, G, F, hN, hRead, hF⟩

theorem exists_canonical_l {T : type_l hℳ B}
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val) :
    ∃ V C : SecondOrderModel.set_l ℳ, SecondOrderInternalFormulaSyntax.spec_l V ∧
      SecondOrderLegacyFormulaTranslation.spec_l C ∧ ∃ N G F : type_l hℳ B,
        PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val ∧
          (∀ n l, value_l (ℳ := 𝒱) G.val (code_l K n) (code_l K l) ↔ SecondOrderPairing.relation_l V n l) ∧
            ∀ c s : SecondOrderQuotient.type_l hℳ, value_l (ℳ := 𝒱) F.val c s ↔ relation_l K C c s := by
  obtain ⟨V, hV, _⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  obtain ⟨C, hC, _⟩ := SecondOrderLegacyFormulaTranslation.exists_l hℳ
  obtain ⟨N, G, F, hN, hG, hF⟩ := exists_for_coding_l K hω hωEq hT hSpec hV hC
  exact ⟨V, C, hV, hC, N, G, F, hN, hG, hF⟩

/-- 数值编码母集、三角图、旧合法图和原部分翻译图全在同一实际 Class 内取得。 -/
theorem exists_complete_l : ∃ T : type_l hℳ B,
    map_l (ℳ := 𝒱) T.val K.omega K.omega ∧ PowerlessBMSQuotientPairingBounds.spec_l K T.val ∧
      ∃ V C : SecondOrderModel.set_l ℳ, SecondOrderInternalFormulaSyntax.spec_l V ∧
        SecondOrderLegacyFormulaTranslation.spec_l C ∧ ∃ N G F : type_l hℳ B,
          PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val ∧
            (∀ n l, value_l (ℳ := 𝒱) G.val (code_l K n) (code_l K l) ↔ SecondOrderPairing.relation_l V n l) ∧
              ∀ c s : SecondOrderQuotient.type_l hℳ, value_l (ℳ := 𝒱) F.val c s ↔ relation_l K C c s := by
  have hZero : PowerlessRelativeClassCorrespondence.member_l hℳ B
      (code_l K (SecondOrderModel.zero_l ℳ)) := by
    apply PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
    simpa only [hωEq, code_l, member_l, SecondOrderQuotient.structure_l]
      using (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  let e : type_l hℳ B := ⟨code_l K (SecondOrderModel.zero_l ℳ), hZero⟩
  obtain ⟨S, hS, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (X := ω) hω
  rw [hωEq] at hS
  obtain ⟨T, hT, hSpec⟩ := PowerlessRelativeClassTriangular.exists_spec_l
    (hBase := hBase) K ω e S hωEq rfl hS
  have hMap : map_l (ℳ := 𝒱) T.val K.omega K.omega := by
    simpa only [ThirdOrderSemantics.map_l, ThirdOrderSemantics.member_l, ThirdOrderSemantics.value_l,
      ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l, SecondOrderQuotient.structure_l,
      SecondOrderFunctionObjects.map_l, SecondOrderFunctionObjects.value_l,
      SecondOrderPairObjects.ordered_l, SecondOrderPairObjects.pair_l, hωEq]
      using (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) T ω ω).mp hT.1
  exact ⟨T, hMap, hSpec, exists_canonical_l K hω hωEq hMap hSpec⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyTranslation
