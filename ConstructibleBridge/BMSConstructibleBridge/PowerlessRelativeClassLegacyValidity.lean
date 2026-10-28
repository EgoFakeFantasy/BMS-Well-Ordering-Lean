import BMSConstructibleBridge.PowerlessLegacyValidityGraph
import BMSConstructibleBridge.PowerlessLegacyValidityTrace
import BMSConstructibleBridge.PowerlessRelationalCodeValidity
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives

/-! # 原五标签合法性关系的实际 Class 图

在同一原 Z₂ 编码 K 下，由二维有限证书取得全部内部旧码的合法性图。
零至四的标签直接由给定 Class ω 的成员闭包取得，不作 Type 层选择，
也不要求原实数 V 自身属于类。图规格覆盖全部原商坐标，不限于标准码。

完整有限序列母集 N 可在证明内实际构造；原旧合法性 V 的存在也可用
原内部递归接口取得。本模块只交付语义 Class 图及其完整守卫，不建立
翻译图、统一历史、完整源模型或 BMS 的对象推导终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyValidity

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  (K : source_coding_l hℳ) {ω : type_l hℳ B}
  (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

include hω hωEq

theorem certificate_iff_l {N : type_l hℳ B}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (c l : SecondOrderQuotient.type_l hℳ) :
    PowerlessLegacyValidityBounded.certificate_holds_l («𝒩» := 𝒱)
      ω.val (code_l K (numeral_l ℳ 0)) N.val
        (code_l K (numeral_l ℳ 1)) (code_l K (numeral_l ℳ 2))
        (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4)) c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l := by
  have hRead (n m : SecondOrderModel.num_l ℳ) :
      PowerlessLegacyValidityBounded.certificate_holds_l («𝒩» := 𝒱)
        ω.val (code_l K (numeral_l ℳ 0)) N.val
          (code_l K (numeral_l ℳ 1)) (code_l K (numeral_l ℳ 2))
          (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4)) (code_l K n) (code_l K m) ↔
        SecondOrderPairing.relation_l V n m := by
    rw [hωEq]
    exact PowerlessLegacyValidityTrace.certificate_iff_l K hN hω hωEq hV n m
  constructor
  · intro hCertificate
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨c, hωEq ▸ hCertificate.1⟩
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨l, hωEq ▸ hCertificate.2.1⟩
    have hc : c = code_l K n := (congrArg Subtype.val hn).symm
    have hl : l = code_l K m := (congrArg Subtype.val hm).symm
    refine ⟨n, m, hc, hl, ?_⟩
    rw [hc, hl] at hCertificate
    exact (hRead n m).mp hCertificate
  · rintro ⟨n, m, rfl, rfl, hValid⟩
    exact (hRead n m).mpr hValid

theorem exists_l {N : type_l hℳ B}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderInternalFormulaSyntax.spec_l V) :
    ∃ F : type_l hℳ B, ∀ c l : SecondOrderQuotient.type_l hℳ,
      value_l (ℳ := 𝒱) F.val c l ↔ PowerlessRelationalCodeValidity.valid_l K V c l := by
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
  obtain ⟨F, hF⟩ := PowerlessLegacyValidityGraph.exists_l (hBase := hBase) ω e N t₁ t₂ t₃ t₄
  exact ⟨F, fun c l => (hF c l).trans (certificate_iff_l K hω hωEq hN hV c l)⟩

/-- 完整数值有限序列母集实际构造，不留作未证的存在前提。 -/
theorem exists_for_coding_l {V : SecondOrderModel.set_l ℳ}
    (hV : SecondOrderInternalFormulaSyntax.spec_l V) : ∃ N F : type_l hℳ B,
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val ∧
      ∀ c l : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := 𝒱) F.val c l ↔ PowerlessRelationalCodeValidity.valid_l K V c l := by
  obtain ⟨N, hN, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (X := ω) hω
  rw [hωEq] at hN
  obtain ⟨F, hF⟩ := exists_l K hω hωEq hN hV
  exact ⟨N, F, hN, hF⟩

/-- 原旧合法性实数只在 Prop 中取得；不选择一个全局 Type 值。 -/
theorem exists_canonical_l : ∃ V : SecondOrderModel.set_l ℳ,
    SecondOrderInternalFormulaSyntax.spec_l V ∧ ∃ N F : type_l hℳ B,
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N.val ∧
        ∀ c l : SecondOrderQuotient.type_l hℳ,
          value_l (ℳ := 𝒱) F.val c l ↔ PowerlessRelationalCodeValidity.valid_l K V c l := by
  obtain ⟨V, hV, _⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  obtain ⟨N, F, hN, hF⟩ := exists_for_coding_l K hω hωEq hV
  exact ⟨V, hV, N, F, hN, hF⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyValidity
