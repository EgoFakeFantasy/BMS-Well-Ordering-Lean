import BMSConstructibleBridge.PowerlessRelativeClassLegacyMemberDef
import BMSConstructibleBridge.PowerlessRelativeClassSatisfaction
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionSpecification
import BMSConstructibleBridge.PowerlessRelativeClassLegacyTranslation
import BMSConstructibleBridge.PowerlessRelativeClassPowersReal
import BMSConstructibleBridge.PowerlessRelativeClassProduct
import BMSConstructibleBridge.PowerlessLegacyEnumeratedEvaluation

/-! # 指定实际 Class 满射下的原非空 Def 完整证书装配

背景是原 num/set 语言的 Z₂ 模型及其实际相对 Class 子模型；辅助公式仍
使用纯隶属语言 ℒ。给定 Class ω、A、U 及实际 ω↠A 规格后，在证明内
取得同一 K 的 Sat、旧合法图、旧翻译图、二进制幂图与原求值行族，并
实际证明全内部旧码求值保持性，再构造精确 Class 原 Def 呈现。

Sat 静态包的 Seq(ω,ω) 母集 N₁ 与旧图包装的母集 N₂ 分别保留；后续
原旧码有界读取只消费 N₂ 的完整规格，不混用两个见证。幂实数的 Class
子集代表也不误作二元幂图，二元图另由 graph_l 取得。

全部模型、实数、图和赋值见证保持在 Prop 中，不抽取 Type 选择函数；
不要求 A 的良序，不使用全集 Collection，也不以保持性作为额外入参。
本模块输出任意原模型中的 nonempty_l 语义证书，不是最终原 Derives，
空母集分支及统一后继历史仍由调用端接续。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyMemberDefAssembly

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderQuotient (mem_l)
open SecondOrderModel (num_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase
local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 指定实际 Class 满射的原 Def 对象本身有实际 Class 见证。 -/
theorem exists_l {ω A U : type_l hℳ B}
    (hΩ : omega_l (ℳ := ClassModel) ω)
    (hUraw : map_l (ℳ := RawModel) U.val ω.val A.val)
    (hOnto : ∀ y : SecondOrderQuotient.type_l hℳ, mem_l hℳ y A.val →
      ∃ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x ω.val ∧
        value_l (ℳ := RawModel) U.val x y) :
    ∃ Y : type_l hℳ B, SecondOrderMemberDef.nonempty_l hℳ A.val Y.val := by
  obtain ⟨K, W, hW, e, t₁, t₂, t₃, Pair, _N₁, Valid,
    hωEq, he, hPairMap, hPair, _hN₁, hValid, hDomain⟩ :=
      PowerlessRelativeClassSatisfaction.exists_l (hBase := hBase) hΩ
  obtain ⟨Seq, Eval, Sat, hSystem, hSeqRaw, hSatGraph⟩ := hDomain A
  have hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := ClassModel)
      ω A e t₁ t₂ t₃ Pair Valid Sat :=
    PowerlessRelativeClassSatisfactionSpecification.instance_l (hBase := hBase)
      (hR := hSatGraph) K hωEq hSeqRaw hValid hSystem he hPairMap hPair hW
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hSystem.1
  have hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω A Seq := hSystem.2.2.2.1
  obtain ⟨Idx, hIdx⟩ := PowerlessRelativeClassProduct.exists_l hBase ω Seq
  have hU : map_l (ℳ := RawModel) U.val K.omega A.val := by
    simpa only [hωEq] using hUraw
  have hOntoNumeric : ∀ y : SecondOrderQuotient.type_l hℳ, mem_l hℳ y A.val →
      ∃ v : num_l ℳ, value_l (ℳ := RawModel) U.val (code_l K v) y := by
    intro y hy
    obtain ⟨x, hxω, hxy⟩ := hOnto y hy
    have hxK : mem_l hℳ x K.omega := hωEq ▸ hxω
    obtain ⟨v, hv⟩ := numberCode_surjective_l K ⟨x, hxK⟩
    have hxEq : x = code_l K v := (congrArg Subtype.val hv).symm
    rw [hxEq] at hxy
    exact ⟨v, hxy⟩
  obtain ⟨V, hV, _hVUnique⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  obtain ⟨C, hC, _hCUnique⟩ := SecondOrderLegacyFormulaTranslation.exists_l hℳ
  obtain ⟨N₂, G, F, hN₂, hGnumeric, hFraw⟩ :=
    PowerlessRelativeClassLegacyTranslation.exists_for_coding_l
      (hBase := hBase) K hΩ hωEq hPairMap hPair hV hC
  have hFnumeric (n m : num_l ℳ) :
      value_l (ℳ := RawModel) F.val (code_l K n) (code_l K m) ↔
        SecondOrderPairing.relation_l C n m :=
    (hFraw _ _).trans (PowerlessRelativeClassLegacyTranslation.numeric_l K C n m)
  obtain ⟨E, hE, _EReal, _hERealSubset, _hERealRep⟩ :=
    PowerlessRelativeClassPowersReal.binary_exists_l (hBase := hBase) K hωEq
  obtain ⟨P, hPowerGraph⟩ := PowerlessRelativeClassPowersReal.graph_l (hBase := hBase) K hωEq hE
  have hPnumeric (n m : num_l ℳ) :
      value_l (ℳ := RawModel) P.val (code_l K n) (code_l K m) ↔
        SecondOrderPairing.relation_l E n m := hPowerGraph n m
  obtain ⟨D, Q₀, R₀, T, F₀, hD, hEquality, hMembership, hEvaluation, hFamily⟩ :=
    PowerlessLegacyEnumeratedEvaluation.exists_l K hU E
  have hPreservation := PowerlessLegacyEvaluationPreservation.preservation_l
    (hBase := hBase) K hΩ hωEq he hPairMap hPair hValid hSat ht₁ ht₂ ht₃ hW hC
      hE hD hEvaluation hU hOntoNumeric hEquality hMembership
  obtain ⟨Y, _hPresentation, hNonempty⟩ := PowerlessRelativeClassLegacyMemberDef.exists_l
    (hBase := hBase) K hΩ hωEq he hN₂ hPnumeric hFnumeric hGnumeric hE hV hC hD
      hFamily hEvaluation hPreservation hU hOntoNumeric hEquality hMembership hSeq hIdx
  exact ⟨Y, hNonempty⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyMemberDefAssembly
