import BMSConstructibleBridge.PowerlessRelativeClassLegacyImageIndices
import BMSConstructibleBridge.PowerlessRelativeClassSelectedSatisfactionRows
import BMSConstructibleBridge.PowerlessLegacyImageDefIdentification
import BMSConstructibleBridge.PowerlessLegacyMemberEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassSatisfaction
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionSpecification
import BMSConstructibleBridge.PowerlessRelativeClassLegacyTranslation
import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute

/-! # 任意实际 Class 母集的原 Def 精确翻译像闭包

背景为原 num/set 语言的 SecondOrderArithmetic.theory_m，辅助筛选 AST
为纯隶属语言 ℒ。非空分支保留原 Def 呈现的合法图、二进制幂、求值图
及精确行族，不另造旧求值数据。实际 Sat 包、完整数字序列与旧翻译图
共用同一 K，受限 Class 指标只包含旧四标签翻译像及从槽 l 起的常值尾。

规范成员枚举 U 留在原商；它仅供全 raw 行像的认同，不进入类内参数，
也不要求 U 属于 Class 或 A 类内可数。正向构造实际有限 Class 赋值，
反向以原成员呈现恢复参数码。所有坐标遍历全部内部数，所有行及元素
读数量化全部 raw 商对象。原行像认同消费独立共享 image_iff_l，最后
由原商外延性认同实际原 Def 对象。

本文件给出原 Def 对象的 Class 成员语义证书；对象闭句及原 Derives
封装由调用端接续，不声称统一枚举族、共同历史或 BMS 终局已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyImageDefClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderQuotient (mem_l mk_l)
open SecondOrderModel (num_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 非空原呈现的精确集合等于受限翻译像的实际 Class 行族。 -/
theorem nonempty_class_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {A H : SecondOrderQuotient.type_l hℳ}
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hDef : SecondOrderMemberDef.nonempty_l hℳ A H) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H := by
  obtain ⟨A₀, a, ha, V, E, D, Q₀, R₀, T₀, F₀, H₀, rfl, h, rfl⟩ := hDef
  let A : type_l hℳ B := ⟨mk_l hℳ A₀, hA⟩
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  let ω : type_l hℳ B := ⟨K₀.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K₀ hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K₀.omega_spec)⟩
  have hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr K₀.omega_spec
  obtain ⟨K, W, hW, e, t₁, t₂, t₃, Pair, _N₁, Valid,
    hωEq, he, hPairMap, hPair, _hN₁, hValid, hDomain⟩ :=
      PowerlessRelativeClassSatisfaction.exists_l (hBase := hBase) hΩ
  obtain ⟨Seq, Eval, Sat, hSystem, hSeqRaw, hSatGraph⟩ := hDomain A
  have hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
      ω A e t₁ t₂ t₃ Pair Valid Sat :=
    PowerlessRelativeClassSatisfactionSpecification.instance_l (hBase := hBase)
      (hR := hSatGraph) K hωEq hSeqRaw hValid hSystem he hPairMap hPair hW
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hSystem.1
  have hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω A Seq := hSystem.2.2.2.1
  obtain ⟨U, hU, hNumber, hOnto, hEquality, hMembership⟩ :=
    PowerlessLegacyMemberEnumeration.exists_l K h (A := A) rfl
  obtain ⟨C, hC, _hCUnique⟩ := SecondOrderLegacyFormulaTranslation.exists_l hℳ
  obtain ⟨N₂, _G, F, hN₂, _hGnumeric, hFraw⟩ :=
    PowerlessRelativeClassLegacyTranslation.exists_for_coding_l
      (hBase := hBase) K hΩ hωEq hPairMap hPair h.formula_codes hC
  have hFnumeric (n m : num_l ℳ) : value_l (ℳ := RawModel) F.val (code_l K n) (code_l K m) ↔
      SecondOrderPairing.relation_l C n m :=
    (hFraw _ _).trans (PowerlessRelativeClassLegacyTranslation.numeric_l K C n m)
  have hPreservation := PowerlessLegacyEvaluationPreservation.preservation_l
    (hBase := hBase) K hΩ hωEq he hPairMap hPair hValid hSat ht₁ ht₂ ht₃ hW hC
      h.powers h.domain h.evaluation hU hOnto hEquality hMembership
  obtain ⟨Idx, I, hIdx, hI⟩ := PowerlessRelativeClassLegacyImageIndices.exists_l
    (hBase := hBase) ω e N₂ F A Seq
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassSelectedSatisfactionRows.exists_l
    (hBase := hBase) ω A Seq Idx Sat I
  have hIdxIncludes (q f t : type_l hℳ B)
      (hq : mem_l hℳ q.val ω.val) (hf : mem_l hℳ f.val Seq.val)
      (ht : ordered_l (ℳ := structure_l hℳ B hBase) q f t) : mem_l hℳ t.val Idx.val :=
    (hIdx t).mpr ⟨q, f, hq, hf, ht⟩
  have hImage := PowerlessLegacyImageDefIdentification.image_iff_l
    hBase K (ω := ω) (A := A) (Seq := Seq) (Sat := Sat)
      (e := e.val) (N₂ := N₂.val) (F := F.val) (Idx := Idx.val) (I := I.val) (U := U)
      rfl h hωEq he hN₂ hFnumeric hC hU hNumber hSeq hPreservation hIdxIncludes hI
  have hEqual : Y.val = mk_l hℳ H₀ := by
    apply SecondOrderQuotient.ext_l hℳ
    intro Z
    exact (hY Z).trans (hImage Z).symm
  exact hEqual ▸ Y.property

/-- 任意实际 Class A 的实际原 Def 对象仍属 Class，不要求类内枚举。 -/
theorem class_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {A H : SecondOrderQuotient.type_l hℳ}
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hDef : SecondOrderMemberDef.spec_l hℳ A H) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H := by
  rcases hDef with ⟨_hEmpty, hPair⟩ | hNonempty
  · exact PowerlessRelativeClassPair.pair_l hℳ hBase hA hA hPair
  · exact nonempty_class_l hBase hA hNonempty

#print axioms nonempty_class_l
#print axioms class_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyImageDefClosure
