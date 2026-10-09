import BMSConstructibleBridge.PowerlessRelativeClassRowFamily
import BMSConstructibleBridge.SecondOrderEnumeratedMemberDef
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.PowerlessFormulaValidityReading

/-! # 原合法索引的精确实际 Class 行族

给定实际 Class 指标集 I、母集 A、指定枚举 U 和统一查询图 Q，先取原
Class 行族。索引图与查询图的全 raw 规格把每行精确读成原数值行的 U 像。
前向由 Y 的成员闭包取得实际 Class 行；后向对任意 raw 集合 Z 先构造
实际 Class 行 W，再用全部 raw 元素的外延性证明 Z = W.val，才将 Z 放入 Y。

不从 Z 是某个 Class 母集合的子集推断 Z 属于 Class，不删除任意 raw x
或 raw Z 的量词，不使用 U 输出唯一性或 Type 层选择。本模块提供原
EnumeratedMemberDef.collection 字段的语义接线，不宣称完成最终 BMS
或原推导关系 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyRowFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderModel (num_l set_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

/-- 实际 Class 行与原数值行的指定 U 像，在全部 raw 输出上双向相等。 -/
theorem row_reading_l (K : source_coding_l hℳ) {A U Q : type_l hℳ B}
    (hU : map_l (ℳ := RawModel) U.val K.omega A.val) {V E F₀ : set_l ℳ}
    (hQ : ∀ i x : SecondOrderQuotient.type_l hℳ,
      value_l (ℳ := RawModel) Q.val i x ↔ ∃ n v,
        i = code_l K n ∧ value_l (ℳ := RawModel) U.val (code_l K v) x ∧
          SecondOrderLegalFormulaIndex.spec_l V E n ∧ SecondOrderPairing.relation_l F₀ n v)
    {i Z : type_l hℳ B} {n : num_l ℳ} (hi : i.val = code_l K n)
    (hn : SecondOrderLegalFormulaIndex.spec_l V E n) :
    PowerlessRelativeClassRowFamily.row_l (ℳ₀ := ClassModel) A Q i Z ↔
      ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x Z.val ↔
        ∃ v, SecondOrderPairing.relation_l F₀ n v ∧
          value_l (ℳ := RawModel) U.val (code_l K v) x := by
  have hQn (x : SecondOrderQuotient.type_l hℳ) :
      value_l (ℳ := RawModel) Q.val i.val x ↔
        ∃ v, SecondOrderPairing.relation_l F₀ n v ∧
          value_l (ℳ := RawModel) U.val (code_l K v) x := by
    constructor
    · intro hValue
      obtain ⟨m, v, him, hv, _hm, hF⟩ := (hQ i.val x).mp hValue
      have hm : m = n := numberCode_injective_l K (Subtype.ext (him.symm.trans hi))
      subst m
      exact ⟨v, hF, hv⟩
    · rintro ⟨v, hF, hv⟩
      exact (hQ i.val x).mpr ⟨n, v, hi, hv, hn, hF⟩
  constructor
  · intro hRow x
    constructor
    · intro hxZ
      let x' : type_l hℳ B := ⟨x,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Z.property hxZ⟩
      have hValue := ((hRow x').mp hxZ).2
      exact (hQn x).mp ((PowerlessRelativeClassFunctionAbsolute.value_l
        (hBase := hBase) Q i x').mp hValue)
    · rintro ⟨v, hF, hv⟩
      have hxA := (SecondOrderFunctionProperties.value_mem_l hℳ hU hv).2
      let x' : type_l hℳ B := ⟨x,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hxA⟩
      exact (hRow x').mpr ⟨hxA,
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Q i x').mpr
          ((hQn x).mpr ⟨v, hF, hv⟩)⟩
  · intro hSlice x
    constructor
    · intro hxZ
      obtain ⟨v, hF, hv⟩ := (hSlice x.val).mp hxZ
      have hxA := (SecondOrderFunctionProperties.value_mem_l hℳ hU hv).2
      exact ⟨hxA, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Q i x).mpr
        ((hQn x.val).mpr ⟨v, hF, hv⟩)⟩
    · rintro ⟨_hxA, hValue⟩
      exact (hSlice x.val).mpr ((hQn x.val).mp
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Q i x).mp hValue))

include hBase in
/-- 精确 Class 行族满足原 presentation 的全部 raw collection 规格。 -/
theorem exists_l (K : source_coding_l hℳ) {I A U Q : type_l hℳ B}
    (hU : map_l (ℳ := RawModel) U.val K.omega A.val) {V E F₀ : set_l ℳ}
    (hI : ∀ i : SecondOrderQuotient.type_l hℳ, mem_l hℳ i I.val ↔
      ∃ n, i = code_l K n ∧ SecondOrderLegalFormulaIndex.spec_l V E n)
    (hQ : ∀ i x : SecondOrderQuotient.type_l hℳ,
      value_l (ℳ := RawModel) Q.val i x ↔ ∃ n v,
        i = code_l K n ∧ value_l (ℳ := RawModel) U.val (code_l K v) x ∧
          SecondOrderLegalFormulaIndex.spec_l V E n ∧ SecondOrderPairing.relation_l F₀ n v) :
    ∃ Y : type_l hℳ B, ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z Y.val ↔
      ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧
        ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x Z ↔
          ∃ v, SecondOrderPairing.relation_l F₀ i v ∧
            value_l (ℳ := RawModel) U.val (code_l K v) x := by
  obtain ⟨Y, _F, _hMap, _hOnto, _hRead, hRange⟩ :=
    PowerlessRelativeClassRowFamily.exists_l (hBase := hBase) I A Q
  refine ⟨Y, fun Z => ?_⟩
  constructor
  · intro hZY
    let Z' : type_l hℳ B := ⟨Z,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hZY⟩
    obtain ⟨i, hiI, hRow⟩ := (hRange Z').mp hZY
    obtain ⟨n, hi, hn⟩ := (hI i.val).mp hiI
    exact ⟨n, hn, (row_reading_l K hU hQ hi hn).mp hRow⟩
  · rintro ⟨n, hn, hSlice⟩
    have hCodeI : mem_l hℳ (code_l K n) I.val := (hI _).mpr ⟨n, rfl, hn⟩
    let i : type_l hℳ B := ⟨code_l K n,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I.property hCodeI⟩
    obtain ⟨W, hRow, _hUnique⟩ := PowerlessRelativeClassRowFamily.row_exists_l (hBase := hBase) A Q i
    have hWSlice := (row_reading_l K hU hQ (i := i) rfl hn).mp hRow
    have hZW : Z = W.val := by
      apply SecondOrderQuotient.ext_l hℳ
      intro x
      exact (hSlice x).trans (hWSlice x).symm
    rw [hZW]
    exact (hRange W).mpr ⟨i, hCodeI, hRow⟩

#print axioms row_reading_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyRowFamily
