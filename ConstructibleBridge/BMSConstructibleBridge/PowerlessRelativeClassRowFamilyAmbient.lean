import BMSConstructibleBridge.PowerlessRelativeClassRowFamily

/-! # 实际 Class 行族的全部原商对象规格

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。本文件把
已有 Class 行族精确读到任意 raw 行对象；反向先用 Δ₀ 分离取得实际 Class
行，再以全 raw 外延性识别给定对象。不能由 Z⊆A 单独推出 Z 是 Class。

这是原 Def 翻译像行族可复用的语义接线，不选择枚举，也不预设 A 可数。
最终对象推导及实际旧 Def 的双向行规格仍由消费端完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRowFamilyAmbient

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassRowFamily (row_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

theorem row_absolute_l (A Q i Z : type_l hℳ B) :
    row_l (ℳ₀ := ClassModel) A Q i Z ↔ row_l (ℳ₀ := RawModel) A.val Q.val i.val Z.val := by
  constructor
  · intro hRow x
    constructor
    · intro hx
      let x' : type_l hℳ B := ⟨x,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Z.property hx⟩
      have h := (hRow x').mp hx
      exact ⟨h.1, (PowerlessRelativeClassFunctionAbsolute.value_l Q i x').mp h.2⟩
    · rintro ⟨hx, hValue⟩
      let x' : type_l hℳ B := ⟨x,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hx⟩
      exact (hRow x').mpr ⟨hx,
        (PowerlessRelativeClassFunctionAbsolute.value_l Q i x').mpr hValue⟩
  · intro hRow x
    exact (hRow x.val).trans
      (and_congr Iff.rfl (PowerlessRelativeClassFunctionAbsolute.value_l Q i x).symm)

include hBase in
/-- 给定实际关系行而非任意子集；通过已构造行的外延相等取得 Class 成员性。 -/
theorem row_class_l {A Q i : type_l hℳ B} {Z : SecondOrderQuotient.type_l hℳ}
    (hRow : row_l (ℳ₀ := RawModel) A.val Q.val i.val Z) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B Z := by
  obtain ⟨W, hW, _⟩ := PowerlessRelativeClassRowFamily.row_exists_l (hBase := hBase) A Q i
  have hWRaw := (row_absolute_l (hBase := hBase) A Q i W).mp hW
  have hZW : Z = W.val := SecondOrderQuotient.ext_l hℳ Z W.val
    (fun x => (hRow x).trans (hWRaw x).symm)
  exact hZW.symm ▸ W.property

include hBase in
/-- 全 raw 指标与行对象均保留；不要求 raw Z 已属于 Class。 -/
theorem exists_l (I A Q : type_l hℳ B) :
    ∃ Y : type_l hℳ B, ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z Y.val ↔
      ∃ i : SecondOrderQuotient.type_l hℳ, mem_l hℳ i I.val ∧
        row_l (ℳ₀ := RawModel) A.val Q.val i Z := by
  obtain ⟨Y, _F, _hMap, _hOnto, _hRead, hRange⟩ :=
    PowerlessRelativeClassRowFamily.exists_l (hBase := hBase) I A Q
  refine ⟨Y, fun Z => ⟨?_, ?_⟩⟩
  · intro hZY
    let Z' : type_l hℳ B := ⟨Z,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hZY⟩
    obtain ⟨i, hi, hRow⟩ := (hRange Z').mp hZY
    exact ⟨i.val, hi, (row_absolute_l (hBase := hBase) A Q i Z').mp hRow⟩
  · rintro ⟨i, hi, hRow⟩
    let i' : type_l hℳ B := ⟨i,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I.property hi⟩
    let Z' : type_l hℳ B := ⟨Z, row_class_l (hBase := hBase) (i := i') hRow⟩
    exact (hRange Z').mpr ⟨i', hi, (row_absolute_l (hBase := hBase) A Q i' Z').mpr hRow⟩

#print axioms row_absolute_l
#print axioms row_class_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRowFamilyAmbient
