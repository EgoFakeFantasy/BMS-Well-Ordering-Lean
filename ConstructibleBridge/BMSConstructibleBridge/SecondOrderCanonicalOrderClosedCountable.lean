import BMSConstructibleBridge.PowerlessRelativeClassLegacyDefClosure
import BMSConstructibleBridge.SecondOrderCanonicalOrderCountableDerives
import BMSConstructibleBridge.SecondOrderCanonicalOrderPreservation

/-! # 不预设原 Def 输出属于 Class 的可数规范后继

对象语言仍为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。实际
Class 枚举先给出母集的类内可数性，再由原 Def 闭包把任意 raw Def 见证
提升为 Class，消费已有固定六对象包的统一后继总性。编码 K 仅用于 ω
及可数性转换，不与已有后继包的编码混配。

本文件交付的是任意原模型中的单步语义接口；没有收集枚举或规范序
历史，没有 Type 层见证选择，也尚未封装新的对象句或 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderClosedCountable

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

/-- 固定同一六对象包后，原 Def 输出只需给为任意 raw 对象。 -/
theorem class_total_l {ω : type_l hℳ B} (hΩ : omega_l (ℳ := ClassModel) ω) :
    ∃ e t₁ t₂ t₃ Pair Valid : type_l hℳ B,
      ∀ A P G : type_l hℳ B, ∀ D : SecondOrderQuotient.type_l hℳ,
        wellOrder_l (ℳ := RawModel) A.val P.val →
        (∀ x y, mem_l hℳ x A.val → mem_l hℳ y x → mem_l hℳ y A.val) →
        SecondOrderMemberDef.spec_l hℳ A.val D →
        map_l (ℳ := RawModel) G.val ω.val A.val →
        (∀ x, mem_l hℳ x A.val → ∃ i,
          mem_l hℳ i ω.val ∧ value_l (ℳ := RawModel) G.val i x) →
        PowerlessRelativeClassCorrespondence.member_l hℳ B D ∧
        ∃ E : type_l hℳ B,
          SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := RawModel)
            ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D E.val ∧
          wellOrder_l (ℳ := RawModel) D E.val ∧
          SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := RawModel) A.val P.val D E.val ∧
          PowerlessRelativeOrdinalCutoff.countable_l B ω.val D ∧
          ∀ E' : SecondOrderQuotient.type_l hℳ,
            SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := RawModel)
              ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D E' →
              E' = E.val := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωRaw : SecondOrderOmega.omega_l hℳ ω.val :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hΩ
  obtain ⟨e, t₁, t₂, t₃, Pair, Valid, hAll⟩ :=
    SecondOrderCanonicalOrderCountableDerives.class_total_l (hBase := hBase) hΩ
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  intro A P G D hP hTrans hDef hG hOnto
  have hCountA := PowerlessRelativeClassOntoCountability.countable_l
    (hBase := hBase) K hωRaw A.property G.property hG hOnto
  have hDClass := PowerlessRelativeClassLegacyDefClosure.class_l
    K hBase hωRaw A.property hCountA hDef
  let D' : type_l hℳ B := ⟨D, hDClass⟩
  obtain ⟨E, hStep, hOrder, hCountD, hUnique⟩ :=
    hAll A P D' G hP hTrans hDef hG hOnto
  exact ⟨hDClass, E, hStep, hOrder,
    SecondOrderCanonicalOrderPreservation.extension_l hStep hTrans hDef, hCountD, hUnique⟩

#print axioms class_total_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderClosedCountable
