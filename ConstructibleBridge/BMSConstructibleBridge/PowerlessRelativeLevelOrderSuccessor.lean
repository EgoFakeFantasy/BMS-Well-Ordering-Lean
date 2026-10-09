import BMSConstructibleBridge.PowerlessLegacyMemberDefWellOrderAmbient
import BMSConstructibleBridge.PowerlessRelativeClassWellOrderEndExtension

/-! # 相对层后继的旧序初段保持

实际后继层已由原 Def 给出。先在同一相对类内构造 Def 的环境良序图，
再把旧序作为初段保留。此处没有指定唯一规范后继，亦没有递归收集
各层序图；所交付的是后续规范递归要消费的实际存在与初段规格。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLevelOrderSuccessor

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l successor_l)
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {ω C R : type_l hℳ B} {a : SecondOrderQuotient.type_l hℳ}
    (hΩ : omega_l (ℳ := 𝒩) ω) (hC : level_l hℳ B a C.val)
    (hR : wellOrder_l (ℳ := 𝒱) C.val R.val) :
    ∃ b : SecondOrderQuotient.type_l hℳ, ∃ D L : type_l hℳ B,
      successor_l hℳ a b ∧ level_l hℳ B b D.val ∧ wellOrder_l (ℳ := 𝒱) D.val L.val ∧
        (∀ x y : SecondOrderQuotient.type_l hℳ, mem_l hℳ x C.val → mem_l hℳ y C.val →
          (value_l (ℳ := 𝒱) L.val x y ↔ value_l (ℳ := 𝒱) R.val x y)) ∧
        (∀ x y : SecondOrderQuotient.type_l hℳ, mem_l hℳ x C.val →
          value_l (ℳ := 𝒱) L.val y x → mem_l hℳ y C.val) := by
  obtain ⟨b, d, hSucc, hD, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC
  let D : type_l hℳ B := ⟨d, PowerlessRelativeLevelClosure.class_l hℳ hBase hD⟩
  obtain ⟨S, hS⟩ := PowerlessLegacyMemberDefWellOrderAmbient.of_spec_l (A := C) (P := R) hΩ hR hDef
  obtain ⟨L, hL, hRead⟩ := PowerlessRelativeClassWellOrderEndExtension.exists_l
    (hBase := hBase) (D := D) hR hS
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hCD : subset_l (ℳ := 𝒱) C.val D.val :=
    SecondOrderMemberDefProperties.contains_l hℳ hDef (fun x y hx hy => hTrans x hx y hy)
  exact ⟨b, D, L, hSucc, hD, hL,
    fun x y hx hy => SecondOrderWellOrderEndExtension.old_l hCD hRead hx hy,
    fun x y hx hyx => SecondOrderWellOrderEndExtension.initial_l hRead hx hyx⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLevelOrderSuccessor
