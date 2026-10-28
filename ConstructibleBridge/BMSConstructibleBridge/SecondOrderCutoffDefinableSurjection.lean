import BMSConstructibleBridge.SecondOrderMemberDefSourceRelation
import BMSConstructibleBridge.PowerlessRelativeClassOntoCountability
import BMSConstructibleBridge.PowerlessRelativeCutoffLimit

/-! # 截断域中有限公式定义的满射反证

实际源公式的关系图进入下一 Def 层，下一层本身属于相对类。
若该公式总且单值，全部值低于 Ω，而又覆盖 Ω，则取得真正的
类内 ω 满射，与首个类内不可数性矛盾。Ω 无须是源域成员。
这是连接已证对象模式的语义中间接口，尚非秩界或最终 BMS 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCutoffDefinableSurjection

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B ω Ω C : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "CType" => PowerlessMemberStructure.type_l (ℳ := 𝒱) C

theorem impossible_l (K : source_coding_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω C) (hωC : mem_l hℳ ω C)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) C (Exists.intro ω hωC)) [] Δ)
    (hTotal : ∀ x : CType, mem_l hℳ x.val ω → ∃! y : CType, φ.satisfies ((η.pushFree y).pushFree x))
    (hRange : ∀ x y : CType, mem_l hℳ x.val ω →
      φ.satisfies ((η.pushFree y).pushFree x) → mem_l hℳ y.val Ω)
    (hOnto : ∀ y : CType, mem_l hℳ y.val Ω →
      ∃ x : CType, mem_l hℳ x.val ω ∧ φ.satisfies ((η.pushFree y).pushFree x)) : False := by
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel
  obtain ⟨β, D, _, hD, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hLevel
  let O : CType := ⟨ω, hωC⟩
  obtain ⟨f, hfD, hRead⟩ := SecondOrderMemberDefSourceRelation.limit_l hℳ hBase hLimit hLevel
    (Exists.intro ω hωC) hDef φ η O
  have hfClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hD) hfD
  have hMap := SecondOrderMemberDefSourceRelation.map_l hℳ (Exists.intro ω hωC)
    (fun x y hx hy => hTrans x hx y hy) φ η O hRead hTotal hRange
  apply PowerlessRelativeClassOntoCountability.cutoff_l (hBase := hBase) K hω hΩ hfClass hMap
  intro y hy
  have hyC := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω C hLevel y hy
  obtain ⟨x, hx, hφ⟩ := hOnto ⟨y, hyC⟩ hy
  exact ⟨x.val, hx, (SecondOrderMemberDefSourceRelation.value_l hℳ (Exists.intro ω hωC)
    φ η O hRead x ⟨y, hyC⟩).mpr ⟨hx, hφ⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCutoffDefinableSurjection
