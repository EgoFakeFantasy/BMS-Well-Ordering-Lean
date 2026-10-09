import BMSConstructibleBridge.PowerlessRelativeHierarchyDerives

/-! # 相对并类的纯集合定义与原图定义对应

不同阶段和层值的见证保留在 Prop。纯类公式可以用于既有分离与类归纳接口，
但此对应本身不提供内部可数性、Collection 或最终 BMS 解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCorrespondence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def member_l (hℳ : Theory.Models ℳ theory_m) (B X : type_l hℳ) : Prop :=
  ∃ a c, PowerlessRelativeHierarchySemantics.level_l hℳ B a c ∧ mem_l hℳ X c

theorem iff_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)}
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩) (X : SecondOrderGraph.code_l ℳ) :
    member_l hℳ (mk_l hℳ ⟨B, zero_l ℳ, hB⟩) (mk_l hℳ X) ↔
      SecondOrderRelativeClass.member_l hℳ B hB X := by
  constructor
  · rintro ⟨a, c, hLevel, hX⟩
    obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
    obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
    exact ⟨A, C, (PowerlessRelativeLevelCorrespondence.iff_l hℳ hBase A C).mp hLevel, hX⟩
  · rintro ⟨a, c, hLevel, hX⟩
    exact ⟨mk_l hℳ a, mk_l hℳ c, (PowerlessRelativeLevelCorrespondence.iff_l hℳ hBase a c).mpr hLevel, hX⟩

theorem transitive_l (hℳ : Theory.Models ℳ theory_m) {B X Y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : member_l hℳ B X) (hYX : mem_l hℳ Y X) : member_l hℳ B Y := by
  obtain ⟨W, hW, hWB, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ X
  obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ Y
  rw [← hWB] at hX ⊢
  exact (iff_l hℳ hTrans C).mpr (SecondOrderRelativeClass.transitive_l hℳ ((iff_l hℳ hTrans A).mp hX) hYX)

theorem base_l (hℳ : Theory.Models ℳ theory_m) {B X : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hX : mem_l hℳ X B) : member_l hℳ B X := by
  obtain ⟨W, hW, hWB, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ X
  rw [← hWB] at hX ⊢
  exact (iff_l hℳ hTrans A).mpr (SecondOrderRelativeClass.base_l hℳ W hW hTrans A hX)

theorem base_object_l (hℳ : Theory.Models ℳ theory_m) {B : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) : member_l hℳ B B := by
  obtain ⟨W, hW, hWB, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  rw [← hWB]
  exact (iff_l hℳ hTrans ⟨W, zero_l ℳ, hW⟩).mpr (SecondOrderRelativeLevelZero.base_object_l hℳ W hW hTrans)

#print axioms iff_l
#print axioms transitive_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCorrespondence
