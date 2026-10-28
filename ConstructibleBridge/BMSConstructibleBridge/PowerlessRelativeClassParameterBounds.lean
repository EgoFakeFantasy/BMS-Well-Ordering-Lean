import BMSConstructibleBridge.PowerlessRelativeClassBounded

/-! # 类子模型有限源环境的共同层界

只对源语法的外部有限自由上下文作归纳。量化模型内部数的有限序列不能
由这里替代，更不能把本结论用作任意集合参数族的 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassParameterBounds

open Logic FirstOrder
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ) (X : type_l hℳ B) :
    ∃ a c, PowerlessRelativeHierarchySemantics.level_l hℳ B a c ∧ mem_l hℳ X.val c ∧
      ∀ (s : SetTheory.SetSort) (v : Variable Δ s), mem_l hℳ (η.freeVal v).val c := by
  induction Δ with
  | nil =>
      obtain ⟨a, c, hc, hXc⟩ := X.property
      exact ⟨a, c, hc, hXc, fun _ v => nomatch v⟩
  | cons s Δ ih =>
      cases s
      let η' : Env (structure_l hℳ B hBase) [] Δ :=
        { boundVal := fun v => nomatch v
          freeVal := fun v => η.freeVal (.there v) }
      obtain ⟨a, c, hc, hXc, hParams⟩ := ih η'
      have hC := PowerlessRelativeLevelClosure.class_l hℳ hBase hc
      obtain ⟨b, d, hd, hCd, hyD⟩ := PowerlessRelativeClassBounds.common_l hℳ hBase hC (η.freeVal .here).property
      have hLift x (hx : mem_l hℳ x c) := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hd c hCd x hx
      refine ⟨b, d, hd, hLift X.val hXc, ?_⟩
      intro t v
      cases t
      cases v with
      | here => exact hyD
      | there v => exact hLift (η.freeVal (.there v)).val (hParams _ v)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassParameterBounds
