import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 固定极限层中有限源参数的严格先前层界

归纳仅针对对象公式的外部有限自由上下文。先前层本身进入其后继 Def，
故仍属于给定非零极限层；再用两参数共同界和传递性提升已有参数。
不收集任意内部参数族，也不抽取 Type 层的层界选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitParameterBounds

open Logic FirstOrder
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : type_l hℳ}

theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    {X : type_l hℳ} (hX : mem_l hℳ X C)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C) :
    ∃ a c, mem_l hℳ a β ∧ level_l hℳ B a c ∧ mem_l hℳ X c ∧
      ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) c := by
  induction Δ with
  | nil =>
      obtain ⟨a, c, ha, hc, hXc⟩ := (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hC X).mp hX
      exact ⟨a, c, ha, hc, hXc, fun _ v => nomatch v⟩
  | cons s Δ ih =>
      cases s
      let η' : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
        { boundVal := fun v => nomatch v
          freeVal := fun v => η.freeVal (.there v) }
      obtain ⟨a, c, ha, hc, hXc, hTail⟩ := ih η' (fun _ v => hParams _ (.there v))
      obtain ⟨b, d, hb, hd, hDef⟩ := PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hC ha hc
      have hcC : mem_l hℳ c C := (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hC c).mpr
        ⟨b, d, hb, hd, SecondOrderMemberDefProperties.mother_member_l hℳ hDef⟩
      obtain ⟨e, f, he, hf, hcf, hHead⟩ :=
        PowerlessRelativeLimitClosure.common_l hℳ hBase hLimit hC hcC (hParams _ .here)
      have hLift x (hx : mem_l hℳ x c) :=
        PowerlessRelativeLevelClosure.transitive_l hℳ hBase hf c hcf x hx
      refine ⟨e, f, he, hf, hLift X hXc, ?_⟩
      intro t v
      cases t
      cases v with
      | here => exact hHead
      | there v => exact hLift (η.freeVal (.there v)) (hTail _ v)

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitParameterBounds
