import BMSConstructibleBridge.PowerlessArithmeticRelation
import BMSConstructibleBridge.SecondOrderProgramTotality

/-!
# 原七构造程序的内部集合函数图

消费原编译器的任意模型总性，不重选标准等价程序。
同时保留数码关系实数与 Kuratowski 图，供原程序定理和纯集合标签定理共同调用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticPrograms

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (c : PrimitiveProgram.code_m) :
    ∃ X : PowerlessArithmetic.set_l ω, ∃ G : carrier_l ℳ,
      SecondOrderProgramSemantics.graph_semantics_l (ℳ := 𝒩) (PrimitiveProgram.graph_m c) X ∧
      PowerlessArithmeticRelation.graph_l (he := he) (h₀ := h₀) (F := F) X G ∧ map_l G ω ω := by
  obtain ⟨X, hX, h₁⟩ := SecondOrderProgramTotality.graph_total_l
    (PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)) c
  obtain ⟨G, hG⟩ := PowerlessArithmeticRelation.exists_l hℳ hω (he := he) (h₀ := h₀) (F := F) X
  exact ⟨X, G, h₁, hG, (PowerlessArithmeticRelation.function_l hℳ hG).mp hX⟩

theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {c : PrimitiveProgram.code_m} {X : PowerlessArithmetic.set_l ω} {G : carrier_l ℳ}
    (hX : SecondOrderProgramSemantics.graph_semantics_l (ℳ := 𝒩) (PrimitiveProgram.graph_m c) X)
    (hG : PowerlessArithmeticRelation.graph_l (he := he) (h₀ := h₀) (F := F) X G)
    {Γ Δ : SortContext SecondOrderSyntax.signature_m} (η : Env 𝒩 Γ Δ)
    (s t : Term SecondOrderSyntax.signature_m Γ Δ .num) :
    (PrimitiveProgram.form_m c s t).satisfies η ↔
      value_l G (s.eval η).val (t.eval η).val :=
  (hX η s t).trans (PowerlessArithmeticRelation.value_l hℳ hG _ _).symm

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticPrograms
