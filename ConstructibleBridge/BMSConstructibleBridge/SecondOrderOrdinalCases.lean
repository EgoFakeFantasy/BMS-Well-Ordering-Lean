import BMSConstructibleBridge.SecondOrderOrdinalSuccessor

/-! # 实际商序数的零、后继、极限分类

分类只用序数的传递性与隶属线序、商外延性。证书保留在 Prop；没有对序数
作宿主归纳，也没有假定模型 ω 标准或整个商模型满足 KP。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalCases

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def successor_l (α β : SecondOrderGraph.code_l ℳ) : Prop :=
  ∀ X, SecondOrderGraph.mem_l X β ↔ SecondOrderGraph.mem_l X α ∨ SecondOrderGraph.eq_l X α

theorem cases_l (hℳ : Theory.Models ℳ theory_m) (β : SecondOrderGraph.code_l ℳ)
    (hβ : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ β)) :
    (∀ X, ¬SecondOrderGraph.mem_l X β) ∨ (∃ α, successor_l α β) ∨
      ((∃ γ, SecondOrderGraph.mem_l γ β) ∧ ∀ γ, SecondOrderGraph.mem_l γ β →
        ∃ δ, SecondOrderGraph.mem_l δ β ∧ SecondOrderGraph.mem_l γ δ) := by
  classical
  by_cases hEmpty : ∀ X, ¬SecondOrderGraph.mem_l X β
  · exact Or.inl hEmpty
  by_cases hSucc : ∃ α, successor_l α β
  · exact Or.inr (Or.inl hSucc)
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · by_contra h
    exact hEmpty (fun X hX => h ⟨X, hX⟩)
  · intro γ hγ
    by_contra h
    have hMax : ∀ δ, SecondOrderGraph.mem_l δ β → ¬SecondOrderGraph.mem_l γ δ :=
      fun δ hδ hγδ => h ⟨δ, hδ, hγδ⟩
    apply hSucc
    refine ⟨γ, fun X => ⟨?_, ?_⟩⟩
    · intro hX
      rcases hβ.wellOrder.linear.compare (SecondOrderQuotient.mk_l hℳ X) hX
        (SecondOrderQuotient.mk_l hℳ γ) hγ with hEq | hXγ | hγX
      · exact Or.inr ((SecondOrderQuotient.eq_iff_l hℳ X γ).mp
          (SecondOrderQuotient.ext_l hℳ _ _ hEq))
      · exact Or.inl hXγ
      · exact False.elim (hMax X hX hγX)
    · rintro (hXγ | hXγ)
      · exact hβ.transitive (SecondOrderQuotient.mk_l hℳ γ) hγ (SecondOrderQuotient.mk_l hℳ X) hXγ
      · exact (SecondOrderGraph.mem_congr_l hℳ hXγ (SecondOrderGraph.refl_l hℳ β)).mpr hγ

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalCases
