import BMSConstructibleBridge.PowerlessOrdinalBounded
import BMSConstructibleBridge.SecondOrderOrdinalSuccessor

/-! # 原图商中无 Collection 的 Δ₀ 序数判定

复用既有有界序数 AST，但不调用其完整 PowerlessTheory 模型前提。
实际正则、外延和隶属线序最小元足以核验该判定与上游 IsOrdinal 一致。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalBounded

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) := SecondOrderQuotient.structure_l hℳ

theorem of_transitive_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {a : type_l hℳ}
    (ha : ∀ x, mem_l hℳ x a → ∀ y, mem_l hℳ y x → mem_l hℳ y a)
    (hMembers : ∀ x, mem_l hℳ x a → ∀ y, mem_l hℳ y x → ∀ z, mem_l hℳ z y → mem_l hℳ z x)
    (hCompare : ∀ x y, mem_l hℳ x a → mem_l hℳ y a → mem_l hℳ x y ∨ x = y ∨ mem_l hℳ y x) :
    SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) a := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  apply SecondOrderOrdinalSuccessor.ordinal_of_linear_l hℳ A
  · exact fun X Y hX hY => ha (mk_l hℳ X) hX (mk_l hℳ Y) hY
  · constructor
    · intro x _ hxx
      obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
      exact SecondOrderFoundation.irrefl_l hℳ X hxx
    · exact fun x _ y _ z hz hxy hyz => hMembers z hz y hyz x hxy
    · intro x hx y hy
      rcases hCompare x y hx hy with h | h | h
      · exact Or.inr (Or.inl h)
      · subst y
        exact Or.inl (fun _ => Iff.rfl)
      · exact Or.inr (Or.inr h)

theorem formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (a : Term ℒ Γ Δ .set) :
    (PowerlessOrdinalBounded.ordinal_m a).satisfies η ↔
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) (a.eval η) := by
  have h : (PowerlessOrdinalBounded.ordinal_m a).satisfies η ↔
      PowerlessNaturalOrder.transitive_l (ℳ := quotient_l hℳ) (a.eval η) ∧
        (∀ x, mem_l hℳ x (a.eval η) → PowerlessNaturalOrder.transitive_l (ℳ := quotient_l hℳ) x) ∧
          (∀ x, mem_l hℳ x (a.eval η) → ∀ y, mem_l hℳ y (a.eval η) →
            mem_l hℳ x y ∨ x = y ∨ mem_l hℳ y x) := by
    simp only [PowerlessOrdinalBounded.ordinal_m, Formula.LevyBound.boundedForall, Formula.satisfies,
      PowerlessOrdinalBounded.transitive_formula_l, Formula.LevyBound.membership, membershipLevyBound,
      SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
    rfl
  rw [h]
  constructor
  · rintro ⟨hTrans, hMembers, hCompare⟩
    exact of_transitive_l hℳ (fun x hx y hy => hTrans x y hx hy)
      (fun x hx y hy z hz => hMembers x hx y z hy hz) (fun x y hx hy => hCompare x hx y hy)
  · intro ha
    refine ⟨fun x y hx hy => ha.transitive x hx y hy, ?_, ?_⟩
    · intro x hx y z hy hz
      have hX : SetTheory.Structure.IsOrdinal
          (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) x := by
        apply SetTheory.Structure.IsOrdinal.mem ha
        exact hx
      exact hX.transitive y hy z hz
    · intro x hx y hy
      rcases ha.wellOrder.linear.compare x hx y hy with hSame | hxy | hyx
      · exact Or.inr (Or.inl (SecondOrderQuotient.ext_l hℳ x y hSame))
      · exact Or.inl hxy
      · exact Or.inr (Or.inr hyx)

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalBounded
