import BMSConstructibleBridge.PowerlessRelativeHierarchySemantics
import BMSConstructibleBridge.PowerlessWeakSeparationSyntax

/-! # 无 Collection 的实际商序数三歧性

上游三歧定理只需外延性、差集和交集。两种集合分别由实际纯公式的分离
构造，避免为比较序数传入整个 KP 或完整源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalComparison

open Logic FirstOrder SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem compare_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {α β : type_l hℳ}
    (hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ) α)
    (hβ : SetTheory.Structure.IsOrdinal (quotient_l hℳ) β) : α = β ∨ mem_l hℳ α β ∨ mem_l hℳ β α := by
  have hDifference (left right : type_l hℳ) : ∃ d, ∀ x,
      mem_l hℳ x d ↔ mem_l hℳ x right ∧ ¬mem_l hℳ x left := by
    let φ : Formula ℒ [] [.set, .set] := .neg (member_m (.fvar .here) (.fvar (.there .here)))
    let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set] := Env.empty |>.pushFree left
    obtain ⟨d, hd⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
      (SecondOrderSeparationAxiom.models_l hℳ φ η) right
    exact ⟨d, hd⟩
  have hIntersection : ∃ d, ∀ x, mem_l hℳ x d ↔ mem_l hℳ x α ∧ mem_l hℳ x β := by
    let φ : Formula ℒ [] [.set, .set] := member_m (.fvar .here) (.fvar (.there .here))
    let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set] := Env.empty |>.pushFree β
    obtain ⟨d, hd⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
      (SecondOrderSeparationAxiom.models_l hℳ φ η) α
    exact ⟨d, hd⟩
  have hExt : SetTheory.Extensional (quotient_l hℳ) := ⟨SecondOrderQuotient.ext_l hℳ⟩
  rcases SetTheory.Structure.IsOrdinal.trichotomy hExt hα hβ hDifference hIntersection with h | h | h
  · exact Or.inl (SecondOrderQuotient.ext_l hℳ α β h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

#print axioms compare_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalComparison
