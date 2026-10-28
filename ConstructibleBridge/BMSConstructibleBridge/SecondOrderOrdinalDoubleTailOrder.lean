import BMSConstructibleBridge.SecondOrderOrdinalDoubleTailMembers
import BMSConstructibleBridge.SecondOrderOrdinalSuccessor

/-! # 双指标尾节点的传递性与序数性

精确成员规格直接给出所有尾节点的传递性；字典序比较给出隶属线序，
原商正则性再给出集合意义下的良序。因此无需额外的序数归纳或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalDoubleTailOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderOrdinalDoubleTailGraph
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem lex_trans_l (hℳ : Theory.Models ℳ theory_m) {i j k l n m : num_l ℳ}
    (h₁ : lex_l i j k l) (h₂ : lex_l k l n m) : lex_l i j n m := by
  rcases h₁ with h₁ | ⟨rfl, h₁⟩
  · rcases h₂ with h₂ | ⟨rfl, _⟩
    · exact Or.inl (SecondOrderOrder.trans_l hℳ h₁ h₂)
    · exact Or.inl h₁
  · rcases h₂ with h₂ | ⟨rfl, h₂⟩
    · exact Or.inl h₂
    · exact Or.inr ⟨rfl, SecondOrderOrder.trans_l hℳ h₁ h₂⟩

theorem lex_compare_l (hℳ : Theory.Models ℳ theory_m) (n m i j : num_l ℳ) :
    lex_l n m i j ∨ (n = i ∧ m = j) ∨ lex_l i j n m := by
  rcases SecondOrderOrder.trichotomy_l hℳ n i with h | rfl | h
  · exact Or.inl (Or.inl h)
  · rcases SecondOrderOrder.trichotomy_l hℳ m j with h | rfl | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inl h))

variable (hℳ : Theory.Models ℳ theory_m) {S G : SecondOrderModel.set_l ℳ} {r : num_l ℳ}
  (hG : spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a)

noncomputable abbrev base_l (r : num_l ℳ) : type_l hℳ := mk_l hℳ ⟨S, r, hS r⟩
noncomputable abbrev tail_l (n m : num_l ℳ) : type_l hℳ := mk_l hℳ (code_l hℳ hG hS n m)

theorem reading_l (n m : num_l ℳ) (x : type_l hℳ) :
    mem_l hℳ x (tail_l hℳ hG hS n m) ↔
      mem_l hℳ x (base_l hℳ hS r) ∨ x = base_l hℳ hS r ∨
        ∃ i j, lex_l i j n m ∧ x = tail_l hℳ hG hS i j := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact (SecondOrderOrdinalDoubleTailMembers.members_l hℳ hG hS n m X).trans
    (or_congr Iff.rfl (or_congr (SecondOrderQuotient.eq_iff_l hℳ _ _).symm
      (exists_congr (fun _ => exists_congr (fun _ =>
        and_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ _ _).symm)))))

variable (hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (base_l hℳ hS r))

include hα

theorem transitive_l (n m : num_l ℳ) (x : type_l hℳ)
    (hx : mem_l hℳ x (tail_l hℳ hG hS n m))
    (y : type_l hℳ) (hy : mem_l hℳ y x) : mem_l hℳ y (tail_l hℳ hG hS n m) := by
  apply (reading_l hℳ hG hS n m y).mpr
  rcases (reading_l hℳ hG hS n m x).mp hx with hx | rfl | ⟨i, j, hij, rfl⟩
  · exact Or.inl (hα.transitive x hx y hy)
  · exact Or.inl hy
  · rcases (reading_l hℳ hG hS i j y).mp hy with hy | hy | ⟨k, l, hkl, hy⟩
    · exact Or.inl hy
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr ⟨k, l, lex_trans_l hℳ hkl hij, hy⟩)

/-- 任意只含基础成员、基础根和尾节点的集合，其成员关系已经是线序。 -/
theorem linear_l (C : type_l hℳ)
    (hTypes : ∀ x, mem_l hℳ x C → mem_l hℳ x (base_l hℳ hS r) ∨
      x = base_l hℳ hS r ∨ ∃ n m, x = tail_l hℳ hG hS n m) :
    SetTheory.Structure.MembershipLinearOrder (quotient_l hℳ) C := by
  constructor
  · intro x _ hx
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact SecondOrderFoundation.irrefl_l hℳ X hx
  · intro x _ y _ z hz hxy hyz
    rcases hTypes z hz with hz | rfl | ⟨n, m, rfl⟩
    · have hZ : SetTheory.Structure.IsOrdinal (quotient_l hℳ) z := by
        apply SetTheory.Structure.IsOrdinal.mem hα
        exact hz
      exact hZ.transitive y hyz x hxy
    · exact hα.transitive y hyz x hxy
    · exact transitive_l hℳ hG hS hα n m y hyz x hxy
  · intro x hx y hy
    rcases hTypes x hx with hx | rfl | ⟨n, m, rfl⟩
    · rcases hTypes y hy with hy | rfl | ⟨i, j, rfl⟩
      · exact hα.wellOrder.linear.compare x hx y hy
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inl ((reading_l hℳ hG hS i j x).mpr (Or.inl hx)))
    · rcases hTypes y hy with hy | rfl | ⟨i, j, rfl⟩
      · exact Or.inr (Or.inr hy)
      · exact Or.inl (fun _ => Iff.rfl)
      · exact Or.inr (Or.inl ((reading_l hℳ hG hS i j _).mpr (Or.inr (Or.inl rfl))))
    · rcases hTypes y hy with hy | rfl | ⟨i, j, rfl⟩
      · exact Or.inr (Or.inr ((reading_l hℳ hG hS n m y).mpr (Or.inl hy)))
      · exact Or.inr (Or.inr ((reading_l hℳ hG hS n m _).mpr (Or.inr (Or.inl rfl))))
      · rcases lex_compare_l hℳ n m i j with h | ⟨rfl, rfl⟩ | h
        · exact Or.inr (Or.inl ((reading_l hℳ hG hS i j _).mpr (Or.inr (Or.inr ⟨n, m, h, rfl⟩))))
        · exact Or.inl (fun _ => Iff.rfl)
        · exact Or.inr (Or.inr ((reading_l hℳ hG hS n m _).mpr (Or.inr (Or.inr ⟨i, j, h, rfl⟩))))

theorem ordinal_l (n m : num_l ℳ) :
    SetTheory.Structure.IsOrdinal (quotient_l hℳ) (tail_l hℳ hG hS n m) := by
  apply SecondOrderOrdinalSuccessor.ordinal_of_linear_l hℳ (code_l hℳ hG hS n m)
  · exact fun X Y hX hY => transitive_l hℳ hG hS hα n m (mk_l hℳ X) hX (mk_l hℳ Y) hY
  · apply linear_l hℳ hG hS hα
    intro x hx
    rcases (reading_l hℳ hG hS n m x).mp hx with hx | hx | ⟨i, j, _, hx⟩
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr ⟨i, j, hx⟩)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalDoubleTailOrder
